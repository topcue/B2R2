(*
  B2R2 - the Next-Generation Reversing Platform

  Copyright (c) SoftSec Lab. @ KAIST, since 2016

  Permission is hereby granted, free of charge, to any person obtaining a copy
  of this software and associated documentation files (the "Software"), to deal
  in the Software without restriction, including without limitation the rights
  to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
  copies of the Software, and to permit persons to whom the Software is
  furnished to do so, subject to the following conditions:

  The above copyright notice and this permission notice shall be included in all
  copies or substantial portions of the Software.

  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
  IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
  FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
  AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
  LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
  OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
  SOFTWARE.
*)

module B2R2.RearEnd.BinDump.Program

open B2R2
open B2R2.FrontEnd.BinFile
open B2R2.FrontEnd.BinInterface
open B2R2.RearEnd
open B2R2.RearEnd.BinDump.DisasmLiftHelper
open B2R2.RearEnd.BinDump.DiffCore
open B2R2.RearEnd.BinDump.MyersDiff
open B2R2.RearEnd.BinDump.HistogramDiff
open B2R2.RearEnd.BinDump.DiffPrintHelper

open OutString

let [<Literal>] private toolName = "bindump"
let [<Literal>] private usageTail = "<binary file(s) | -s hexstring>"

let private printFileName (filepath: string) =
  out.PrintLine (String.wrapSqrdBracket filepath)
  out.PrintLine ()

let private getTableConfig hdl isLift =
  if isLift then [ LeftAligned 10 ]
  else
    let addrWidth = WordSize.toByteWidth hdl.ISA.WordSize * 2
    let binaryWidth =
      match hdl.ISA.Arch with
      | Arch.IntelX86 | Arch.IntelX64 -> 36
      | _ -> 16
    [ LeftAligned addrWidth; LeftAligned binaryWidth; LeftAligned 10 ]

let private isARM32 hdl =
  match hdl.ISA.Arch with
  | Arch.ARMv7
  | Arch.AARCH32 -> true
  | _ -> false

let private makeCodePrinter hdl cfg (opts: BinDumpOpts) =
  let opti = getOptimizer opts
  if isARM32 hdl then
    if opts.ShowLowUIR then
      ContextSensitiveCodeIRPrinter (hdl, cfg, opti) :> BinPrinter
    else
      let showSymb, showColor = opts.ShowSymbols, opts.ShowColor
      ContextSensitiveCodeDisasmPrinter (hdl, cfg, showSymb, showColor)
      :> BinPrinter
  else
    if opts.ShowLowUIR then BinCodeIRPrinter (hdl, cfg, opti) :> BinPrinter
    else
      let showSymb, showColor = opts.ShowSymbols, opts.ShowColor
      BinCodeDisasmPrinter (hdl, cfg, showSymb, showColor) :> BinPrinter

let private makeTablePrinter hdl cfg (opts: BinDumpOpts) =
  let opti = getOptimizer opts
  if isARM32 hdl then
    if opts.ShowLowUIR then
      ContextSensitiveTableIRPrinter (hdl, cfg, opti) :> BinPrinter
    else
      ContextSensitiveTableDisasmPrinter (hdl, cfg) :> BinPrinter
  else
    if opts.ShowLowUIR then BinTableIRPrinter (hdl, cfg, opti) :> BinPrinter
    else BinTableDisasmPrinter (hdl, cfg) :> BinPrinter

let private dumpRawBinary (hdl: BinHandle) (opts: BinDumpOpts) cfg =
  let bp = hdl.FileInfo.ToBinaryPointer hdl.FileInfo.BaseAddress
  let prn = makeCodePrinter hdl cfg opts
  prn.Print bp
  out.PrintLine ()

let printHexdump (opts: BinDumpOpts) sec hdl =
  let bp = BinaryPointer.OfSection sec
  let bytes = BinHandle.ReadBytes (hdl, bp=bp, nBytes=int sec.Size)
  let chunkSize = if opts.ShowWide then 32 else 16
  HexDumper.dump chunkSize hdl.FileInfo.WordSize opts.ShowColor bp.Addr bytes
  |> Array.iter out.PrintLine

let private hasNoContent (sec: Section) (fi: FileInfo) =
  match fi with
  | :? ELFFileInfo as fi ->
    match fi.ELF.SecInfo.SecByName.TryFind sec.Name with
    | Some section -> section.SecType = ELF.SectionType.SHTNoBits
    | None -> true
  | _ -> false

let dumpHex (opts: BinDumpOpts) (sec: Section) hdl =
  if hasNoContent sec hdl.FileInfo then
    out.PrintTwoCols "" "NOBITS section."
  else printHexdump opts sec hdl
  out.PrintLine ()

let private createBinHandleFromPath (opts: BinDumpOpts) filepath =
  BinHandle.Init (
    opts.ISA,
    opts.ArchOperationMode,
    opts.AutoDetect,
    opts.BaseAddress,
    fileName=filepath)

let private isRawBinary hdl =
  match hdl.FileInfo.FileFormat with
  | FileFormat.ELFBinary
  | FileFormat.MachBinary
  | FileFormat.PEBinary -> false
  | _ -> true

let private printCodeOrTable (printer: BinPrinter) sec =
  printer.Print (BinaryPointer.OfSection sec)
  out.PrintLine ()

let private buildCodeOrTable (builder: BinBuilder) sec =
  builder.Build (BinaryPointer.OfSection sec) [ ]

let initHandleForTableOutput hdl =
  match hdl.ISA.Arch with
  (* For ARM PLTs, we just assume the ARM mode (if no symbol is given). *)
  | Arch.ARMv7
  | Arch.AARCH32 -> hdl.Parser.OperationMode <- ArchOperationMode.ARMMode
  | _ -> ()

let private dumpSections hdl (opts: BinDumpOpts) (sections: seq<Section>) cfg =
  let mymode = hdl.Parser.OperationMode
  let codeprn = makeCodePrinter hdl cfg opts
  let tableprn = makeTablePrinter hdl cfg opts
  sections
  |> Seq.iter (fun s ->
    if s.Size > 0UL then
      out.PrintSectionTitle (String.wrapParen s.Name)
      match s.Kind with
      | SectionKind.ExecutableSection ->
        hdl.Parser.OperationMode <- mymode
        printCodeOrTable codeprn s
      | SectionKind.LinkageTableSection ->
        initHandleForTableOutput hdl
        printCodeOrTable tableprn s
      | _ ->
        if opts.OnlyDisasm then printCodeOrTable codeprn s
        else dumpHex opts s hdl
    else ())

let private dumpRegularFile hdl (opts: BinDumpOpts) cfg =
  opts.ShowSymbols <- true
  match opts.InputSecName with
  | Some secname ->
    dumpSections hdl opts (hdl.FileInfo.GetSections (secname)) cfg
  | None ->
    dumpSections hdl opts (hdl.FileInfo.GetSections ()) cfg

let dumpFile (opts: BinDumpOpts) filepath =
  opts.ShowAddress <- true
  let hdl = createBinHandleFromPath opts filepath
  let cfg = getTableConfig hdl opts.ShowLowUIR
  printFileName hdl.FileInfo.FilePath
  if isRawBinary hdl then dumpRawBinary hdl opts cfg
  else dumpRegularFile hdl opts cfg

let dumpFileMode files (opts: BinDumpOpts) =
  match List.partition System.IO.File.Exists files with
  | [], [] ->
    Printer.printErrorToConsole "File(s) must be given."
    CmdOpts.PrintUsage toolName usageTail Cmd.spec
  | files, [] -> files |> List.iter (dumpFile opts)
  | _, errs ->
    Printer.printErrorToConsole ("File(s) " + errs.ToString() + " not found!")

let private assertBinaryLength hdl hexstr =
  let multiplier = getInstructionAlignment hdl
  if (Array.length hexstr) % multiplier = 0 then ()
  else
    Printer.printErrorToConsole <|
      "The hex string length must be multiple of " + multiplier.ToString ()
    exit 1

let dumpHexStringMode (opts: BinDumpOpts) =
  let hdl = BinHandle.Init (opts.ISA,
                            opts.ArchOperationMode,
                            false,
                            opts.BaseAddress,
                            opts.InputHexStr)
  let cfg = getTableConfig hdl opts.ShowLowUIR
  assertBinaryLength hdl opts.InputHexStr
  opts.ShowColor <- true
  let printer = makeCodePrinter hdl cfg opts
  let baseAddr = defaultArg opts.BaseAddress 0UL
  let bp = BinaryPointer (baseAddr, 0, opts.InputHexStr.Length)
  printer.Print bp
  out.PrintLine ()

let private buildHexdump (opts: BinDumpOpts) sec hdl =
  let bp = BinaryPointer.OfSection sec
  let bytes = BinHandle.ReadBytes (hdl, bp=bp, nBytes=int sec.Size)
  let chunkSize = if opts.ShowWide then 32 else 16
  HexDumper.dumpWithoutAddr chunkSize hdl.FileInfo.WordSize bp.Addr bytes
  |> Array.collect (fun x -> [| HexStr(toString x) |])

let private myDumpHex (opts: BinDumpOpts) (sec: Section) hdl =
  if hasNoContent sec hdl.FileInfo then
    [| HexStr(""); HexStr("NOBITS section.") |]
  else buildHexdump opts sec hdl

let private diffTwoLines linesA linesB diff prepare =
  let rchgA, rchgB =
    (linesA, linesB)
    ||> prepare
    ||> diff
  { LengthA = Array.length linesA
    LengthB = Array.length linesB
    LinesA = linesA
    LinesB = linesB
    RchgA = rchgA
    RchgB = rchgB }

let private diffBinarySection detailsA detailsB (opts: BinDumpOpts) =
  let linesA = detailsToStr detailsA
  let linesB = detailsToStr detailsB
  let prepare, diff =
    if opts.HistogramDiff then prepareHistogramFamily, histogramDiff
    else prepareHistogramFamily, histogramDiff
  let diffResult = diffTwoLines linesA linesB diff prepare
  let details = { A = detailsA; B = detailsB }
  printDiffResult diffResult details diff prepare

let private getDetailsFromSection sec hdl builder (opts: BinDumpOpts) =
  match sec.Kind with
  | SectionKind.ExecutableSection ->
    buildCodeOrTable builder sec
  | SectionKind.LinkageTableSection ->
    initHandleForTableOutput hdl
    buildCodeOrTable builder sec
  | _ ->
    if opts.OnlyDisasm then buildCodeOrTable builder sec
    else myDumpHex opts sec hdl

let private diffForMetric detailsA detailsB (opts: BinDumpOpts) secName =
  let linesA = detailsToStr detailsA
  let linesB = detailsToStr detailsB
  let prepare, diff =
    if opts.MyersDiff then prepareMyersFamily, myersDiff
    else prepareHistogramFamily, histogramDiff
  let diffResult = diffTwoLines linesA linesB diff prepare

  let NLD = diffResult.RchgA |> Array.filter (fun e -> e = true ) |> Array.length
  let NLA = diffResult.RchgB |> Array.filter (fun e -> e = true ) |> Array.length
  if NLA = 0 && NLD = 0 then ()
  else
    printfn "[*] Section: %s" secName
    printfn "[*] LNA: %A" NLA
    printfn "[*] LND: %A" NLD
    printfn ""

let diffBinWithHdl hdlA hdlB cfg (opts: BinDumpOpts) =
  let sectionsA = hdlA.FileInfo.GetSections ()
  let sectionsB = hdlB.FileInfo.GetSections ()
  let builderA = MyBuilder (hdlA, cfg) :> BinBuilder
  let builderB = MyBuilder (hdlB, cfg) :> BinBuilder
  (sectionsA, sectionsB)
  ||> Seq.iter2 (fun secA secB ->
    if secA.Size > 0UL && secB.Size > 0UL then
      let detailsA = getDetailsFromSection secA hdlA builderA opts
      let detailsB = getDetailsFromSection secB hdlB builderB opts
      if opts.ShowDiff then
        printDiffSectionsName secA.Name secB.Name
        diffBinarySection detailsA detailsB opts
      elif opts.MultipleDiff then
        diffForMetric detailsA detailsB opts secA.Name

    else ())

let diffTextFile (opts: BinDumpOpts) (filepaths: string list) =
  let linesA = readFile filepaths[0]
  let linesB = readFile filepaths[1]
  let prepare, diff =
    if opts.HistogramDiff then prepareHistogramFamily, histogramDiff
    else prepareHistogramFamily, histogramDiff
  let result = diffTwoLines linesA linesB diff prepare

  if opts.ShowDiff then
    printDiffResult' result diff prepare
  elif opts.MultipleDiff then
    printfn "[*] Multiple Diff"


let diffBinaryFile (opts: BinDumpOpts) (filepaths: string list) =
  opts.ShowAddress <- true
  let hdlA = createBinHandleFromPath opts filepaths[0]
  let hdlB = createBinHandleFromPath opts filepaths[1]
  let cfg = getTableConfig hdlA opts.ShowLowUIR
  if not opts.MultipleDiff then
    printDiffFilesName hdlA.FileInfo.FilePath hdlB.FileInfo.FilePath
  if isRawBinary hdlA then
    (* dumpRawBinary hdl opts cfg *)
    Printer.printErrorToConsole "Not implemented!"
  else
    diffBinWithHdl hdlA hdlB cfg opts

let diffMode (files: string list) (opts: BinDumpOpts) =
  match List.partition System.IO.File.Exists files with
  | [], [] ->
    Printer.printErrorToConsole "Files must be given."
    CmdOpts.PrintUsage toolName usageTail Cmd.spec
  | files, [] ->
    if opts.TextDiff then files |> diffTextFile opts
    else files |> diffBinaryFile opts
  | _, errs ->
    Printer.printErrorToConsole ("File(s) " + errs.ToString() + " not found!")

let multipleDiffMode (files: string list) (opts: BinDumpOpts) =
  let rec loop (paths: string list) opts =
    match paths with
    | h::t ->
      let files = h.Split [|' '|] |> List.ofArray
      printfn "================================================================"
      printfn "[*] fileA: %s" files[0]
      printfn "[*] fileB: %s" files[1]
      printfn ""
      diffMode files opts
      loop t opts
    | _ -> ()

  let paths = readFile files[0] |> List.ofArray
  loop paths opts

let private dump files (opts: BinDumpOpts) =
#if DEBUG
  let sw = System.Diagnostics.Stopwatch.StartNew ()
#endif
  CmdOpts.SanitizeRestArgs files
  try
    if opts.ShowDiff then diffMode files opts
    elif opts.MultipleDiff then multipleDiffMode files opts
    elif Array.isEmpty opts.InputHexStr then dumpFileMode files opts
    else dumpHexStringMode opts
  finally
    out.Flush ()
#if DEBUG
  sw.Stop ()
  eprintfn "Total dump time: %f sec." sw.Elapsed.TotalSeconds
#endif

[<EntryPoint>]
let main args =
  let opts = BinDumpOpts ()
  CmdOpts.ParseAndRun dump toolName usageTail Cmd.spec opts args
