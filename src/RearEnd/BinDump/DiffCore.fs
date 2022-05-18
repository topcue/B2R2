module internal B2R2.RearEnd.BinDump.DiffCore

open System.Collections.Generic
open B2R2
open B2R2.FrontEnd.BinFile
open B2R2.FrontEnd.BinLifter
open B2R2.FrontEnd.BinInterface
open B2R2.RearEnd.BinDump.DisasmLiftHelper

open type System.IO.File

type DiffTag =
  | ContextHead
  | Equal
  | Remove
  | Insert

type DiffData = {
  Idx  : int[]
  Ha     : int[]
  Len : int
  mutable Rchg : bool[]
}

/// TODO: Rename it
type Detail =
  | AddrAsmPair of string * string[]
  | FuncSymbol of string
  | HexStr of string
  | EmptyStr

type DiffResult = {
  LengthA : int
  LengthB : int
  LinesA  : string[]
  LinesB  : string[]
  RchgA   : bool[]
  RchgB   : bool[]
}

type Details = {
  A : Detail[]
  B : Detail[]
}

let readFile filePath = filePath |> ReadLines |> Array.ofSeq

let rec findDiffstart n haA haB =
  if n >= min (Array.length haA) (Array.length haB) then 0
  elif haA[n] <> haB[n] then n
  else findDiffstart (n + 1) haA haB

let rec findDiffend n haA haB =
  if n >= min (Array.length haA) (Array.length haB) then 1
  elif haA[(Array.length haA - 1) - n] <> haB[(Array.length haB - 1) - n] then n
  else findDiffend (n + 1) haA haB

let trim haA haB (rindexA: int[]) (rindexB: int[]) =
  let diffStart = findDiffstart 0 haA haB
  let diffEnd = findDiffend 0 haA haB
  let haA' = haA[diffStart .. (Array.length haA - 1) - diffEnd]
  let haB' = haB[diffStart .. (Array.length haB - 1) - diffEnd]
  let rindexA' = rindexA[diffStart .. (Array.length rindexA - 1) - diffEnd]
  let rindexB' = rindexB[diffStart .. (Array.length rindexB - 1) - diffEnd]
  haA', haB', rindexA', rindexB'

let rec findUniqId lineNum cnt lines (dict: Dictionary<string, int>) =
  if lineNum = Array.length lines then dict
  else
    let isFound, _ = dict.TryGetValue lines[lineNum]
    if not isFound then
      dict.Add(lines[lineNum], cnt)
      findUniqId (lineNum + 1) (cnt + 1) lines dict
    else
      findUniqId (lineNum + 1) cnt lines dict

let rec findRchg lineNum rchg (lineToId: Dictionary<string, int>)
  (lines: string[]) =

  if lineNum = -1 then
    Array.ofList rchg
  else
    let isFound, _ = lineToId.TryGetValue lines[lineNum]
    if isFound then
      findRchg (lineNum - 1) (false :: rchg) lineToId lines
    else
      findRchg (lineNum - 1) (true :: rchg) lineToId lines

let rec buildRindex lineNum index (lineToId: Dictionary<string, int>)
  (lines: string[]) =

  if lineNum = -1 then
    Array.ofList index
  else
    let isFound, id = lineToId.TryGetValue lines[lineNum]
    let index' = if isFound then id :: index else -1 :: index
    buildRindex (lineNum - 1) index' lineToId lines

let rec buildHaRindex n ha rindex (rchg: bool[])
  (lineToId: Dictionary<string,int>) lines =

  if n = Array.length lines then
    ha, rindex
  elif rchg[n] then
    buildHaRindex (n + 1) ha rindex rchg lineToId lines
  else
    let ha' = Array.append ha [| lineToId[lines[n]] |]
    let rindex' = Array.append rindex [| n |]
    buildHaRindex (n + 1) ha' rindex' rchg lineToId lines

let prepareMyersFamily linesA linesB =
  let lineToIdA =
    Dictionary<string, int> ()
    |> findUniqId 0 0 linesA
  let lineToIdB =
    Dictionary<string, int> ()
    |> findUniqId 0 0 linesB
  let rchgA = findRchg (Array.length linesA - 1) [ ] lineToIdB linesA
  let rchgB = findRchg (Array.length linesB - 1) [ ] lineToIdA linesB
  let haA, rindexA = buildHaRindex 0 [| |] [| |] rchgA lineToIdA linesA
  let haB, rindexB = buildHaRindex 0 [| |] [| |] rchgB lineToIdA linesB

  let haA, haB, rindexA, rindexB = trim haA haB rindexA rindexB
  let dd1 = { Idx = rindexA; Ha = haA; Rchg = rchgA; Len = Array.length rindexA}
  let dd2 = { Idx = rindexB; Ha = haB; Rchg = rchgB; Len = Array.length rindexB}
  dd1, dd2

let prepareHistogramFamily linesA linesB =
  let lenA = Array.length linesA
  let lenB = Array.length linesB
  let lineToId =
    Dictionary<string, int> ()
    |> findUniqId 0 0 linesA
  let dd1 =
    { Idx = buildRindex (lenA - 1) [ ] lineToId linesA;
      Rchg = Array.init lenA (fun _ -> false)
      Ha = [| |]; Len = lenA }
  let dd2 =
    { Idx = buildRindex (lenB - 1) [ ] lineToId linesB
      Rchg = Array.init lenB (fun _ -> false)
      Ha = [| |]; Len = lenB }
  dd1, dd2

let detailsToStr details =
  Array.collect (fun d ->
    match d with
    | AddrAsmPair(_, asm) -> [| String.concat "" asm |]
    | FuncSymbol(sym) -> [| sym |]
    | HexStr(str) -> [| str |]
    | EmptyStr(_) -> [| "" |]) details

let splitStr xs = Array.collect (fun x -> [| string x |]) xs

let buildAddrAndAsm words wordSize addr =
  let addrStr = Addr.toString wordSize addr
  addrStr, (ConvertToDisasmNoColorStr words)

let regularDisBuilder (hdl: BinHandle) (bp: BinaryPointer) (ins: Instruction) =
  let words = ins.Decompose (false)
  let wordSize = hdl.FileInfo.WordSize
  buildAddrAndAsm words wordSize bp.Addr

let buildFuncSymbol (dict: Dictionary<Addr, string>) addr =
  match (dict: Dictionary<Addr, string>).TryGetValue (addr) with
  | true, name -> String.wrapAngleBracket name
  | false, _ -> ""

[<AbstractClass>]
type BinBuilder (hdl, cfg, isLift) =
  abstract member BuildFuncSymbol: Addr -> string
  abstract member BuildInstr:
    BinHandle -> BinaryPointer -> Instruction -> string * string[]
  abstract member UpdateMode: BinHandle -> Addr -> unit

  member __.buildDetail hdl bp details =
    if BinaryPointer.IsValid bp then
      let funcSym = __.BuildFuncSymbol bp.Addr
      let details =
        if funcSym <> "" then FuncSymbol(funcSym) :: EmptyStr :: details
        else details
      match BinHandle.TryParseInstr (hdl, bp=bp) with
      | Ok (ins) ->
        let bp' = BinaryPointer.Advance bp (int ins.Length)
        let details' = AddrAsmPair(__.BuildInstr hdl bp ins) :: details
        __.buildDetail hdl bp' details'
      | Error _ ->
        __.buildDetail hdl (handleInvalidIns hdl bp isLift cfg) details
    else details, bp

  member __.Build bp details =
    fst (__.buildDetail hdl bp details)
    |> List.toArray
    |> Array.rev

[<AbstractClass>]
type BinFuncBuilder (hdl, cfg, isLift) =
  inherit BinBuilder (hdl, cfg, isLift)
  let dict = makeFuncSymbolDic hdl
  override _.BuildFuncSymbol addr = buildFuncSymbol dict addr

type MyBuilder (hdl, cfg) =
  inherit BinFuncBuilder (hdl, cfg, false)
  override _.BuildInstr hdl bp ins = regularDisBuilder hdl bp ins
  override _.UpdateMode _ _ = ()
