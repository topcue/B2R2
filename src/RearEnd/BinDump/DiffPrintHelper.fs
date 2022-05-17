module internal B2R2.RearEnd.BinDump.DiffPrintHelper

open B2R2
open B2R2.RearEnd.BinDump.DisasmLiftHelper
open B2R2.RearEnd.BinDump.DiffCore

let printLineOnLeftSide color detail (line: string) =
  let addr =
    match detail with
    | AddrAsmPair(addr, _) -> addr + ": "
    | _ -> ""
  let padSz = System.Console.WindowWidth / 2 - String.length addr
  colorout.Print [ NoColor, addr ]
  colorout.Print [ color, line.PadRight padSz ]

let printLineOnRightSide color detail line =
  let addr =
    match detail with
    | AddrAsmPair(addr, _) -> addr + ": "
    | _ -> ""
  colorout.Print [ NoColor, addr ]
  colorout.Print [ color, line ]
  colorout.PrintLine ()

let printColorExceptSpace color line =
  line
  |> String.iter (fun ch ->
    match ch with
    | ' ' -> colorout.Print [ NoColor, " " ]
    | _ -> colorout.Print [ color, string ch ])

let printHighlightColor rchg (strs: string[]) color colorHighlight =
  rchg
  |> Array.iteri (fun i x ->
    match x with
    | true -> printColorExceptSpace colorHighlight strs[i]
    | false -> colorout.Print [ color, strs[i] ] )

let printFinerDiffResult (lineA: string[]) (lineB: string[]) addrA addrB
  rchgA rchgB =

  let halfWidth = System.Console.WindowWidth / 2
  let lenA = lineA |> Array.sumBy (fun s -> s.Length)
  let skipSz = lenA + String.length addrA
  (* Print left side *)
  colorout.Print [ NoColor, addrA ]
  printHighlightColor rchgA lineA Red RedHighlight
  colorout.Print [ NoColor, "".PadRight (halfWidth - skipSz) ]
  (* Print right side *)
  colorout.Print [ NoColor, addrB ]
  printHighlightColor rchgB lineB Green GreenHighlight
  colorout.PrintLine ()

let printDiffFilesName fnameA fnameB =
  printLineOnLeftSide NoColor EmptyStr (String.wrapSqrdBracket fnameA)
  printLineOnRightSide NoColor EmptyStr (String.wrapSqrdBracket fnameB)

let printDiffSectionsName secA secB =
  colorout.PrintLine ()
  printLineOnLeftSide Blue EmptyStr (String.wrapParen secA)
  printLineOnRightSide Blue EmptyStr (String.wrapParen secB)

let doFinerDiffDataSection aPtr bPtr result prepare diffAlgo =
  let finerLinesA = result.LinesA[aPtr] |> Seq.toArray |> splitStr
  let finerLinesB = result.LinesB[bPtr] |> Seq.toArray |> splitStr

  (finerLinesA, finerLinesB)
  ||> prepare
  ||> diffAlgo
  ||> printFinerDiffResult finerLinesA finerLinesB "" ""


let doFinerDiffCodeSection aPtr bPtr result prepare diffAlgo =
  let finerLinesA, addrA =
    match result.DetailA[aPtr] with
    | AddrAsmPair(addr, asm) -> asm, addr + ": "
    | FuncSymbol(sym) -> [| sym |], ""
    | _ -> [| "" |], ""
  let finerLinesB, addrB =
    match result.DetailB[bPtr] with
    | AddrAsmPair(addr, asm) -> asm, addr + ": "
    | FuncSymbol(sym) -> [| sym |], ""
    | _ -> [| "" |], ""

  (finerLinesA, finerLinesB)
  ||> prepare
  ||> diffAlgo
  ||> printFinerDiffResult finerLinesA finerLinesB addrA addrB

let doFineGranularityDiff aPtr bPtr result prepare diffAlgo =
  match result.DetailA[aPtr] with
  | HexStr(_) -> doFinerDiffDataSection aPtr bPtr result prepare diffAlgo
  | _ -> doFinerDiffCodeSection aPtr bPtr result prepare diffAlgo

let rec printDiffLeftRightSide aPtr bPtr result prepare diffAlgo =
  if aPtr = result.LengthA || bPtr = result.LengthB then aPtr, bPtr
  elif not result.RchgA[aPtr] && not result.RchgB[bPtr] then
    printLineOnLeftSide NoColor result.DetailA[aPtr] result.LinesA[aPtr]
    printLineOnRightSide NoColor result.DetailB[bPtr] result.LinesB[bPtr]
    printDiffLeftRightSide (aPtr + 1) (bPtr + 1) result prepare diffAlgo
  elif not result.RchgA[aPtr] then
    printLineOnLeftSide NoColor EmptyStr ""
    printLineOnRightSide Green result.DetailB[bPtr] result.LinesB[bPtr]
    printDiffLeftRightSide aPtr (bPtr + 1) result prepare diffAlgo
  elif not result.RchgB[bPtr] then
    printLineOnLeftSide Red result.DetailA[aPtr] result.LinesA[aPtr]
    printLineOnRightSide NoColor EmptyStr ""
    printDiffLeftRightSide (aPtr + 1) bPtr result prepare diffAlgo
  else
    doFineGranularityDiff aPtr bPtr result prepare diffAlgo
    printDiffLeftRightSide (aPtr + 1) (bPtr + 1) result prepare diffAlgo

let rec printRestOfRightSide bPtr result =
  if bPtr = result.LengthB then ()
  else
    printLineOnLeftSide NoColor EmptyStr ""
    if not result.RchgB[bPtr] then
      printLineOnRightSide NoColor result.DetailB[bPtr] result.LinesB[bPtr]
    else
      printLineOnRightSide Green result.DetailB[bPtr] result.LinesB[bPtr]
    printRestOfRightSide (bPtr + 1) result

let rec printRestOfLeftSide aPtr result =
  if aPtr = result.LengthA then ()
  else
    if not result.RchgA[aPtr] then
      printLineOnLeftSide NoColor result.DetailA[aPtr] result.LinesB[aPtr]
    else
      printLineOnLeftSide Red result.DetailA[aPtr] result.LinesB[aPtr]
    printLineOnRightSide NoColor EmptyStr ""
    printRestOfLeftSide (aPtr + 1) result

let printDiffSideBySide result prepare diffAlgo =
  let aPtr, bPtr = printDiffLeftRightSide 0 0 result prepare diffAlgo
  if aPtr < result.LengthA then printRestOfLeftSide aPtr result
  if bPtr < result.LengthB then printRestOfRightSide bPtr result
