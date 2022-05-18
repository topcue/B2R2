module internal B2R2.RearEnd.BinDump.DiffPrintHelper

open B2R2
open B2R2.RearEnd.BinDump.DisasmLiftHelper
open B2R2.RearEnd.BinDump.DiffCore

let isLineEqual aPtr bPtr result =
  not result.RchgA[aPtr] && not result.RchgB[bPtr]

let isLineAdded ptr result = not result.RchgA[ptr]

let isLineDeleted ptr result = not result.RchgB[ptr]

let getDiffType aPtr bPtr result =
  if isLineEqual aPtr bPtr result then 'E'
  elif isLineAdded aPtr result then 'A'
  elif isLineDeleted bPtr result then 'D'
  else 'R'

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

let printDiffFilesName fnameA fnameB =
  printLineOnLeftSide NoColor EmptyStr (String.wrapSqrdBracket fnameA)
  printLineOnRightSide NoColor EmptyStr (String.wrapSqrdBracket fnameB)

let printDiffSectionsName secA secB =
  colorout.PrintLine ()
  printLineOnLeftSide Blue EmptyStr (String.wrapParen secA)
  printLineOnRightSide Blue EmptyStr (String.wrapParen secB)

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

let doFinerDiffDataSection aPtr bPtr result diffAlgo prepare =
  let finerLinesA = result.LinesA[aPtr] |> Seq.toArray |> splitStr
  let finerLinesB = result.LinesB[bPtr] |> Seq.toArray |> splitStr

  (finerLinesA, finerLinesB)
  ||> prepare
  ||> diffAlgo
  ||> printFinerDiffResult finerLinesA finerLinesB "" ""

let doFinerDiffCodeSection aPtr bPtr result details diffAlgo prepare =
  let finerLinesA, addrA =
    match details.A[aPtr] with
    | AddrAsmPair(addr, asm) -> asm, addr + ": "
    | FuncSymbol(sym) -> [| sym |], ""
    | _ -> [| "" |], ""
  let finerLinesB, addrB =
    match details.B[bPtr] with
    | AddrAsmPair(addr, asm) -> asm, addr + ": "
    | FuncSymbol(sym) -> [| sym |], ""
    | _ -> [| "" |], ""

  (finerLinesA, finerLinesB)
  ||> prepare
  ||> diffAlgo
  ||> printFinerDiffResult finerLinesA finerLinesB addrA addrB

let doFineGranularityDiff aPtr bPtr result details diffAlgo prepare =
  match details.A[aPtr] with
  | HexStr(_) -> doFinerDiffDataSection aPtr bPtr result diffAlgo prepare
  | _ -> doFinerDiffCodeSection aPtr bPtr result details diffAlgo prepare

/// for binary file diff
let rec printDiffSideBySide aPtr bPtr result details diffAlgo prepare =
  if aPtr = result.LengthA || bPtr = result.LengthB then aPtr, bPtr
  else
    match getDiffType aPtr bPtr result with
    | 'E' ->
      printLineOnLeftSide NoColor details.A[aPtr] result.LinesA[aPtr]
      printLineOnRightSide NoColor details.B[bPtr] result.LinesB[bPtr]
      printDiffSideBySide (aPtr + 1) (bPtr + 1) result details diffAlgo prepare
    | 'A' ->
      printLineOnLeftSide NoColor EmptyStr ""
      printLineOnRightSide Green details.B[bPtr] result.LinesB[bPtr]
      printDiffSideBySide aPtr (bPtr + 1) result details diffAlgo prepare
    | 'D' ->
      printLineOnLeftSide Red details.A[aPtr] result.LinesA[aPtr]
      printLineOnRightSide NoColor EmptyStr ""
      printDiffSideBySide (aPtr + 1) bPtr result details diffAlgo prepare
    | 'R' ->
      doFineGranularityDiff aPtr bPtr result details diffAlgo prepare
      printDiffSideBySide (aPtr + 1) (bPtr + 1) result details diffAlgo prepare
    | _ -> (0, 0)

/// for text file diff
let rec printDiffSideBySide' aPtr bPtr result diffAlgo prepare =
  if aPtr = result.LengthA || bPtr = result.LengthB then
    aPtr, bPtr
  else
    match getDiffType aPtr bPtr result with
    | 'E' ->
      printLineOnLeftSide NoColor EmptyStr result.LinesA[aPtr]
      printLineOnRightSide NoColor EmptyStr result.LinesB[bPtr]
      printDiffSideBySide' (aPtr + 1) (bPtr + 1) result diffAlgo prepare
    | 'A' ->
      printLineOnLeftSide NoColor EmptyStr ""
      printLineOnRightSide Green EmptyStr result.LinesB[bPtr]
      printDiffSideBySide' aPtr (bPtr + 1) result diffAlgo prepare
    | 'D' ->
      printLineOnLeftSide Red EmptyStr result.LinesA[aPtr]
      printLineOnRightSide NoColor EmptyStr ""
      printDiffSideBySide' (aPtr + 1) bPtr result diffAlgo prepare
    | 'R' ->
      printLineOnLeftSide Red EmptyStr result.LinesA[aPtr]
      printLineOnRightSide Green EmptyStr result.LinesB[bPtr]
      printDiffSideBySide' (aPtr + 1) (bPtr + 1) result diffAlgo prepare
    | _ -> (0, 0)

/// for binary file diff
let rec printRemainingRightSide bPtr result details =
  if bPtr = result.LengthB then ()
  else
    printLineOnLeftSide NoColor EmptyStr ""
    if isLineDeleted bPtr result then
      printLineOnRightSide NoColor details.B[bPtr] result.LinesB[bPtr]
    else
      printLineOnRightSide Green details.B[bPtr] result.LinesB[bPtr]
    printRemainingRightSide (bPtr + 1) result details

/// for text file diff
let rec printRemainingRightSide' bPtr result =
  if bPtr = result.LengthB then ()
  else
    printLineOnLeftSide NoColor EmptyStr ""
    if isLineDeleted bPtr result then
      printLineOnRightSide NoColor EmptyStr result.LinesB[bPtr]
    else
      printLineOnRightSide Green EmptyStr result.LinesB[bPtr]
    printRemainingRightSide' (bPtr + 1) result

/// for binary file diff
let rec printRemainingLeftSide aPtr result details =
  if aPtr = result.LengthA then ()
  else
    if isLineAdded aPtr result then
      printLineOnLeftSide NoColor details.A[aPtr] result.LinesB[aPtr]
    else
      printLineOnLeftSide Red details.A[aPtr] result.LinesB[aPtr]
    printLineOnRightSide NoColor EmptyStr ""
    printRemainingLeftSide (aPtr + 1) result details

/// for text file diff
let rec printRemainingLeftSide' aPtr result =
  if aPtr = result.LengthA then ()
  else
    if isLineAdded aPtr result then
      printLineOnLeftSide NoColor EmptyStr result.LinesB[aPtr]
    else
      printLineOnLeftSide Red EmptyStr result.LinesB[aPtr]
    printLineOnRightSide NoColor EmptyStr ""
    printRemainingLeftSide' (aPtr + 1) result

/// for binary file diff
let printDiffResult result details diffAlgo prepare =
  let aPtr, bPtr =
    printDiffSideBySide 0 0 result details diffAlgo prepare
  if aPtr < result.LengthA then
    printRemainingLeftSide aPtr result details
  if bPtr < result.LengthB then
    printRemainingRightSide bPtr result details

/// for text file diff
let printDiffResult' result diffAlgo prepare =
  let aPtr, bPtr =
    printDiffSideBySide' 0 0 result diffAlgo prepare
  if aPtr < result.LengthA then
    printRemainingLeftSide' aPtr result
  if bPtr < result.LengthB then
    printRemainingRightSide' bPtr result
