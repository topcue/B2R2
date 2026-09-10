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

namespace B2R2.RearEnd.Transformer

open System
open System.Collections.Generic
open System.Text.Json
open B2R2
open B2R2.RearEnd.Transformer.Utils

type DiffAlgorithm =
  | Myers
  | Histogram

type DiffFormat =
  | SideBySide
  | Summary
  | Json

type DiffOptions =
  { Algorithm: DiffAlgorithm
    Format: DiffFormat
    Context: int option
    Width: int
    UseColor: bool }
with
  static member Default =
    { Algorithm = Myers
      Format = SideBySide
      Context = None
      Width = 16
      UseColor = true }

type DiffMetrics =
  { LeftLength: int
    RightLength: int
    Equal: int
    Added: int
    Removed: int
    Similarity: float }

type DiffPair =
  { Left: int option
    Right: int option
    Changed: bool }

type KVecDim =
  { XOffsets: int[]
    IdxForward: int
    IdxBackward: int }

type OverlappedPosition =
  { X: int
    Y: int }

type Box =
  { XOff: int
    XLim: int
    YOff: int
    YLim: int }

type DiffData =
  { LineNo: int[]
    LineID: int[]
    ChangedLineNumbers: bool[]
    Len: int }

/// The `diff` action.
type DiffAction() =
  let parsePositive (name: string) (value: string) =
    match Int32.TryParse value with
    | true, parsed when parsed > 0 -> parsed
    | _ -> invalidArg name $"{name} must be a positive integer."

  let parseNonnegative (name: string) (value: string) =
    match Int32.TryParse value with
    | true, parsed when parsed >= 0 -> parsed
    | _ -> invalidArg name $"{name} must be a nonnegative integer."

  let parseOptions (args: string list) =
    args
    |> List.fold (fun (opts: DiffOptions) (arg: string) ->
      match arg.ToLowerInvariant().Split('=', 2) with
      | [| "myers" |] ->
        { opts with Algorithm = Myers }
      | [| "histogram" |] ->
        { opts with Algorithm = Histogram }
      | [| "side-by-side" |] ->
        { opts with Format = SideBySide }
      | [| "summary" |] ->
        { opts with Format = Summary }
      | [| "json" |] ->
        { opts with Format = Json }
      | [| "no-color" |] ->
        { opts with UseColor = false }
      | [| "context"; value |] ->
        { opts with Context = Some(parseNonnegative "context" value) }
      | [| "width"; value |] ->
        { opts with Width = parsePositive "width" value }
      | _ ->
        invalidArg (nameof args) $"Invalid diff option: {arg}"
    ) DiffOptions.Default

  let rec findUniqId lineNum cnt lines (dict: Dictionary<_, int>) =
    if lineNum = Array.length lines then
      dict
    else
      let found, _ = dict.TryGetValue lines[lineNum]
      if not found then
        dict.Add(lines[lineNum], cnt)
        findUniqId (lineNum + 1) (cnt + 1) lines dict
      else
        findUniqId (lineNum + 1) cnt lines dict

  let rec findChangedLines lineNum rchg lineToId (lines: _[]) =
    if lineNum = -1 then
      Array.ofList rchg
    else
      let found, _ = (lineToId: Dictionary<_, _>).TryGetValue lines[lineNum]
      if found then
        findChangedLines (lineNum - 1) (false :: rchg) lineToId lines
      else
        findChangedLines (lineNum - 1) (true :: rchg) lineToId lines

  let rec matchIndices n
                       lineID
                       rindex
                       (rchg: bool[])
                       (lineToId: Dictionary<_, int>)
                       lines =
    if n = Array.length lines then
      lineID, rindex
    elif rchg[n] then
      matchIndices (n + 1) lineID rindex rchg lineToId lines
    else
      let lineID' = Array.append lineID [| lineToId[lines[n]] |]
      let rindex' = Array.append rindex [| n |]
      matchIndices (n + 1) lineID' rindex' rchg lineToId lines

  let rec findDiffstart n idA idB =
    if n >= min (Array.length idA) (Array.length idB) then 0
    elif idA[n] <> idB[n] then n
    else findDiffstart (n + 1) idA idB

  let rec findDiffend n idA idB =
    if n >= min (Array.length idA) (Array.length idB) then
      1
    elif idA[(Array.length idA - 1) - n] <> idB[(Array.length idB - 1) - n] then
      n
    else
      findDiffend (n + 1) idA idB

  let trim idA idB (lnumA: int[]) (lnumB: int[]) =
    let diffStart = findDiffstart 0 idA idB
    let diffEnd = findDiffend 0 idA idB
    let idA' = idA[diffStart..(Array.length idA - 1 - diffEnd)]
    let idB' = idB[diffStart..(Array.length idB - 1 - diffEnd)]
    let lnumA' = lnumA[diffStart..(Array.length lnumA - 1 - diffEnd)]
    let lnumB' = lnumB[diffStart..(Array.length lnumB - 1 - diffEnd)]
    idA', idB', lnumA', lnumB'

  let prepareMyers linesA linesB =
    let lineToIdA = Dictionary<_, int>() |> findUniqId 0 0 linesA
    let lineToIdB = Dictionary<_, int>() |> findUniqId 0 0 linesB
    let clnumA = findChangedLines (Array.length linesA - 1) [] lineToIdB linesA
    let clnumB = findChangedLines (Array.length linesB - 1) [] lineToIdA linesB
    let idA, lnumA = matchIndices 0 [||] [||] clnumA lineToIdA linesA
    let idB, lnumB = matchIndices 0 [||] [||] clnumB lineToIdA linesB
    let idA, idB, lnumA, lnumB = trim idA idB lnumA lnumB
    let lnumA =
      { LineNo = lnumA
        LineID = idA
        ChangedLineNumbers = clnumA
        Len = Array.length lnumA }
    let lnumB =
      { LineNo = lnumB
        LineID = idB
        ChangedLineNumbers = clnumB
        Len = Array.length lnumB }
    lnumA, lnumB

  /// Initialize the external K value
  let adjustMin kvd idx min dmin value =
    if min > dmin then
      kvd.XOffsets[idx + (min - 1) - 1] <- value
      min - 1
    else
      min + 1

  /// Initialize the external K value
  let adjustMax kvd idx max dmax value =
    if max < dmax then
      kvd.XOffsets[idx + (max + 1) + 1] <- value
      max + 1
    else
      max - 1

  let adjustBoundaryForward kvd min max dmin dmax =
    let min' = adjustMin kvd kvd.IdxForward min dmin -1
    let max' = adjustMax kvd kvd.IdxForward max dmax -1
    min', max'

  let adjustBoundaryBackward kvd min max dmin dmax =
    let min' = adjustMin kvd kvd.IdxBackward min dmin Int32.MaxValue
    let max' = adjustMax kvd kvd.IdxBackward max dmax Int32.MaxValue
    min', max'

  let rec takeSnakeForward x y boundX boundY (idA: int[]) (idB: int[]) =
    if x < boundX && y < boundY && idA[x] = idB[y] then
      takeSnakeForward (x + 1) (y + 1) boundX boundY idA idB
    else
      x

  let rec takeSnakeBackward x y boundX boundY (idA: int[]) (idB: int[]) =
    if x > boundX && y > boundY && idA[x - 1] = idB[y - 1] then
      takeSnakeBackward (x - 1) (y - 1) boundX boundY idA idB
    else
      x

  let rec traverseForward d fmin kvd idA idB box bmin bmax isOdd =
    if d < fmin then
      None
    else
      let x =
        if kvd.XOffsets[kvd.IdxForward + d - 1]
          >= kvd.XOffsets[kvd.IdxForward + d + 1] then
          kvd.XOffsets[kvd.IdxForward + d - 1] + 1
        else
          kvd.XOffsets[kvd.IdxForward + d + 1]
      let x = takeSnakeForward x (x - d) box.XLim box.YLim idA idB
      kvd.XOffsets[kvd.IdxForward + d] <- x
      if isOdd
        && bmin <= d
        && d <= bmax
        && kvd.XOffsets[kvd.IdxBackward + d] <= x
      then Some { X = x; Y = x - d }
      else traverseForward (d - 2) fmin kvd idA idB box bmin bmax isOdd

  let rec traverseBackward d bmin kvd idA idB box fmin fmax isOdd =
    if d < bmin then
      None
    else
      let x =
        if kvd.XOffsets[kvd.IdxBackward + d - 1]
          < kvd.XOffsets[kvd.IdxBackward + d + 1]
        then kvd.XOffsets[kvd.IdxBackward + d - 1]
        else kvd.XOffsets[kvd.IdxBackward + d + 1] - 1
      let x = takeSnakeBackward x (x - d) box.XOff box.YOff idA idB
      kvd.XOffsets[kvd.IdxBackward + d] <- x
      if not isOdd
        && fmin <= d
        && d <= fmax
        && x <= kvd.XOffsets[kvd.IdxForward + d] then Some { X = x; Y = x - d }
      else traverseBackward (d - 2) bmin kvd idA idB box fmin fmax isOdd

  let rec splitBox kvd idA idB box fmin fmax bmin bmax isOdd =
    let dmin = box.XOff - box.YLim
    let dmax = box.XLim - box.YOff
    (* Forward *)
    let fmin, fmax = adjustBoundaryForward kvd fmin fmax dmin dmax
    let overlap1 = traverseForward fmax fmin kvd idA idB box bmin bmax isOdd
    (* Backward *)
    let bmin, bmax = adjustBoundaryBackward kvd bmin bmax dmin dmax
    let overlap2 = traverseBackward bmax bmin kvd idA idB box fmin fmax isOdd
    match (overlap1, overlap2) with
    | (Some ov1, _) -> ov1
    | (_, Some ov2) -> ov2
    | (_, _) -> splitBox kvd idA idB box fmin fmax bmin bmax isOdd

  /// Shrink the box by walking through SW diagonal snake.
  let rec walkThroughDiagonalSW (idA: int[]) (idB: int[]) off1 lim1 off2 lim2 =
    if off1 < lim1 && off2 < lim2 && idA[off1] = idB[off2] then
      walkThroughDiagonalSW idA idB (off1 + 1) lim1 (off2 + 1) lim2
    else
      { XOff = off1; XLim = lim1; YOff = off2; YLim = lim2 }

  /// Shrink the box by walking through NE diagonal snake.
  let rec walkThroughDiagonalNE (idA: int[]) (idB: int[]) off1 lim1 off2 lim2 =
    if off1 < lim1 && off2 < lim2 && idA[lim1 - 1] = idB[lim2 - 1] then
      walkThroughDiagonalNE idA idB off1 (lim1 - 1) off2 (lim2 - 1)
    else
      { XOff = off1; XLim = lim1; YOff = off2; YLim = lim2 }

  let rec markChangedLines dd off lim =
    if off < lim then
      dd.ChangedLineNumbers[dd.LineNo[off]] <- true
      markChangedLines dd (off + 1) lim
    else
      ()

  let shrinkBox idA idB box =
    let box' = walkThroughDiagonalSW idA idB box.XOff box.XLim box.YOff box.YLim
    walkThroughDiagonalNE idA idB box'.XOff box'.XLim box'.YOff box'.YLim

  let rec cmpChangedLines kvd dd1 dd2 box =
    (* Shrink the box by walking through each diagonal snake (SW and NE). *)
    let box = shrinkBox dd1.LineID dd2.LineID box
    if box.XOff = box.XLim then
      markChangedLines dd2 box.YOff box.YLim
    elif box.YOff = box.YLim then
      markChangedLines dd1 box.XOff box.XLim
    else
      (* Divide *)
      let fmid, bmid = box.XOff - box.YOff, box.XLim - box.YLim
      let isOdd = (fmid - bmid) % 2 <> 0
      kvd.XOffsets[kvd.IdxForward + fmid] <- box.XOff
      kvd.XOffsets[kvd.IdxBackward + bmid] <- box.XLim
      let spl = splitBox kvd dd1.LineID dd2.LineID box fmid fmid bmid bmid isOdd
      (* Conquer *)
      { XOff = box.XOff; XLim = spl.X; YOff = box.YOff; YLim = spl.Y }
      |> cmpChangedLines kvd dd1 dd2
      { XOff = spl.X; XLim = box.XLim; YOff = spl.Y; YLim = box.YLim }
      |> cmpChangedLines kvd dd1 dd2

  let myersDiff dd1 dd2 =
    let nDiags = dd1.Len + dd2.Len + 3
    let kvd =
      { XOffsets = Array.zeroCreate (2 * nDiags + 2)
        IdxForward = dd2.Len + 1
        IdxBackward = dd2.Len + 1 + nDiags }
    { XOff = 0; XLim = dd1.Len; YOff = 0; YLim = dd2.Len }
    |> cmpChangedLines kvd dd1 dd2
    dd1.ChangedLineNumbers, dd2.ChangedLineNumbers

  let hasCommonValue (left: byte[]) (right: byte[]) =
    let values = HashSet<byte> right
    left |> Array.exists values.Contains

  let compareMyers (left: byte[]) (right: byte[]) =
    if Array.isEmpty left then
      [||], Array.create right.Length true
    elif Array.isEmpty right then
      Array.create left.Length true, [||]
    elif left = right then
      Array.create left.Length false, Array.create right.Length false
    elif not (hasCommonValue left right) then
      Array.create left.Length true, Array.create right.Length true
    else
      let leftData, rightData = prepareMyers left right
      myersDiff leftData rightData

  let countValues (values: byte[]) (startIdx: int) (endIdx: int) =
    let counts = Dictionary<byte, int>()
    for idx = startIdx to endIdx - 1 do
      let value = values[idx]
      match counts.TryGetValue value with
      | true, count -> counts[value] <- count + 1
      | false, _ -> counts[value] <- 1
    counts

  let markRange (changed: bool[]) startIdx endIdx =
    for idx = startIdx to endIdx - 1 do
      changed[idx] <- true

  let copyChanged (target: bool[]) offset source =
    source |> Array.iteri (fun idx changed ->
      if changed then
        target[offset + idx] <- true
      else
        ())

  let findRareAnchor
    (left: byte[])
    (right: byte[])
    leftStart
    leftEnd
    rightStart
    rightEnd =
    let leftCounts = countValues left leftStart leftEnd
    let rightCounts = countValues right rightStart rightEnd
    let mutable best = None
    let mutable bestScore = Int32.MaxValue
    let mutable bestDistance = Int32.MaxValue
    for leftIdx = leftStart to leftEnd - 1 do
      let value = left[leftIdx]
      match rightCounts.TryGetValue value with
      | true, rightCount ->
        let score = max leftCounts[value] rightCount
        if score <= 64 && score <= bestScore then
          for rightIdx = rightStart to rightEnd - 1 do
            if right[rightIdx] = value then
              let leftOffset = leftIdx - leftStart
              let rightOffset = rightIdx - rightStart
              let distance = abs (leftOffset - rightOffset)
              if score < bestScore || distance < bestDistance then
                best <- Some(leftIdx, rightIdx)
                bestScore <- score
                bestDistance <- distance
              else
                ()
            else
              ()
        else
          ()
      | false, _ ->
        ()
    best

  let compareHistogram (left: byte[]) (right: byte[]) =
    let leftChanged = Array.create left.Length false
    let rightChanged = Array.create right.Length false
    let rec compareRange leftStart leftEnd rightStart rightEnd =
      let mutable leftStart = leftStart
      let mutable rightStart = rightStart
      while leftStart < leftEnd && rightStart < rightEnd
            && left[leftStart] = right[rightStart] do
        leftStart <- leftStart + 1
        rightStart <- rightStart + 1
      let mutable leftEnd = leftEnd
      let mutable rightEnd = rightEnd
      while leftStart < leftEnd && rightStart < rightEnd
            && left[leftEnd - 1] = right[rightEnd - 1] do
        leftEnd <- leftEnd - 1
        rightEnd <- rightEnd - 1
      if leftStart = leftEnd then
        markRange rightChanged rightStart rightEnd
      elif rightStart = rightEnd then
        markRange leftChanged leftStart leftEnd
      else
        let anchor =
          findRareAnchor left right leftStart leftEnd rightStart rightEnd
        match anchor with
        | Some(leftAnchor, rightAnchor) ->
          compareRange leftStart leftAnchor rightStart rightAnchor
          compareRange (leftAnchor + 1) leftEnd (rightAnchor + 1) rightEnd
        | None ->
          let leftSlice = left[leftStart..leftEnd - 1]
          let rightSlice = right[rightStart..rightEnd - 1]
          let sliceLeftChanged, sliceRightChanged =
            compareMyers leftSlice rightSlice
          copyChanged leftChanged leftStart sliceLeftChanged
          copyChanged rightChanged rightStart sliceRightChanged
    compareRange 0 left.Length 0 right.Length
    leftChanged, rightChanged

  let compareBytes
    (algorithm: DiffAlgorithm)
    (left: byte[])
    (right: byte[]) =
    match algorithm with
    | Myers -> compareMyers left right
    | Histogram -> compareHistogram left right

  let calculateMetrics
    leftLength
    rightLength
    (leftChanged: bool[])
    (rightChanged: bool[]) =
    let removed = leftChanged |> Array.filter id |> Array.length
    let added = rightChanged |> Array.filter id |> Array.length
    let equal = min (leftLength - removed) (rightLength - added)
    let total = leftLength + rightLength
    let similarity =
      if total = 0 then 1.0 else 2.0 * float equal / float total
    { LeftLength = leftLength
      RightLength = rightLength
      Equal = equal
      Added = added
      Removed = removed
      Similarity = similarity }

  let alignChanges (leftChanged: bool[]) (rightChanged: bool[]) =
    let pairs = ResizeArray<DiffPair>()
    let mutable leftIdx = 0
    let mutable rightIdx = 0
    while leftIdx < leftChanged.Length || rightIdx < rightChanged.Length do
      let leftEqual =
        leftIdx < leftChanged.Length && not leftChanged[leftIdx]
      let rightEqual =
        rightIdx < rightChanged.Length && not rightChanged[rightIdx]
      if leftEqual && rightEqual then
        pairs.Add { Left = Some leftIdx
                    Right = Some rightIdx
                    Changed = false }
        leftIdx <- leftIdx + 1
        rightIdx <- rightIdx + 1
      else
        let leftEnd =
          let mutable idx = leftIdx
          while idx < leftChanged.Length && leftChanged[idx] do
            idx <- idx + 1
          idx
        let rightEnd =
          let mutable idx = rightIdx
          while idx < rightChanged.Length && rightChanged[idx] do
            idx <- idx + 1
          idx
        let count = max (leftEnd - leftIdx) (rightEnd - rightIdx)
        if count = 0 then
          let left = if leftIdx < leftChanged.Length then Some leftIdx else None
          let right =
            if rightIdx < rightChanged.Length then Some rightIdx else None
          pairs.Add { Left = left; Right = right; Changed = true }
          if Option.isSome left then
            leftIdx <- leftIdx + 1
          else
            ()
          if Option.isSome right then
            rightIdx <- rightIdx + 1
          else
            ()
        else
          for offset = 0 to count - 1 do
            let left =
              if leftIdx + offset < leftEnd then Some(leftIdx + offset)
              else None
            let right =
              if rightIdx + offset < rightEnd then Some(rightIdx + offset)
              else None
            pairs.Add { Left = left; Right = right; Changed = true }
          leftIdx <- leftEnd
          rightIdx <- rightEnd
    pairs.ToArray()

  let algorithmName = function
    | Myers -> "myers"
    | Histogram -> "histogram"

  let binaryName (fallback: string) (bin: Binary) =
    let path = (Binary.Handle bin).File.Path
    if String.IsNullOrWhiteSpace path then fallback else path

  let formatMetrics
    (algorithm: DiffAlgorithm)
    leftName
    rightName
    (metrics: DiffMetrics) =
    let similarity = metrics.Similarity.ToString("F6")
    $"algorithm: {algorithmName algorithm}{Environment.NewLine}" +
    $"left: {leftName} ({metrics.LeftLength} bytes){Environment.NewLine}" +
    $"right: {rightName} ({metrics.RightLength} bytes){Environment.NewLine}" +
    $"equal: {metrics.Equal}{Environment.NewLine}" +
    $"added: {metrics.Added} (NLA){Environment.NewLine}" +
    $"removed: {metrics.Removed} (NLD){Environment.NewLine}" +
    $"similarity: {similarity}{Environment.NewLine}"

  let formatJson
    (algorithm: DiffAlgorithm)
    leftName
    rightName
    (metrics: DiffMetrics) =
    JsonSerializer.Serialize
      {| algorithm = algorithmName algorithm
         left = leftName
         right = rightName
         leftLength = metrics.LeftLength
         rightLength = metrics.RightLength
         equal = metrics.Equal
         added = metrics.Added
         removed = metrics.Removed
         similarity = metrics.Similarity |}

  let appendByte
    (cs: ColoredString)
    color
    (bytes: byte[])
    (index: int option) =
    match index with
    | Some idx -> cs.Append(color, $"{bytes[idx]:x2} ")
    | None -> cs.Append(NoColor, "-- ")

  let appendSide
    cs
    color
    (bytes: byte[])
    (indexes: (int option * bool)[]) =
    indexes
    |> Array.fold (fun (cs: ColoredString) (index, changed) ->
      let color = if changed then color else NoColor
      appendByte cs color bytes index) cs

  let rowOffset (selector: DiffPair -> int option) (row: DiffPair[]) =
    row
    |> Array.tryPick selector
    |> Option.map (fun offset -> $"{offset:x8}")
    |> Option.defaultValue "--------"

  let selectRows context (rows: DiffPair[][]) =
    match context with
    | None ->
      Array.create rows.Length true
    | Some context ->
      let selected = Array.create rows.Length false
      rows |> Array.iteri (fun idx row ->
        if row |> Array.exists (fun pair -> pair.Changed) then
          let first = max 0 (idx - context)
          let last = min (rows.Length - 1) (idx + context)
          for selectedIdx = first to last do
            selected[selectedIdx] <- true
        else
          ())
      selected

  let renderSideBySide
    (opts: DiffOptions)
    leftName
    rightName
    (left: byte[])
    (right: byte[])
    (changedLeft: bool[])
    (changedRight: bool[]) =
    let rows =
      alignChanges changedLeft changedRight
      |> Array.chunkBySize opts.Width
    let selected = selectRows opts.Context rows
    let cs = ColoredString()
    cs.Append(NoColor, $"left : {leftName}{Environment.NewLine}")
      .Append(NoColor, $"right: {rightName}{Environment.NewLine}")
      .Append(NoColor, $"algorithm: {algorithmName opts.Algorithm}")
      .Append(NoColor, Environment.NewLine) |> ignore
    let mutable skipped = false
    rows |> Array.iteri (fun idx row ->
      if not selected[idx] then
        skipped <- true
      else
        if skipped then
          cs.Append(NoColor, $"...{Environment.NewLine}") |> ignore
          skipped <- false
        else
          ()
        let leftOffset = rowOffset (fun pair -> pair.Left) row
        let rightOffset = rowOffset (fun pair -> pair.Right) row
        cs.Append(NoColor, $"{leftOffset} | ") |> ignore
        let leftCells = row |> Array.map (fun pair -> pair.Left, pair.Changed)
        appendSide cs Red left leftCells |> ignore
        let padding = (opts.Width - row.Length) * 3
        cs.Append(NoColor, String(' ', padding) + "| ") |> ignore
        let rightCells = row |> Array.map (fun pair -> pair.Right, pair.Changed)
        appendSide cs Green right rightCells |> ignore
        cs.Append(NoColor, $"| {rightOffset}{Environment.NewLine}") |> ignore)
    if opts.UseColor then OutputColored cs else OutputNormal(cs.ToString())

  let diff opts bin1 bin2 =
    let hdl1, hdl2 = Binary.Handle bin1, Binary.Handle bin2
    let bs1, bs2 = hdl1.File.RawBytes.ToArray(), hdl2.File.RawBytes.ToArray()
    let changed1, changed2 = compareBytes opts.Algorithm bs1 bs2
    let metrics = calculateMetrics bs1.Length bs2.Length changed1 changed2
    let leftName = binaryName "<left>" bin1
    let rightName = binaryName "<right>" bin2
    match opts.Format with
    | Summary ->
      formatMetrics opts.Algorithm leftName rightName metrics |> OutputNormal
    | Json ->
      formatJson opts.Algorithm leftName rightName metrics |> OutputNormal
    | SideBySide ->
      renderSideBySide opts leftName rightName bs1 bs2 changed1 changed2

  interface IAction with
    member _.ActionID with get() = "diff"
    member _.Signature with get() = "Binary collection -> OutString"
    member _.Description with get() =
      """
    Take in two binaries as input and return a diff string as output.

      - myers | histogram: select the diff algorithm (default: myers).
      - side-by-side | summary | json: select the output format.
      - context=N: show N unchanged rows around each changed row.
      - width=N: show N byte columns per row (default: 16).
      - no-color: render plain text without terminal colors.
"""
    member _.Transform(args, collection) =
      let bins = collection.Values
      if bins.Length <> 2 then
        invalidArg (nameof DiffAction) "Can only diff exactly two binaries."
      else
        let opts = parseOptions args
        let outstr = diff opts (unbox<Binary> bins[0]) (unbox<Binary> bins[1])
        { Values = [| box outstr |] }
