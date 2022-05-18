module internal B2R2.RearEnd.BinDump.MyersDiff

open System.Collections.Generic
open B2R2
open B2R2.RearEnd.BinDump.DiffCore
open B2R2.RearEnd.BinDump.DisasmLiftHelper

type KVecDim = {
  mutable Arr : int[]
  IdxF : int
  IdxB : int
}

type Overlap = {
 X : int
 Y : int
 MinLow : bool
 MinHi  : bool
}

type Box = {
  Off1: int
  Lim1: int
  Off2: int
  Lim2: int
}

/// Classical integer square root approximation using shifts.
let rec bogoSqrt n i =
  if n <= 0 then i
  else bogoSqrt (n >>> 2) (i <<< 1)

/// Initialize the external K value
let adjustMin kvd idx min dmin setValue =
  if min > dmin then
    kvd.Arr[idx + (min - 1) - 1] <- setValue
    min - 1
  else
    min + 1

/// Initialize the external K value
let adjustMax kvd idx max dmax setValue =
  if max < dmax then
    kvd.Arr[idx + (max + 1) + 1] <- setValue
    max + 1
  else
    max - 1

let adjustBoundaryForward kvd min max dmin dmax =
  let min' = adjustMin kvd kvd.IdxF min dmin -1
  let max' = adjustMax kvd kvd.IdxF max dmax -1
  min', max'

let adjustBoundaryBackward kvd min max dmin dmax =
  let min' = adjustMin kvd kvd.IdxB min dmin System.Int32.MaxValue
  let max' = adjustMax kvd kvd.IdxB max dmax System.Int32.MaxValue
  min', max'

let rec takeSnakeForward x y boundX boundY (haA: int[]) (haB: int[]) =
  if x < boundX && y < boundY && haA[x] = haB[y] then
    takeSnakeForward (x + 1) (y + 1) boundX boundY haA haB
  else x

let rec takeSnakeBackward x y boundX boundY (haA: int[]) (haB: int[]) =
  if x > boundX && y > boundY && haA[x - 1] = haB[y - 1] then
    takeSnakeBackward (x - 1) (y - 1) boundX boundY haA haB
  else x

let rec traverseForward d fmin kvd haA haB box bmin bmax isOdd =
  if d < fmin then None
  else
    let x =
      if kvd.Arr[kvd.IdxF + d - 1] >= kvd.Arr[kvd.IdxF + d + 1] then
        kvd.Arr[kvd.IdxF + d - 1] + 1
      else
        kvd.Arr[kvd.IdxF + d + 1]
    let x = takeSnakeForward x (x - d) box.Lim1 box.Lim2 haA haB
    kvd.Arr[kvd.IdxF + d] <- x
    if isOdd && bmin <= d && d <= bmax && kvd.Arr[kvd.IdxB + d] <= x then
      Some { X = x; Y = x - d; MinLow = true; MinHi = true }
    else
      traverseForward (d - 2) fmin kvd haA haB box bmin bmax isOdd

let rec traverseBackward d bmin kvd haA haB box fmin fmax isOdd =
  if d < bmin then None
  else
    let x =
      if kvd.Arr[kvd.IdxB + d - 1] < kvd.Arr[kvd.IdxB + d + 1] then
        kvd.Arr[kvd.IdxB + d - 1]
      else
        kvd.Arr[kvd.IdxB + d + 1] - 1
    let x = takeSnakeBackward x (x - d) box.Off1 box.Off2 haA haB
    kvd.Arr[kvd.IdxB + d] <- x
    if not isOdd && fmin <= d && d <= fmax && x <= kvd.Arr[kvd.IdxF + d] then
      Some { X = x; Y = x - d; MinLow = true; MinHi = true }
    else
      traverseBackward (d - 2) bmin kvd haA haB box fmin fmax isOdd

let rec splitBox kvd haA haB box fmin fmax bmin bmax isOdd =
  let dmin = box.Off1 - box.Lim2
  let dmax = box.Lim1 - box.Off2

  /// Forward
  let fmin, fmax = adjustBoundaryForward kvd fmin fmax dmin dmax
  let overlap1 = traverseForward fmax fmin kvd haA haB box bmin bmax isOdd

  /// Backward
  let bmin, bmax = adjustBoundaryBackward kvd bmin bmax dmin dmax
  let overlap2 =  traverseBackward bmax bmin kvd haA haB box fmin fmax isOdd

  match (overlap1, overlap2) with
  | (Some ov1, _) -> ov1
  | (_, Some ov2) -> ov2
  | (_, _) -> splitBox kvd haA haB box fmin fmax bmin bmax isOdd

/// Shrink the box by walking through SW diagonal snake.
let rec walkThroughDiagonalSW (haA: int[]) (haB: int[]) box =
  if box.Off1 < box.Lim1 && box.Off2 < box.Lim2 &&
    haA[box.Off1] = haB[box.Off2] then

    { Off1 = box.Off1 + 1; Lim1 = box.Lim1;
      Off2 = box.Off2 + 1; Lim2 = box.Lim2 }
    |> walkThroughDiagonalSW haA haB
  else
    box

/// Shrink the box by walking through NE diagonal snake.
let rec walkThroughDiagonalNE (haA: int[]) (haB: int[]) box =
  if box.Off1 < box.Lim1 && box.Off2 < box.Lim2 &&
    haA[box.Lim1 - 1] = haB[box.Lim2 - 1] then

    { Off1 = box.Off1; Lim1 = box.Lim1 - 1;
      Off2 = box.Off2; Lim2 = box.Lim2 - 1 }
    |> walkThroughDiagonalNE haA haB
  else
    box

let rec markRchg foo off lim =
  if off < lim then
    foo.Rchg[foo.Idx[off]] <- true
    markRchg foo (off + 1) lim
  else ()

let shrinkBox haA haB box =
  box
  |> walkThroughDiagonalSW haA haB
  |> walkThroughDiagonalNE haA haB


let rec cmpRecs kvd dd1 dd2 box (* needMin mxcost *) =
  /// Shrink the box by walking through each diagonal snake (SW and NE).
  let box = shrinkBox dd1.Ha dd2.Ha box
  if box.Off1 = box.Lim1 then
    markRchg dd2 box.Off2 box.Lim2
  elif box.Off2 = box.Lim2 then
    markRchg dd1 box.Off1 box.Lim1
  else
    /// Divide
    let fmid, bmid = box.Off1 - box.Off2, box.Lim1 - box.Lim2
    let isOdd = if (fmid - bmid) % 2 <> 0 then true else false
    kvd.Arr[kvd.IdxF + fmid] <- box.Off1
    kvd.Arr[kvd.IdxB + bmid] <- box.Lim1
    let spl = splitBox kvd dd1.Ha dd2.Ha box fmid fmid bmid bmid isOdd

    /// Conquer
    { Off1 = box.Off1; Lim1 = spl.X; Off2 = box.Off2; Lim2 = spl.Y }
    |> cmpRecs kvd dd1 dd2
    { Off1 = spl.X; Lim1 = box.Lim1; Off2 = spl.Y; Lim2 = box.Lim2 }
    |> cmpRecs kvd dd1 dd2

let myersDiff dd1 dd2 =
  let nDiags = dd1.Len + dd2.Len + 3
  let kvd =
    { Arr = Array.zeroCreate (2 * nDiags + 2);
      IdxF = dd2.Len + 1
      IdxB = dd2.Len + 1 + nDiags }
  { Off1 = 0; Lim1 = dd1.Len; Off2 = 0; Lim2 = dd2.Len }
  |> cmpRecs kvd dd1 dd2
  dd1.Rchg, dd2.Rchg
