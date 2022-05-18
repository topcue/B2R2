module internal B2R2.RearEnd.BinDump.HistogramDiff

open B2R2
open B2R2.RearEnd.BinDump.DiffCore

type Record = {
  Ptr : int
  Cnt : int
}

/// TODO: Try not to use mutable
type RecordInfo = {
  Records  : Record[]
  LineMap  : Record[]
  NextPtrs : int[]
  mutable HasCommon : bool
  mutable Cnt       : int
}

type LCS = {
  S1 : int
  S2 : int
  E1 : int
  E2 : int
}

type SectionRange = {
  S1   : int
  S2   : int
  Cnt1 : int
  Cnt2 : int
}

let getId indexLen id =
  if id < indexLen && id >= 0 then id
  else -1

let rec scanA dd1 dd2 recInfo (recExist: bool[]) ptr ptrShift =
  if ptr = ptrShift - 1 || recInfo.Cnt = 64 then
    recInfo
  else
    let id = getId dd1.Len dd1.Idx[ptr - 1]
    let r = recInfo.Records[id]
    if recExist[id] then
      /// Insert ptr onto the front of the existing element chain
      recInfo.NextPtrs[ptr - ptrShift] <- r.Ptr
      recInfo.LineMap[ptr - ptrShift] <- { Ptr = ptr; Cnt = r.Cnt + 1 }
    else
      /// Construct a new chain for ptr
      recExist[id] <- true
      recInfo.Records[id] <- { Ptr = ptr; Cnt = 1 }
      recInfo.LineMap[ptr - ptrShift] <- { Ptr = ptr; Cnt = 1 }
    scanA dd1 dd2 recInfo recExist (ptr - 1) ptrShift

let setLCS start1 start2 end1 end2 =
  { S1 = start1; S2 = start2; E1 = end1; E2 = end2 }

let rec findUpper dd1 dd2 recInfo startA startB recCnt s1 s2 ptrShift =
  if s1 < startA && s2 < startB &&
    dd1.Idx[startA - 2] = dd2.Idx[startB - 2] then
    let recCnt =
      if 1 < recCnt then min recCnt recInfo.LineMap[startA - 1 - ptrShift].Cnt
      else recCnt
    findUpper dd1 dd2 recInfo (startA - 1) (startB - 1) recCnt s1 s2 ptrShift
  else
    startA, startB, recCnt

let rec findLower dd1 dd2 recInfo endA endB recCnt e1 e2 ptrShift =
  if endA < e1 && endB < e2 && dd1.Idx[endA] = dd2.Idx[endB] then
    let recCnt =
      if 1 < recCnt then min recCnt recInfo.LineMap[endA + 1 - ptrShift].Cnt
      else recCnt
    findLower dd1 dd2 recInfo (endA + 1) (endB + 1) recCnt e1 e2 ptrShift
  else
    endA, endB, recCnt

let rec checkNextExist recInfo shouldBreak ptrA ptrShift maxLen =
  if ptrA = 0 then
    false, ptrA
  elif ptrA > maxLen then
    shouldBreak, ptrA
  else
    let nextPtrA = recInfo.NextPtrs[ptrA - ptrShift]
    checkNextExist recInfo shouldBreak nextPtrA ptrShift maxLen

let rec findUniqLines dd1 dd2 recInfo sec nextPtrB lcs startA recCnt ptrB =
  let nextPtrA = recInfo.NextPtrs[startA - sec.S1]
  let endA = startA
  let endB = ptrB
  let e1, e2 = sec.S1 + sec.Cnt1 - 1, sec.S2 + sec.Cnt2 - 1
  let startA, startB, recCnt =
    findUpper dd1 dd2 recInfo startA ptrB recCnt sec.S1 sec.S2 sec.S1
  let endA, endB, recCnt =
    findLower dd1 dd2 recInfo endA endB recCnt e1 e2 sec.S1
  let nextPtrB = if nextPtrB <= endB then endB + 1 else nextPtrB
  let isFoundLongerLCS = lcs.E1 - lcs.S1 < endA - startA || recCnt < recInfo.Cnt
  let lcs = if isFoundLongerLCS then setLCS startA startB endA endB else lcs

  (* Consider whether to continue *)
  if isFoundLongerLCS then recInfo.Cnt <- recCnt
  let isNextExist, nextPtrA = checkNextExist recInfo true nextPtrA sec.S1 endA
  if not isNextExist then nextPtrB, lcs
  else findUniqLines dd1 dd2 recInfo sec nextPtrB lcs nextPtrA recCnt ptrB

let tryLCS dd1 dd2 recInfo sec ptrB lcs =
  let nextPtrB = ptrB + 1
  let id = getId dd1.Len dd2.Idx[ptrB - 1]
  if id = -1 then nextPtrB, lcs
  else
    let r = recInfo.Records[id]
    if r.Cnt > recInfo.Cnt then
      if not recInfo.HasCommon then
        recInfo.HasCommon <- dd1.Idx[r.Ptr - 1] = dd2.Idx[ptrB - 1]
      nextPtrB, lcs
    else
      if r.Ptr = -1 || dd1.Idx[r.Ptr - 1] <> dd2.Idx[ptrB - 1] then
        nextPtrB, lcs
      else
        recInfo.HasCommon <- true
        findUniqLines dd1 dd2 recInfo sec nextPtrB lcs r.Ptr r.Cnt ptrB

let rec recTryLCS dd1 dd2 recInfo sec ptrB lcs  =
  let nextPtrB, lcs = tryLCS dd1 dd2 recInfo sec ptrB lcs
  if nextPtrB > sec.S2 + sec.Cnt2 - 1 then lcs
  else recTryLCS dd1 dd2 recInfo sec nextPtrB lcs

let findSeperator dd1 dd2 sec =
  let recInfo =
    { Records = Array.init dd1.Len (fun _ -> { Ptr = -1; Cnt = -1 })
      LineMap = Array.init dd1.Len (fun _ -> { Ptr = -1; Cnt = -1 })
      NextPtrs = Array.init dd1.Len (fun _ -> 0)
      HasCommon = false
      Cnt = 63 }
  let recExist = Array.init dd1.Len (fun _ -> false)
  let recInfo = scanA dd1 dd2 recInfo recExist (sec.S1 + sec.Cnt1 - 1) sec.S1
  { S1 = 0; S2 = 0; E1 = 0; E2 = 0 }
  |> recTryLCS dd1 dd2 recInfo sec sec.S2

let rec markRchg (rchg: bool[]) cnt ln =
  if cnt = 0 then ()
  else
    rchg[ln - 1] <- true
    markRchg rchg (cnt - 1) (ln + 1)

let rec doRecursiveDiff dd1 dd2 sec =
  if sec.Cnt1 <= 0 && sec.Cnt2 <= 0 then ()
  elif sec.Cnt1 = 0 then markRchg dd2.Rchg sec.Cnt2 sec.S2
  elif sec.Cnt2 = 0 then markRchg dd1.Rchg sec.Cnt1 sec.S1
  else
    /// Divide: Find seperator(unique lines)
    let lcs = findSeperator dd1 dd2 sec
    if lcs.S1 = 0 && lcs.S2 = 0 then
      markRchg dd1.Rchg sec.Cnt1 sec.S1
      markRchg dd2.Rchg sec.Cnt2 sec.S2
    else
      /// Conquer (upper section)
      { S1 = sec.S1; Cnt1 = lcs.S1 - sec.S1
        S2 = sec.S2; Cnt2 = lcs.S2 - sec.S2 }
      |> doRecursiveDiff dd1 dd2

      /// Conquer (lower section)
      { S1 = lcs.E1 + 1; Cnt1 = sec.S1 + sec.Cnt1 - 1 - lcs.E1
        S2 = lcs.E2 + 1; Cnt2 = sec.S2 + sec.Cnt2 - 1 - lcs.E2 }
      |> doRecursiveDiff dd1 dd2

let histogramDiff dd1 dd2 =
  { S1 = 1; S2 = 1; Cnt1 = dd1.Len; Cnt2 = dd2.Len }
  |> doRecursiveDiff dd1 dd2
  dd1.Rchg, dd2.Rchg
