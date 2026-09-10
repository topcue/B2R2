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

namespace B2R2.RearEnd.Transformer.Tests

open System
open System.Text.Json
open Microsoft.VisualStudio.TestTools.UnitTesting
open B2R2
open B2R2.FrontEnd
open B2R2.RearEnd.Transformer

[<TestClass>]
type DiffTests() =
  let makeBinary bytes =
    lazy BinHandle.LoadRawImage(bytes, ISA Architecture.Intel)
    |> Binary.PlainInit

  let run args left right =
    let action = DiffAction() :> IAction
    let input =
      { Values = [| box (makeBinary left); box (makeBinary right) |] }
    let result = action.Transform(args, input)
    Assert.AreEqual(1, result.Values.Length)
    (result.Values[0] :?> OutString).ToString()

  let summaryEqual left right =
    let output = run [ "json" ] left right
    use document = JsonDocument.Parse output
    document.RootElement.GetProperty("equal").GetInt32()

  let lcsLength (left: byte[]) (right: byte[]) =
    let lengths = Array2D.zeroCreate (left.Length + 1) (right.Length + 1)
    for leftIdx = 1 to left.Length do
      for rightIdx = 1 to right.Length do
        lengths[leftIdx, rightIdx] <-
          if left[leftIdx - 1] = right[rightIdx - 1] then
            lengths[leftIdx - 1, rightIdx - 1] + 1
          else
            max lengths[leftIdx - 1, rightIdx]
                lengths[leftIdx, rightIdx - 1]
    lengths[left.Length, right.Length]

  [<TestMethod>]
  member _.``Summary reports edit metrics``() =
    let output =
      run [ "summary" ]
        [| 0x10uy; 0x20uy |]
        [| 0x10uy; 0x30uy; 0x20uy |]
    StringAssert.Contains(output, "equal: 2")
    StringAssert.Contains(output, "added: 1")
    StringAssert.Contains(output, "removed: 0")

  [<TestMethod>]
  member _.``JSON supports histogram algorithm``() =
    let output =
      run [ "json"; "histogram" ]
        [| 1uy; 2uy; 1uy |]
        [| 1uy; 3uy; 1uy |]
    use document = JsonDocument.Parse output
    let root = document.RootElement
    Assert.AreEqual("histogram", root.GetProperty("algorithm").GetString())
    Assert.AreEqual(2, root.GetProperty("equal").GetInt32())
    Assert.AreEqual(1, root.GetProperty("added").GetInt32())
    Assert.AreEqual(1, root.GetProperty("removed").GetInt32())

  [<TestMethod>]
  member _.``Side by side output aligns insertion``() =
    let output =
      run [ "width=4"; "no-color" ]
        [| 0x10uy; 0x20uy |]
        [| 0x10uy; 0x30uy; 0x20uy |]
    StringAssert.Contains(output, "00000000")
    StringAssert.Contains(output, "--")

  [<TestMethod>]
  member _.``Context must be nonnegative``() =
    Assert.Throws<ArgumentException>(Action(fun () ->
      run [ "context=-1" ] [| 0uy |] [| 1uy |] |> ignore))
    |> ignore

  [<TestMethod>]
  member _.``Myers handles empty and identical inputs``() =
    Assert.AreEqual(0, summaryEqual [||] [||])
    Assert.AreEqual(3, summaryEqual [| 1uy; 2uy; 3uy |]
                                      [| 1uy; 2uy; 3uy |])

  [<TestMethod>]
  member _.``Myers metrics match LCS on small inputs``() =
    let random = Random 0
    for _ = 1 to 100 do
      let left =
        Array.init (random.Next(0, 9)) (fun _ -> byte (random.Next 4))
      let right =
        Array.init (random.Next(0, 9)) (fun _ -> byte (random.Next 4))
      Assert.AreEqual(lcsLength left right, summaryEqual left right)
