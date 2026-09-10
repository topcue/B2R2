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
open System.Diagnostics
open System.IO
open System.Text
open System.Text.Json
open Microsoft.VisualStudio.TestTools.UnitTesting
open B2R2
open B2R2.FrontEnd
open B2R2.RearEnd.Transformer
open B2R2.RearEnd.Transformer.ForkDiff

[<TestClass>]
type DiffTests() =
  let makeBinary bytes =
    lazy BinHandle.LoadRawImage(bytes, ISA Architecture.Intel)
    |> Binary.PlainInit

  let run args left right =
    let action = EnhancedDiffAction() :> IAction
    let input =
      { Values = [| box (makeBinary left); box (makeBinary right) |] }
    let result = action.Transform(args, input)
    Assert.AreEqual(1, result.Values.Length)
    (result.Values[0] :?> OutString).ToString()

  let summaryEqual left right =
    let output = run [ "json" ] left right
    use document = JsonDocument.Parse output
    document.RootElement.GetProperty("equal").GetInt32()

  let summaryMetrics args left right =
    let output = run ("json" :: args) left right
    use document = JsonDocument.Parse output
    let root = document.RootElement
    let equal = root.GetProperty("equal").GetInt32()
    let added = root.GetProperty("added").GetInt32()
    let removed = root.GetProperty("removed").GetInt32()
    equal, added, removed

  let gitMetrics algorithm left right =
    let directory =
      let name = "b2r2-git-diff-" + Guid.NewGuid().ToString()
      Path.Combine(Path.GetTempPath(), name)
    Directory.CreateDirectory directory |> ignore
    let leftPath = Path.Combine(directory, "left.txt")
    let rightPath = Path.Combine(directory, "right.txt")
    let asLines bytes =
      bytes |> Array.map (fun (value: byte) -> value.ToString("X2"))
    try
      File.WriteAllLines(leftPath, asLines left)
      File.WriteAllLines(rightPath, asLines right)
      let startInfo = ProcessStartInfo("git")
      startInfo.UseShellExecute <- false
      startInfo.RedirectStandardOutput <- true
      startInfo.RedirectStandardError <- true
      let options =
        [ "--no-index"
          "--text"
          $"--diff-algorithm={algorithm}"
          "--numstat"
          "--"
          leftPath
          rightPath ]
      let arguments =
        if algorithm = "myers" then
          "diff" :: "--minimal" :: options
        else
          "diff" :: options
      arguments
      |> List.iter startInfo.ArgumentList.Add
      use gitProcess = Process.Start startInfo
      let output = gitProcess.StandardOutput.ReadToEnd()
      let error = gitProcess.StandardError.ReadToEnd()
      gitProcess.WaitForExit()
      let validExitCode =
        gitProcess.ExitCode = 0 || gitProcess.ExitCode = 1
      Assert.AreEqual(true, validExitCode, error)
      if gitProcess.ExitCode = 0 then
        left.Length, 0, 0
      else
        let fields = output.Trim().Split('\t')
        Assert.AreEqual(true, fields.Length >= 2, output)
        let added = Int32.Parse fields[0]
        let removed = Int32.Parse fields[1]
        let equal = (left.Length + right.Length - added - removed) / 2
        equal, added, removed
    finally
      Directory.Delete(directory, true)

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
  member _.``Fork diff and upstream diff have distinct action IDs``() =
    let enhanced = EnhancedDiffAction() :> IAction
    let upstream = DiffAction() :> IAction
    Assert.AreEqual("diff", enhanced.ActionID)
    Assert.AreEqual("legacy-diff", upstream.ActionID)

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

  [<TestMethod>]
  member _.``Myers metrics match Git xdiff ground truth``() =
    let cases =
      [ [||], [||]
        [| 1uy |], [||]
        [| 1uy; 2uy; 1uy |], [| 1uy; 1uy; 2uy |]
        [| 0uy; 1uy; 0uy; 1uy |], [| 1uy; 0uy; 1uy; 0uy |]
        [| 1uy; 2uy; 3uy; 4uy |], [| 4uy; 3uy; 2uy; 1uy |] ]
    for left, right in cases do
      let expected = gitMetrics "myers" left right
      let actual = summaryMetrics [] left right
      Assert.AreEqual(expected, actual)

  [<TestMethod>]
  member _.``Histogram metrics match Git xdiff samples``() =
    let random = Random 1
    for _ = 1 to 40 do
      let left =
        Array.init (random.Next(0, 20)) (fun _ -> byte (random.Next 6))
      let right =
        Array.init (random.Next(0, 20)) (fun _ -> byte (random.Next 6))
      let expected = gitMetrics "histogram" left right
      let actual = summaryMetrics [ "histogram" ] left right
      Assert.AreEqual(expected, actual)

  [<TestMethod>]
  member _.``Myers scales across long repeated input``() =
    let left = Array.create 100000 0x41uy
    let right = Array.copy left
    right[50000] <- 0x42uy
    Assert.AreEqual((99999, 1, 1), summaryMetrics [] left right)

  [<TestMethod>]
  member _.``Histogram falls back for frequent common values``() =
    let left = Array.append (Array.create 70 1uy) (Array.create 70 2uy)
    let right = Array.append (Array.create 70 2uy) (Array.create 70 1uy)
    let expected = gitMetrics "histogram" left right
    let actual = summaryMetrics [ "histogram" ] left right
    Assert.AreEqual(expected, actual)

  [<TestMethod>]
  member _.``Text mode compares lines instead of bytes``() =
    let left = Encoding.UTF8.GetBytes("alpha\nbeta\n")
    let right = Encoding.UTF8.GetBytes("alpha\nnew\nbeta\n")
    let output = run [ "mode=text"; "histogram"; "summary" ] left right
    StringAssert.Contains(output, "equal: 2")
    StringAssert.Contains(output, "added: 1")
    StringAssert.Contains(output, "unit: lines")

  [<TestMethod>]
  member _.``Instruction mode renders disassembly and addresses``() =
    let output =
      run [ "mode=instructions"; "no-color" ]
        [| 0x90uy; 0xc3uy |]
        [| 0x90uy; 0x90uy; 0xc3uy |]
    StringAssert.Contains(output, "0000000000000000")
    StringAssert.Contains(output, "nop")
    StringAssert.Contains(output, "ret")

  [<TestMethod>]
  member _.``Section mode labels binary sections``() =
    let output =
      run [ "mode=sections"; "section=.text"; "no-color" ]
        [| 0x90uy; 0xc3uy |]
        [| 0x90uy; 0x90uy; 0xc3uy |]
    StringAssert.Contains(output, "[.text]")

  [<TestMethod>]
  member _.``Diff mode must be recognized``() =
    Assert.Throws<ArgumentException>(Action(fun () ->
      run [ "mode=unknown" ] [| 0uy |] [| 1uy |] |> ignore))
    |> ignore
