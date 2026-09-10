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

module B2R2.RearEnd.Transformer.ForkDiff.DiffCommand

open System
open System.IO
open B2R2
open B2R2.FrontEnd
open B2R2.RearEnd.Utils
open B2R2.RearEnd.Transformer

let private diffUsage = """[Usage]
b2r2 diff [options] <left file> <right file>
b2r2 diff [options] --batch <pair manifest>

[Options]
--algorithm <myers|histogram>  Select the diff algorithm (default: myers).
--format <side-by-side|summary|json>
                               Select the output format.
--mode <bytes|text|instructions|sections>
                               Select comparison semantics.
--isa <name>                   Specify the ISA used for disassembly.
--section <name>               Compare one named section.
--context <rows>               Show unchanged rows around changes.
--width <bytes>                Set byte columns per row (default: 16).
--column <characters>          Set semantic column width (default: 72).
--no-color                     Disable colored output.
--batch <file>                 Compare tab- or pipe-separated path pairs.
"""

let private parseDiffArgs argv =
  let rec loop paths options batch = function
    | [] ->
      List.rev paths, List.rev options, batch
    | ("--help" | "-h") :: _ ->
      printsn diffUsage
      exit 0
    | "--algorithm" :: value :: rest ->
      loop paths (value :: options) batch rest
    | "--format" :: value :: rest ->
      loop paths (value :: options) batch rest
    | "--mode" :: value :: rest ->
      loop paths ($"mode={value}" :: options) batch rest
    | "--isa" :: value :: rest ->
      loop paths ($"isa={value}" :: options) batch rest
    | "--section" :: value :: rest ->
      loop paths ($"section={value}" :: options) batch rest
    | "--context" :: value :: rest ->
      loop paths ($"context={value}" :: options) batch rest
    | "--width" :: value :: rest ->
      loop paths ($"width={value}" :: options) batch rest
    | "--column" :: value :: rest ->
      loop paths ($"column={value}" :: options) batch rest
    | "--no-color" :: rest ->
      loop paths ("no-color" :: options) batch rest
    | "--batch" :: value :: rest ->
      loop paths options (Some value) rest
    | option :: rest when option.StartsWith("--algorithm=") ->
      loop paths (option[12..] :: options) batch rest
    | option :: rest when option.StartsWith("--format=") ->
      loop paths (option[9..] :: options) batch rest
    | option :: rest when option.StartsWith("--mode=") ->
      loop paths (option[2..] :: options) batch rest
    | option :: rest when option.StartsWith("--isa=") ->
      loop paths (option[2..] :: options) batch rest
    | option :: rest when option.StartsWith("--section=") ->
      loop paths (option[2..] :: options) batch rest
    | option :: rest when option.StartsWith("--context=") ->
      loop paths (option[2..] :: options) batch rest
    | option :: rest when option.StartsWith("--width=") ->
      loop paths (option[2..] :: options) batch rest
    | option :: rest when option.StartsWith("--column=") ->
      loop paths (option[2..] :: options) batch rest
    | option :: rest when option.StartsWith("--batch=") ->
      loop paths options (Some option[8..]) rest
    | option :: _ when option.StartsWith('-') ->
      invalidArg (nameof argv) $"Unknown diff option: {option}"
    | path :: rest ->
      loop (path :: paths) options batch rest
  loop [] [] None (List.ofArray argv)

let private loadBinary isa path =
  if not (File.Exists path) then
    invalidArg (nameof path) $"File not found: {path}"
  else
    ()
  lazy BinHandle.LoadFile(path, isa, None)
  |> Binary.PlainInit

let private diffISA options =
  options
  |> List.tryPick (fun (option: string) ->
    match option.Split('=', 2) with
    | [| "isa"; name |] -> Some(ISA name)
    | _ -> None)
  |> Option.defaultValue (ISA Architecture.Intel)

let private makeDiffOutput options left right =
  let isa = diffISA options
  let action = EnhancedDiffAction() :> IAction
  let input =
    { Values = [| box (loadBinary isa left); box (loadBinary isa right) |] }
  action.Transform(options, input).Values[0] :?> OutString

let private trimManifestPath (path: string) =
  path.Trim().Trim('"')

let private parseManifestPair lineNumber (line: string) =
  if String.IsNullOrWhiteSpace line || line.TrimStart().StartsWith('#') then
    None
  else
    let separator = if line.Contains('\t') then '\t' else '|'
    match line.Split(separator, 2) with
    | [| left; right |] ->
      Some(trimManifestPath left, trimManifestPath right)
    | _ ->
      invalidArg (nameof line)
        $"Invalid pair manifest entry at line {lineNumber}."

let private resolveManifestPath directory (path: string) =
  if Path.IsPathRooted path then path else Path.Combine(directory, path)

let private runBatch options manifest =
  if not (File.Exists manifest) then
    invalidArg (nameof manifest) $"File not found: {manifest}"
  else
    ()
  let directory = Path.GetDirectoryName(Path.GetFullPath manifest)
  let isJson = List.contains "json" options
  File.ReadAllLines manifest
  |> Array.iteri (fun idx line ->
    match parseManifestPair (idx + 1) line with
    | Some(left, right) ->
      let left = resolveManifestPath directory left
      let right = resolveManifestPath directory right
      if not isJson then printsn $"[*] pair {idx + 1}: {left} <> {right}"
      else ()
      makeDiffOutput options left right |> printon
    | None ->
      ())

let run argv =
  try
    match parseDiffArgs argv with
    | [ left; right ], options, None ->
      makeDiffOutput options left right |> printon
      0
    | [], options, Some manifest ->
      runBatch options manifest
      0
    | _ ->
      eprintsn "Diff requires exactly two file paths."
      eprintsn diffUsage
      1
  with
  | :? ArgumentException as e ->
    eprintsn e.Message
    1
  | e ->
    eprintsn $"diff: {e.Message}"
    1
