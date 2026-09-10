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

module B2R2.RearEnd.Transformer.Program

open System
open System.IO
open System.Reflection
open B2R2
open B2R2.FrontEnd
open B2R2.RearEnd.Utils

let private usage = $"""[Usage]
b2r2 transformer [-d file] [action] (-- [action] ...){"\n"}
Transformer runs a chain of transforming actions (IAction). An action takes in a
collection of objects as input and returns another collection of objects as
output. Any number of actions can be chained together as long as their types
match. Users can define their own action(s) by implementing the IAction
interface.{"\n"}
[Options]{"\n"}
-d <dll file>  : Load a dll file defining custom actions.{"\n"}
[Actions]
"""

/// The `help` action.
type private HelpAction(map: Map<string, IAction>) =
  interface IAction with
    member _.ActionID with get() = "help"
    member _.Signature with get() = "'a -> 'b"
    member _.Description with get() = ""
    member _.Transform(_args, _) =
      printsn ""
      CmdOpts.writeIntro ()
      printsn usage
      map |> Map.iter (fun id act ->
        printsn $"- {id}: {act.Signature}"
        printsn $"{act.Description}")
      exit 0

let private accumulateActions map actions =
  actions
  |> Array.fold (fun map t ->
    let act = Activator.CreateInstance t :?> IAction
    if Map.containsKey act.ActionID map then
      invalidOp $"Duplicate action ID: {act.ActionID}"
    else
      Map.add act.ActionID act map) map

let inline private filterIActionType types =
  (types: System.Type[])
  |> Array.filter (fun t ->
    t.IsPublic
    && (t.GetInterface(nameof IAction) |> isNull |> not))

let private loadUserDLL dllPath =
  if File.Exists dllPath then
    let dllPath = Path.GetFullPath dllPath
    let dll = Assembly.LoadFile dllPath
    dll.GetExportedTypes()
    |> filterIActionType
    |> accumulateActions Map.empty
  else
    invalidOp $"File not found: {dllPath}"

let private retrieveActionMap map =
  let actionType = typeof<IAction>
  let map =
    actionType.Assembly.GetExportedTypes()
    |> filterIActionType
    |> accumulateActions map
  let helpAction = HelpAction map :> IAction
  Map.add helpAction.ActionID helpAction map

let private splitBySpecialSeparators (args: string list) =
  args
  |> List.collect (fun arg ->
    arg.Replace("--", " -- ").Replace(",", " , ")
      .Split(' ', StringSplitOptions.RemoveEmptyEntries) |> Array.toList)

let rec private breakCommandByComma cmds cmd = function
  | [] ->
    List.rev (List.rev cmd :: cmds)
  | "," :: rest ->
    let cmds = if List.isEmpty cmd then cmds else (List.rev cmd) :: cmds
    breakCommandByComma cmds [] rest
  | arg :: rest ->
    breakCommandByComma cmds (arg :: cmd) rest

let private accumulateIfNotEmpty grp acc =
  if List.isEmpty grp then acc else List.rev grp :: acc

let rec private parseActionCommands grps grp = function
  | [] ->
    List.rev (accumulateIfNotEmpty grp grps)
  | "--" :: rest ->
    let grps = if List.isEmpty grp then grps else accumulateIfNotEmpty grp grps
    parseActionCommands grps [] rest
  | arg :: rest ->
    parseActionCommands grps (arg :: grp) rest

let private checkValidityOfCommandGroup cmdgrp =
  let actionIDs = cmdgrp |> List.map List.tryHead
  let fstActionID = List.head actionIDs
  if actionIDs |> List.forall (fun actionID -> actionID = fstActionID) then
    ()
  else
    eprintsn "different actions in the same group."
    exit 1

let private runCommand actionMap input (cmd: string list) =
  let actionID = List.head cmd
  let args = List.tail cmd
  let action: IAction =
    match Map.tryFind (actionID.ToLowerInvariant()) actionMap with
    | Some act ->
      act
    | None ->
      eprintsn $"({actionID}) is not a valid action."
      exit 1
#if DEBUG
  if actionID <> "help" then printsn $"[*] {actionID}" else ()
#endif
  try
    action.Transform(args, input)
  with
    | :? InvalidCastException ->
      eprintsn $"({actionID}) action type mismatch."
      exit 1
    | :? NullReferenceException ->
      eprintsn $"({actionID}) action should follow another."
      exit 1
    | :? ArgumentException as e ->
      eprintsn $"{e.Message}"
      exit 1
    | e ->
      eprintsn $"({actionID}): {e}"
      exit 1

let inline private unwrap (c: ObjCollection) = c.Values

let autoPrint actionMap collection =
  if collection.Values.Length = 0 then ()
  else runCommand actionMap collection [ "print" ] |> ignore

let private parseActions args actionMap =
  args
  |> splitBySpecialSeparators
  |> parseActionCommands [] []
  |> List.map (breakCommandByComma [] [])
  |> List.fold (fun input cmdgrp ->
    checkValidityOfCommandGroup cmdgrp
    { Values = cmdgrp
               |> List.map (fun cmd -> runCommand actionMap input cmd |> unwrap)
               |> Array.concat }
  ) { Values = [| () |] }
  |> autoPrint actionMap

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
  let action = DiffAction() :> IAction
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

let diffMain argv =
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

[<EntryPoint>]
let main argv =
  match List.ofArray argv with
  | [] ->
    retrieveActionMap Map.empty
    |> parseActions [ "help" ]
    |> ignore
  | "-d" :: file :: args ->
    loadUserDLL file
    |> retrieveActionMap
    |> parseActions args
    |> ignore
  | args ->
    retrieveActionMap Map.empty
    |> parseActions args
    |> ignore
  0
