(*
  B2R2 - the Next-Generation Reversing Platform

  Author: Sang Kil Cha <sangkilc@kaist.ac.kr>

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

module internal B2R2.BinFile.Mach.Helper

open B2R2
open B2R2.BinFile

let rec getMainCmd = function
  | [] -> raise FileFormatMismatchException
  | Main m :: _ -> m
  | _ :: tl -> getMainCmd tl

let rec getPageZeroSeg = function
  | [] -> raise FileFormatMismatchException
  | Segment s :: _ when s.SegName = "__PAGEZERO" -> s
  | _ :: tl -> getPageZeroSeg tl

let parseMach offset reader  =
  let machHdr = Header.parse reader offset
  let cmds = LoadCommands.parse reader offset machHdr
  let segs = Segment.filter cmds
  let secs = Section.parseSections reader machHdr.Class segs
  let symInfo = Symbol.parse machHdr cmds secs reader
  { EntryPoint = (getPageZeroSeg cmds).VMSize + (getMainCmd cmds).EntryOff
    SymInfo = symInfo
    MachHdr = machHdr
    Segments = segs
    Sections = secs }

let initMach bytes =
  let reader = BinReader.Init (bytes)
  if Header.isMach reader 0 then ()
  else raise FileFormatMismatchException
  Header.peekEndianness reader 0
  |> BinReader.RenewReader reader
  |> parseMach 0

let transFileType = function
  | MachFileType.MHExecute -> FileType.ExecutableFile
  | MachFileType.MHObject -> FileType.ObjFile
  | MachFileType.MHDylib | MachFileType.MHFvmlib -> FileType.LibFile
  | MachFileType.MHCore -> FileType.CoreFile
  | _ -> FileType.UnknownFile

let tryFindFunctionSymb mach addr =
  match Map.tryFind addr mach.SymInfo.SymbolMap with
  | Some s -> Some s.SymName
  | None -> None

let machTypeToSymbKind (sym: MachSymbol) =
  if sym.SymType.HasFlag SymbolType.NFun then
    if sym.IsExternal then SymbolKind.ExternFunctionType
    else SymbolKind.FunctionType
  elif sym.SymType.HasFlag SymbolType.NSO
    || sym.SymType.HasFlag SymbolType.NOSO then
    SymbolKind.FileType
  else
    SymbolKind.NoType

let machSymbolToSymbol target (sym: MachSymbol) =
  { Address = sym.SymAddr
    Name = sym.SymName
    Kind = machTypeToSymbKind sym
    Target = target
    LibraryName = Symbol.getSymbolLibName sym }

let getAllStaticSymbols mach =
  mach.SymInfo.Symbols
  |> Array.filter (fun s -> int s.SymType &&& 0xe0 <> 0
                         || s.SymType.HasFlag SymbolType.NStSym)
  |> Array.map (machSymbolToSymbol TargetKind.StaticSymbol)

let getAllDynamicSymbols mach =
  mach.SymInfo.Symbols
  |> Array.filter (fun s -> int s.SymType &&& 0xe0 = 0
                         && not (s.SymType.HasFlag SymbolType.NSect))
  |> Array.map (machSymbolToSymbol TargetKind.DynamicSymbol)

let secFlagToSectionKind = function
  | SectionType.NonLazySymbolPointers
  | SectionType.LazySymbolPointers
  | SectionType.SymbolStubs -> SectionKind.LinkageTableSection
  | SectionType.Regular -> SectionKind.ExecutableSection
  | _ -> SectionKind.ExtraSection

let machSectionToSection (sec: MachSection) =
  { Address = sec.SecAddr
    Kind = secFlagToSectionKind sec.SecType
    Size = sec.SecSize
    Name = sec.SecName }

// vim: set tw=80 sts=2 sw=2:
