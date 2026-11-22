/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Sebastian Ullrich, Thomas Murrills
-/

/-
Source-header handling shared by `agitate` and `agitate-nonmodule`: parsing headers, decoding
imports, and applying `--fix` edits. Copied from upstream `Lake/CLI/Shake.lean` (Lean `v4.33.1`;
unchanged in `v4.36.0`).
-/
module

public import Lean.Util.Path
public import Lean.Parser.Module
import Init.Data.Range.Polymorphic.Iterators
meta import Lean.Parser.Module

public section

open Lean

namespace Agitate

/-- The list of edits that will be applied in `--fix`. `edits[i] = (removed, added)` where:

* If `j ∈ removed` then we want to delete module named `j` from the imports of `i`
* If `j ∈ added` then we want to add module index `j` to the imports of `i`.
-/
abbrev Edits := Std.HashMap Name (Array Import × Array Import)

/-- Register that we want to remove `tgt` from the imports of `src`. -/
def Edits.remove (ed : Edits) (src : Name) (tgt : Import) : Edits :=
  match ed.get? src with
  | none => ed.insert src (#[tgt], #[])
  | some (a, b) => ed.insert src (a.push tgt, b)

/-- Register that we want to add `tgt` to the imports of `src`. -/
def Edits.add (ed : Edits) (src : Name) (tgt : Import) : Edits :=
  match ed.get? src with
  | none => ed.insert src (#[], #[tgt])
  | some (a, b) => ed.insert src (a, b.push tgt)

/-- Parse a source file to extract the location of the import lines, for edits and error messages.

Returns `(path, inputCtx, imports, endPos)` where `imports` is the `Lean.Parser.Module.import` list
and `endPos` is the position of the end of the header.
-/
def parseHeaderFromString (text path : String) :
    IO (System.FilePath × (ictx : Parser.InputContext) ×
      TSyntax ``Parser.Module.header × String.Pos ictx.fileMap.source) := do
  let inputCtx := Parser.mkInputContext text path
  let (header, parserState, msgs) ← Parser.parseHeader inputCtx
  if !msgs.toList.isEmpty then -- skip this file if there are parse errors
    msgs.forM fun msg => msg.toString >>= IO.println
    throw <| .userError "parse errors in file"
  -- the insertion point for `add` is the first newline after the imports
  let insertion := header.raw.getTailPos?.getD parserState.pos
  let insertion := inputCtx.fileMap.source.pos! insertion |>.find (· == '\n')
  let insertion := insertion.next?.getD insertion
  pure ⟨path, inputCtx, header, insertion⟩

/-- Parse a source file to extract the location of the import lines, for edits and error messages.

Returns `(path, inputCtx, imports, endPos)` where `imports` is the `Lean.Parser.Module.import` list
and `endPos` is the position of the end of the header.
-/
def parseHeader (source? : Name → IO (Option System.FilePath)) (mod : Name) :
    IO (System.FilePath × (ictx : Parser.InputContext) ×
      TSyntax ``Parser.Module.header × String.Pos ictx.fileMap.source) := do
  -- Parse the input file
  let some path ← source? mod
    | throw <| .userError s!"error: failed to find source file for {mod}"
  let text ← IO.FS.readFile path
  parseHeaderFromString text path.toString

def decodeHeader : TSyntax ``Parser.Module.header → Option (TSyntax `module) × Option (TSyntax `prelude) × TSyntaxArray ``Parser.Module.import
  | `(Parser.Module.header| $[module%$moduleTk?]? $[prelude%$preludeTk?]? $imports*) =>
    (moduleTk?.map .mk, preludeTk?.map .mk, imports)
  | stx => panic! s!"unexpected header syntax {stx}"

def decodeImport : TSyntax ``Parser.Module.import → Import
  | `(Parser.Module.import| $[public%$pubTk?]? $[meta%$metaTk?]? import $[all%$allTk?]? $id) =>
    { module := id.getId, isExported := pubTk?.isSome, isMeta := metaTk?.isSome, importAll := allTk?.isSome }
  | stx => panic! s!"unexpected syntax {stx}"

/-- The parsed header of a module's source file: path, input context, header syntax, and the
insertion point for added imports (see `parseHeader`). -/
abbrev ParsedHeader :=
  System.FilePath × (ictx : Parser.InputContext) ×
    TSyntax ``Parser.Module.header × String.Pos ictx.fileMap.source

local instance : Ord Import where
  compare :=
    let _ := @lexOrd
    compareOn fun imp => (!imp.isExported, imp.module.toString)

/--
Applies `edits` to the source files whose parsed headers are given, for `--fix`; returns the number
of files changed. From the end of upstream `Lake.Shake.run`.
-/
def applyEdits (edits : Edits) (modNames : Array Name)
    (headers : Array (Task (Except IO.Error ParsedHeader))) : IO Nat := do
  let mut count := 0
  for mod in modNames, header? in headers do
    let some (remove, add) := edits[mod]? | continue
    let add : Array Import := add.qsortOrd

    -- Parse the input file
    let .ok ⟨path, inputCtx, stx, insertion⟩ := header?.get | continue
    let (_, _, imports) := decodeHeader stx
    let text := inputCtx.fileMap.source

    -- Calculate the edit result
    let mut pos : String.Pos text := text.startPos
    let mut out : String := ""
    let mut seen : Std.HashSet Import := {}
    for stx in imports do
      let mod := decodeImport stx
      if remove.contains mod || seen.contains mod then
        out := out ++ text.extract pos (text.pos! stx.raw.getPos?.get!)
        -- We use the end position of the syntax, but include whitespace up to the first newline
        pos := text.pos! stx.raw.getTailPos?.get! |>.find '\n'
        pos := pos.next?.getD pos
      seen := seen.insert mod
    out := out ++ text.extract pos insertion
    for mod in add do
      if !seen.contains mod then
        seen := seen.insert mod
        out := out ++ s!"{mod}\n"
    out := out ++ text.extract insertion text.endPos

    IO.FS.writeFile path out
    count := count + 1
  return count

/-- Whether a comment in the header (anywhere before the end of the imports) contains `marker`.
Non-module files have no `module` token to attach `shake: keep-all`/`keep-downstream` to. -/
def headerHasMarker (h : ParsedHeader) (marker : String) : Bool :=
  let ⟨_, ictx, _, endPos⟩ := h
  (ictx.fileMap.source.extract ictx.fileMap.source.startPos endPos).contains marker

/--
Rewrites a non-module source file as a module, for `modulate --fix` (`agitate` addition; the
layout follows core's `script/Modulize.lean`):
* `module` where the header starts. Text before it (comments) is kept, and `shake: keep-all` /
  `shake: keep-downstream` markers found in header comments are repeated on the `module` line,
  where module-mode shake reads them.
* `prelude` if the file had it.
* `imports`, one per line in module syntax. A kept import keeps the trailing comment on its line
  (e.g. `-- shake: keep`); comment lines between imports are dropped.
* `@[expose] public section`, or `public meta section` if `isMeta`, below an initial module
  docstring if there is one, else below the imports; none if no command follows the header.
-/
def convertToModuleText (h : ParsedHeader) (imports : Array Import) (isMeta : Bool) : IO String := do
  let ⟨_, ictx, stx, insertion⟩ := h
  let text := ictx.fileMap.source
  let (_, prelude?, importStxs) := decodeHeader stx
  let (_, parserState, msgs) ← Parser.parseHeader ictx
  let (initCmd, _, msgs') :=
    Parser.parseCommand ictx { env := ← mkEmptyEnvironment, options := {} } parserState msgs
  let hasCommands := !initCmd.isOfKind ``Parser.Command.eoi || msgs'.hasErrors
  let docEnd? := guard (initCmd.isOfKind ``Parser.Command.moduleDoc) *> initCmd.getTailPos?
  let mut comments : Std.HashMap Name String := {}
  for s in importStxs do
    if let some tr := s.raw.getTrailing? then
      let line := (tr.toString.splitOn "\n").headD ""
      if line.contains "--" then
        comments := comments.insert (decodeImport s).module (" " ++ line.trimAscii.copy)
  -- the header starts at its first token, or after the leading whitespace and comments
  let start := text.pos! (stx.raw.getPos?.getD parserState.pos)
  -- `insertion` is just after the line of the last header token
  let headerEnd := if stx.raw.getPos?.isSome then insertion else start
  let markers := ["shake: keep-all", "shake: keep-downstream"].filter (headerHasMarker h ·)
  let mut out := text.extract text.startPos start
  if !out.trimAscii.isEmpty then
    out := out.trimAsciiEnd.copy ++ "\n"
  out := out ++ "module" ++ (if markers.isEmpty then "" else " -- " ++ ", ".intercalate markers) ++ "\n\n"
  if prelude?.isSome then
    out := out ++ "prelude\n"
  for imp in imports do
    out := out ++ s!"{imp}" ++ comments.getD imp.module "" ++ "\n"
  let body := text.extract headerEnd text.endPos
  if !hasCommands then
    return out ++ body
  let sec := if isMeta then "public meta section" else "@[expose] public section"
  match docEnd? with
  | some p =>
    let p := text.pos! p
    return out ++ text.extract headerEnd p ++ "\n\n" ++ sec ++ text.extract p text.endPos
  | none =>
    return out ++ "\n" ++ sec ++ "\n" ++ (if body.startsWith "\n" then body else "\n" ++ body)

/-- Parses the headers of the modules selected by `pkgs`, in parallel (others get a dummy). -/
def parseHeaders (pkgs : Array Name) (source? : Name → IO (Option System.FilePath))
    (modNames : Array Name) :
    BaseIO (Array (Task (Except IO.Error ParsedHeader))) :=
  modNames.mapM fun mod =>
    if !pkgs.any (·.isPrefixOf mod) then
      pure <| Task.pure <| .ok ⟨default, default, default, default⟩
    else
      BaseIO.asTask (parseHeader source? mod |>.toBaseIO)

end Agitate
