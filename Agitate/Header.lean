/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Sebastian Ullrich, Thomas Murrills
-/

/-
Source-header handling shared by `agitate` and `agitate-nonmodule`: parsing headers, decoding
imports, and applying `--fix` edits. Copied from upstream `Lake/CLI/Shake.lean` (Lean `v4.33.1`).
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
def parseHeader (srcSearchPath : SearchPath) (mod : Name) :
    IO (System.FilePath × (ictx : Parser.InputContext) ×
      TSyntax ``Parser.Module.header × String.Pos ictx.fileMap.source) := do
  -- Parse the input file
  let some path ← srcSearchPath.findModuleWithExt "lean" mod
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

/-- Parses the headers of the modules selected by `pkgs`, in parallel (others get a dummy). -/
def parseHeaders (pkgs : Array Name) (srcSearchPath : SearchPath) (modNames : Array Name) :
    BaseIO (Array (Task (Except IO.Error ParsedHeader))) :=
  modNames.mapM fun mod =>
    if !pkgs.any (·.isPrefixOf mod) then
      pure <| Task.pure <| .ok ⟨default, default, default, default⟩
    else
      BaseIO.asTask (parseHeader srcSearchPath mod |>.toBaseIO)

end Agitate
