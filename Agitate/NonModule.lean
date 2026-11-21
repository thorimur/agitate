/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Sebastian Ullrich, Thomas Murrills
-/

/-
`agitate-nonmodule`: import minimization for code that does not use the module system.

Non-module files are elaborated at the `.private` level, so every import behaves like `import all`
and is re-exported. There is a single kind of need. A module needs the modules that declare the
constants its terms refer to, its recorded extra module uses, and the indirect module uses of
those constants that it already reaches. Import closure is plain reachability. This file is the
single-kind counterpart of `Agitate.Shake.visitModule`, following its structure (and upstream
`Lake/CLI/Shake.lean`) step by step.

There is no oracle (`lake shake` refuses non-module code). Correctness is tested on
`tests/fixture-nonmodule` (golden output, `--fix` result builds, a second run suggests nothing).
-/
module

public import Agitate.Args
public import Agitate.Bitset
public import Agitate.Header
public import Agitate.Refs
import Init.Data.Range.Polymorphic.Iterators

open Lean

namespace Agitate.NonModule

/-- The state of the analysis. -/
structure State where
  ix : Index
  refs : RefCtx
  /--
  `transDeps[i]` is the non-reflexive transitive closure of the imports of module `i`. Since
  non-module imports re-export everything, this is plain reachability.
  -/
  transDeps : Array Bitset := #[]
  /-- `transDeps` before any edits. -/
  transDepsOrig : Array Bitset := #[]
  /-- Modules to keep downstream (`shake: keep-downstream`, extra reverse uses). -/
  preserve : Bitset := ∅
  edits : Edits := {}

/-- `j` together with everything it reaches. -/
def State.closure (s : State) (j : ModuleIdx) : Bitset :=
  s.transDeps[j]!.insert j

/-- The distinct modules imported by module `i` (the olean also records `Init` twice). -/
def importIdxs (ix : Index) (i : ModuleIdx) : Array ModuleIdx := Id.run do
  let mut out := #[]
  for imp in ix.imports i do
    if let some j := ix.getModuleIdx? imp.module then
      if !out.contains j then
        out := out.push j
  return out

def initState (ix : Index) (args : Args) : State := Id.run do
  let ignore kind := args.ignoreIndirectKinds.contains "*" || args.ignoreIndirectKinds.contains kind
  let refs : RefCtx := { ix, reserved := { ix, upstream := args.upstreamReserved },
                         reservedRefsToBase := args.reservedRefsToBase,
                         indirectModUses := ix.indirectModUsesExcept ignore,
                         implementedByNeeds := args.implementedByNeeds,
                         resolveDuplicates := args.resolveDuplicates }
  let mut transDeps : Array Bitset := #[]
  for i in 0...ix.size do
    let mut t : Bitset := ∅
    for j in importIdxs ix i do
      t := t ∪ transDeps[j]!.insert j
    transDeps := transDeps.push t
  return { ix, refs, transDeps, transDepsOrig := transDeps }

/--
The modules that module `i` needs: declarers of the constants its terms refer to (resolved once per
distinct name, see `resolveRef`), indirect uses it already reaches, and recorded extra module uses.
-/
def calcNeeds (s : State) (i : ModuleIdx) : Bitset := Id.run do
  let mut acc : Bitset × Std.HashMap Name (Option Resolved) := (∅, {})
  for ci in s.ix.constants i do
    acc := visitExpr ci.type acc
    if let some e := ci.value? (allowOpaque := true) then
      acc := visitExpr e acc
    if let some (_, j, _) := implementedByTarget? s.refs ci.name then
      if j != i then
        acc := (acc.1.insert j, acc.2)
  let mut needs := acc.1
  for use in s.ix.getExtraModUses i do
    if let some j := s.ix.getModuleIdx? use.module then
      needs := needs.insert j
  return needs
where
  visitExpr (e : Expr) (acc : Bitset × Std.HashMap Name (Option Resolved)) :
      Bitset × Std.HashMap Name (Option Resolved) :=
    Lean.Expr.foldConsts e acc fun c (deps, cache) => Id.run do
      let (r?, cache) := match cache[c]? with
        | some r? => (r?, cache)
        | none => let r? := resolveRef s.refs c; (r?, cache.insert c r?)
      let mut deps := deps
      if let some r := r? then
        if let some j := r.moduleFor i fun _ => #[(s.transDepsOrig[i]!.has ·)] then
          deps := deps.insert j
          for indMod in r.indirect do
            if s.transDepsOrig[i]!.has indMod then
              deps := deps.insert indMod
      return (deps, cache)

/-- For `--explain`: a `(user, used)` pair of constants per needed module, or `none` for a recorded
extra use (shortest user name wins, as upstream). -/
def getExplanations (s : State) (i : ModuleIdx) : Std.HashMap ModuleIdx (Option (Name × Name)) := Id.run do
  let mut deps := {}
  for ci in s.ix.constants i do
    deps := visitExpr ci.name ci.type deps
    if let some e := ci.value? (allowOpaque := true) then
      deps := visitExpr ci.name e deps
    if let some (g, j, _) := implementedByTarget? s.refs ci.name then
      if j != i then
        deps := add j ci.name g deps
  for use in s.ix.getExtraModUses i do
    if let some j := s.ix.getModuleIdx? use.module then
      if !deps.contains j then
        deps := deps.insert j none
  return deps
where
  visitExpr (name : Name) (e : Expr) deps :=
    Lean.Expr.foldConsts e deps fun c deps => Id.run do
      let mut deps := deps
      if let some r := resolveRef s.refs c then
        if let some j := r.moduleFor i fun _ => #[(s.transDepsOrig[i]!.has ·)] then
          deps := add j name c deps
          for indMod in r.indirect do
            if s.transDepsOrig[i]!.has indMod then
              deps := add indMod name (`_indirect ++ c) deps
      return deps
  add (j : ModuleIdx) (use def_ : Name) (deps : Std.HashMap ModuleIdx (Option (Name × Name))) :=
    if
      if let some (some (name', _)) := deps[j]? then
        decide (use.toString.chars.length < name'.toString.chars.length)
      else true
    then deps.insert j (some (use, def_))
    else deps

/-- Whether a comment in the header (anywhere before the end of the imports) contains `marker`.
Non-module files have no `module` token to attach `shake: keep-all`/`keep-downstream` to. -/
def headerHasMarker (h : ParsedHeader) (marker : String) : Bool :=
  let ⟨_, ictx, _, endPos⟩ := h
  (ictx.fileMap.source.extract ictx.fileMap.source.startPos endPos).contains marker

/-- Analyze and report on module `i`; the single-kind version of `Agitate.Shake.visitModule`. -/
def visitModule (pkgs : Array Name) (source? : Name → IO (Option System.FilePath)) (i : ModuleIdx)
    (needs : Bitset)
    (header : ParsedHeader) (args : Args) : StateT State IO Unit := do
  let ix := (← get).ix
  let modName := ix.modName i
  -- plain `import X`, as `decodeImport` reads it from non-module sources
  let imp (j : ModuleIdx) : Import := { module := ix.modName j, isExported := false }
  if ix.isExtraRevModUse i then
    modify fun s => { s with preserve := s.preserve.insert i }
    if args.trace then
      IO.eprintln s!"Preserving `{modName}` because of recorded extra rev use"

  -- only process modules in the selected packages
  if !pkgs.any (·.isPrefixOf modName) then
    return

  let ⟨_, _, headerStx, _⟩ := header
  let (_, prelude?, importStxs) := decodeHeader headerStx
  if headerHasMarker header "shake: keep-downstream" then
    modify fun s => { s with preserve := s.preserve.insert i }

  let s ← get
  let addOnly := (!args.onlyMods.isEmpty && !args.onlyMods.contains modName) ||
    headerHasMarker header "shake: keep-all"
  let mut deps := needs
  let mut reasons : Std.HashMap ModuleIdx String := {}

  -- Additional preserved imports
  for impStx in importStxs do
    let some j := ix.getModuleIdx? (decodeImport impStx).module | continue
    let reason? :=
      if impStx.raw.getTrailing?.any (·.toString.contains "shake: keep") then
        some "`shake: keep`"
      else if addOnly then
        some "`--only` / `shake: keep-all`"
      else none
    if let some msg := reason? then
      deps := deps.insert j
      reasons := reasons.insert j msg
      if args.trace then
        IO.eprintln s!"Adding `{imp j}` as additional dependency"
  for j in (s.preserve ∩ s.transDepsOrig[i]!).toArray do
    deps := deps.insert j
    reasons := reasons.insert j s!"`shake: keep-downstream`/extra rev use in `{ix.modName j}`"

  -- Transitive reduction of `deps` (only removes, so iterating a snapshot is exact)
  if !addOnly then
    for j in deps.toArray do
      if deps.has j then
        deps := deps \ s.transDeps[j]!

  if prelude?.isNone then
    if let some j := ix.getModuleIdx? `Init then
      deps := deps.insert j
      reasons := reasons.insert j "the implicit `Init` import"

  -- The closure of the still-live imports; folder-nested imports are always kept
  let imports := importIdxs ix i
  let mut transDeps : Bitset := ∅
  for j in imports do
    if deps.has j then
      transDeps := transDeps ∪ s.closure j
    else if modName.isPrefixOf (ix.modName j) then
      if args.trace then
        IO.eprintln s!"`{imp j}` is preserved as folder-nested import"
      transDeps := transDeps ∪ s.closure j
      deps := deps.insert j
      reasons := reasons.insert j "folder-nested import"

  -- Add back imports until the closure covers `deps`, in descending order so that new imports
  -- implied by other new imports are skipped
  let mut keptPrefix := false
  let mut newTransDeps := transDeps
  let mut toAdd : Array Import := #[]
  for j in deps.toArray.reverse do
    if deps.has j && !newTransDeps.has j then
      let mut j := j
      if args.trace then
        IO.eprintln s!"`{imp j}` is needed{if needs.has j then " (calculated)" else ""}"
      if args.keepPrefix then
        let rec tryPrefix : Name → Option ModuleIdx
          | .str p _ => tryPrefix p <|> (do
            let j' ← ix.getModuleIdx? p
            -- `j'` must be reachable from `i` and must reach `j`
            guard <| s.transDepsOrig[i]!.has j'
            guard <| s.transDeps[j']!.has j
            return j')
          | _ => none
        if let some j' := tryPrefix (ix.modName j) then
          if args.trace then
            IO.eprintln s!"* upgrading to `{imp j'}` because of `--keep-prefix`"
          reasons := reasons.insert j' s!"`--keep-prefix` upgrade from `{ix.modName j}`"
          j := j'
          keptPrefix := true
      if !imports.contains j then
        toAdd := toAdd.push (imp j)
      deps := deps.insert j
      newTransDeps := newTransDeps ∪ s.closure j

  if keptPrefix then
    -- `--keep-prefix` may have broken the descending order; redo the closure check
    newTransDeps := transDeps
    for j in deps.toArray.reverse do
      if deps.has j then
        if toAdd.contains (imp j) && newTransDeps.has j then
          if args.trace then
            IO.eprintln s!"Removing `{imp j}` from imports to be added because it is now implied"
          toAdd := toAdd.erase (imp j)
          deps := deps.erase j
        else
          newTransDeps := newTransDeps ∪ s.closure j

  -- Any import still not in `deps` is unused (`Init` is implicit and never in the source)
  let mut toRemove : Array Import := #[]
  for j in imports do
    if prelude?.isNone && ix.modName j == `Init then
      continue
    if args.keepImplied && newTransDeps.has j then
      if args.trace && !deps.has j then
        IO.eprintln s!"`{imp j}` is implied by other imports"
    else if !deps.has j then
      if args.trace then
        IO.eprintln s!"`{imp j}` is now unused"
      toRemove := toRemove.push (imp j)

  modify fun s => { s with edits := toRemove.foldl (init := s.edits) (·.remove modName ·) }

  if !toAdd.isEmpty || !toRemove.isEmpty || args.explain then
    if let some path ← source? modName then
      println! "{path}:"
    else
      println! "{modName}:"

  if !toRemove.isEmpty then
    println! "  remove {toRemove}"

  if args.githubStyle then
    let ⟨path, inputCtx, _, endHeader⟩ := header
    for stx in importStxs do
      if toRemove.any (· == decodeImport stx) then
        let pos := inputCtx.fileMap.toPosition stx.raw.getPos?.get!
        println! "{path}:{pos.line}:{pos.column+1}: warning: unused import \
          (use `agitate-nonmodule --fix` to fix this)"
    if !toAdd.isEmpty then
      let pos := inputCtx.fileMap.toPosition endHeader.offset
      println! "{path}:{pos.line-1}:1: warning: add {toAdd} instead"

  modify fun s => { s with edits := toAdd.foldl (init := s.edits) (·.add modName ·) }

  if !toAdd.isEmpty then
    println! "  add {toAdd}"

  -- Recalculate the transitive dependencies of `i` for downstream modules
  let mut newTransDepsI : Bitset := ∅
  for j in imports do
    if !toRemove.contains (imp j) then
      newTransDepsI := newTransDepsI ∪ s.closure j
  for a in toAdd do
    if let some j := ix.getModuleIdx? a.module then
      newTransDepsI := newTransDepsI ∪ s.closure j
  modify fun s => { s with transDeps := s.transDeps.set! i newTransDepsI }

  if args.explain then
    let explanation := getExplanations s i
    let sanitize n := if n.hasMacroScopes then (sanitizeName n).run' { options := {} } else n
    let explainOne (j : ModuleIdx) := do
      println! "  note: `{imp j}` required"
      match explanation[j]? with
      | some (some (n, c)) => println! "    because `{sanitize n}` refers to `{sanitize c}`"
      | some none => println! "    because of additional compile-time dependencies"
      | none =>
        if let some msg := reasons[j]? then
          println! "    because of {msg}"
        else
          println! "    (no traced reason)"
    for j in imports do
      if !toRemove.contains (imp j) then
        explainOne j
    for a in toAdd do
      if let some j := ix.getModuleIdx? a.module then
        explainOne j

/-- Run the analysis. Assumes Lean's search path has been configured. -/
public def run (args : Args) (r : Resolver) : IO UInt32 := do
  let timed {α} := args.timed (α := α)
  let pkgs := args.mods.map (·.getRoot)
  let modules ← timed "readModules" <| readModules r.olean args.mods (allowNonModule := true)
  let ix ← timed "Index.build" <| Index.build modules Reserved.extNames
  let s ← timed "initState (transDeps)" <| IO.lazyPure fun _ => initState ix args
  if args.listIndirectKinds then
    printIndirectKinds ix
    return 0

  StateT.run' (s := s) do
  let s ← get
  let needs := ix.modNames.mapIdx fun i _ =>
    if !pkgs.any (·.isPrefixOf (ix.modName i)) then Task.pure ∅
    else Task.spawn fun _ => calcNeeds s i
  if args.profile then
    timed "calcNeeds (selected modules, parallel)" <| needs.forM fun t => discard <| IO.wait t
  let headers ← parseHeaders pkgs r.source? ix.modNames

  if args.fix then
    println! "The following changes will be made automatically:"

  let t0 ← IO.monoNanosNow
  for i in [0:ix.size], t in needs, header in headers do
    match header.get with
    | .ok h => visitModule pkgs r.source? i t.get h args
    | .error e => println! e.toString
  if args.profile then
    IO.eprintln s!"[profile] visitModule loop (sequential): {((← IO.monoNanosNow) - t0) / 1000000} ms"

  if !args.fix then
    return if (← get).edits.isEmpty then 0 else 1
  let count ← applyEdits (← get).edits ix.modNames headers
  if count > 0 then
    println! "Successfully applied {count} suggestions."
  else
    println! "No edits required."
  return 0

end Agitate.NonModule
