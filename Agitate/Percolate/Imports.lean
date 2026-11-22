/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/

/-
The imports of each project module once some items are deleted, for `percolate`: the deletion
tool can rewrite headers without a rebuild, and it exercises the import algebra and stances of
`Agitate.ImportGraph` on real needs.

A module needs what its remaining declarations need from other modules (`moduleDeclNeeds`, turned
into imports by `Stance.importNeeds`), its recorded extra module uses (commands can remain without
declarations, so these are kept), and, as shake counts them, the modules recording attributes on
what it uses that it reached before. Two needs that declarations do not show are recovered from
what the oleans record:
* Entries in an extension registered by `initialize` (an attribute, say) need its initializer to
  have run while elaborating: any import of its module if the initializer is meta code, a meta
  import if it is runtime code. The toolchain's initializers are part of `lean` and always run.
* `import all`s are kept, as shake keeps them: they serve unfolding non-exposed definitions, which
  leaves no trace in terms. Modules are processed in
`ModuleIdx` order (imports first): a project module's new imports are `ImportNeeds.reduce` over the
hierarchy of the new imports of the modules before it; other modules keep theirs.

Non-module files are plain reachability: every need becomes a phaseless public need, and their
imports re-export everything (`import` there is kept as kind `pub` in the hierarchy).
-/
module

public import Agitate.Percolate.Needs
public import Agitate.ImportGraph.Imports
public import Lean.Compiler.InitAttr

public section

open Lean Agitate.ImportGraph

namespace Agitate.Percolate

/-- The modules of `p` at every kind, as one set. -/
def Needs.flatten (p : Needs) : Bitset :=
  ImportKind.kinds.foldl (init := ∅) fun s k => s ∪ p.get k

/--
Module `i`'s import needs once the items `deleted` are gone. `indirect` are the indirect module uses
(per used declaration, the modules that applied attributes to it), and `reached` the modules `i`
reached before.
-/
def moduleImportNeeds (refs : RefCtx) (a : Analysis) (dnOf : ModuleIdx → ModuleDeclNeeds)
    (isToolchain : Array Bool)
    (indirect : Std.HashMap Name (Array ModuleIdx)) (deleted : Nat → Bool) (reached : Bitset)
    (i : ModuleIdx) : ImportNeeds := Id.run do
  let ix := refs.ix
  -- a module whose items are all deleted keeps only the needs of what is not a declaration
  let anyKept := (List.range a.items[i]!.items.size).any fun k => !deleted (a.offset[i]! + k)
  let mut out : ImportNeeds := {}
  if anyKept then
    let dn := dnOf i
    let kept := dn.consts.map fun ci =>
      (a.items[i]!.constItem[ci.name]?).all fun r => !deleted (a.globalId r)
    for h : e in 0...dn.users.size do
      let u := dn.users[e]
      let j := dn.usedMods[e]!
      if j == i || !kept[u]! then continue
      let d := dn.used[e]!
      for need in dn.stances[u]!.importNeeds ⟨dn.kinds[e]!⟩ (stanceOf ix d) do
        out := out.insert need j
      for q in indirect[d]?.getD #[] do
        if q != i && reached.has q then
          out := out.insert { isExported := false } q
  -- an extension registered by `initialize` (attributes, …) exists while elaborating only if its
  -- initializer ran: through any import if it is meta code, through a `meta import` if it is runtime
  -- code; the toolchain's initializers are part of `lean` and always run
  for (ext, es) in ix.modules[i]!.priv.entries do
    if es.isEmpty then continue
    if let some j := ix.getModuleIdxFor? ext then
      if j != i && !isToolchain[j]! && (ix.getParam? regularInitAttr ext).isSome then
        out := out.insert
          { isExported := false, isMeta? := if isDeclMeta' ix ext then none else some true } j
  -- `import all` is kept, as shake does: it serves unfolding non-exposed definitions, which leaves
  -- no reference in terms
  for imp in ix.imports i do
    if imp.importAll then
      if let some j := ix.getModuleIdx? imp.module then
        out := out.insert { isExported := false, isAll := true,
                            isMeta? := if imp.isMeta then some true else none } j
  for use in ix.getExtraModUses i do
    if let some j := ix.getModuleIdx? use.module then
      if j != i then
        out := out.insert { isExported := use.isExported,
                            isMeta? := if use.isMeta then some true else none } j
  if !ix.modules[i]!.priv.isModule then
    return { any := { pub := Needs.flatten out.phased ∪ Needs.flatten out.any } }
  return out

/-- A module's imports, as written in its header (without the implicit `Init` imports). -/
def importStrings (imps : Array Import) (isModule : Bool) : Array String :=
  imps.filterMap fun imp =>
    if imp.module == `Init then none
    else if isModule then some s!"{(ImportKind.ofImport imp).toImportString} {imp.module}"
    else some s!"import {imp.module}"

/--
The imports of each project module once the items `deleted` are gone (`none` for other modules),
computed in `ModuleIdx` order over the hierarchy of the new imports. Project modules that declare
nothing gather imports (`Mathlib.lean`): they need exactly what they import, so only imports that
the others already provide are dropped.
-/
def importsAfter (refs : RefCtx) (a : Analysis) (dnOf : ModuleIdx → ModuleDeclNeeds)
    (isToolchain : Array Bool) (deleted : Nat → Bool)
    (profile : Bool := false) :
    IO (Array (Option (Array Import))) := do
  let ix := refs.ix
  let kindOf (i : ModuleIdx) (imp : Import) : ImportKind :=
    if ix.modules[i]!.priv.isModule then .ofImport imp else .pub
  let idx (imp : Import) : Option Nat := (ix.getModuleIdx? imp.module).map (·.toNat)
  -- the hierarchy as it is, for "reached before"
  let t0 ← IO.monoMsNow
  let orig ← IO.lazyPure fun _ => Id.run do
    let mut h : Hierarchy := .emptyWithCapacity ix.size
    for i in 0...ix.size do
      let imps := (ix.imports i).filterMap fun imp => (idx imp).map (·, kindOf i imp)
      h := h.push (h.provides i imps)
    return h
  let t1 ← IO.monoMsNow
  let indirect := ix.indirectModUsesExcept fun _ => false
  let needTasks := (Array.range ix.size).map fun i =>
    if a.isProject[i]! then
      Task.spawn fun _ =>
        some (moduleImportNeeds refs a dnOf isToolchain indirect deleted (Needs.flatten orig[i]!) i)
    else .pure none
  let needs ← needTasks.mapM fun t => IO.wait t
  let t2 ← IO.monoMsNow
  let mut h : Hierarchy := .emptyWithCapacity ix.size
  let mut out : Array (Option (Array Import)) := .emptyWithCapacity ix.size
  for i in 0...ix.size do
    let imps := ix.imports i
    -- files that declare nothing gather imports (`Mathlib.lean`): they need what they import, each
    -- in its own kind, so that the reduction only drops imports the others already provide
    let aggregator := a.isProject[i]! && (ix.constants i).isEmpty
    let needsI := if aggregator then
        some <| imps.foldl (init := ({} : ImportNeeds)) fun n imp =>
          if imp.module == `Init then n else match idx imp with
          | some j => n.insert { isExported := imp.isExported, isAll := imp.importAll,
                                 isMeta? := some imp.isMeta } j
          | none => n
      else needs[i]!
    match needsI with
    | none =>
      h := h.push (h.provides i (imps.filterMap fun imp => (idx imp).map (·, kindOf i imp)))
      out := out.push none
    | some n =>
      -- the implicit `Init` imports stay, and provide what they provide
      let inits := imps.filter (·.module == `Init) |>.filterMap fun imp => (idx imp).map (·, kindOf i imp)
      let base := inits.foldl (init := Needs.reflOf i) fun acc (j, k) => acc ∪ h.closure j k
      let reduced := n.reduce h base
      let newImps := reduced.toArray.map fun (k, j) => (j, k)
      h := h.push (h.provides i (inits ++ newImps))
      let isModule := ix.modules[i]!.priv.isModule
      out := out.push <| some <| (reduced.toImports ix.modName).map fun imp =>
        if isModule then imp else { imp with isExported := false }
  let t3 ← IO.monoMsNow
  if profile then
    IO.eprintln s!"[profile] imports: original hierarchy {t1 - t0} ms, needs (parallel) {t2 - t1} ms, \
      reduction {t3 - t2} ms"
  return out

end Agitate.Percolate
