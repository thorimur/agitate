/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/

/-
The imports of each project module once some items are deleted, for `percolate`: the deletion
tool can rewrite headers without a rebuild, and it exercises the import algebra and stances of
`Agitate.ImportGraph` on real needs.

A module needs what its remaining declarations need from other modules (`Stance.importNeeds`, with
presentability propagated through its meta declarations), its recorded extra module uses
(commands can remain without declarations, so these are kept), and, as shake counts them, the
modules recording attributes on what it uses that it reached before. Three needs that terms do not
show are recovered from what the oleans record:
* Auxiliary declarations (abstracted proofs, matchers, …) count as being where their parent uses
  them: a proof abstracted from an exposed definition was elaborated in its public value.
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
def moduleImportNeeds (refs : RefCtx) (a : Analysis) (isToolchain : Array Bool)
    (indirect : Std.HashMap Name (Array ModuleIdx)) (deleted : Nat → Bool) (reached : Bitset)
    (i : ModuleIdx) : ImportNeeds := Id.run do
  let ix := refs.ix
  let order : Thunk (Array Index.LoadedModule) := .mk fun _ => ix.loadOrder i
  let consts : Std.HashMap Name ConstantInfo :=
    ix.constants i |>.foldl (fun m ci => m.insert ci.name ci) {}
  let ranged : Std.HashSet Name := a.items[i]!.items.foldl (init := {}) fun s it =>
    if it.range.isSome then it.names.foldl (·.insert ·) s else s
  -- the declaration of `i` an auxiliary declaration (no range of its own) was made for
  let parentOf? (c : Name) : Option Name := Id.run do
    if ranged.contains c then return none
    let mut n := c
    for _ in 0...64 do
      let p := n.getPrefix
      if p.isAnonymous then return none
      if consts.contains p then return some p
      if isPrivateName p && consts.contains (privateToUserName p) then
        return some (privateToUserName p)
      n := p
    return none
  -- an auxiliary declaration counts as being where its parent uses it: abstracted proofs of an
  -- exposed definition were elaborated in its public value
  let rec exportedAt (c : Name) (fuel : Nat) : Bool :=
    match fuel, parentOf? c with
    | fuel + 1, some p =>
      let sp := stanceOf ix p
      let inType := (consts[p]?).any fun ci => ci.type.getUsedConstants.contains c
      (if inType then sp.isPublic else sp.isExposed) || exportedAt p fuel
    | _, _ => false
  -- the constants that stay, with their stances and resolved references
  let mut kept : Array (Name × Stance × Array (Name × ModuleIdx × NeedKinds)) := #[]
  for ci in ix.constants i do
    if let some r := a.items[i]!.constItem[ci.name]? then
      if deleted (a.globalId r) then continue
    let su := stanceOf ix ci.name
    let su := if exportedAt ci.name 8 then { su with isExposed := true } else su
    -- an auxiliary declaration of code (a matcher, say) is checked in its parent's phase
    let su := match su.phase, parentOf? ci.name with
      | .none, some p => { su with phase := (stanceOf ix p).phase }
      | _, _ => su
    let (names, kinds) := constRefs refs ci (code := su.phase != Phase.none)
    let mut rs := #[]
    for h : e in 0...names.size do
      if let some (m, j, _) := resolveDecl refs order i names[e] then
        rs := rs.push (m, j, (⟨kinds.get! e⟩ : NeedKinds))
    kept := kept.push (ci.name, su, rs)
  -- presentable code: public meta declarations, and the meta declarations of `i` their code reaches
  let localCode : Std.HashMap Name (Array Name) := kept.foldl (init := {}) fun m (n, su, rs) =>
    if su.phase == .meta then
      m.insert n (rs.filterMap fun (d, j, k) => if j == i && k.has .code then some d else none)
    else m
  let mut presentable : Std.HashSet Name := {}
  let mut todo := kept.filterMap fun (n, su, _) =>
    if su.phase == .meta && su.isPublic then some n else none
  while let some n := todo.back? do
    todo := todo.pop
    if presentable.contains n then continue
    presentable := presentable.insert n
    todo := todo ++ localCode[n]?.getD #[]
  let mut out : ImportNeeds := {}
  for (n, su, rs) in kept do
    for (d, j, k) in rs do
      if j == i then continue
      for need in su.importNeeds k (stanceOf ix d) (presentable := presentable.contains n) do
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
nothing gather imports (`Mathlib.lean`) and keep theirs.
-/
def importsAfter (refs : RefCtx) (a : Analysis) (isToolchain : Array Bool) (deleted : Nat → Bool)
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
        some (moduleImportNeeds refs a isToolchain indirect deleted (Needs.flatten orig[i]!) i)
    else .pure none
  let needs ← needTasks.mapM fun t => IO.wait t
  let t2 ← IO.monoMsNow
  let mut h : Hierarchy := .emptyWithCapacity ix.size
  let mut out : Array (Option (Array Import)) := .emptyWithCapacity ix.size
  for i in 0...ix.size do
    let imps := ix.imports i
    -- files that declare nothing gather imports (`Mathlib.lean`): they keep them
    let aggregator := a.isProject[i]! && (ix.constants i).isEmpty
    match if aggregator then none else needs[i]! with
    | none =>
      h := h.push (h.provides i (imps.filterMap fun imp => (idx imp).map (·, kindOf i imp)))
      out := out.push (if aggregator then some imps else none)
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
