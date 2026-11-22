/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/

/-
Declaration needs from the olean index: for every declaration of a module, what it needs and how
(`Agitate.ImportGraph.DeclNeedKind`). This is agitate's producer for the model in
`Agitate.ImportGraph`; ImportGraph's `calcDeclConstInfoNeeds` and `calcIRNeeds` are the
`Environment`-based counterparts. It reads only what the oleans record:

* References in types and values (`expr .type`/`expr .value`), constructors of an inductive and the
  mutual block of a recursor (`structural`), `@[implemented_by]` targets, and names preresolved by
  syntax quotations. References are resolved as `agitate` resolves them (`resolveDecl`); one to a
  declaration regenerated from another (an equation lemma, say) counts as one to that declaration
  (`regenerated`).
* Code (`runtimeIR`, `metaIR`). Lean checks phases on a declaration's initial LCNF, which the oleans
  do not keep, so code references are approximated by the value references of declarations that
  have code (DESIGN.md: the IR is after inlining and specialisation). Auxiliary definitions without a
  phase of their own (matchers, …) are code in the phases of the same-module code that uses them.
* Presentability: a public meta declaration re-exports what the private meta code of its module
  that it reaches uses (`metaIR (some true) through`, as Lean's `checkMeta` recurses).
* Auxiliary declarations (no declaration range of their own: abstracted proofs, matchers, …) stay
  distinct users, but their needs are re-exported as where their parent uses them: a proof abstracted
  from an exposed definition was elaborated in its public value (`isReExported? := some true`).

Upstream locations are always `.type`: unfolding leaves no trace in the oleans.
-/
module

public import Agitate.Preresolved
public import Agitate.ImportGraph.DeclNeedKinds
public import Agitate.ImportGraph.Stance

public section

open Lean Agitate.ImportGraph

namespace Agitate

/--
The stance of declaration `n`, from the index: public if its module's public part declares it (and
its name is not private), exposed if that part has its value, meta if marked or inferred meta, and
runtime if it is a definition other than a matcher (matchers are inlined). Noncomputable
definitions count as runtime: an approximation.
-/
def stanceOf (ix : Index) (n : Name) : Stance :=
  let pub? := if isPrivateName n then none else ix.findPublic? n
  let phase := if isDeclMeta' ix n then .meta else match ix.find? n with
    | some (.defnInfo _) | some (.opaqueInfo _) => if ix.matchers.contains n then .none else .runtime
    | _ => .none
  { isPublic := pub?.isSome, isExposed := pub?.any (·.hasValue (allowOpaque := true)), phase }

/--
The declaration that a reference to `ref` from module `i` counts as: its name and declaring module,
and whether the reference was redirected to it (a reserved name or `_simp_` constant regenerated
from it). Resolved as `agitate` resolves references (`resolveRef`, `Resolved.forModule`), so a
duplicated theorem resolves to the copy `i` saw, or to `i` itself. `none` if the reference is
ignored (not an imported constant).
-/
def resolveDecl (refs : RefCtx) (order : Thunk (Array Index.LoadedModule)) (i : ModuleIdx)
    (ref : Name) : Option (Name × ModuleIdx × Bool) := do
  let r ← resolveRef refs ref
  let (n, j) := match r.forModule refs.ix order i with
    | some r' => (r'.name, r'.mod)
    | none => (r.name, i)  -- `i` declares its own copy
  return (n, j, n != ref)

/-- The kinds of the references `constRefs` reports, before module context is added. -/
private def kindBits (k : DeclNeedKind) : UInt32 := (DeclNeedKinds.single k).bits

/--
The references of constant `ci`, each with its kinds (`DeclNeedKinds.bits`), before module context:
its type's constants, its value's, names preresolved by quotations in its value, an inductive's
constructors or a recursor's mutual block, and its `@[implemented_by]` target. The same name may
occur several times.
-/
def constRefs (refs : RefCtx) (ci : ConstantInfo) : Array Name × Array UInt32 := Id.run do
  let push (k : DeclNeedKind) (acc : Array Name × Array UInt32) (n : Name) :=
    (acc.1.push n, acc.2.push (kindBits k))
  let mut acc := ci.type.getUsedConstants.foldl (push (.expr .type)) (#[], #[])
  if let some v := ci.value? (allowOpaque := true) then
    let vs := v.getUsedConstants
    acc := vs.foldl (push (.expr .value)) acc
    -- only scanned if the value builds `Syntax.Preresolved`
    if refs.preresolvedNeeds && vs.contains ``Syntax.Preresolved.decl then
      acc := (Preresolved.declNames v).foldl (push .preresolved) acc
  match ci with
  | .inductInfo val => acc := val.ctors.foldl (push .structural) acc
  | .recInfo val => acc := val.all.foldl (push .structural) acc
  | _ => pure ()
  if refs.implementedByNeeds then
    if let some g := refs.ix.implementedBy? ci.name then
      acc := push .implementedBy acc g
  return acc

/-- The needs of one module's declarations, as parallel arrays with one entry per need. -/
structure ModuleDeclNeeds where
  /-- The module's constants (`Index.constants`); `users` index into this. -/
  consts : Array ConstantInfo := #[]
  stances : Array Stance := #[]
  users : Array Nat := #[]
  /-- The needed declaration and its module. -/
  used : Array Name := #[]
  usedMods : Array ModuleIdx := #[]
  /-- `DeclNeedKinds.bits`. -/
  kinds : Array UInt32 := #[]
  /-- The `through` path of `metaIR (some true)` needs, by need index. -/
  through : Std.HashMap Nat (List Name) := {}
deriving Inhabited

private def ModuleDeclNeeds.push (m : ModuleDeclNeeds) (u : Nat) (d : Name) (j : ModuleIdx)
    (k : UInt32) : ModuleDeclNeeds :=
  { m with users := m.users.push u, used := m.used.push d, usedMods := m.usedMods.push j,
           kinds := m.kinds.push k }

/-- The needs of module `i`'s declarations; see the module docstring. -/
def moduleDeclNeeds (refs : RefCtx) (i : ModuleIdx) : ModuleDeclNeeds := Id.run do
  let ix := refs.ix
  let order : Thunk (Array Index.LoadedModule) := .mk fun _ => ix.loadOrder i
  let consts := ix.constants i
  let idxOf : Std.HashMap Name Nat := consts.zipIdx.foldl (fun m (ci, k) => m.insert ci.name k) {}
  let ranged : Std.HashSet Name :=
    (ix.moduleEntries declRangeExt.toPersistentEnvExtension i).foldl (·.insert ·.1) {}
  let stances := consts.map (stanceOf ix ·.name)
  -- the declaration of `i` an auxiliary declaration (no range of its own) was made for
  let parentOf? (c : Name) : Option Nat := Id.run do
    if ranged.contains c then return none
    let mut n := c
    for _ in 0...64 do
      let p := n.getPrefix
      if p.isAnonymous then return none
      if let some k := idxOf[p]? then return some k
      if isPrivateName p then
        if let some k := idxOf[privateToUserName p]? then return some k
      n := p
    return none
  -- references, resolved once per name
  let mut cache : Std.HashMap Name (Option (Name × ModuleIdx × Bool)) := {}
  let mut resolved : Array (Array (Name × ModuleIdx × UInt32)) := .emptyWithCapacity consts.size
  for ci in consts do
    let (names, kinds) := constRefs refs ci
    let mut rs := #[]
    for h : e in 0...names.size do
      let n := names[e]
      let r := match cache[n]? with
        | some r => r
        | none => resolveDecl refs order i n
      cache := cache.insert n r
      if let some (d, j, redirected) := r then
        let k := kinds[e]! ||| (if redirected then kindBits .regenerated else 0)
        rs := rs.push (d, j, k)
    resolved := resolved.push rs
  let isCodeRef (k : UInt32) : Bool :=
    k &&& (kindBits (.expr .value) ||| kindBits .implementedBy) != 0
  -- the same-module declarations each declaration's code may use
  let localCode : Array (Array Nat) := resolved.map fun rs =>
    rs.filterMap fun (d, j, k) => if j == i && isCodeRef k then idxOf[d]? else none
  -- code phases: a declaration's own, and for auxiliary definitions those of the code using them
  let mut runtime : Array Bool := stances.map (·.phase == .runtime)
  let mut isMeta : Array Bool := stances.map (·.phase == .meta)
  let parent : Array (Option Nat) := consts.map (parentOf? ·.name)
  let isAuxDef (k : Nat) : Bool :=
    stances[k]!.phase == .none && consts[k]!.isDefinition && parent[k]!.isSome
  for (flags, own) in [(true, Phase.runtime), (false, Phase.meta)] do
    let mut todo := (Array.range consts.size).filter (stances[·]!.phase == own)
    let mut seen : Std.HashSet Nat := {}
    while let some k := todo.back? do
      todo := todo.pop
      if seen.contains k then continue
      seen := seen.insert k
      for l in localCode[k]! do
        if isAuxDef l && !seen.contains l then
          if flags then runtime := runtime.set! l true else isMeta := isMeta.set! l true
          todo := todo.push l
  -- where an auxiliary declaration counts: as its parent's type (public if the parent is) or value
  -- (public if exposed); auxiliaries of auxiliaries inherit
  -- the names in each parent's type
  let parentTypes : Std.HashMap Nat (Std.HashSet Name) := parent.foldl (init := {}) fun m p? =>
    match p? with
    | some p => if m.contains p then m else
        m.insert p (consts[p]!.type.getUsedConstants.foldl (·.insert ·) {})
    | none => m
  let rec exportedAt (k : Nat) (fuel : Nat) : Bool :=
    match fuel, parent[k]! with
    | fuel + 1, some p =>
      let inType := (parentTypes[p]?).any (·.contains consts[k]!.name)
      (if inType then stances[p]!.isPublic else stances[p]!.isExposed) || exportedAt p fuel
    | _, _ => false
  let mut out : ModuleDeclNeeds := { consts, stances }
  for k in 0...consts.size do
    let x := parent[k]!.isSome && exportedAt k 8
    let su := stances[k]!
    for (d, j, kinds) in resolved[k]! do
      let mut ks : UInt32 := kinds
      -- re-export as where the parent uses the auxiliary (an override only where it changes
      -- something)
      if x then
        for (loc, dflt) in [(ConstLocation.type, su.isPublic), (.value, su.isExposed)] do
          if !dflt && ks &&& kindBits (.expr loc) != 0 then
            ks := (ks &&& ~~~(kindBits (.expr loc))) ||| kindBits (.expr loc (some true))
      if isCodeRef kinds then
        if runtime[k]! then ks := ks ||| kindBits .runtimeIR
        if isMeta[k]! then ks := ks ||| kindBits (.metaIR none)
      out := out.push k d j ks
  -- presentability: a public meta declaration re-exports the code needs of the private meta code
  -- of `i` it reaches (`Lean.Compiler.LCNF.checkMeta` recurses into it)
  for u in 0...consts.size do
    if !(stances[u]!.phase == .meta && stances[u]!.isPublic) then continue
    let mut todo : Array (Nat × List Name) := #[(u, [])]
    let mut seen : Std.HashSet Nat := {u}
    while let some (k, path) := todo.back? do
      todo := todo.pop
      for l in localCode[k]! do
        if seen.contains l || !isMeta[l]! then continue
        seen := seen.insert l
        if stances[l]!.isPublic then continue  -- checked as public meta code itself
        let path' := path ++ [consts[l]!.name]
        for (d, j, kinds) in resolved[l]! do
          if j != i && isCodeRef kinds then
            out := { out with through := out.through.insert out.users.size path' }
            out := out.push u d j (kindBits (.metaIR (some true)))
        todo := todo.push (l, path')
  return out

end Agitate
