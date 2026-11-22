/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/

/-
Needs between source items, and which items given seed declarations need (`percolate`).

An item needs the items of everything its constants need, as recorded in the oleans:
* the constants their types and values refer to, redirected as `agitate` resolves references
  (`resolveRef`, `Resolved.forModule`): reserved names to the declaration they are regenerated
  from, `_simp_` constants to their base, and duplicated theorems to the copy the module saw;
* `@[implemented_by]` targets, and names preresolved by syntax quotations (`Agitate.Preresolved`).

Lean also records uses that name no declaration. Extra module uses (notation, macros, tactics,
elaborators, the lemmas `simp` and `dsimp` used, …) give only the used *module*, and uses inside a
module are not recorded at all. Two approximations, each a level of the result (`Status`):
* `candidate`: the declarations such a use can name without leaving a term behind. A meta use
  (tactics, macros, elaborators, parsers) can name a metaprogram; a non-meta use, as `simp` records
  for every lemma it used, also an rfl theorem (`@[backward_defeq]`), which `dsimp` uses without a
  proof term (Lean's reason for recording them, `recordSimpUses`). Uses inside a module: its own
  metaprograms and rfl theorems.
* `moduleUse`: any item of a module that a needed module records an extra use of. This covers the
  remaining recorders of non-meta uses (coercions, docstrings, delaborators, …).
-/
module

public import Agitate.Percolate.Items
public import Agitate.Preresolved
public import Lean.DefEqAttrib
public import Agitate.ImportGraph.Graph
public import Agitate.ImportGraph.Bitset

public section

open Lean Agitate.ImportGraph

namespace Agitate.Percolate

/-- How an item stands with respect to the seeds, by the weakest kind of need that reaches it. -/
inductive Status where
  /-- A seed needs it through recorded needs between declarations. -/
  | needed
  /-- A seed may need it through a module-level or in-module use that leaves no other record, of a
  kind of declaration such uses can name. -/
  | candidate
  /-- A seed may need it only through a module-level use of its module. -/
  | moduleUse
  /-- No seed needs it. -/
  | unused
deriving BEq, Repr

def Status.toString : Status → String
  | .needed => "needed" | .candidate => "candidate" | .moduleUse => "moduleUse"
  | .unused => "unused"

/-- Everything known about the project's items. -/
structure Analysis where
  /-- Whether module `i` belongs to the project (the workspace's root package). -/
  isProject : Array Bool
  /-- `items[i]` for project modules; empty otherwise. -/
  items : Array ModuleItems
  /-- The global id of module `i`'s first item. -/
  offset : Array Nat
  /-- The number of items. -/
  numItems : Nat

namespace Analysis

def globalId (a : Analysis) (r : ModuleIdx × Nat) : Nat := a.offset[r.1]! + r.2

end Analysis

/--
Builds the items of all project modules: ranged items in parallel, then the assignment of
unranged constants in parallel (it looks up other modules' ranged items).
-/
def analyse (refs : RefCtx) (isProject : Array Bool) : IO Analysis := do
  let ix := refs.ix
  let rangedTasks := (Array.range ix.size).map fun i =>
    if isProject[i]! then Task.spawn fun _ => some (rangedItems ix i) else .pure none
  let ranged := rangedTasks.map Task.get
  let itemTasks := (Array.range ix.size).map fun i =>
    if isProject[i]! then Task.spawn fun _ => moduleItems refs.reserved ranged i else .pure default
  let items := itemTasks.map Task.get
  let mut offset := #[]
  let mut n := 0
  for m in items do
    offset := offset.push n
    n := n + m.items.size
  return { isProject, items, offset, numItems := n }

/-- The item that a reference to `ref` from module `i` resolves to (`none` outside the project). -/
private def resolveItem (refs : RefCtx) (a : Analysis) (order : Thunk (Array Index.LoadedModule))
    (i : ModuleIdx) (ref : Name) : Option Nat := do
  let r ← resolveRef refs ref
  let (n, j) := match r.forModule refs.ix order i with
    | some r' => (r'.name, r'.mod)
    | none => (r.name, i)  -- `i` declares its own copy
  guard a.isProject[j]!
  return a.globalId (← a.items[j]!.constItem[n]?)

/-- What one module contributes to the graph. -/
structure ModuleNeeds where
  /-- Recorded needs: `(item, needed items)`, one entry per constant. -/
  edges : Array (Nat × Array Nat) := #[]
  /-- The module's items containing a metaprogram (see `isMetaprogram`). -/
  metaItems : Array Nat := #[]
  /-- The module's items containing an rfl theorem (`@[backward_defeq]`). -/
  rflItems : Array Nat := #[]
deriving Inhabited

/--
Whether `c` is a metaprogram: a meta declaration, or one whose type mentions a `Lean` declaration
(non-module code marks nothing meta, and simprocs need not be). A heuristic, erring on the side of
keeping declarations.
-/
def isMetaprogram (ix : Index) (c : Name) : Bool :=
  isDeclMeta' ix c || (ix.find? c).any fun ci => ci.type.getUsedConstants.any (`Lean).isPrefixOf

/-- The needs of module `i`'s constants. References are resolved once per distinct name. -/
def moduleNeeds (refs : RefCtx) (a : Analysis) (i : ModuleIdx) : ModuleNeeds := Id.run do
  let ix := refs.ix
  let order : Thunk (Array Index.LoadedModule) := .mk fun _ => ix.loadOrder i
  let rfl : Std.HashSet Name := ix.moduleEntries backwardDefeqAttr.ext i |>.foldl (·.insert ·) {}
  let mut cache : Std.HashMap Name (Option Nat) := {}
  let mut out : ModuleNeeds := {}
  let mut metaItems : Std.HashSet Nat := {}
  let mut rflItems : Std.HashSet Nat := {}
  for ci in ix.constants i do
    let some (j, k) := a.items[i]!.constItem[ci.name]? | continue
    let src := a.globalId (j, k)
    if j == i then
      if !metaItems.contains src && isMetaprogram ix ci.name then metaItems := metaItems.insert src
      if !rflItems.contains src && rfl.contains ci.name then rflItems := rflItems.insert src
    let mut names := ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque := true) then
      names := names ++ v.getUsedConstants
      -- names preresolved by quotations (only scanned if the value builds `Syntax.Preresolved`)
      if refs.preresolvedNeeds && names.contains ``Syntax.Preresolved.decl then
        names := names ++ Preresolved.declNames v
    -- as `ConstantInfo.getUsedConstantsAsSet`: an inductive needs its constructors, a recursor
    -- its mutual block
    match ci with
    | .inductInfo val => names := names ++ val.ctors
    | .recInfo val => names := names ++ val.all
    | _ => pure ()
    if refs.implementedByNeeds then
      if let some g := ix.implementedBy? ci.name then
        names := names.push g
    let mut dsts := #[]
    for n in names do
      let d := match cache[n]? with
        | some d => d
        | none => resolveItem refs a order i n
      cache := cache.insert n d
      if let some d := d then
        if d != src then
          dsts := dsts.push d
    -- deduplicate (constants of one item often need the same items)
    dsts := dsts.qsort (· < ·)
    dsts := dsts.zipIdx.filterMap fun (d, k) => if k > 0 && dsts[k - 1]! == d then none else some d
    out := { out with edges := out.edges.push (src, dsts) }
  return { out with metaItems := metaItems.toArray, rflItems := rflItems.toArray }

/-- The result for each item: the seeds (indices) reaching it at each level of `Status`. -/
structure Result where
  needed : Array Bitset
  /-- Includes `needed`. -/
  candidate : Array Bitset
  /-- Includes `candidate`. -/
  moduleUse : Array Bitset

def Result.status (r : Result) (v : Nat) : Status :=
  if !r.needed[v]!.isEmpty then .needed
  else if !r.candidate[v]!.isEmpty then .candidate
  else if !r.moduleUse[v]!.isEmpty then .moduleUse
  else .unused

/--
Percolates the seeds (`seeds[s]`: the item ids of seed `s`) through the needs of the modules in
`closure` (the seeds' import closure; nothing outside it can be needed), at the three levels.
-/
def percolate (refs : RefCtx) (a : Analysis) (closure : Array ModuleIdx)
    (seeds : Array (Array Nat)) (profile : Bool := false) : IO Result := do
  let ix := refs.ix
  let t0 ← IO.monoMsNow
  let needTasks := closure.map fun i => Task.spawn fun _ => moduleNeeds refs a i
  let needs : Array ModuleNeeds ← needTasks.mapM fun t => IO.wait t
  let t1 ← IO.monoMsNow
  -- items, then five pseudo-vertices per module `m` of the closure (`p` is its position):
  let n := a.numItems
  let candV (p : Nat) := n + 5 * p      -- what `m`'s unrecorded uses can name
  let metaV (p : Nat) := n + 5 * p + 1  -- `m`'s metaprograms
  let rflV (p : Nat) := n + 5 * p + 2   -- `m`'s rfl theorems
  let usesV (p : Nat) := n + 5 * p + 3  -- every module `m` records an extra use of
  let allV (p : Nat) := n + 5 * p + 4   -- every item of `m`
  let pos : Std.HashMap ModuleIdx Nat := closure.zipIdx.foldl (fun m (i, p) => m.insert i p) {}
  let mut succs : Array (Array Nat) := .replicate (n + 5 * closure.size) #[]
  for mn in needs do
    for (src, dsts) in mn.edges do
      succs := succs.modify src (· ++ dsts)
  let recorded : Graph := ⟨succs⟩
  for (i, p) in closure.zipIdx do
    let mn := needs[p]!
    succs := succs.set! (metaV p) mn.metaItems
    succs := succs.set! (rflV p) mn.rflItems
    let mut cand := #[metaV p, rflV p]
    for use in ix.getExtraModUses i do
      if let some q := (ix.getModuleIdx? use.module).bind (pos[·]?) then
        if q != p then
          cand := cand.push (metaV q)
          if !use.isMeta then cand := cand.push (rflV q)
    succs := succs.set! (candV p) cand
    for k in 0...a.items[i]!.items.size do
      succs := succs.modify (a.offset[i]! + k) (·.push (candV p))
  let candidate : Graph := ⟨succs⟩
  for (i, p) in closure.zipIdx do
    let ids := (Array.range a.items[i]!.items.size).map (a.offset[i]! + ·)
    succs := succs.set! (allV p) ids
    let mut uses := #[]
    for use in ix.getExtraModUses i do
      if let some q := (ix.getModuleIdx? use.module).bind (pos[·]?) then
        if q != p && !uses.contains (allV q) then uses := uses.push (allV q)
    succs := succs.set! (usesV p) uses
    for v in ids do
      succs := succs.modify v (·.push (usesV p))
  let coarse : Graph := ⟨succs⟩
  let t2 ← IO.monoMsNow
  let mut init : Std.HashMap Nat Bitset := {}
  for (ids, s) in seeds.zipIdx do
    for v in ids do
      init := init.insert v ((init.getD v ∅).insert s)
  let roots := init.toArray.map (·.1)
  let flow (g : Graph) := (g.flowForward roots (init.getD · ∅)).extract 0 n
  -- `lazyPure`, so that the timings below measure the percolation itself
  let res ← IO.lazyPure fun _ =>
    ({ needed := flow recorded, candidate := flow candidate, moduleUse := flow coarse } : Result)
  let t3 ← IO.monoMsNow
  if profile then
    IO.eprintln s!"[profile] needs between items (parallel, {closure.size} modules): {t1 - t0} ms"
    IO.eprintln s!"[profile] graph assembly ({n} items): {t2 - t1} ms"
    IO.eprintln s!"[profile] percolation (three levels): {t3 - t2} ms"
  return res

end Agitate.Percolate
