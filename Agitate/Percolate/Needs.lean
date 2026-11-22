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
public import Agitate.DeclNeeds
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
  /-- The module of each item. -/
  modOfItem : Array ModuleIdx

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
  let mut modOfItem : Array ModuleIdx := .emptyWithCapacity n
  for (m, i) in items.zipIdx do
    for _ in m.items do modOfItem := modOfItem.push i
  return { isProject, items, offset, numItems := n, modOfItem }

/-- The item that declaration `n` of module `j` belongs to (`none` outside the project). -/
def Analysis.itemOf? (a : Analysis) (n : Name) (j : ModuleIdx) : Option Nat := do
  guard a.isProject[j]!
  return a.globalId (← a.items[j]!.constItem[n]?)

/-- What one module contributes to the graph. -/
structure ModuleNeeds where
  /-- Recorded needs between items, as parallel arrays: `srcs[k] → dsts[k]` with kinds `kinds[k]`. -/
  srcs : Array Nat := #[]
  dsts : Array Nat := #[]
  kinds : ByteArray := .empty
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

/--
The needs of module `i`'s constants between items. References are resolved once per distinct name;
each constant's needs are merged per needed item (kinds or-ed) by sorting `item * 256 + kinds`.
-/
def moduleNeeds (refs : RefCtx) (a : Analysis) (i : ModuleIdx) : ModuleNeeds := Id.run do
  let ix := refs.ix
  let order : Thunk (Array Index.LoadedModule) := .mk fun _ => ix.loadOrder i
  let rfl : Std.HashSet Name := ix.moduleEntries backwardDefeqAttr.ext i |>.foldl (·.insert ·) {}
  -- per referenced name: the item it resolves to, with `regenerated` if redirected
  let mut cache : Std.HashMap Name (Option (Nat × Bool)) := {}
  let mut out : ModuleNeeds := {}
  let mut metaItems : Std.HashSet Nat := {}
  let mut rflItems : Std.HashSet Nat := {}
  for ci in ix.constants i do
    let some (j, k) := a.items[i]!.constItem[ci.name]? | continue
    let src := a.globalId (j, k)
    if j == i then
      if !metaItems.contains src && isMetaprogram ix ci.name then metaItems := metaItems.insert src
      if !rflItems.contains src && rfl.contains ci.name then rflItems := rflItems.insert src
    let (names, kinds) := constRefs refs ci
    let mut codes : Array Nat := #[]
    for h : e in 0...names.size do
      let n := names[e]
      let d := match cache[n]? with
        | some d => d
        | none => (resolveDecl refs order i n).bind fun (m, jm, redirected) =>
            (a.itemOf? m jm).map (·, redirected)
      cache := cache.insert n d
      if let some (d, redirected) := d then
        if d != src then
          let kind := kinds.get! e ||| (if redirected then NeedKinds.regenerated.bits else 0)
          codes := codes.push (d * 256 + kind.toNat)
    -- merge the needs of this constant per needed item
    codes := codes.qsort (· < ·)
    let mut last := none
    for c in codes do
      let (d, kind) := (c / 256, (c % 256).toUInt8)
      if last == some d then
        let p := out.kinds.size - 1
        out := { out with kinds := out.kinds.set! p (out.kinds.get! p ||| kind) }
      else
        out := { out with srcs := out.srcs.push src, dsts := out.dsts.push d,
                          kinds := out.kinds.push kind }
        last := some d
  return { out with metaItems := metaItems.toArray, rflItems := rflItems.toArray }

/-- An edge list under construction, as parallel arrays. -/
structure EdgeList where
  srcs : Array Nat := #[]
  dsts : Array Nat := #[]
  kinds : ByteArray := .empty

/-- Adds the edge `s → d` without kinds (an approximation's edge). -/
@[inline] def EdgeList.add (es : EdgeList) (s d : Nat) : EdgeList :=
  { srcs := es.srcs.push s, dsts := es.dsts.push d, kinds := es.kinds.push 0 }

/--
Everything `percolate` computes: per level, the graph over items and pseudo-vertices, the seeds
reaching each item (`reach`), and a breadth-first tree from the seeds (`tree`, for `why`).

Pseudo-vertices: five per module `m` of the closure, at `numItems + 5 * p + r` for `m`'s position
`p` in `closure` and role `r`: `0` what `m`'s unrecorded uses can name, `1` `m`'s metaprograms,
`2` `m`'s rfl theorems, `3` every module `m` records an extra use of, `4` every item of `m`.
-/
structure Percolation where
  numItems : Nat
  closure : Array ModuleIdx
  graphs : Array LGraph
  reach : Array (Array Bitset)
  trees : Array Graph.BfsTree

namespace Percolation

/-- The seeds that reach item `v` at level index `l` (levels include the ones before them). -/
def reachAt (p : Percolation) (l : Nat) (v : Nat) : Bitset := p.reach[l]![v]!

def status (p : Percolation) (v : Nat) : Status :=
  if !(p.reachAt 0 v).isEmpty then .needed
  else if !(p.reachAt 1 v).isEmpty then .candidate
  else if !(p.reachAt 2 v).isEmpty then .moduleUse
  else .unused

/-- For a pseudo-vertex: the module and the role (see `Percolation`). -/
def pseudo? (p : Percolation) (v : Nat) : Option (ModuleIdx × Nat) :=
  if v < p.numItems then none
  else some (p.closure[(v - p.numItems) / 5]!, (v - p.numItems) % 5)

end Percolation

/--
Percolates the seeds (`seeds[s]`: the item ids of seed `s`) through the needs of the modules in
`closure` (the seeds' import closure; nothing outside it can be needed), at the three levels.
-/
def percolate (refs : RefCtx) (a : Analysis) (closure : Array ModuleIdx)
    (seeds : Array (Array Nat)) (profile : Bool := false) : IO Percolation := do
  let ix := refs.ix
  let t0 ← IO.monoMsNow
  let needTasks := closure.map fun i => Task.spawn fun _ => moduleNeeds refs a i
  let needs : Array ModuleNeeds ← needTasks.mapM fun t => IO.wait t
  let t1 ← IO.monoMsNow
  let n := a.numItems
  let size := n + 5 * closure.size
  let candV (p : Nat) := n + 5 * p
  let metaV (p : Nat) := n + 5 * p + 1
  let rflV (p : Nat) := n + 5 * p + 2
  let usesV (p : Nat) := n + 5 * p + 3
  let allV (p : Nat) := n + 5 * p + 4
  let pos : Std.HashMap ModuleIdx Nat := closure.zipIdx.foldl (fun m (i, p) => m.insert i p) {}
  let mut srcs : Array Nat := #[]
  let mut dsts : Array Nat := #[]
  let mut kinds : ByteArray := .empty
  for mn in needs do
    srcs := srcs ++ mn.srcs
    dsts := dsts ++ mn.dsts
    kinds := kinds ++ mn.kinds
  let mut es : EdgeList := { srcs, dsts, kinds }
  let mut edgeLists := #[es]
  -- `candidate`: what unrecorded uses can name
  for (i, p) in closure.zipIdx do
    let mn := needs[p]!
    for v in mn.metaItems do es := es.add (metaV p) v
    for v in mn.rflItems do es := es.add (rflV p) v
    es := es.add (candV p) (metaV p) |>.add (candV p) (rflV p)
    for use in ix.getExtraModUses i do
      if let some q := (ix.getModuleIdx? use.module).bind (pos[·]?) then
        if q != p then
          es := es.add (candV p) (metaV q)
          if !use.isMeta then es := es.add (candV p) (rflV q)
    for k in 0...a.items[i]!.items.size do
      es := es.add (a.offset[i]! + k) (candV p)
  edgeLists := edgeLists.push es
  -- `moduleUse`: any item of a used module
  for (i, p) in closure.zipIdx do
    for k in 0...a.items[i]!.items.size do
      es := es.add (allV p) (a.offset[i]! + k) |>.add (a.offset[i]! + k) (usesV p)
    for use in ix.getExtraModUses i do
      if let some q := (ix.getModuleIdx? use.module).bind (pos[·]?) then
        if q != p then es := es.add (usesV p) (allV q)
  edgeLists := edgeLists.push es
  let graphs := edgeLists.map fun es => (Graph.ofEdgesL size es.srcs es.dsts es.kinds).dedup
  let t2 ← IO.monoMsNow
  let mut init : Std.HashMap Nat Bitset := {}
  for (ids, s) in seeds.zipIdx do
    for v in ids do
      init := init.insert v ((init.getD v ∅).insert s)
  let roots := init.toArray.map (·.1)
  -- `lazyPure`, so that the timings below measure the work itself
  let reach ← IO.lazyPure fun _ => graphs.map fun g => g.graph.flowForward roots (init.getD · ∅)
  let t3 ← IO.monoMsNow
  let trees ← IO.lazyPure fun _ => graphs.map (·.graph.bfs roots)
  let t4 ← IO.monoMsNow
  if profile then
    IO.eprintln s!"[profile] needs between items (parallel, {closure.size} modules): {t1 - t0} ms"
    IO.eprintln s!"[profile] graph assembly ({n} items, {graphs[0]!.graph.numEdges} needs): {t2 - t1} ms"
    IO.eprintln s!"[profile] percolation (three levels): {t3 - t2} ms"
    IO.eprintln s!"[profile] search trees for `why` (three levels): {t4 - t3} ms"
  return { numItems := n, closure, graphs, reach, trees }

/-- Why an item has its status: the last step of a shortest path from a seed, at its level. -/
structure Why where
  /-- The seed, if the item is one. -/
  seed? : Option Nat := none
  /-- The declaration that needs the item (for an approximation, the first of its item). -/
  user? : Option Name := none
  /-- The module of `user?`. -/
  userModule? : Option Name := none
  /-- The item's declaration that `user?` refers to (recorded needs only). -/
  uses? : Option Name := none
  /-- The kinds of the recorded need (`NeedKinds`). -/
  kinds : Array String := #[]
  /-- For an approximation: `metaprogram`, `rflTheorem` or `moduleUse`, and whether the use is
  inside the item's own module. -/
  rule? : Option String := none
  sameModule? : Option Bool := none

/-- The first name of item `v`, unmangled, and its module. -/
def Analysis.firstName (a : Analysis) (ix : Index) (v : Nat) : Name × Name :=
  let i := a.modOfItem[v]!
  (privateToUserName a.items[i]!.items[v - a.offset[i]!]!.names[0]!, ix.modName i)

/--
For each wanted recorded need `u → v` (`wanted`: per `u`, the `v`s), a declaration of `u`, the
declaration of `v` it refers to, and the kinds. Found by resolving the references of the constants
of `u`'s module again, one pass per module, in parallel.
-/
def explainNeeds (refs : RefCtx) (a : Analysis) (wanted : Std.HashMap Nat (Array Nat)) :
    Std.HashMap (Nat × Nat) (Name × Name × NeedKinds) := Id.run do
  let ix := refs.ix
  let mut byModule : Std.HashMap ModuleIdx (Array Nat) := {}
  for (u, _) in wanted do
    byModule := byModule.alter a.modOfItem[u]! (·.getD #[] |>.push u)
  let tasks := byModule.toArray.map fun (i, _) => Task.spawn fun _ => Id.run do
    let order : Thunk (Array Index.LoadedModule) := .mk fun _ => ix.loadOrder i
    let mut out : Array ((Nat × Nat) × (Name × Name × NeedKinds)) := #[]
    let mut done : Std.HashSet (Nat × Nat) := {}
    for ci in ix.constants i do
      let some r := a.items[i]!.constItem[ci.name]? | continue
      let u := a.globalId r
      let some vs := wanted[u]? | continue
      let (names, kinds) := constRefs refs ci
      for h : e in 0...names.size do
        if let some (m, jm, redirected) := resolveDecl refs order i names[e] then
          if let some v := a.itemOf? m jm then
            if vs.contains v && !done.contains (u, v) then
              let k : NeedKinds := ⟨kinds.get! e⟩
              done := done.insert (u, v)
              let k := if redirected then k ||| NeedKinds.regenerated else k
              out := out.push ((u, v), (ci.name, m, k))
    return out
  return tasks.foldl (init := {}) fun m t => t.get.foldl (init := m) fun m (uv, x) => m.insert uv x

/-- Why each item has its status (`none` if unused). -/
def Percolation.whys (p : Percolation) (refs : RefCtx) (a : Analysis) (seeds : Array (Array Nat)) :
    Array (Option Why) := Id.run do
  let ix := refs.ix
  let mut seedOf : Std.HashMap Nat Nat := {}
  for (ids, s) in seeds.zipIdx do
    for v in ids do
      seedOf := seedOf.insertIfNew v s
  -- the last step to each item: its predecessor and the edge, at the item's level
  let level (v : Nat) : Option Nat := match p.status v with
    | .needed => some 0 | .candidate => some 1 | .moduleUse => some 2 | .unused => none
  let step (l v : Nat) : Nat × Nat :=
    let e := p.trees[l]!.pred[v]! - 1
    (p.trees[l]!.edgeSrc[e]!, e)
  let mut wanted : Std.HashMap Nat (Array Nat) := {}
  for v in 0...p.numItems do
    if let some l := level v then
      if !seedOf.contains v then
        let (u, _) := step l v
        if u < p.numItems then wanted := wanted.alter u (·.getD #[] |>.push v)
  let explained := explainNeeds refs a wanted
  return (Array.range p.numItems).map fun v => do
    let l ← level v
    if let some s := seedOf[v]? then return { seed? := s }
    let (u, e) := step l v
    if u < p.numItems then
      let (userName, userModule) := a.firstName ix u
      match explained[(u, v)]? with
      | some (c, m, k) => return { user? := privateToUserName c, userModule? := userModule,
                                   uses? := privateToUserName m, kinds := k.toNames }
      | none => return { user? := userName, userModule? := userModule,
                         kinds := (NeedKinds.mk (p.graphs[l]!.labels.get! e)).toNames }
    -- an approximation: `v` ← role vertex of module `q` ← … ← an item `x` of module `p`
    let (q, role) ← p.pseudo? u
    let rule := match role with | 1 => "metaprogram" | 2 => "rflTheorem" | _ => "moduleUse"
    let mut w := u
    for _ in 0...4 do
      if w < p.numItems then break
      w := (step l w).1
    let (userName, userModule) := a.firstName ix w
    return { user? := userName, userModule? := userModule, rule? := rule,
             sameModule? := userModule == ix.modName q }

end Agitate.Percolate
