/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/

/-
Source items for `percolate`, from the olean index: what deleting one span of a source file removes.

Ranged constants are grouped into maximal ranges by `Agitate.ImportGraph.groupRanges` (see there
for why that groups exactly what cannot be deleted separately). Constants without a range
(auxiliary definitions, recursors, equation lemmas, `_proof_`s, …) belong to the item of their
parent: the declaration a reserved name is regenerated from (`Reserved.reservedBase?`), else their
name's prefix, walking up until a ranged constant of a project module is found. A private prefix
that is not a constant stands for its public name: auxiliary lemmas are private
(`_private.M.0.foo._simp_1`) even when `foo` is public. That parent may live in another module (an
equation lemma realised downstream belongs to its definition). A constant with no ranged ancestor
forms an unranged item with the topmost ancestor that its own module declares.
-/
module

public import Agitate.Refs
public import Agitate.ImportGraph.SourceItems

public section

open Lean Agitate.ImportGraph

namespace Agitate.Percolate

/-- One source item of a module. -/
structure Item where
  /-- The full declaration range (docstring, attributes and modifiers included), or `none`. -/
  range : Option DeclarationRange
  /--
  The constants of the item's module that have a range inside it, or for an unranged item its
  root. These are the item's names as written (or derived) in the source.
  -/
  names : Array Name
deriving Inhabited

/-- The ranged items of one module, before unranged constants are assigned. -/
structure RangedItems where
  groups : RangeGroups
  /-- All constants of the module. -/
  consts : Std.HashSet Name
deriving Inhabited

/-- All items of one module. -/
structure ModuleItems where
  /-- Ranged items in source order, then unranged ones. -/
  items : Array Item
  /--
  The item of every constant of the module, as (module, index): constants without a range of their
  own may belong to an item of another module.
  -/
  constItem : Std.HashMap Name (ModuleIdx × Nat)
deriving Inhabited

/-- Module `i`'s ranged constants, grouped into maximal ranges (`groupRanges`). -/
def rangedItems (ix : Index) (i : ModuleIdx) : RangedItems :=
  let consts : Std.HashSet Name := ix.constants i |>.foldl (·.insert ·.name) {}
  let ranged := ix.moduleEntries declRangeExt.toPersistentEnvExtension i
    |>.filter (consts.contains ·.1)
    |>.map fun (n, r) => (n, r.range)
  { groups := groupRanges ranged, consts }

/-- The next ancestor of `n` that might carry its item: the base of a reserved name, else the prefix. -/
def parentName? (reserved : Reserved.Ctx) (n : Name) : Option Name :=
  let p := (Reserved.reservedBase? reserved n).filter (· != n) |>.getD n.getPrefix
  if p.isAnonymous then none else some p

/--
Assigns every constant of module `i` to an item, given all project modules' ranged items
(`ranged[j]` for project module `j`, `none` otherwise). Unranged items are appended to `i`'s
ranged items.
-/
def moduleItems (reserved : Reserved.Ctx) (ranged : Array (Option RangedItems)) (i : ModuleIdx) :
    ModuleItems := Id.run do
  let ix := reserved.ix
  let some own := ranged[i]! | return { items := #[], constItem := {} }
  let mut items : Array Item := (own.groups.ranges.zip own.groups.members).map fun (r, ns) =>
    { range := r, names := ns }
  let mut constItem : Std.HashMap Name (ModuleIdx × Nat) := {}
  let mut unranged : Std.HashMap Name Nat := {}
  for ci in ix.constants i do
    let c := ci.name
    if let some k := own.groups.groupOf[c]? then
      constItem := constItem.insert c (i, k)
      continue
    -- walk up to a ranged ancestor, remembering the topmost ancestor that `i` declares
    let mut n := c
    let mut root := c
    let mut found : Option (ModuleIdx × Nat) := none
    for _ in 0...64 do
      let some p := parentName? reserved n | break
      n := p
      let declarer? (q : Name) := if own.consts.contains q then some i else ix.getModuleIdxFor? q
      -- auxiliary lemmas are private (`_private.M.0.foo._simp_1`) also when `foo` is not
      let (p, j?) := match declarer? p with
        | some j => (p, some j)
        | none => if isPrivateName p then (privateToUserName p, declarer? (privateToUserName p))
                  else (p, none)
      let some j := j? | continue  -- not a constant (a namespace): keep walking
      n := p
      let some rj := ranged[j]! | break  -- outside the project: stop
      if j == i then root := p
      if let some k := rj.groups.groupOf[p]? then
        found := some (j, k)
        break
    match found with
    | some r => constItem := constItem.insert c r
    | none =>
      let k := unranged[root]?.getD items.size
      if k == items.size then
        unranged := unranged.insert root k
        items := items.push { range := none, names := #[root] }
      constItem := constItem.insert c (i, k)
  return { items, constItem }

end Agitate.Percolate
