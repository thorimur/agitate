/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/

/-
Source items for `agitate-deps`: what deleting one span of a source file removes.

Lean records a declaration range (`declRangeExt`) for each declaration written in the source, and
gives generated declarations the range of the syntax that made them: constructors, structure
fields, `where`/`let rec` helpers, `deriving` instances, `@[ext]` lemmas. An item is a maximal range
of a module together with every constant whose range lies inside it, so a structure, its fields and
its derived instances form one item: none of them can be deleted alone.

Constants without a range (auxiliary definitions, recursors, equation lemmas, `_proof_`s, …) belong
to the item of their parent: the declaration a reserved name is regenerated from
(`Reserved.reservedBase?`), else their name's prefix, walking up until a ranged constant of a
project module is found. A private prefix that is not a constant stands for its public name:
auxiliary lemmas are private (`_private.M.0.foo._simp_1`) even when `foo` is public. That parent may live in another module (an equation lemma realised
downstream belongs to its definition). A constant with no ranged ancestor forms an unranged item
with the topmost ancestor that its own module declares.
-/
module

public import Agitate.Refs
public import Lean.DeclarationRange

public section

open Lean

namespace Agitate.Deps

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
  items : Array Item
  /-- The item index of each ranged constant. -/
  byName : Std.HashMap Name Nat
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

private def posLt (a b : Position) : Bool :=
  a.line < b.line || (a.line == b.line && a.column < b.column)

/-- Groups module `i`'s ranged constants into maximal ranges, in source order. -/
def rangedItems (ix : Index) (i : ModuleIdx) : RangedItems := Id.run do
  let consts : Std.HashSet Name := ix.constants i |>.foldl (·.insert ·.name) {}
  let ranged := ix.moduleEntries declRangeExt.toPersistentEnvExtension i
    |>.filter (consts.contains ·.1)
    |>.map (fun (n, r) => (n, r.range))
    -- by start; for equal starts, the longer range first, so that it encloses the others
    |>.qsort fun (_, a) (_, b) => posLt a.pos b.pos || (a.pos == b.pos && posLt b.endPos a.endPos)
  let mut items : Array Item := #[]
  let mut byName : Std.HashMap Name Nat := {}
  for (n, r) in ranged do
    if let some last := items.back? then
      if let some cur := last.range then
        if posLt r.pos cur.endPos || r.pos == cur.pos then
          -- inside (or overlapping) the current item: merge, extending it if needed
          let cur := if posLt cur.endPos r.endPos then
              { cur with endPos := r.endPos, endCharUtf16 := r.endCharUtf16 } else cur
          items := items.set! (items.size - 1) { range := cur, names := last.names.push n }
          byName := byName.insert n (items.size - 1)
          continue
    byName := byName.insert n items.size
    items := items.push { range := r, names := #[n] }
  return { items, byName, consts }

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
  let mut items := own.items
  let mut constItem : Std.HashMap Name (ModuleIdx × Nat) := {}
  let mut unranged : Std.HashMap Name Nat := {}
  for ci in ix.constants i do
    let c := ci.name
    if let some k := own.byName[c]? then
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
      if let some k := rj.byName[p]? then
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

end Agitate.Deps
