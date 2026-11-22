/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/

/-
# Source items (upstreamable)

A source item is what deleting one span of a source file removes. Lean records a declaration range
(`declRangeExt`) for each declaration written in the source, and gives generated declarations the
range of the syntax that made them: constructors, structure fields, `where`/`let rec` helpers,
`deriving` instances, `@[ext]` lemmas. Grouping a module's declarations by maximal ranges, with every
declaration whose range lies inside one, therefore yields what can be deleted separately: a
structure, its fields and its derived instances form one item.

This is the range half of ImportGraph's notion of auto-generated declarations (which it detects by a
`_` name component and the absence of a range, `isDeclNeedsAutoDecl`); declarations without a range
are assigned to items by their callers.
-/
module

public import Lean.Data.DeclarationRange
public import Std.Data.HashMap.Basic

public section

open Lean

namespace Agitate.ImportGraph

/-- A module's declarations grouped into maximal ranges, in source order. -/
structure RangeGroups where
  /-- The range of each group: the union of its members' ranges. -/
  ranges : Array DeclarationRange
  /-- The declarations of each group, in source order (equal ranges by name). -/
  members : Array (Array Name)
  /-- The group of each declaration. -/
  groupOf : Std.HashMap Name Nat
deriving Inhabited

private def posLt (a b : Position) : Bool :=
  a.line < b.line || (a.line == b.line && a.column < b.column)

/--
Groups declarations by their full ranges (`DeclarationRanges.range`): a declaration whose range
starts inside the current group's range joins it (extending it if it reaches further). The result
does not depend on the order of `ranged`.
-/
def groupRanges (ranged : Array (Name × DeclarationRange)) : RangeGroups := Id.run do
  -- by start; for equal starts, the longer range first, so that it encloses the others; equal
  -- ranges by name
  let ranged := ranged.qsort fun (na, a) (nb, b) => posLt a.pos b.pos || (a.pos == b.pos &&
    (posLt b.endPos a.endPos || (a.endPos == b.endPos && Name.lt na nb)))
  let mut ranges : Array DeclarationRange := #[]
  let mut members : Array (Array Name) := #[]
  let mut groupOf : Std.HashMap Name Nat := {}
  for (n, r) in ranged do
    if let some cur := ranges.back? then
      if posLt r.pos cur.endPos || r.pos == cur.pos then
        let k := ranges.size - 1
        if posLt cur.endPos r.endPos then
          ranges := ranges.set! k { cur with endPos := r.endPos, endCharUtf16 := r.endCharUtf16 }
        members := members.modify k (·.push n)
        groupOf := groupOf.insert n k
        continue
    groupOf := groupOf.insert n ranges.size
    ranges := ranges.push r
    members := members.push #[n]
  return { ranges, members, groupOf }

end Agitate.ImportGraph
