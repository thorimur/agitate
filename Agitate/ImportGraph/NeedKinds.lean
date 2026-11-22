/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/

/-
# Kinds of need between declarations (upstreamable)

How one declaration needs another, as bit flags in a byte, so that a graph of needs stores one
byte per edge (`LGraph`) and merging two needs is a bitwise or.

This recreates the part of ImportGraph's `DeclDeclNeedsKind` (`ImportGraph/Shake/DeclNeeds.lean`
at `b9ec7f6`) that is recorded in `.olean` files, for performance rather than by copying:
* `type`/`value` correspond to `expr .type`/`expr .value` (where in the *user* the reference is);
  ImportGraph's `isReExported` and upstream location are not modelled.
* `runtimeIR` and `metaIR` are not modelled: they need the compiler's LCNF.
* `comptime` (syntax and indirect module uses) is per module in the oleans (extra module uses), so
  it is not a need between declarations here.
The remaining flags record what ImportGraph does not: `implementedBy`, `preresolved` (names
preresolved by syntax quotations), `structural` (an inductive needs its constructors, a recursor its
mutual block) and `regenerated` (the reference was to a declaration regenerated from the needed one,
such as an equation lemma, which ImportGraph and shake drop).
-/
module

public section

namespace Agitate.ImportGraph

/-- A set of kinds of need, as bit flags. -/
structure NeedKinds where
  bits : UInt8
deriving BEq, Inhabited, Hashable

namespace NeedKinds

/-- No kind. -/
def none : NeedKinds := ⟨0⟩
/-- Mentioned in the user's type. -/
def type : NeedKinds := ⟨1⟩
/-- Mentioned in the user's value (body or proof). -/
def value : NeedKinds := ⟨2⟩
/-- The `@[implemented_by]` target of the user. -/
def implementedBy : NeedKinds := ⟨4⟩
/-- Preresolved by a syntax quotation in the user's value. -/
def preresolved : NeedKinds := ⟨8⟩
/-- A constructor of the inductive user, or the mutual block of the recursor user. -/
def structural : NeedKinds := ⟨16⟩
/-- Reached through a declaration regenerated from the needed one (a reserved name or `_simp_`). -/
def regenerated : NeedKinds := ⟨32⟩

instance : OrOp NeedKinds := ⟨fun a b => ⟨a.bits ||| b.bits⟩⟩

/-- Whether `k` contains every kind of `flag`. -/
@[inline] def has (k flag : NeedKinds) : Bool := k.bits &&& flag.bits == flag.bits

/-- The flags with their names, in order. -/
def named : Array (NeedKinds × String) :=
  #[(type, "type"), (value, "value"), (implementedBy, "implementedBy"),
    (preresolved, "preresolved"), (structural, "structural"), (regenerated, "regenerated")]

/-- The names of the kinds in `k`. -/
def toNames (k : NeedKinds) : Array String :=
  named.filterMap fun (f, s) => if k.has f then some s else Option.none

instance : ToString NeedKinds := ⟨fun k => ", ".intercalate k.toNames.toList⟩

end NeedKinds

end Agitate.ImportGraph
