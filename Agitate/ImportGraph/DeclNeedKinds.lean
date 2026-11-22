/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/

/-
# Kinds of need between declarations (upstreamable)

How one declaration (the *user*) needs another (the *used* one). Recreated from ImportGraph's
`DeclDeclNeedsKind` (`ImportGraph/Shake/DeclNeeds.lean` at `b9ec7f6`), with the same constructors
and four more that the oleans let agitate record:

* `expr downstream isReExported? upstream`: the user mentions the used declaration in its type or
  value (`downstream`), needing the used declaration's type or value (`upstream`; needing the value
  means unfolding it, which matters for `@[expose]`). `isReExported?` overrides whether the need is
  public; `none` inherits it from the user (public type, exposed value).
* `runtimeIR`, `metaIR isReExported? through`: the user's code uses the used declaration, at runtime
  or at compile time. A public meta declaration re-exports what the private meta declarations of
  its module that its code reaches use (`through`: that path).
* `comptime source`: needed while elaborating the user (syntax, indirect module uses, …).
* agitate's additions, recording *why*: `implementedBy` (the user's `@[implemented_by]` target),
  `preresolved` (a name a syntax quotation in the user resolves), `structural` (a constructor of
  the inductive user, or the mutual block of the recursor user) and `regenerated` (the user refers
  to a declaration regenerated from the used one, such as an equation lemma).

`DeclNeedKinds` is a set of kinds, packed in a `UInt32` (one bit per kind without its payload), so
that a graph of needs stores a word per edge and merging needs is a bitwise or. Payloads (`through`,
`comptime`'s source) are not part of the set; producers that record them keep them alongside.
-/
module

public section

namespace Agitate.ImportGraph

/-- A part of a declaration: its type or its value. -/
inductive ConstLocation where
  | type
  | value
deriving BEq, Hashable, Repr, Inhabited

/-- What makes a declaration needed while elaborating another (`DeclNeedKind.comptime`). -/
inductive ComptimeSource where
  /-- Syntax of the used declaration's kind appears in the user's command. -/
  | stx
  /-- An attribute on the used declaration, applied in another module. -/
  | indirect (kind : String)
  /-- Not known (as for extra module uses, which name no declaration). -/
  | other
deriving BEq, Hashable, Repr, Inhabited

/-- One way a declaration needs another; see the module docstring. -/
inductive DeclNeedKind where
  | expr (downstream : ConstLocation) (isReExported? : Option Bool := none)
      (upstream : ConstLocation := .type)
  | runtimeIR
  | metaIR (isReExported? : Option Bool := none) (through : List Lean.Name := [])
  | comptime (source : ComptimeSource := .other)
  | implementedBy
  | preresolved
  | structural
  | regenerated
deriving BEq, Hashable, Repr, Inhabited

namespace DeclNeedKind

private def optIdx : Option Bool → Nat
  | none => 0 | some false => 1 | some true => 2

private def locIdx : ConstLocation → Nat
  | .type => 0 | .value => 1

/-- The bit of the kind (its payload dropped) in `DeclNeedKinds`. -/
def bit : DeclNeedKind → Nat
  | expr d r u => 6 * locIdx d + 2 * optIdx r + locIdx u
  | runtimeIR => 12
  | metaIR r _ => 13 + optIdx r
  | comptime _ => 16
  | implementedBy => 17
  | preresolved => 18
  | structural => 19
  | regenerated => 20

/-- The number of bits in use. -/
def numBits : Nat := 21

/-- The kind of each bit, payloads empty. -/
def ofBit (b : Nat) : DeclNeedKind :=
  let opt (i : Nat) : Option Bool := if i == 0 then none else some (i == 2)
  let loc (i : Nat) : ConstLocation := if i == 0 then .type else .value
  if b < 12 then expr (loc (b / 6)) (opt (b % 6 / 2)) (loc (b % 2))
  else match b with
    | 12 => runtimeIR | 13 | 14 | 15 => metaIR (opt (b - 13)) | 16 => comptime
    | 17 => implementedBy | 18 => preresolved | 19 => structural | _ => regenerated

/-- A short description, for reports. -/
def toString : DeclNeedKind → String
  | expr d r u =>
    let loc := fun | ConstLocation.type => "type" | .value => "value"
    s!"{loc d}{if u == .value then " (unfolds)" else ""}\
      {match r with | some true => " (public)" | some false => " (private)" | none => ""}"
  | runtimeIR => "runtimeIR"
  | metaIR r through =>
    s!"metaIR{match r with | some true => " (public)" | some false => " (private)" | none => ""}\
      {if through.isEmpty then "" else s!" through {through}"}"
  | comptime _ => "comptime"
  | implementedBy => "implementedBy"
  | preresolved => "preresolved"
  | structural => "structural"
  | regenerated => "regenerated"

instance : ToString DeclNeedKind := ⟨DeclNeedKind.toString⟩

end DeclNeedKind

/-- A set of `DeclNeedKind`s (payloads dropped), one bit each. -/
structure DeclNeedKinds where
  bits : UInt32
deriving BEq, Hashable, Inhabited

namespace DeclNeedKinds

def empty : DeclNeedKinds := ⟨0⟩
instance : EmptyCollection DeclNeedKinds := ⟨empty⟩

def single (k : DeclNeedKind) : DeclNeedKinds := ⟨(1 : UInt32) <<< k.bit.toUInt32⟩
instance : Coe DeclNeedKind DeclNeedKinds := ⟨single⟩

instance : Union DeclNeedKinds := ⟨fun a b => ⟨a.bits ||| b.bits⟩⟩

def insert (s : DeclNeedKinds) (k : DeclNeedKind) : DeclNeedKinds := s ∪ single k

/-- Whether `s` contains `k` (payload ignored). -/
def contains (s : DeclNeedKinds) (k : DeclNeedKind) : Bool :=
  s.bits &&& ((1 : UInt32) <<< k.bit.toUInt32) != 0

def isEmpty (s : DeclNeedKinds) : Bool := s.bits == 0

/-- The kinds in `s`, in bit order. -/
def toArray (s : DeclNeedKinds) : Array DeclNeedKind :=
  (Array.range DeclNeedKind.numBits).filterMap fun b =>
    if s.bits &&& ((1 : UInt32) <<< b.toUInt32) != 0 then some (DeclNeedKind.ofBit b) else none

def toStrings (s : DeclNeedKinds) : Array String := s.toArray.map toString

instance : ToString DeclNeedKinds := ⟨fun s => ", ".intercalate s.toStrings.toList⟩

end DeclNeedKinds

end Agitate.ImportGraph
