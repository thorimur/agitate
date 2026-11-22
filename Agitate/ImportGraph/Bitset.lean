/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Sebastian Ullrich, Thomas Murrills
-/

module

public section

namespace Agitate.ImportGraph

/--
A set of small naturals (usually module indices), packed eight per byte.

Changed from Lake's `shake` (`Lake/CLI/Shake.lean`, Lean `v4.33.1`; unchanged in `v4.36.0`), which
uses a `Nat` here.
There `has` is `Nat.testBit`, i.e. `1 &&& (m >>> i)`, which copies the whole bignum on every
membership test, and every `∪ {j}` allocates the singleton `1 <<< j`. That made the sequential
`visitModule` loop dominate shake's runtime (agitate's DESIGN.md, B1). Here `has` is O(1), and
`insert`, `∪`, `∩` and `\` update the left operand in place when it is uniquely referenced. Sets
may have different byte lengths; missing bytes are zero.

The trade-off, measured against `Nat` (compiled; 20 000 sets of 30 elements over 10 000 indices):
`insert` and `has` are 30–100× faster, but `∪` is 3–20× slower, since it loops over bytes in Lean
while `Nat.lor` works on words in C (agitate's DESIGN.md, "`Agitate.ImportGraph`").
-/
structure Bitset where
  bytes : ByteArray
deriving Inhabited

namespace Bitset

instance : EmptyCollection Bitset where
  emptyCollection := ⟨.empty⟩

/-- A block of zero bytes to grow bitsets from (enough for 512k modules). -/
private def zeros : ByteArray := ⟨Array.replicate 65536 0⟩

/-- Pads `bytes` with zeros to at least `n` bytes (in C, via `copySlice`). -/
private def grow (bytes : ByteArray) (n : Nat) : ByteArray := Id.run do
  if n ≤ bytes.size then return bytes
  if n - bytes.size ≤ zeros.size then
    return zeros.copySlice 0 bytes bytes.size (n - bytes.size)
  let mut bytes := bytes
  for _ in bytes.size...n do
    bytes := bytes.push 0
  return bytes

@[inline] def has (s : Bitset) (i : Nat) : Bool :=
  let b := i / 8
  if h : b < s.bytes.size then
    (s.bytes[b] >>> (i % 8).toUInt8) &&& 1 != 0
  else
    false

def insert (s : Bitset) (i : Nat) : Bitset :=
  let b := i / 8
  let bytes := grow s.bytes (b + 1)
  ⟨bytes.set! b (bytes.get! b ||| ((1 : UInt8) <<< (i % 8).toUInt8))⟩

def erase (s : Bitset) (i : Nat) : Bitset :=
  let b := i / 8
  if b < s.bytes.size then
    ⟨s.bytes.set! b (s.bytes.get! b &&& ~~~((1 : UInt8) <<< (i % 8).toUInt8))⟩
  else
    s

instance : Insert Nat Bitset where
  insert i s := s.insert i

instance : Singleton Nat Bitset where
  singleton i := (∅ : Bitset).insert i

/-- `a ∪ b`, in place in the longer operand (`a` on ties), so nothing ever needs to grow. -/
def union (a b : Bitset) : Bitset := Id.run do
  let (long, short) := if a.bytes.size < b.bytes.size then (b, a) else (a, b)
  let mut bytes := long.bytes
  for h : i in 0...short.bytes.size do
    bytes := bytes.set! i (bytes.get! i ||| short.bytes[i])
  return ⟨bytes⟩

/-- `a ∩ b`, in place in `a`. -/
def inter (a b : Bitset) : Bitset := Id.run do
  let mut bytes := a.bytes
  for i in 0...bytes.size do
    bytes := bytes.set! i (bytes.get! i &&& b.bytes.get! i)
  return ⟨bytes⟩

/-- `a \ b`, in place in `a`. -/
def diff (a b : Bitset) : Bitset := Id.run do
  let mut bytes := a.bytes
  for i in 0...min bytes.size b.bytes.size do
    bytes := bytes.set! i (bytes.get! i &&& ~~~(b.bytes.get! i))
  return ⟨bytes⟩

instance : Union Bitset := ⟨union⟩
instance : Inter Bitset := ⟨inter⟩
instance : SDiff Bitset := ⟨diff⟩

/-- Whether the set has no elements. -/
def isEmpty (s : Bitset) : Bool :=
  s.bytes.data.all (· == 0)

/-- The elements in ascending order. -/
def toArray (s : Bitset) : Array Nat := Id.run do
  let mut out := #[]
  for h : b in 0...s.bytes.size do
    let byte := s.bytes[b]
    if byte != 0 then
      for bit in 0...8 do
        if (byte >>> bit.toUInt8) &&& 1 != 0 then
          out := out.push (8 * b + bit)
  return out

/-- Whether every element of `a` is in `b`. -/
def subset (a b : Bitset) : Bool := Id.run do
  for h : i in 0...a.bytes.size do
    if a.bytes[i] &&& ~~~(b.bytes.get! i) != 0 then return false
  return true

instance : HasSubset Bitset := ⟨fun a b => a.subset b⟩
instance : DecidableRel (α := Bitset) (· ⊆ ·) := fun a b => inferInstanceAs (Decidable (a.subset b = true))

instance : BEq Bitset := ⟨fun a b => a.subset b && b.subset a⟩

/-- The elements in descending order. -/
def toArrayRev (s : Bitset) : Array Nat := s.toArray.reverse

instance : Repr Bitset where
  reprPrec s _ := repr s.toArray

end Bitset

end Agitate.ImportGraph
