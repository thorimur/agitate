/-
Resolving the constants that a module's terms refer to, shared by `agitate` and
`agitate-nonmodule`. Adapted from upstream `Lake/CLI/Shake.lean` (Lean `v4.33.1`).
-/
module

public import Agitate.Reserved

public section

open Lean

namespace Agitate

/-- Everything needed to resolve references (`agitate`; upstream keeps these in shake's state). -/
structure RefCtx where
  ix : Index
  /-- How reserved names are decided. -/
  reserved : Reserved.Ctx
  /-- See `Args.reservedRefsToBase`. -/
  reservedRefsToBase : Bool
  /-- Indirect module uses of the kinds not ignored (`Args.ignoreIndirectKinds`). -/
  indirectModUses : Std.HashMap Name (Array ModuleIdx)
  /-- See `Args.implementedByNeeds`. -/
  implementedByNeeds : Bool

def isDeclMeta' (ix : Index) (declName : Name) : Bool :=
  -- Matchers are not compiled by themselves but inlined by the compiler, so there is no IR decl
  -- to be tagged as `meta`.
  -- TODO: It would be better to base the entire `meta` inference on the IR only and consider module
  -- references from any other context as compatible with both phases.
  let inferFor :=
    if declName.isStr && (declName.getString!.startsWith "match_" || declName.getString! == "_unsafe_rec") then declName.getPrefix else declName
  -- `isMarkedMeta` knows about non-defs such as `meta structure`, isDeclMeta knows about decls
  -- implicitly marked meta
  ix.isMarkedMeta inferFor || ix.isDeclMeta inferFor

/--
Given an `Expr` reference, returns the declaration name that should be considered the reference, if
any.
-/
def getDepConstName? (s : RefCtx) (ref : Name) : Option Name := do
  -- Ignore references to reserved names, they can be re-generated in-place
  -- (`agitate`: decided lazily per referenced name, see `Agitate.Reserved`; by default, count the
  -- reference as one to the declaration the name is regenerated from, which regeneration needs)
  if let some base := Reserved.reservedBase? s.reserved ref then
    guard s.reservedRefsToBase
    return base
  -- `_simp_...` constants are similar, use base decl instead
  return if ref.isStr && ref.getString!.startsWith "_simp_" then
    ref.getPrefix
  else
    ref

/--
How a constant referenced from an `Expr` counts towards a module's needs: the module that declares
the (possibly redirected) dependency, whether that declaration is `meta`, and its indirect module
uses. `none` if the reference is ignored (reserved, or not an imported constant).
-/
structure Resolved where
  mod : ModuleIdx
  isMeta : Bool
  indirect : Array ModuleIdx

/-- Resolves a reference; independent of the referencing module (`agitate` addition). -/
def resolveRef (s : RefCtx) (ref : Name) : Option Resolved := do
  let c ← getDepConstName? s ref
  let j ← s.ix.getModuleIdxFor? c
  return { mod := j, isMeta := isDeclMeta' s.ix c, indirect := s.indirectModUses[c]?.getD #[] }

/--
The `@[implemented_by]` target of `decl` with its module and meta-ness, if it is to be counted as a
need of `decl`'s module (`Args.implementedByNeeds`; `agitate` addition). The attribute names the
target only in its argument, so neither terms nor recorded uses mention it.
-/
def implementedByTarget? (s : RefCtx) (decl : Name) : Option (Name × ModuleIdx × Bool) := do
  guard s.implementedByNeeds
  let g ← s.ix.implementedBy? decl
  let j ← s.ix.getModuleIdxFor? g
  return (g, j, isDeclMeta' s.ix g)

end Agitate
