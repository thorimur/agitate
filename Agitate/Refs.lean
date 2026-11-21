/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Sebastian Ullrich, Thomas Murrills
-/

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
  /-- See `Args.resolveDuplicates`. -/
  resolveDuplicates : Bool
  /-- See `Args.preresolvedNeeds`. -/
  preresolvedNeeds : Bool
  /--
  `modulate`: files converted with `public meta section`, whose declarations will all be meta
  (`Args.metaGlobs`). References to them count as references to meta declarations.
  -/
  metaModules : Std.HashSet ModuleIdx := {}

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
  /-- The (possibly redirected) name of the dependency. -/
  name : Name
  /-- The first declaring module (core's `getModuleIdxFor?`). -/
  mod : ModuleIdx
  isMeta : Bool
  indirect : Array ModuleIdx
  /--
  All declaring modules if the name is declared in more than one (`Index.dupDecls`) and
  `Args.resolveDuplicates` is set; otherwise empty (`agitate` addition).
  -/
  decls : Array ModuleIdx := #[]

/-- Resolves a reference; independent of the referencing module (`agitate` addition). -/
def resolveRef (s : RefCtx) (ref : Name) : Option Resolved := do
  let c ← getDepConstName? s ref
  let j ← s.ix.getModuleIdxFor? c
  return { name := c, mod := j, isMeta := isDeclMeta' s.ix c || s.metaModules.contains j,
           indirect := s.indirectModUses[c]?.getD #[],
           decls := if s.resolveDuplicates then s.ix.dupDecls[c]?.getD #[] else #[] }

/--
Specializes a resolution to referencing module `i` (`agitate` addition). For a name declared in
several modules (identical theorems up to binder annotations, which imports merge), upstream
charges every use to the first declarer, which may be outside `i`'s imports, and may charge `i`'s
own theorem to another module. Here `none` means `i` declares the name itself. Otherwise `mod`
becomes the declarer whose copy `i`'s environment showed (`Index.visibleDeclarer` over `i`'s load
order, `order`). Copies equal for the kernel can elaborate differently (binder annotations), so
that copy is the one `i` relies on. For other names, `r` is returned unchanged. Called once per
distinct name per module; `order` is computed at most once per module, and only when needed.
-/
def Resolved.forModule (ix : Index) (order : Thunk (Array Index.LoadedModule)) (i : ModuleIdx)
    (r : Resolved) : Option Resolved :=
  if r.decls.isEmpty then
    some r
  else if r.decls.contains i then
    none
  else
    some { r with mod := (ix.visibleDeclarer order.get r.name r.decls).getD r.mod, decls := #[] }

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
