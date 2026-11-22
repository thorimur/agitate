/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/

/-
# Stances and the imports a need demands (upstreamable)

Recreated from ImportGraph's `Stance` and `Stance.toImportNeedsKind` (`ImportGraph/Shake/DeclNeeds.lean`
at `b9ec7f6`), with the phase rules of the module system quickstart
(leanprover-community.github.io/extras/module-system-quickstart.html):

* A reference from a type, or from a value, only needs the used declaration to be visible where the
  reference is: publicly if the user's type is public, or its value exposed; otherwise privately,
  and from the private scope (`import all`) if the used declaration is private. Types and values are
  erased in code, so either phase will do.
* Code references keep phases apart, as Lean checks them (`Lean.Compiler.LCNF.checkMeta`): what
  code uses (constructors included) is available only in the phase it was imported in, unless it is
  marked meta. Runtime code needs it imported without `meta`; meta code needs it lifted by a
  `meta import`, unless it is meta already, when any import will do.
* Meta code that must be presentable (usable downstream: public meta declarations, and private meta
  declarations of the same module that their code reaches) needs its code imported publicly.
-/
module

public import Agitate.ImportGraph.Imports
public import Agitate.ImportGraph.NeedKinds

public section

namespace Agitate.ImportGraph

/-- The phase of a declaration's code, if it has code. -/
inductive Phase where
  /-- No code: theorems, types, constructors, noncomputable definitions, … -/
  | none
  | runtime
  | «meta»
deriving BEq, Inhabited, Repr

/-- What determines how a declaration may be needed. -/
structure Stance where
  isPublic : Bool
  /-- Whether its value is public (`@[expose]`d definitions; public abbreviations, instances). -/
  isExposed : Bool := false
  phase : Phase := .none
deriving BEq, Inhabited, Repr

namespace Stance

/--
The import needs of a declaration with stance `user` on one with stance `used`, through a need of
kinds `k`. `presentable` says whether the user's code must be presentable (by default, iff it is
public); it matters only for meta code.
-/
def importNeeds (user : Stance) (k : NeedKinds) (used : Stance)
    (presentable : Bool := user.isPublic) : Array ImportNeed := Id.run do
  let mut out := #[]
  let visible (exported : Bool) : ImportNeed :=
    { isExported := exported, isAll := !exported && !used.isPublic }
  if k.has .type || k.has .structural then
    out := out.push (visible user.isPublic)
  if k.has .value then
    out := out.push (visible user.isExposed)
  if k.has .code || k.has .implementedBy then
    -- as Lean checks code (`Lean.Compiler.LCNF.checkMeta`): anything not marked meta (constructors
    -- included) is available to code only in the phase it was imported in
    match user.phase with
    | .meta =>
      out := out.push { visible presentable with
        isMeta? := if used.phase == .meta then none else some true }
    | .runtime =>
      out := out.push { visible false with isMeta? := some false }
    | .none => pure ()
  if k.has .preresolved then
    -- the name must resolve when the quotation's code runs downstream: a runtime need, public if
    -- the user is (as `agitate` counts it)
    out := out.push { visible user.isPublic with isMeta? := some false }
  return out

end Stance

end Agitate.ImportGraph
