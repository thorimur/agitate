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
  declarations of the same module that their code reaches) needs its code imported publicly
  (`metaIR (some true)`).
* A need on the used declaration's value (`expr _ _ .value`: unfolding it) needs that value visible:
  exposed, or else `import all`.
-/
module

public import Agitate.ImportGraph.Imports
public import Agitate.ImportGraph.DeclNeedKinds

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

/-- Whether the declaration's data at `loc` is private: its type if the declaration is private, its
value unless exposed. -/
def isPrivateAt (s : Stance) : ConstLocation → Bool
  | .type => !s.isPublic
  | .value => !s.isExposed

/--
The import need of a declaration with stance `user` on one with stance `used`, through a need of
kind `k` (as ImportGraph's `Stance.toImportNeedsKind`). `none` for kinds that only record why
(`implementedBy`, `regenerated`): producers add the need itself.
-/
def importNeedOf (user : Stance) (k : DeclNeedKind) (used : Stance) : Option ImportNeed :=
  -- visible where needed: from the private scope (`import all`) if what is needed is private
  let visible (exported : Bool) (loc : ConstLocation := .type) : ImportNeed :=
    { isExported := exported, isAll := !exported && used.isPrivateAt loc }
  match k with
  | .expr down r up =>
    some (visible (r.getD (match down with | .type => user.isPublic | .value => user.isExposed)) up)
  | .structural => some (visible user.isPublic)
  -- code: anything not marked meta (constructors included) is available only in its import's phase
  | .runtimeIR => some { visible false with isMeta? := some false }
  | .metaIR r _ =>
    some { visible (r.getD user.isPublic) with isMeta? := if used.phase == .meta then none else some true }
  | .comptime _ => some { visible false with isMeta? := if used.phase == .meta then none else some true }
  -- the name must resolve where the quotation's code runs: at runtime, publicly if the user is
  | .preresolved => some { visible user.isPublic with isMeta? := some false }
  | .implementedBy | .regenerated => none

/-- The import needs of `user` on `used` through the needs `ks`. -/
def importNeeds (user : Stance) (ks : DeclNeedKinds) (used : Stance) : Array ImportNeed :=
  ks.toArray.filterMap (user.importNeedOf · used)

end Stance

end Agitate.ImportGraph
