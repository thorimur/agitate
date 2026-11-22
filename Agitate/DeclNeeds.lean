/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/

/-
Declaration needs from the olean index: what each constant refers to, with the kind of need
(`Agitate.ImportGraph.NeedKinds`), and how a reference resolves to a declaration. This is agitate's
producer for the model in `Agitate.ImportGraph` (ImportGraph's `calcDeclConstInfoNeeds` is the
`Environment`-based counterpart); it reads only what the oleans record.
-/
module

public import Agitate.Preresolved
public import Agitate.ImportGraph.NeedKinds
public import Agitate.ImportGraph.Stance

public section

open Lean Agitate.ImportGraph

namespace Agitate

/--
The stance of declaration `n`, from the index: public if its module's public part declares it (and
its name is not private), exposed if that part has its value, meta if marked or inferred meta, and
runtime if it is a definition other than a matcher (matchers are inlined). Noncomputable
definitions count as runtime: an approximation.
-/
def stanceOf (ix : Index) (n : Name) : Stance :=
  let pub? := if isPrivateName n then none else ix.findPublic? n
  let phase := if isDeclMeta' ix n then .meta else match ix.find? n with
    | some (.defnInfo _) | some (.opaqueInfo _) => if ix.matchers.contains n then .none else .runtime
    | _ => .none
  { isPublic := pub?.isSome, isExposed := pub?.any (·.hasValue (allowOpaque := true)), phase }

/--
The references of constant `ci`, with the kind of each: its type's constants (`type`), its value's
(`value`), names preresolved by quotations in its value (`preresolved`), an inductive's constructors
and a recursor's mutual block (`structural`, as `ConstantInfo.getUsedConstantsAsSet`), and its
`@[implemented_by]` target. The same name may occur several times, with different kinds.

If `code` (the constant has code), its value's references are also `code` references. This
approximates the references of its compiled code, which the oleans keep separately (IR): it also
counts references that compilation erases, such as those in proofs.
-/
def constRefs (refs : RefCtx) (ci : ConstantInfo) (code := false) : Array Name × ByteArray :=
    Id.run do
  let push (k : NeedKinds) (acc : Array Name × ByteArray) (n : Name) :=
    (acc.1.push n, acc.2.push k.bits)
  let mut acc := ci.type.getUsedConstants.foldl (push .type) (#[], .empty)
  if let some v := ci.value? (allowOpaque := true) then
    let vs := v.getUsedConstants
    acc := vs.foldl (push (if code then .value ||| .code else .value)) acc
    -- only scanned if the value builds `Syntax.Preresolved`
    if refs.preresolvedNeeds && vs.contains ``Syntax.Preresolved.decl then
      acc := (Preresolved.declNames v).foldl (push .preresolved) acc
  match ci with
  | .inductInfo val => acc := val.ctors.foldl (push .structural) acc
  | .recInfo val => acc := val.all.foldl (push .structural) acc
  | _ => pure ()
  if refs.implementedByNeeds then
    if let some g := refs.ix.implementedBy? ci.name then
      acc := push .implementedBy acc g
  return acc

/--
The declaration that a reference to `ref` from module `i` counts as: its name and declaring module,
and whether the reference was redirected to it (a reserved name or `_simp_` constant regenerated
from it). Resolved as `agitate` resolves references (`resolveRef`, `Resolved.forModule`), so a
duplicated theorem resolves to the copy `i` saw, or to `i` itself. `none` if the reference is
ignored (not an imported constant).
-/
def resolveDecl (refs : RefCtx) (order : Thunk (Array Index.LoadedModule)) (i : ModuleIdx)
    (ref : Name) : Option (Name × ModuleIdx × Bool) := do
  let r ← resolveRef refs ref
  let (n, j) := match r.forModule refs.ix order i with
    | some r' => (r'.name, r'.mod)
    | none => (r.name, i)  -- `i` declares its own copy
  return (n, j, n != ref)

end Agitate
