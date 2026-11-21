/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/

/-
Needs from names that syntax quotations preresolve (`Args.preresolvedNeeds`, `agitate` addition;
DESIGN.md "Preresolved names in quotations").

A quotation such as `` `(foo) `` resolves `foo` when it is elaborated and stores the result in the
syntax: the compiled term contains `Syntax.Preresolved.decl `foo []`, a `Name` literal rather than
a constant, so `Expr.foldConsts` does not see it, and Lean records no extra module use for it. If
that is the only use of `foo`'s module, `lake shake` removes the import. The quotation's module
still builds (preresolution just finds nothing), but every expansion then fails with
``Unknown identifier `foo✝` ``: the name carries macro scopes, so only preresolution can resolve it.

This file works around that by synthesizing the extra module use that Lean would record if
`quoteSyntax` did what `` ``foo `` does (`elabDoubleQuotedName`): a non-meta use of the
declaring module, public if the declaration containing the quotation is. The ideal fix is in
Lean, see DESIGN.md. Kept separate so it can be removed once Lean records these uses itself.
-/
module

public import Agitate.Refs

public section

open Lean

namespace Agitate.Preresolved

private def decodeStr? : Expr → Option String
  | .lit (.strVal s) => some s
  | .mdata _ e => decodeStr? e
  | _ => none

private partial def decodeNat? (e : Expr) : Option Nat :=
  match e.consumeMData with
  | .lit (.natVal n) => some n
  | e => if e.isAppOfArity ``OfNat.ofNat 3 then decodeNat? e.appFn!.appArg! else none

/--
Decodes a closed `Name` term as `ToExpr Name` builds it (`Name.mkStr1` … `Name.mkStr8`, `Name.str`,
`Name.num`, `Name.anonymous`), also accepting `Name.mkStr`, `Name.mkNum` and `Name.mkSimple`.
-/
partial def decodeName? (e : Expr) : Option Name := do
  let e := e.consumeMData
  let .const c _ := e.getAppFn | none
  let args := e.getAppArgs
  match c, args.size with
  | ``Name.anonymous, 0 => return .anonymous
  | ``Name.str, 2 | ``Name.mkStr, 2 => return .str (← decodeName? args[0]!) (← decodeStr? args[1]!)
  | ``Name.num, 2 | ``Name.mkNum, 2 => return .num (← decodeName? args[0]!) (← decodeNat? args[1]!)
  | ``Name.mkSimple, 1 => return .str .anonymous (← decodeStr? args[0]!)
  | _, n =>
    guard (0 < n && n ≤ 8 && c == .str ``Name s!"mkStr{n}")
    args.foldlM (init := .anonymous) fun p a => return .str p (← decodeStr? a)

private partial def collect (e : Expr) : StateM (Std.HashSet Expr × Array Name) Unit := do
  if (← get).1.contains e then return
  modify fun (v, ns) => (v.insert e, ns)
  if e.isAppOfArity ``Syntax.Preresolved.decl 2 then
    if let some n := decodeName? e.appFn!.appArg! then
      modify fun (v, ns) => (v, if ns.contains n then ns else ns.push n)
    return
  match e with
  | .app f a => collect f; collect a
  | .lam _ t b _ | .forallE _ t b _ => collect t; collect b
  | .letE _ t v b _ => collect t; collect v; collect b
  | .mdata _ b | .proj _ _ b => collect b
  | _ => pure ()

/-- The names `n` of the subterms `Syntax.Preresolved.decl n _` of `e` whose `n` is a closed
`Name` term, without duplicates. -/
def declNames (e : Expr) : Array Name :=
  ((collect e).run ({}, #[])).2.2

/--
Whether module `i` may contain quotations: `consts` are the names its terms refer to. Callers that
have already collected them use this to skip the scan of modules without any.
-/
def mayHave (consts : Name → Bool) : Bool :=
  consts ``Syntax.Preresolved.decl

/--
The extra module uses that the quotations in `ci` (a declaration of module `i`) imply, as
`(preresolved name, declaring module)`, each module at most once. Names are resolved like constant
references (`resolveRef`, `Resolved.forModule`). Unlike `recordExtraModUseFromDecl`, the declaring
module's indirect uses are not added: those are needs of the expansion sites, which reference the
declaration as a constant, while the quotation's module only needs the name to resolve.
Empty unless `Args.preresolvedNeeds`.
-/
def uses (refs : RefCtx) (order : Thunk (Array Index.LoadedModule)) (i : ModuleIdx)
    (ci : ConstantInfo) : Array (Name × ModuleIdx) := Id.run do
  if !refs.preresolvedNeeds then return #[]
  let some e := ci.value? (allowOpaque := true) | return #[]
  let mut out := #[]
  for n in declNames e do
    if let some r := (resolveRef refs n).bind (·.forModule refs.ix order i) then
      if r.mod != i && !out.any (·.2 == r.mod) then
        out := out.push (n, r.mod)
  return out

end Agitate.Preresolved
