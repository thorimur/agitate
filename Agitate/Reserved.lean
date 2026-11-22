/-
Copyright (c) 2019-2021 Microsoft Corporation. All rights reserved.
Copyright (c) 2024-2025 Lean FRO, LLC. All rights reserved.
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Joachim Breitner, Henrik Böving, Thomas Murrills
-/

/-
Reserved names, computed from the olean index.

`lake shake` ignores references to reserved names, deciding them with `isReservedName env`, i.e. by
running the predicates that core registers with `registerReservedNamePredicate`. Those take an
`Environment`, which agitate does not build. So each predicate is ported here from its Lean
`v4.36.0` source (the source location is named on each), with environment queries replaced by the
`Index` lookups that mirror them. Changes since the `v4.33.1` port: `bv_decide`'s enum names became
private (`bvEnumsFor?`), and partial-fixpoint induction gained the `strong_` variants.

Two semantics are supported (see DESIGN.md, "Reserved names"):
* `upstream`: exactly `lake shake`, whose environment has an anonymous `mainModule` and an
  unloaded matcher extension. Private generated names are never reserved, and `isMatcherCore` is
  always false.
* fixed (default): predicates see the module that declared the name as `mainModule`, and the
  imported matchers.

`agitate-check` compares both against core's own `isReservedName` on a real environment.
-/
module

public import Agitate.Index
public import Lean.Elab.PreDefinition.TerminationHint
import Lean.Meta.Eqns
import Lean.Meta.CongrTheorems
import Lean.Meta.Match.Basic
import all Lean.Structure
import all Lean.Meta.Constructions.SparseCasesOn
import all Lean.Meta.MethodSpecs
import all Lean.Meta.Tactic.BVDecide.Normalize.Enums
import Lean.Elab.PreDefinition.WF.Eqns
import Lean.Elab.PreDefinition.Structural.Eqns
import Lean.Elab.PreDefinition.PartialFixpoint.Eqns
import all Lean.Elab.PreDefinition.PartialFixpoint.Induction

open Lean Lean.Meta Lean.Elab

namespace Agitate.Reserved

/-- The context in which reserved-name predicates are evaluated. -/
public structure Ctx where
  ix : Index
  /-- Reproduce `lake shake`'s semantics, quirks included. -/
  upstream : Bool

variable (cx : Ctx)

/-! ### Environment queries, as seen by the predicates -/

/-- `env.mainModule` while deciding whether `n` is reserved. -/
def mainModuleFor (n : Name) : Name :=
  if cx.upstream then .anonymous else
  match cx.ix.getModuleIdxFor? n with
  | some i => cx.ix.modName i
  | none => .anonymous

/-- `mkPrivateName env n` while deciding whether `forName` is reserved. -/
def mkPrivateName (forName n : Name) : Name :=
  mkPrivateNameCore (mainModuleFor cx forName) (privateToUserName n)

/-- `isMatcherCore` (`Lean.Meta.Match.Extension.getMatcherInfo?`). -/
def isMatcherCore (declName : Name) : Bool :=
  if cx.upstream then false else
  match declName.eraseMacroScopes with
  | .str _ s => s.startsWith "match_" && cx.ix.matchers.contains declName
  | _ => false

/-- `Environment.isSafeDefinition`. -/
def isSafeDefinition (declName : Name) : Bool :=
  (cx.ix.find? declName matches some (.defnInfo { safety := .safe, .. }))

/-- `Environment.hasExposedBody`. -/
def hasExposedBody (n : Name) : Bool :=
  cx.ix.findPublic? n |>.any (·.hasValue)

/-- `isInductiveCore?`. -/
def isInductiveCore? (declName : Name) : Option InductiveVal :=
  match cx.ix.find? declName with
  | some (.inductInfo val) => some val
  | _ => none

/-- `getStructureFields`, via `getStructureInfo` (which panics on non-structures). -/
def getStructureFields (structName : Name) : Array Name :=
  let info? := match cx.ix.getModuleIdxFor? structName with
    | some i => (cx.ix.moduleEntries structureExt i).binSearch { structName } StructureInfo.lt
    | none => none
  match info? with
  | some info => info.fieldNames
  | none => (panic! "structure expected" : StructureInfo).fieldNames

/-! ### The predicates -/

/-- `declFromEqLikeName`. -/
def declFromEqLikeName (n : Name) : Option (Name × String) := Id.run do
  if let .str p s := n then
    if isEqnLikeSuffix s then
      for p in [p, privateToUserName p] do
        if isSafeDefinition cx p && !isMatcherCore cx p then
          return some (p, s)
  return none

/-- `Lean/Meta/Eqns.lean`: `f.eq_<i>`, `f.eq_def`, `f.eq_unfold` of safe definitions. -/
def eqns (n : Name) : Bool :=
  if let some (declName, suffix) := declFromEqLikeName cx n then
    -- `mkEqLikeNameFor`
    let name := Name.str declName suffix
    let name := if hasExposedBody cx declName then name else mkPrivateName cx n name
    n == name
  else
    false

/-- `Lean/Meta/Match/MatchEqs.lean`: `isMatchEqName?`, returning the matcher. -/
def matchEqFor? (n : Name) : Option Name := do
  let .str p s := n | failure
  guard <| isEqnReservedNameSuffix s || s == "splitter"
  let p ← privateToUserName? p
  guard <| isMatcherCore cx p
  return p

def matchEq (n : Name) : Bool := (matchEqFor? cx n).isSome

/-- `Lean/Meta/Match/MatchEqs.lean`: `isMatchCongrEqName?`. -/
def matchCongrEq (n : Name) : Bool := Option.isSome do
  let .str p s := n | failure
  guard <| Match.isCongrEqnReservedNameSuffix s
  guard <| isMatcherCore cx p

/-- `Lean/Meta/CongrTheorems.lean`: `f.hcongr_<i>`, `f.congr_simp`. -/
def congr (n : Name) : Bool :=
  match n with
  | .str p s => (isHCongrReservedNameSuffix s || s == congrSimpSuffix) && cx.ix.contains p
  | _ => false

/-- `Lean/Meta/CtorIdxHInj.lean`: `T.ctorIdx.hinj`. -/
def ctorIdxHInj (n : Name) : Bool :=
  -- `isCtorIdxCore?`
  if let .str (.str indName "ctorIdx") "hinj" := n then
    (isInductiveCore? cx indName).isSome
  else
    false

/-- `Lean/Meta/Injective.lean`: `C.hinj` for constructors. -/
def injective (n : Name) : Bool :=
  match n with
  | .str p "hinj" => (cx.ix.find? p matches some (.ctorInfo _))
  | _ => false

/-- `Lean/Meta/Constructions/SparseCasesOnEq.lean`: `isName`. -/
def sparseCasesOnEq (n : Name) : Bool :=
  if let .str p "else_eq" := n then
    (cx.ix.mapFind? sparseCasesOnInfoExt p).isSome
  else
    false

/-- `Lean/Meta/MethodSpecs.lean`: `isSpecThmNameFor`, returning the instance. -/
def methodSpecsFor? (name : Name) : Option Name := do
  let .str p s := name | none
  [p, privateToUserName p].firstM fun p => do
    let attrData ← cx.ix.getParam? methodSpecsAttr p
    for fieldName in getStructureFields cx attrData.clsName do
      if isSpecThmLikeSuffix fieldName s then
        -- `mkSpecTheoremName`
        let thmName := p.str s
        let thmName := if attrData.privateSpecs then mkPrivateName cx name thmName else thmName
        if name == thmName then
          return p
    none

def methodSpecs (name : Name) : Bool := (methodSpecsFor? cx name).isSome

open Tactic.BVDecide.Normalize in
/--
`Lean/Meta/Tactic/BVDecide/Normalize/Enums.lean`: the predicate, via `isRealizedName?`, returning
the enum type or matcher. The names are private to the module realizing them (`mkRealizedName`).
-/
def bvEnumsFor? (name : Name) : Option Name := Id.run do
  let .str p s := name | return none
  -- `isRealizedName?.isSupportedSuffix`
  unless s == enumToBitVecSuffix || s == eqIffEnumToBitVecEqSuffix || s == enumToBitVecLeSuffix ||
      s == matchEqCondSuffix do
    return none
  let some declName := [p, privateToUserName p].find? cx.ix.contains | return none
  -- `mkRealizedName`
  if name != mkPrivateName cx name (.str declName s) then return none
  if s == matchEqCondSuffix && !isMatcherCore cx declName then return none
  return some declName

def bvEnums (name : Name) : Bool := (bvEnumsFor? cx name).isSome

/-- `Lean/Meta/Tactic/FunInd.lean`: `isFunInductName`. -/
def funInduct (name : Name) : Bool := Id.run do
  let .str p s := name | return false
  match s with
  | "induct"
  | "induct_unfolding" =>
    unless isSafeDefinition cx p do return false
    if let some _ := cx.ix.mapFind? WF.eqnInfoExt p then
      return true
    if (cx.ix.mapFind? Structural.eqnInfoExt p).isSome then return true
    return false
  | "mutual_induct"
  | "mutual_induct_unfolding" =>
    unless isSafeDefinition cx p do return false
    if let some eqnInfo := cx.ix.mapFind? WF.eqnInfoExt p then
      if h : eqnInfo.declNames.size > 1 then
        return eqnInfo.declNames[0] = p
    if let some eqnInfo := cx.ix.mapFind? Structural.eqnInfoExt p then
      if h : eqnInfo.declNames.size > 1 then
        return eqnInfo.declNames[0] = p
    return false
  | _ => return false

/-- `Lean/Meta/Tactic/FunInd.lean`: `isFunCasesName`. -/
def funCases (name : Name) : Bool := Id.run do
  let .str p s := name | return false
  match s with
  | "fun_cases"
  | "fun_cases_unfolding" =>
    unless isSafeDefinition cx p do return false
    return true
  | _ => return false

/-- `Lean/Elab/PreDefinition/PartialFixpoint/Induction.lean`: `isInductName`. -/
def fixpointInduct (name : Name) : Bool := Id.run do
  let .str p s := name | return false
  let find? := cx.ix.mapFind? PartialFixpoint.eqnInfoExt
  match s with
  | "fixpoint_induct" =>
    if let some eqnInfo := find? p then
      return eqnInfo.fixpointType.all isPartialFixpoint
    return false
  | "coinduct" | "strong_coinduct" =>
    if let some eqnInfo := find? p then
      let idx := eqnInfo.declNames.idxOf p
      return isCoinductiveFixpoint eqnInfo.fixpointType[idx]!
    return false
  | "induct" | "strong_induct" =>
    if let some eqnInfo := find? p then
      let idx := eqnInfo.declNames.idxOf p
      return isInductiveFixpoint eqnInfo.fixpointType[idx]!
    return false
  | "mutual_induct" | "strong_mutual_induct" =>
    if let some eqnInfo := find? p then
      return eqnInfo.declNames[0]! == p && eqnInfo.declNames.size > 1 && eqnInfo.fixpointType.all isLatticeTheoretic
    return false
  | "mutual_fixpoint_induct" =>
    if let some eqnInfo := find? p then
      return eqnInfo.declNames[0]! == p && eqnInfo.declNames.size > 1 && eqnInfo.fixpointType.all isPartialFixpoint
    return false
  | _ => return false

/-- `Lean/Elab/PreDefinition/PartialFixpoint/Induction.lean`: `isOptionFixpoint`. -/
def isOptionFixpoint (name : Name) : Bool := Option.isSome do
  let eqnInfo ← cx.ix.mapFind? PartialFixpoint.eqnInfoExt name
  guard <| name == eqnInfo.declNames[0]!
  let defnInfo ← cx.ix.find? eqnInfo.declNameNonRec
  assert! defnInfo.hasValue
  let mut value := defnInfo.value!
  while value.isLambda do value := value.bindingBody!
  let_expr Lean.Order.fix _ inst _ _ := value | panic! s!"isOptionFixpoint: unexpected value {value}"
  let insts := PartialFixpoint.CCPOProdProjs eqnInfo.declNames.size inst
  insts.forM fun inst => do
    let mut inst := inst
    while inst.isAppOfArity ``Lean.Order.instCCPOPi 3 do
      guard inst.appArg!.isLambda
      inst := inst.appArg!.bindingBody!
    guard <| inst.isAppOfArity ``Lean.Order.instCCPOOption 1

/-- `Lean/Elab/PreDefinition/PartialFixpoint/Induction.lean`: `isPartialCorrectnessName`. -/
def partialCorrectness (name : Name) : Bool := Id.run do
  let .str p s := name | return false
  match s with
  | "partial_correctness" => return isOptionFixpoint cx p
  | "mutual_partial_correctness" =>
    if let some eqnInfo := cx.ix.mapFind? PartialFixpoint.eqnInfoExt p then
      return eqnInfo.declNames[0]! == p && isOptionFixpoint cx p && eqnInfo.declNames.size > 1
    return false
  | _ => return false

/-- The extensions the predicates look up; pass to `Index.build` so their entries are pre-resolved. -/
public def extNames : Array Name :=
  #[structureExt.name, sparseCasesOnInfoExt.name, methodSpecsAttr.ext.name, WF.eqnInfoExt.name,
    Structural.eqnInfoExt.name, PartialFixpoint.eqnInfoExt.name]

/-- The number of predicates ported here; `agitate-check` verifies that core registers as many. -/
public def numPredicates : Nat := 13

/-- `isReservedName`: whether any of the ported predicates holds. -/
public def isReserved (n : Name) : Bool :=
  eqns cx n || matchEq cx n || matchCongrEq cx n || congr cx n || ctorIdxHInj cx n ||
  injective cx n || sparseCasesOnEq cx n || methodSpecs cx n || bvEnums cx n || funInduct cx n ||
  funCases cx n || fixpointInduct cx n || partialCorrectness cx n

/--
The declaration a reserved name is regenerated from: the definition for equation lemmas, the matcher
for matcher equations, the instance for method specs, the enum type or matcher for `bv_decide`'s
enum names (which are private, so their prefix is not the base), and otherwise the name's prefix
(the constructor, inductive, function, …). If that is not an imported constant, its nearest prefix
that is.
`none` if `n` is not reserved.

`agitate` counts a reference to a reserved name as a reference to this declaration, since
regenerating the name needs it. Upstream drops the reference entirely (DESIGN.md, "Reserved names").
-/
public def reservedBase? (n : Name) : Option Name := do
  guard <| isReserved cx n
  let base :=
    if let some (declName, _) := (if eqns cx n then declFromEqLikeName cx n else none) then declName
    else if let some p := matchEqFor? cx n then p
    else if let some p := methodSpecsFor? cx n then p
    else if let some p := bvEnumsFor? cx n then p
    else n.getPrefix
  let rec findConst : Name → Option Name
    | .anonymous => none
    | c@(.str p _) | c@(.num p _) =>
      if cx.ix.getModuleIdxFor? c |>.isSome then some c else findConst p
  findConst base

end Agitate.Reserved
