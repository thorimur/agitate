/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/

/-
# The algebra of module-system imports (upstreamable)

Recreated from ImportGraph (`ImportGraph/Shake/Core.lean`, `Shake/Algebra.lean` and the
`ImportNeeds` part of `Shake/DeclNeeds.lean`, at `b9ec7f6`), on `Agitate.ImportGraph.Bitset`.

An import is an arrow between scopes: `public import` puts the imported module's public scope into
the importer's public scope, `import` into its private scope, and `import all` the imported private
scope into the private scope; `meta` additionally lifts the imported runtime code to the meta phase.
Arrows compose (`ImportKind.andThen`), so a module's imports determine, for every module, which of
its scopes arrive where (`Provides`, `Hierarchy`). A need (`ImportNeed`) may fix the phase or leave
it open; `ImportNeeds.reduce` finds minimal imports providing a set of needs.
-/
module

public import Agitate.ImportGraph.Bitset
public import Lean.Setup

public section

namespace Agitate.ImportGraph

/--
The kind of an import, or of an arrow from one module's scope into another's. `isAll` means the
private scope of the source is used (`import all`); `isExported` that the target is the public
scope. Public `import all` does not exist: `¬(isExported ∧ isAll)`.
-/
structure ImportKind where
  isExported : Bool
  isAll : Bool := false
  isMeta : Bool := false
deriving BEq, Hashable, Repr, Inhabited

namespace ImportKind

def pub : ImportKind := { isExported := true }
def priv : ImportKind := { isExported := false }
def all : ImportKind := { isExported := false, isAll := true }
def metaPub : ImportKind := { isExported := true, isMeta := true }
def metaPriv : ImportKind := { isExported := false, isMeta := true }
def metaAll : ImportKind := { isExported := false, isAll := true, isMeta := true }

/-- The six kinds, in the order of `Needs`' fields. -/
def kinds : Array ImportKind := #[pub, priv, all, metaPub, metaPriv, metaAll]

/-- The kind of an import. -/
def ofImport (imp : Lean.Import) : ImportKind :=
  { isExported := imp.isExported, isAll := imp.importAll, isMeta := imp.isMeta }

/-- The import of `module` with kind `k`. -/
def toImport (k : ImportKind) (module : Lean.Name) : Lean.Import :=
  { module, isExported := k.isExported, importAll := k.isAll, isMeta := k.isMeta }

/-- The import command for kind `k`, as in source: `public meta import`, `import all`, … -/
def toImportString (k : ImportKind) : String :=
  s!"{if k.isExported then "public " else ""}{if k.isMeta then "meta " else ""}import\
    {if k.isAll then " all" else ""}"

/--
`k₁` followed by `k₂`: something arriving in module `i` by `k₁`, passed on by an import of `i` with
kind `k₂`. Defined only if `k₁` lands in the scope `k₂` takes from: public for an ordinary import,
private for `import all`.
-/
def andThen? (k₁ k₂ : ImportKind) : Option ImportKind :=
  if k₁.isExported == !k₂.isAll then
    some { isExported := k₂.isExported, isAll := k₁.isAll && k₂.isAll,
           isMeta := k₁.isMeta || k₂.isMeta }
  else none

end ImportKind

/--
A set of modules per `ImportKind`: what a module imports, needs, or is provided with. The meaning of
`all` and `metaAll` is "the private scope", so `Provides` for a module includes its own index there
(`reflOf`).
-/
structure Needs where
  pub : Bitset := ∅
  priv : Bitset := ∅
  all : Bitset := ∅
  metaPub : Bitset := ∅
  metaPriv : Bitset := ∅
  metaAll : Bitset := ∅
deriving Inhabited

/-- What a module is provided with: transitively closed and linearized (`Needs.linearize`). -/
abbrev Provides := Needs

namespace Needs

@[inline] def get (n : Needs) (k : ImportKind) : Bitset :=
  match k.isMeta, k.isExported, k.isAll with
  | false, true, _ => n.pub | false, false, false => n.priv | false, false, true => n.all
  | true, true, _ => n.metaPub | true, false, false => n.metaPriv | true, false, true => n.metaAll

@[inline] def modify (n : Needs) (k : ImportKind) (f : Bitset → Bitset) : Needs :=
  match k.isMeta, k.isExported, k.isAll with
  | false, true, _ => { n with pub := f n.pub }
  | false, false, false => { n with priv := f n.priv }
  | false, false, true => { n with all := f n.all }
  | true, true, _ => { n with metaPub := f n.metaPub }
  | true, false, false => { n with metaPriv := f n.metaPriv }
  | true, false, true => { n with metaAll := f n.metaAll }

@[inline] def has (n : Needs) (k : ImportKind) (i : Nat) : Bool := (n.get k).has i

@[inline] def insert (n : Needs) (k : ImportKind) (i : Nat) : Needs := n.modify k (·.insert i)

def map₂ (a b : Needs) (f : Bitset → Bitset → Bitset) : Needs :=
  { pub := f a.pub b.pub, priv := f a.priv b.priv, all := f a.all b.all,
    metaPub := f a.metaPub b.metaPub, metaPriv := f a.metaPriv b.metaPriv,
    metaAll := f a.metaAll b.metaAll }

instance : Union Needs := ⟨(·.map₂ · (· ∪ ·))⟩
instance : SDiff Needs := ⟨(·.map₂ · (· \ ·))⟩
instance : EmptyCollection Needs := ⟨{ pub := ∅ }⟩

/-- Whether each kind's set of `a` is contained in `b`'s. -/
def le (a b : Needs) : Bool :=
  ImportKind.kinds.all fun k => a.get k ⊆ b.get k

/--
Accounts for `public ⊆ private`: what arrives publicly or from the private scope also arrives
privately, in each phase.
-/
def linearize (a : Needs) : Needs :=
  { a with priv := a.priv ∪ a.pub ∪ a.all, metaPriv := a.metaPriv ∪ a.metaPub ∪ a.metaAll }

/-- Removes what `linearize` adds (for turning needs into imports). -/
def antilinearize (a : Needs) : Needs :=
  { a with priv := a.priv \ (a.pub ∪ a.all), metaPriv := a.metaPriv \ (a.metaPub ∪ a.metaAll) }

/-- What module `i` provides to itself: its public and private scopes, not lifted to meta. -/
def reflOf (i : Nat) : Provides := { pub := {i}, priv := {i}, all := {i} }

/-- Every arrow of `n`, followed by an import of kind `k`. -/
def andThen (n : Needs) (k : ImportKind) : Needs := Id.run do
  let mut out : Needs := ∅
  for k₁ in ImportKind.kinds do
    if let some k' := k₁.andThen? k then
      out := out.modify k' (· ∪ n.get k₁)
  return out

/-- The pairs (kind, module) of `n`. -/
def toArray (n : Needs) : Array (ImportKind × Nat) :=
  ImportKind.kinds.flatMap fun k => (n.get k).toArray.map (k, ·)

/-- The imports `n` stands for (one per module and kind; `n` antilinearized). -/
def toImports (n : Needs) (moduleName : Nat → Lean.Name) : Array Lean.Import := Id.run do
  let mut out := #[]
  for k in ImportKind.kinds do
    for i in (n.get k).toArray do
      out := out.push (k.toImport (moduleName i))
  return out

end Needs

/-- For each module (in an order where imports come first), what it is provided with. -/
abbrev Hierarchy := Array Provides

namespace Hierarchy

/-- What an import of module `i` with kind `k` provides. -/
@[inline] def closure (h : Hierarchy) (i : Nat) (k : ImportKind) : Provides :=
  (h[i]!.andThen k).linearize

/-- What a module importing `imports` (module index and kind) is provided with, `self` included. -/
def provides (h : Hierarchy) (self : Nat) (imports : Array (Nat × ImportKind)) : Provides :=
  imports.foldl (init := Needs.reflOf self) fun acc (j, k) => acc ∪ h.closure j k

end Hierarchy

/--
What a declaration needs from another module: which scope, into which scope, and in which phase.
`isMeta? = none` accepts either phase (types and proofs are erased, so their references have no
phase); `some true` needs the code lifted to meta, `some false` needs it at runtime.
-/
structure ImportNeed where
  isExported : Bool
  isAll : Bool := false
  isMeta? : Option Bool := none
deriving BEq, Hashable, Repr, Inhabited

/-- Import needs: the phased ones (`phased`, by `ImportKind`) and the phaseless ones (`any`, by
`ImportKind` with `isMeta := false`). -/
structure ImportNeeds where
  phased : Needs := { pub := ∅ }
  any : Needs := { pub := ∅ }
deriving Inhabited

namespace ImportNeeds

def insert (n : ImportNeeds) (need : ImportNeed) (i : Nat) : ImportNeeds :=
  let k : ImportKind := { isExported := need.isExported, isAll := need.isAll,
                          isMeta := need.isMeta?.getD false }
  if need.isMeta?.isSome then { n with phased := n.phased.insert k i }
  else { n with any := n.any.insert k i }

instance : Union ImportNeeds := ⟨fun a b => { phased := a.phased ∪ b.phased, any := a.any ∪ b.any }⟩

/-- Whether `p` (linearized, transitively closed) provides every need. -/
def providedBy (n : ImportNeeds) (p : Provides) : Bool :=
  n.phased.le p &&
    #[ImportKind.pub, .priv, .all].all fun k =>
      n.any.get k ⊆ p.get k ∪ p.get { k with isMeta := true }

/--
Minimal imports (antilinearized, as `Needs`) that, with `base` (what the importer is provided with
anyway, e.g. the implicit `Init` imports), provide `n` in the hierarchy `h`. As ImportGraph's
`ImportNeeds.reduceBy`: start from all phased needs, and for each need not yet implied, keep it and
drop everything its closure implies; modules are taken from the highest index down (indices are
topologically sorted, so a module comes before the modules it provides). Phaseless needs not
covered then are met by runtime imports.
-/
def reduce (n : ImportNeeds) (h : Hierarchy) (base : Provides := ∅) : Needs := Id.run do
  let mut reduced := n.phased.linearize \ base
  for k in #[ImportKind.pub, .all, .priv, .metaPub, .metaAll, .metaPriv] do
    for i in (n.phased.antilinearize.get k).toArrayRev do
      if reduced.has k i then
        reduced := (reduced \ h.closure i k).insert k i
  let mut covered := reduced.linearize.toArray.foldl (init := base) fun acc (k, i) =>
    acc ∪ h.closure i k
  for k in #[ImportKind.pub, .all, .priv] do
    for i in (n.any.get k).toArrayRev do
      if !covered.has k i && !covered.has { k with isMeta := true } i then
        let c := h.closure i k
        covered := covered ∪ c
        reduced := (reduced \ c).insert k i
  return reduced.antilinearize

end ImportNeeds

end Agitate.ImportGraph
