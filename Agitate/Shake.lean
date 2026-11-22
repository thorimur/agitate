/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Sebastian Ullrich, Thomas Murrills

Copied from `src/lake/Lake/CLI/Shake.lean` at Lean `v4.33.1` (commit 819816b2e0a3) and updated to
`v4.36.0` (commit 611c117bfaf7; this added `--add-downstream`/`--add-public-downstream`), then
modified for `agitate`, with each change marked `agitate` in place:
* modules are read from their oleans (`Agitate.Index`) instead of importing an `Environment`;
* reserved names are decided lazily by the ported predicates (`Agitate.Reserved`);
* a `ByteArray` bitset, set-bit iteration in `visitModule`, and memoised reference resolution in
  `calcNeeds` for selected modules only (DESIGN.md, B1–B4);
* `--profile` phase timing and `--upstream-reserved`.
-/
module

public import Agitate.Args
public import Agitate.Bitset
public import Agitate.Header
public import Agitate.Refs
public import Agitate.Preresolved
import Init.Data.Range.Polymorphic.Iterators

/-! # Shake: A Lean import minimizer

This command will check the current project (or a specified target module) and all dependencies for
unused imports. This works by looking at generated `.olean` files to deduce required imports and
ensuring that every import is used to contribute some constant or other elaboration dependency
recorded by `recordExtraModUse` and friends.
-/

open Lean

namespace Agitate.Shake

/-- The kind of a module dependency, corresponding to the homonymous `ExtraModUse` fields. -/
structure NeedsKind where
  isExported : Bool
  isMeta : Bool
deriving Inhabited, BEq, Repr, Hashable

namespace NeedsKind

@[match_pattern]  abbrev priv : NeedsKind := { isExported := false, isMeta := false }
@[match_pattern]  abbrev pub  : NeedsKind := { isExported := true,  isMeta := false }
@[match_pattern]  abbrev metaPriv : NeedsKind := { isExported := false, isMeta := true }
@[match_pattern]  abbrev metaPub  : NeedsKind := { isExported := true,  isMeta := true }

def all : Array NeedsKind := #[pub, priv, metaPub, metaPriv]

def ofImport : Lean.Import → NeedsKind
  | { isExported := true, isMeta := true, .. } => .metaPub
  | { isExported := true, isMeta := false, .. } => .pub
  | { isExported := false, isMeta := true, .. } => .metaPriv
  | { isExported := false, isMeta := false, .. } => .priv

end NeedsKind

/-- Logically, a map `NeedsKind → Set ModuleIdx`, or `Set Import`. -/
structure Needs where
  pub : Bitset
  priv : Bitset
  metaPub : Bitset
  metaPriv : Bitset
deriving Inhabited, Repr

def Needs.empty : Needs := default

def Needs.get (needs : Needs) (k : NeedsKind) : Bitset :=
  match k with
  | .pub => needs.pub
  | .priv => needs.priv
  | .metaPub => needs.metaPub
  | .metaPriv => needs.metaPriv

def Needs.has (needs : Needs) (k : NeedsKind) (i : ModuleIdx) : Bool :=
  needs.get k |>.has i

def Needs.set (needs : Needs) (k : NeedsKind) (s : Bitset) : Needs :=
  match k with
  | .pub   => { needs with pub := s }
  | .priv  => { needs with priv := s }
  | .metaPub => { needs with metaPub := s }
  | .metaPriv => { needs with metaPriv := s }

def Needs.modify (needs : Needs) (k : NeedsKind) (f : Bitset → Bitset) : Needs :=
  needs.set k (f (needs.get k))

def Needs.union (needs : Needs) (k : NeedsKind) (s : Bitset) : Needs :=
  needs.modify k (· ∪ s)

def Needs.sub (needs : Needs) (k : NeedsKind) (s : Bitset) : Needs :=
  needs.modify k (· \ s)

/-- `needs.union k {i}` without building the singleton (`agitate` addition). -/
def Needs.insert (needs : Needs) (k : NeedsKind) (i : Nat) : Needs :=
  needs.modify k (·.insert i)

/-- `needs.sub k {i}` without building the singleton (`agitate` addition). -/
def Needs.erase (needs : Needs) (k : NeedsKind) (i : Nat) : Needs :=
  needs.modify k (·.erase i)

/-- The indices present for any kind, ascending (`agitate` addition). -/
def Needs.indices (needs : Needs) : Array Nat :=
  (needs.pub ∪ needs.priv ∪ needs.metaPub ∪ needs.metaPriv).toArray

instance : Union Needs where
  union a b := {
    pub := a.pub ∪ b.pub
    priv := a.priv ∪ b.priv
    metaPub := a.metaPub ∪ b.metaPub
    metaPriv := a.metaPriv ∪ b.metaPriv }

/-- Reasons for why a module dependency was added that are not captured by
constant references (which `getExplanations` already tracks). Keyed by the
`(j, k)` entry written into `deps`. -/
abbrev Reasons := Std.HashMap (ModuleIdx × NeedsKind) String

/-- The main state of the checker, containing information on all loaded modules. -/
structure State where
  /-- Everything known about the imported modules, read from their oleans. -/
  ix : Index
  /-- How reserved names are decided (see `Agitate.Reserved`). -/
  reserved : Reserved.Ctx
  /-- See `Args.reservedRefsToBase`. -/
  reservedRefsToBase : Bool
  /-- See `Args.indirectViaPublic`. -/
  indirectViaPublic : Bool
  /-- See `Args.implementedByNeeds`. -/
  implementedByNeeds : Bool
  /-- See `Args.resolveDuplicates`. -/
  resolveDuplicates : Bool
  /-- See `Args.preresolvedNeeds`. -/
  preresolvedNeeds : Bool
  /-- See `Args.toModule`. -/
  toModule : Bool := false
  /-- `modulate`: the module-system imports of each converted file, and whether it becomes meta. -/
  conversions : Std.HashMap Name (Array Import × Bool) := {}
  /-- `modulate`: converted files that become `public meta section` (`Args.metaGlobs`). -/
  metaModules : Std.HashSet ModuleIdx := {}
  /-- `modulate`: non-module files that could not be converted (their importers cannot be). -/
  notConverted : Std.HashSet ModuleIdx := {}
  /--
  `transDeps[i]` is the (non-reflexive) transitive closure of `mods[i].imports`. More specifically,
  * `j ∈ transDeps[i].pub` if `i -(public import)->+ j`
  * `j ∈ transDeps[i].priv` if `i -(import ...)-> _ -(public import)->* j`
  * `j ∈ transDeps[i].priv` if `i -(import all)->+ i'` and `j ∈ transDeps[i'].pub/priv`
  * `j ∈ transDeps[i].metaPub` if `i -(public (meta)? import)->* _ -(public meta import)-> _ -(public (meta)? import)->* j`
  * `j ∈ transDeps[i].metaPriv` if `i -(meta import ...)-> _ -(public (meta)? import)->* j`
  * `j ∈ transDeps[i].metaPriv` if `i -(import ...)-> i'` and `j ∈ transDeps[i'].metaPub`
  * `j ∈ transDeps[i].metaPriv` if `i -(import all)->+ i'` and `j ∈ transDeps[i'].metaPub/metaPriv`
  -/
  transDeps : Array Needs := #[]
  /--
  `transDepsOrig` is the initial value of `transDeps` before changes potentially resulting from
  changes to upstream headers.
  -/
  transDepsOrig : Array Needs := #[]
  /-- Modules that should always be preserved downstream. -/
  preserve : Needs := default
  /-- Edits to be applied to the module imports. -/
  edits : Edits := {}

  -- Memoizations
  /-- Indirect module uses of the kinds not ignored (`Args.ignoreIndirectKinds`). -/
  indirectModUses : Std.HashMap Name (Array ModuleIdx)
  modNames : Array Name := ix.modNames

/-- The reference-resolution view of the state. -/
def State.refs (s : State) : RefCtx :=
  { ix := s.ix, reserved := s.reserved, reservedRefsToBase := s.reservedRefsToBase,
    indirectModUses := s.indirectModUses, implementedByNeeds := s.implementedByNeeds,
    resolveDuplicates := s.resolveDuplicates, preresolvedNeeds := s.preresolvedNeeds,
    metaModules := s.metaModules }

/--
Given module `j`'s transitive dependencies, computes the union of `transImps` and the transitive
dependencies resulting from importing the module via `imp` according to the rules of
`State.transDeps`.
-/
def addTransitiveImps (transImps : Needs) (imp : Import) (j : Nat) (impTransImps : Needs) : Needs := Id.run do
  let mut transImps := transImps

  -- `j ∈ transDeps[i].pub` if `i -(public import)->+ j`
  if imp.isExported && !imp.isMeta then
    transImps := transImps.insert .pub j |>.union .pub (impTransImps.get .pub)

  if !imp.isExported && !imp.isMeta then
    -- `j ∈ transDeps[i].priv` if `i -(import ...)-> _ -(public import)->* j`
    transImps := transImps.insert .priv j |>.union .priv (impTransImps.get .pub)
    if imp.importAll then
      -- `j ∈ transDeps[i].priv` if `i -(import all)->+ i'` and `j ∈ transDeps[i'].pub/priv`
      transImps := transImps.union .priv (impTransImps.get .pub ∪ impTransImps.get .priv)

  -- `j ∈ transDeps[i].metaPub` if `i -(public (meta)? import)->* _ -(public meta import)-> _ -(public (meta)? import)->* j`
  if imp.isExported then
    transImps := transImps.union .metaPub (impTransImps.get .metaPub)
    if imp.isMeta then
      transImps := transImps.insert .metaPub j |>.union .metaPub (impTransImps.get .pub ∪ impTransImps.get .metaPub)

  if !imp.isExported then
    if imp.isMeta then
      -- `j ∈ transDeps[i].metaPriv` if `i -(meta import ...)-> _ -(public (meta)? import)->* j`
      transImps := transImps.insert .metaPriv j |>.union .metaPriv (impTransImps.get .pub ∪ impTransImps.get .metaPub)
    if imp.importAll then
      -- `j ∈ transDeps[i].metaPriv` if `i -(import all)->+ i'` and `j ∈ transDeps[i'].metaPub/metaPriv`
      transImps := transImps.union .metaPriv (impTransImps.get .metaPub ∪ impTransImps.get .metaPriv)
    else
      -- `j ∈ transDeps[i].metaPriv` if `i -(import ...)-> i'` and `j ∈ transDeps[i'].metaPub`
      transImps := transImps.union .metaPriv (impTransImps.get .metaPub)

  transImps

/-- Whether module `i` reaches `j` with kind `k` in `transDeps`, for the purpose of indirect module
uses; `agitate` also accepts the public version of `k` (`Args.indirectViaPublic`). -/
def reachesForIndirect (s : State) (i : ModuleIdx) (k : NeedsKind) (j : ModuleIdx) : Bool :=
  s.transDeps[i]!.has k j || (s.indirectViaPublic && s.transDeps[i]!.has { k with isExported := true } j)

/-- `modulate`: whether module `i` is a non-module file being converted (`agitate` addition). -/
def State.converting (s : State) (i : ModuleIdx) : Bool :=
  s.toModule && !s.ix.modules[i]!.priv.isModule

/--
`modulate`: the visibility of a declaration `ci` of a converted module `i`, as `(exported, exposed)`.
* `@[expose] public section`: non-private declarations are exported, and definitions are exposed,
  as are the proofs abstracted from them (`d._proof_N`): the module system checks those proofs as
  part of the exposed body.
* `public meta section`: every declaration counts as exported and exposed, private ones included.
  Importers evaluating a public meta definition need the code of everything it calls, so Lean
  requires `public meta import` even for what only private helpers reference. This over-approximates
  for private helpers no public code reaches.
-/
def State.convertedVisibility (s : State) (i : ModuleIdx) (ci : ConstantInfo) : Bool × Bool :=
  if s.metaModules.contains i then (true, true) else
  let exported := !isPrivateName ci.name
  let auxProofOfExposed := match ci.name with
    | .str p str => str.startsWith "_proof_" && !isPrivateName p &&
        (s.ix.find? p matches some (.defnInfo _))
    | _ => false
  (exported, exported && (ci matches .defnInfo _ || auxProofOfExposed))

/--
The visibility of a declaration `ci` of module `i`, as `(exported, exposed)`: from the olean, or
for a converted module as it will be after conversion (`convertedVisibility`).
-/
def State.visibility (s : State) (i : ModuleIdx) (ci : ConstantInfo) : Bool × Bool :=
  if s.converting i then s.convertedVisibility i ci else
  -- Added guard for cases like `structure` that are still exported even if private
  let pubCI? := guard (!isPrivateName ci.name) *> s.ix.findPublic? ci.name
  (pubCI?.isSome, pubCI?.any (·.hasValue (allowOpaque := true)))

/--
Calculates the needs for a given module `mod` from constants and recorded extra uses.

`agitate` change: references are resolved once per distinct name per module (`resolveRef`) instead
of at every occurrence; the per-occurrence work is only the `NeedsKind` bookkeeping (DESIGN.md, B2).
-/
def calcNeeds (s : State) (i : ModuleIdx) : Needs := Id.run do
  let ix := s.ix
  let mut acc : Needs × Std.HashMap Name (Option Resolved) := (default, {})
  -- `agitate`: `i`'s load order, only computed if `i` uses a name declared in several modules
  let order : Thunk (Array Index.LoadedModule) := .mk fun _ => ix.loadOrder i
  let converting := s.converting i
  for ci in ix.constants i do
    -- `agitate` (`modulate`): visibility as under `@[expose] public section`, i.e. non-private
    -- declarations are public and definitions expose their bodies (theorem proofs never do)
    let (exported, exposed) := s.visibility i ci
    -- `modulate --meta`: everything in a `public meta section` is meta
    let k := { isExported := exported,
               isMeta := isDeclMeta' ix ci.name || (converting && s.metaModules.contains i) }
    acc := visitExpr order k ci.type acc
    if let some e := ci.value? (allowOpaque := true) then
      -- type and value has identical visibility under `meta`
      let k := if k.isMeta then k else
        if exposed then .pub else .priv
      acc := visitExpr order k e acc
    -- `agitate`: the `@[implemented_by]` target, with the declaration's visibility (a compiled
    -- caller in another module needs it, so an exported declaration needs it publicly)
    if let some (_, j, gMeta) := implementedByTarget? s.refs ci.name then
      if j != i then
        acc := (acc.1.insert { k with isMeta := k.isMeta && !gMeta } j, acc.2)

  let mut needs := acc.1
  -- `agitate`: names preresolved by quotations, as the extra module uses Lean does not record
  -- (`Agitate.Preresolved`); only modules whose terms mention `Syntax.Preresolved.decl` are scanned
  if Preresolved.mayHave acc.2.contains then
    for ci in ix.constants i do
      for (_, j) in Preresolved.uses s.refs order i ci do
        needs := needs.insert { isExported := (s.visibility i ci).1, isMeta := false } j
  for use in ix.getExtraModUses i do
    let j : Nat := ix.getModuleIdx? use.module |>.get!
    -- `agitate` (`modulate`): non-module elaboration records no exporting context; count the
    -- use as public (conservative: everything is public under `@[expose] public section`)
    -- a compile-time use of a file converted as meta needs no `meta import`: its declarations
    -- will already be meta
    let use := if converting then
        { use with isExported := true, isMeta := use.isMeta && !s.metaModules.contains j }
      else use
    needs := needs.insert { use with } j

  return needs
where
  /-- Accumulate the results from expression `e` into `deps`. -/
  visitExpr (order : Thunk (Array Index.LoadedModule)) (k : NeedsKind) (e : Expr)
      (acc : Needs × Std.HashMap Name (Option Resolved)) : Needs × Std.HashMap Name (Option Resolved) :=
    Lean.Expr.foldConsts e acc fun c (deps, cache) => Id.run do
      let (r?, cache) := match cache[c]? with
        | some r? => (r?, cache)
        | none =>
          let r? := (resolveRef s.refs c).bind (·.forModule s.ix order i)
          (r?, cache.insert c r?)
      let mut deps := deps
      if let some r := r? then
        let k := { k with isMeta := k.isMeta && !r.isMeta }
        if r.mod != i then
          deps := deps.insert k r.mod
          for (indMod : Nat) in r.indirect do
            if reachesForIndirect s i k indMod then
              deps := deps.insert k indMod
      return (deps, cache)

abbrev Explanations := Std.HashMap (ModuleIdx × NeedsKind) (Option (Name × Name))

/--
Calculates the same as `calcNeeds` but tracing each module to a use-def declaration pair or
`none` if merely a recorded extra use.
-/
def getExplanations (s : State) (i : ModuleIdx) : Explanations := Id.run do
  let ix := s.ix
  let mut deps := default
  let order : Thunk (Array Index.LoadedModule) := .mk fun _ => ix.loadOrder i
  let converting := s.converting i
  for ci in ix.constants i do
    let (exported, exposed) := s.visibility i ci
    let k := { isExported := exported,
               isMeta := isDeclMeta' ix ci.name || (converting && s.metaModules.contains i) }
    deps := visitExpr order k ci.name ci.type deps
    if let some e := ci.value? (allowOpaque := true) then
      let k := if k.isMeta then k else
        if exposed then .pub else .priv
      deps := visitExpr order k ci.name e deps
    if let some (g, j, gMeta) := implementedByTarget? s.refs ci.name then
      if j != i then
        deps := addExplanation j { k with isMeta := k.isMeta && !gMeta } ci.name g deps
    for (n, j) in Preresolved.uses s.refs order i ci do
      deps := addExplanation j { isExported := exported, isMeta := false } ci.name n deps

  for use in ix.getExtraModUses i do
    let j := ix.getModuleIdx? use.module |>.get!
    let use := if converting then
        { use with isExported := true, isMeta := use.isMeta && !s.metaModules.contains j }
      else use
    if !deps.contains (j, { use with }) then
      deps := deps.insert (j, { use with }) none

  return deps
where
  /-- Accumulate the results from expression `e` into `deps`. -/
  visitExpr (order : Thunk (Array Index.LoadedModule)) (k : NeedsKind) name e deps :=
    let ix := s.ix
    Lean.Expr.foldConsts e deps fun c deps => Id.run do
      let mut deps := deps
      if let some c := getDepConstName? s.refs c then
        if let some j := ix.getModuleIdxFor? c then
          let k := { k with isMeta := k.isMeta && !isDeclMeta' ix c }
          -- `agitate`: for duplicated names, the declarer `calcNeeds` charges (none: `i` itself)
          let j? := if s.resolveDuplicates && ix.dupDecls.contains c then
              (resolveRef s.refs c).bind (·.forModule ix order i) |>.map (·.mod)
            else some j
          if let some j := j? then
            deps := addExplanation j k name c deps
        for indMod in s.indirectModUses[c]?.getD #[] do
          if reachesForIndirect s i k indMod then
            deps := addExplanation indMod k name (`_indirect ++ c) deps
      return deps
  addExplanation (j : ModuleIdx) (k : NeedsKind) (use def_ : Name) (deps : Explanations) : Explanations :=
    if
      if let some (some (name', _)) := deps[(j, k)]? then
        decide (use.toString.chars.length < name'.toString.chars.length)
      else true
    then
      deps.insert (j, k) (use, def_)
    else deps

def initState (ix : Index) (args : Args) : State := Id.run do
  let ignore kind := args.ignoreIndirectKinds.contains "*" || args.ignoreIndirectKinds.contains kind
  let mut s := { ix, reserved := { ix, upstream := args.upstreamReserved },
                 reservedRefsToBase := args.reservedRefsToBase,
                 indirectViaPublic := args.indirectViaPublic,
                 implementedByNeeds := args.implementedByNeeds,
                 resolveDuplicates := args.resolveDuplicates,
                 preresolvedNeeds := args.preresolvedNeeds,
                 toModule := args.toModule,
                 metaModules := Id.run do
                   let mut ms := {}
                   if args.toModule then
                     for j in 0...ix.size do
                       if !ix.modules[j]!.priv.isModule && args.metaGlobs.any (·.matches (ix.modName j)) then
                         ms := ms.insert j
                   return ms,
                 indirectModUses := ix.indirectModUsesExcept ignore }
  for i in 0...ix.size do
    let mut imps := #[]
    let mut transImps := Needs.empty
    for imp in ix.imports i do
      let j := ix.getModuleIdx? imp.module |>.get!
      imps := imps.push j
      transImps := addTransitiveImps transImps imp j s.transDeps[j]!
    s := { s with transDeps := s.transDeps.push transImps }
  s := { s with transDepsOrig := s.transDeps }
  return s

/--
Returns for each module whether it is a reflexive-transitive import of `i`, disregarding visibility.
-/
def getImportClosure (s : State) (i : Nat) : Array Bool := Id.run do
  let mut closure := Array.replicate s.ix.size false |>.set! i true
  for j in (0...=i).toArray.reverse do
    if closure[j]! then
      for imp in s.ix.imports j do
        closure := closure.set! (s.ix.getModuleIdx? imp.module |>.get!).toNat true
  return closure

/-- Analyze and report issues from module `i`. Arguments:

* `pkgs`: the first components of the input modules
* `source?`: the module's source file (`Resolver.source?`), for reporting and `--gh-style`
* `i`: the module index
* `needs`: the module's calculated needs
* `addDownstream`: if true, ensure that the module has the import `args.addDownstream?`
* `addOnly`: if true, only add missing imports, do not remove unused ones
-/
def visitModule (pkgs : Array Name) (source? : Name → IO (Option System.FilePath))
    (i : Nat) (needs : Needs) (header : ParsedHeader) (args : Args)
    (addDownstream := false) (addOnly := false) : StateT State IO Unit := do
  let ⟨_, _, headerStx, _⟩ := header
  let modName := (← get).modNames[i]!
  if (← get).ix.isExtraRevModUse i then
    modify fun s => { s with preserve := s.preserve.insert (if args.addPublic then .pub else .priv) i }
    if args.trace then
      IO.eprintln s!"Preserving `{modName}` because of recorded extra rev use"

  -- only process modules in the selected packages
  -- TODO: should be after `keep-downstream` but core headers are not found yet?
  if !pkgs.any (·.isPrefixOf modName) then
    return

  let (module?, prelude?, imports) := decodeHeader headerStx
  -- `agitate` (`modulate`): a non-module file has no `module` token; its markers are in header
  -- comments, and its imports re-export (the olean records them as `public import`s).
  let converting := (← get).converting i
  let hasMarker (m : String) :=
    module?.any (·.raw.getTrailing?.any (·.toString.contains m)) ||
    (converting && headerHasMarker header m)
  if hasMarker "shake: keep-downstream" then
    modify fun s => { s with preserve := s.preserve.insert (if args.addPublic then .pub else .priv) i }

  let s ← get

  -- `modulate`: a module cannot import a non-module file, so every non-module file this one
  -- imports must be converted in this run too
  if converting then
    for imp in s.ix.imports i do
      let some j := s.ix.getModuleIdx? imp.module | continue
      if !s.ix.modules[j]!.priv.isModule &&
          (!pkgs.any (·.isPrefixOf s.modNames[j]!) || s.notConverted.contains j) then
        if let some path ← source? modName then println! "{path}:" else println! "{modName}:"
        println! "  cannot convert to `module`: imports non-module `{s.modNames[j]!}`, which is not \
          converted in this run"
        modify fun s => { s with notConverted := s.notConverted.insert i }
        return

  let addOnly := addOnly ||
    (!args.onlyMods.isEmpty && !args.onlyMods.contains modName) ||
    hasMarker "shake: keep-all"
  let mut deps := needs
  let mut reasons : Reasons := {}

  -- Add additional preserved imports
  for impStx in imports do
    let imp := decodeImport impStx
    let imp := if converting then { imp with isExported := true } else imp
    -- `agitate`: oleans are trusted and not checked for freshness; a source import that is not in
    -- the olean's import closure (source edited since the build) is skipped. Upstream panics here
    -- (`get!`) and continues with a wrong module index; it never gets here without `--force`.
    let some j := s.ix.getModuleIdx? imp.module
      | if args.trace then IO.eprintln s!"`{imp}` is not in the oleans' import closure; skipping"
        continue
    let k := NeedsKind.ofImport imp
    let reason? :=
      if impStx.raw.getTrailing?.any (·.toString.contains "shake: keep") then
        some "`shake: keep`"
      else if args.keepPublic && imp.isExported && !(`Init).isPrefixOf modName then
        -- TODO: allow per-library configuration instead of hardcoding `Init`
        some "`--keep-public`"
      else if addOnly then
        some "`--add-only` / `--only` / `shake: keep-all`"
      else none
    if let some msg := reason? then
      deps := deps.insert k j
      reasons := reasons.insert (j, k) msg
      if args.trace then
        IO.eprintln s!"Adding `{imp}` as additional dependency"
  -- `agitate`: only `j ∈ preserve.pub ∪ preserve.priv` can satisfy the condition below, so iterate
  -- over those instead of all modules (DESIGN.md, B1).
  for j in (s.preserve.pub ∪ s.preserve.priv).toArray do
    for k in NeedsKind.all do
      -- Remove `meta` while preserving, no use-case for preserving `meta` so far.
      -- Downgrade to private unless `--add-public` is used.
      if s.transDepsOrig[i]!.has k j &&
          (s.preserve.has { k with isMeta := false, isExported := false } j ||
           s.preserve.has { k with isMeta := false, isExported := true } j) then
        let k' := { k with isMeta := false, isExported := k.isExported && args.addPublic }
        deps := deps.insert k' j
        reasons := reasons.insert (j, k') s!"`--keep-downstream`/extra rev use in `{s.modNames[j]!}`"
  if let some imp := guard addDownstream *> args.addDownstream? then
    let j : Nat := s.ix.getModuleIdx? imp.module |>.get!
    let k := NeedsKind.ofImport imp
    deps := deps.insert k j
    reasons := reasons.insert (j, k) <|
      if k.isExported then "`--add-public-downstream`" else "`--add-downstream`"

  -- Do transitive reduction of `needs` in `deps`.
  if !addOnly then
    -- `agitate`: iterate over the indices in `deps` (re-checked below) instead of all modules; the
    -- loop only removes from `deps`, so a snapshot visits every index the full scan would act on.
    for j in deps.indices do
      let transDeps := s.transDeps[j]!
      for k in NeedsKind.all do
        if deps.has k j then
          let transDeps := addTransitiveImps .empty { k with module := .anonymous } j transDeps
          for k' in NeedsKind.all do
            deps := deps.sub k' (transDeps.erase k' j |>.get k')

  if prelude?.isNone then
    let j : Nat := s.ix.getModuleIdx? `Init |>.get!
    deps := deps.insert .pub j
    deps := deps.insert .metaPub j

  -- Accumulate `transDeps` which is the non-reflexive transitive closure of the still-live imports
  let mut transDeps := Needs.empty
  let mut alwaysAdd : Array Import := #[]  -- to be added even if implied by other imports
  for imp in s.ix.imports i do
    let j : Nat := s.ix.getModuleIdx? imp.module |>.get!
    let k := NeedsKind.ofImport imp
    if deps.has k j || imp.importAll then
      let wasInDeps := deps.has k j
      transDeps := addTransitiveImps transDeps imp j s.transDeps[j]!
      deps := deps.insert k j
      if !wasInDeps && imp.importAll then
        reasons := reasons.insert (j, k) "`import all` always being preserved"
    -- skip folder-nested `public (meta)? import`s but remove `meta`
    else if modName.isPrefixOf imp.module then
      let imp := { imp with isMeta := false }
      let k := { k with isMeta := false }
      if args.trace then
        IO.eprintln s!"`{imp}` is preserved as folder-nested import"
      transDeps := addTransitiveImps transDeps imp j s.transDeps[j]!
      deps := deps.insert k j
      reasons := reasons.insert (j, k) "folder-nested import"
      if !(s.ix.imports i).contains imp then
        alwaysAdd := alwaysAdd.push imp

  -- If `transDeps` does not cover `deps`, then we have to add back some imports until it does.
  -- To minimize new imports we pick only new imports which are not transitively implied by
  -- another new import, so we visit module indices in descending order.
  let mut keptPrefix := false
  let mut newTransDeps := transDeps
  let mut toAdd : Array Import := #[]
  -- `agitate`: iterate over the indices in `deps` instead of all modules. The loop only inserts into
  -- `deps` at indices already visited: an `--add-public` upgrade at the same `j` with an earlier kind
  -- in `NeedsKind.all`, and a `--keep-prefix` module `j' > j` (it imports `j`, so comes later in the
  -- post-order). So a snapshot visits every index the full scan would act on.
  for j in deps.indices.reverse do
    for k in NeedsKind.all do
      if deps.has k j && !newTransDeps.has k j && !newTransDeps.has { k with isExported := true } j then
        -- `add-public/keep-prefix` may change the import and even module we're considering
        let mut k := k
        let mut imp : Import := { k with module := s.modNames[j]! }
        let mut j := j
        if args.trace then
          IO.eprintln s!"`{imp}` is needed{if needs.has k j then " (calculated)" else ""}"
        if args.addPublic && !k.isExported &&
            -- also add as public if previously `public meta`, which could be from automatic porting
            (s.transDepsOrig[i]!.has { k with isExported := true } j || s.transDepsOrig[i]!.has { k with isExported := true, isMeta := true } j) then
          k := { k with isExported := true }
          imp := { imp with isExported := true }
          if args.trace then
            IO.eprintln s!"* upgrading to `{imp}` because of `--add-public`"
          reasons := reasons.insert (j, k) "`--add-public`"
        if args.keepPrefix then
          let rec tryPrefix : Name → Option ModuleIdx
            | .str p _ => tryPrefix p <|> (do
              let j' ← s.ix.getModuleIdx? p
              -- `j'` must be reachable from `i` (allow downgrading from `meta`)
              guard <| s.transDepsOrig[i]!.has k j' || s.transDepsOrig[i]!.has { k with isMeta := true } j'
              let j'transDeps := addTransitiveImps .empty p j' s.transDeps[j']!
              -- `j` must be publicly reachable from `j'` (now downgrading must be done in the other direction)
              guard <| j'transDeps.has { k with isExported := true } j || j'transDeps.has { k with isExported := true, isMeta := false } j
              return j')
            | _ => none
          if let some j' := tryPrefix imp.module then
            let origModule := imp.module
            imp := { imp with module := s.modNames[j']! }
            j := j'
            keptPrefix := true
            if args.trace then
              IO.eprintln s!"* upgrading to `{imp}` because of `--keep-prefix`"
            reasons := reasons.insert (j, k) s!"`--keep-prefix` upgrade from `{origModule}`"
        if !(s.ix.imports i).contains imp then
          toAdd := toAdd.push imp
        deps := deps.insert k j
        newTransDeps := addTransitiveImps newTransDeps imp j s.transDeps[j]!

  if keptPrefix then
    -- if an import was replaced by `--keep-prefix`, we did not necessarily visit the modules in
    -- dependency order anymore and so we have to redo the transitive closure checking
    newTransDeps := transDeps
    -- `agitate`: as above; this loop only removes from `deps`
    for j in deps.indices.reverse do
      for k in NeedsKind.all do
        if deps.has k j then
          let mut imp : Import := { k with module := s.modNames[j]! }
          if toAdd.contains imp && (newTransDeps.has k j || newTransDeps.has { k with isExported := true } j) then
            if args.trace then
              IO.eprintln s!"Removing `{imp}` from imports to be added because it is now implied"
            toAdd := toAdd.erase imp
            deps := deps.erase k j
          else
            newTransDeps := addTransitiveImps newTransDeps imp j s.transDeps[j]!

  -- now that `toAdd` filtering is done, add `alwaysAdd`
  toAdd := alwaysAdd ++ toAdd

  -- Any import which is still not in `deps` was unused
  let mut toRemove : Array Import := #[]
  for imp in s.ix.imports i do
    let j := s.ix.getModuleIdx? imp.module |>.get!
    let k := NeedsKind.ofImport imp
    if args.keepImplied && newTransDeps.has k j then
      if args.trace && !deps.has k j then
        IO.eprintln s!"`{imp}` is implied by other imports"
    else if !deps.has k j then
      if args.trace then
        IO.eprintln s!"`{imp}` is now unused"
      toRemove := toRemove.push imp
    -- A private import should also be removed if the public version has been added
    else if !k.isExported && !imp.importAll && newTransDeps.has { k with isExported := true } j then
      if args.trace then
        IO.eprintln s!"`{imp}` is already covered by `{ { imp with isExported := true } }`"
      toRemove := toRemove.push imp

  if converting then
    -- `agitate` (`modulate`): report and record the module-system imports instead of edits
    let final := (s.ix.imports i).filter (fun imp =>
      !toRemove.contains imp && !(prelude?.isNone && imp.module == `Init)) ++ toAdd
    let isMetaFile := s.metaModules.contains i
    let sec := if isMetaFile then "public meta section" else "@[expose] public section"
    modify fun s => { s with conversions := s.conversions.insert modName (final, isMetaFile) }
    let path? ← source? modName
    if let some path := path? then println! "{path}:" else println! "{modName}:"
    println! "  convert to `module` with `{sec}`, importing {final}"
    if args.githubStyle then
      if let some path := path? then
        println! "{path}:1:1: warning: convert to `module` with `{sec}`, importing {final} \
          (use `modulate --fix`)"
  else
    -- mark and report the removals
    modify fun s => { s with
      edits := toRemove.foldl (init := s.edits) fun edits imp =>
        edits.remove modName imp }

    if !toAdd.isEmpty || !toRemove.isEmpty || args.explain then
      if let some path ← source? s.modNames[i]! then
        println! "{path}:"
      else
        println! "{s.modNames[i]!}:"

    if !toRemove.isEmpty then
      println! "  remove {toRemove}"

    if args.githubStyle then
      try
        let ⟨path, inputCtx, stx, endHeader⟩ ← parseHeader source? s.modNames[i]!
        let (_, _, imports) := decodeHeader stx
        for stx in imports do
          if toRemove.any fun imp => imp == decodeImport stx then
            let pos := inputCtx.fileMap.toPosition stx.raw.getPos?.get!
            println! "{path}:{pos.line}:{pos.column+1}: warning: unused import \
              (use `lake shake --fix` to fix this, or `lake shake --update` to ignore)"
        if !toAdd.isEmpty then
          -- we put the insert message on the beginning of the last import line
          let pos := inputCtx.fileMap.toPosition endHeader.offset
          println! "{path}:{pos.line-1}:1: warning: \
            add {toAdd} instead"
      catch _ => pure ()

    -- mark and report the additions
    modify fun s => { s with
      edits := toAdd.foldl (init := s.edits) fun edits imp =>
        edits.add s.modNames[i]! imp }

    if !toAdd.isEmpty then
      println! "  add {toAdd}"

  -- recalculate transitive dependencies of downstream modules
  let mut newTransDepsI := Needs.empty
  for imp in s.ix.imports i do
    if !toRemove.contains imp then
      let j := s.ix.getModuleIdx? imp.module |>.get!
      newTransDepsI := addTransitiveImps newTransDepsI imp j s.transDeps[j]!
  for imp in toAdd do
    let j := s.ix.getModuleIdx? imp.module |>.get!
    newTransDepsI := addTransitiveImps newTransDepsI imp j s.transDeps[j]!

  modify fun s => { s with transDeps := s.transDeps.set! i newTransDepsI }

  if args.explain then
    let explanation := getExplanations s i
    let sanitize n := if n.hasMacroScopes then (sanitizeName n).run' { options := {} } else n
    let run (imp : Import) := do
      let j := s.ix.getModuleIdx? imp.module |>.get!
      let k := NeedsKind.ofImport imp
      println! "  note: `{imp}` required"
      match explanation[(j, k)]? <|> guard args.addPublic *> explanation[(j, { k with isExported := false})]? with
      | some (some (n, c)) =>
        println! "    because `{sanitize n}` refers to `{sanitize c}`"
      | some none =>
        println! "    because of additional compile-time dependencies"
      | none =>
        if let some msg := reasons[(j, k)]? then
          println! "    because of {msg}"
        else
          println! "    (no traced reason)"
    for j in s.ix.imports i do
      if !toRemove.contains j then
        run j
    for i in toAdd do run i

/--
Run the shake analysis with the given arguments.

Assumes Lean's search path has already been properly configured.
-/
public def run (args : Args) (r : Resolver) : IO UInt32 := do
  -- `--profile`: time each phase; in this mode phases are forced one after another so that the
  -- parallel `needs` computation is not hidden behind the sequential visit loop.
  let timed {α} := args.timed (α := α)

  -- the list of root modules
  let mods := args.mods
  -- Only submodules of `pkgs` will be edited or have info reported on them
  let pkgs := mods.map (·.getRoot)

  -- Load all the modules (`agitate`: straight from their oleans, see `Agitate.Index`)
  let modules ← timed "readModules (.olean, .server, .private)" <| readModules r.olean mods (allowNonModule := args.toModule)
  let ix ← timed "Index.build (constant maps, extension tables)" <| Index.build modules Reserved.extNames
  let s ← timed "initState (transDeps)" <| IO.lazyPure fun _ => initState ix args
  if args.profile then
    IO.eprintln s!"[profile] {ix.size} modules, {ix.privConsts.size} constants"
  if let some imp := args.addDownstream? then
    if ix.getModuleIdx? imp.module |>.isNone then
      throw <| .userError s!"cannot add `{imp.module}` downstream, \
        it is not imported by any of the checked modules"
  if args.listIndirectKinds then
    printIndirectKinds ix
    return 0

  StateT.run' (s := s) do

  let s ← get
  -- Run the calculation of the `needs` array in parallel
  -- `agitate` change: only for modules in the selected packages; `visitModule` returns before
  -- using the needs of any other module (DESIGN.md, B2).
  let needs := s.modNames.mapIdx fun i _ =>
    if !pkgs.any (·.isPrefixOf s.modNames[i]!) then
      Task.pure default
    else
      Task.spawn fun _ => calcNeeds s i
  if args.profile then
    timed "calcNeeds (selected modules, parallel)" <| needs.forM fun t => discard <| IO.wait t

  -- Parse headers in parallel
  let headers ← parseHeaders pkgs r.source? s.modNames
  if args.profile then
    timed "parseHeader (selected modules, parallel)" <| headers.forM fun t => discard <| IO.wait t

  if args.fix then
    println! "The following changes will be made automatically:"

  -- Check all selected modules
  let t0 ← IO.monoNanosNow
  let mut order := Array.range s.ix.size
  -- The modules we must not add the `--add-(public-)downstream` import to, as doing so would
  -- create an import cycle
  let mut noAddDownstream := Array.replicate s.ix.size true
  if let some imp := args.addDownstream? then
    noAddDownstream := getImportClosure s (s.ix.getModuleIdx? imp.module |>.get!).toNat
    -- Visit them first so that their import closures are final when we add the import to the
    -- remaining modules
    order := order.filter (noAddDownstream[·]!) ++ order.filter (!noAddDownstream[·]!)
  for i in order do
    match headers[i]!.get with
    | .ok h =>
      visitModule pkgs r.source? i needs[i]!.get h args (addDownstream := !noAddDownstream[i]!)
    | .error e =>
      println! e.toString
  if args.profile then
    IO.eprintln s!"[profile] visitModule loop (sequential): {((← IO.monoNanosNow) - t0) / 1000000} ms"

  if !args.fix then
    -- return error if any issues were found
    return if (← get).edits.isEmpty && (← get).conversions.isEmpty then 0 else 1

  -- Apply the edits to existing files
  let mut count ← applyEdits (← get).edits s.modNames headers
  -- `modulate`: rewrite converted files as modules
  for mod in s.modNames, header? in headers do
    let some (imports, isMeta) := (← get).conversions[mod]? | continue
    let .ok h := header?.get | continue
    let ⟨path, _, _, _⟩ := h
    IO.FS.writeFile path (← convertToModuleText h imports isMeta)
    count := count + 1

  -- Since we throw an error upon encountering issues, we can be sure that everything worked
  -- if we reach this point of the script.
  if count > 0 then
    println! "Successfully applied {count} suggestions."
  else
    println! "No edits required."
  return 0
