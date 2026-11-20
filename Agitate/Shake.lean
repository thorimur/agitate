/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Sebastian Ullrich, Thomas Murrills

Copied from `src/lake/Lake/CLI/Shake.lean` at Lean `v4.33.1` (commit 819816b2e0a3), then modified
for `agitate`, with each change marked `agitate` in place:
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
    indirectModUses := s.indirectModUses, implementedByNeeds := s.implementedByNeeds }

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

/--
Calculates the needs for a given module `mod` from constants and recorded extra uses.

`agitate` change: references are resolved once per distinct name per module (`resolveRef`) instead
of at every occurrence; the per-occurrence work is only the `NeedsKind` bookkeeping (DESIGN.md, B2).
-/
def calcNeeds (s : State) (i : ModuleIdx) : Needs := Id.run do
  let ix := s.ix
  let mut acc : Needs × Std.HashMap Name (Option Resolved) := (default, {})
  for ci in ix.constants i do
    -- Added guard for cases like `structure` that are still exported even if private
    let pubCI? := guard (!isPrivateName ci.name) *> ix.findPublic? ci.name
    let k := { isExported := pubCI?.isSome, isMeta := isDeclMeta' ix ci.name }
    acc := visitExpr k ci.type acc
    if let some e := ci.value? (allowOpaque := true) then
      -- type and value has identical visibility under `meta`
      let k := if k.isMeta then k else
        if pubCI?.any (·.hasValue (allowOpaque := true)) then .pub else .priv
      acc := visitExpr k e acc
    -- `agitate`: the `@[implemented_by]` target, with the declaration's visibility (a compiled
    -- caller in another module needs it, so an exported declaration needs it publicly)
    if let some (_, j, gMeta) := implementedByTarget? s.refs ci.name then
      if j != i then
        acc := (acc.1.insert { k with isMeta := k.isMeta && !gMeta } j, acc.2)

  let mut needs := acc.1
  for use in ix.getExtraModUses i do
    let j : Nat := ix.getModuleIdx? use.module |>.get!
    needs := needs.insert { use with } j

  return needs
where
  /-- Accumulate the results from expression `e` into `deps`. -/
  visitExpr (k : NeedsKind) (e : Expr) (acc : Needs × Std.HashMap Name (Option Resolved)) :
      Needs × Std.HashMap Name (Option Resolved) :=
    Lean.Expr.foldConsts e acc fun c (deps, cache) => Id.run do
      let (r?, cache) := match cache[c]? with
        | some r? => (r?, cache)
        | none => let r? := resolveRef s.refs c; (r?, cache.insert c r?)
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
  for ci in ix.constants i do
    -- Added guard for cases like `structure` that are still exported even if private
    let pubCI? := guard (!isPrivateName ci.name) *> ix.findPublic? ci.name
    let k := { isExported := pubCI?.isSome, isMeta := isDeclMeta' ix ci.name }
    deps := visitExpr k ci.name ci.type deps
    if let some e := ci.value? (allowOpaque := true) then
      let k := if k.isMeta then k else
        if pubCI?.any (·.hasValue (allowOpaque := true)) then .pub else .priv
      deps := visitExpr k ci.name e deps
    if let some (g, j, gMeta) := implementedByTarget? s.refs ci.name then
      if j != i then
        deps := addExplanation j { k with isMeta := k.isMeta && !gMeta } ci.name g deps

  for use in ix.getExtraModUses i do
    let j := ix.getModuleIdx? use.module |>.get!
    if !deps.contains (j, { use with }) then
      deps := deps.insert (j, { use with }) none

  return deps
where
  /-- Accumulate the results from expression `e` into `deps`. -/
  visitExpr (k : NeedsKind) name e deps :=
    let ix := s.ix
    Lean.Expr.foldConsts e deps fun c deps => Id.run do
      let mut deps := deps
      if let some c := getDepConstName? s.refs c then
        if let some j := ix.getModuleIdxFor? c then
          let k := { k with isMeta := k.isMeta && !isDeclMeta' ix c }
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

/-- Analyze and report issues from module `i`. Arguments:

* `pkgs`: the first components of the input modules
* `srcSearchPath`: Used to find the path for error reporting purposes
* `i`: the module index
* `needs`: the module's calculated needs
* `addOnly`: if true, only add missing imports, do not remove unused ones
-/
def visitModule (pkgs : Array Name) (srcSearchPath : SearchPath)
    (i : Nat) (needs : Needs) (headerStx : TSyntax ``Parser.Module.header) (args : Args)
    (addOnly := false) : StateT State IO Unit := do
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
  if module?.any (·.raw.getTrailing?.any (·.toString.contains "shake: keep-downstream")) then
    modify fun s => { s with preserve := s.preserve.insert (if args.addPublic then .pub else .priv) i }

  let s ← get

  let addOnly := addOnly ||
    (!args.onlyMods.isEmpty && !args.onlyMods.contains modName) ||
    module?.any (·.raw.getTrailing?.any (·.toString.contains "shake: keep-all"))
  let mut deps := needs
  let mut reasons : Reasons := {}

  -- Add additional preserved imports
  for impStx in imports do
    let imp := decodeImport impStx
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

  -- mark and report the removals
  modify fun s => { s with
    edits := toRemove.foldl (init := s.edits) fun edits imp =>
      edits.remove modName imp }

  if !toAdd.isEmpty || !toRemove.isEmpty || args.explain then
    if let some path ← srcSearchPath.findModuleWithExt "lean" s.modNames[i]! then
      println! "{path}:"
    else
      println! "{s.modNames[i]!}:"

  if !toRemove.isEmpty then
    println! "  remove {toRemove}"

  if args.githubStyle then
    try
      let ⟨path, inputCtx, stx, endHeader⟩ ← parseHeader srcSearchPath s.modNames[i]!
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
public def run (args : Args) (srcSearchPath : SearchPath := {}) : IO UInt32 := do
  -- `--profile`: time each phase; in this mode phases are forced one after another so that the
  -- parallel `needs` computation is not hidden behind the sequential visit loop.
  let timed {α} := args.timed (α := α)

  -- the list of root modules
  let mods := args.mods
  -- Only submodules of `pkgs` will be edited or have info reported on them
  let pkgs := mods.map (·.getRoot)

  -- Load all the modules (`agitate`: straight from their oleans, see `Agitate.Index`)
  let modules ← timed "readModules (.olean, .server, .private)" <| readModules mods
  let ix ← timed "Index.build (constant maps, extension tables)" <| Index.build modules Reserved.extNames
  let s ← timed "initState (transDeps)" <| IO.lazyPure fun _ => initState ix args
  if args.profile then
    IO.eprintln s!"[profile] {ix.size} modules, {ix.privConsts.size} constants"
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
  let headers ← parseHeaders pkgs srcSearchPath s.modNames
  if args.profile then
    timed "parseHeader (selected modules, parallel)" <| headers.forM fun t => discard <| IO.wait t

  if args.fix then
    println! "The following changes will be made automatically:"

  -- Check all selected modules
  let t0 ← IO.monoNanosNow
  for i in [0:s.ix.size], t in needs, header in headers do
    match header.get with
    | .ok ⟨_, _, stx, _⟩ =>
      visitModule pkgs srcSearchPath i t.get stx args
    | .error e =>
      println! e.toString
  if args.profile then
    IO.eprintln s!"[profile] visitModule loop (sequential): {((← IO.monoNanosNow) - t0) / 1000000} ms"

  if !args.fix then
    -- return error if any issues were found
    return if (← get).edits.isEmpty then 0 else 1

  -- Apply the edits to existing files
  let count ← applyEdits (← get).edits s.modNames headers

  -- Since we throw an error upon encountering issues, we can be sure that everything worked
  -- if we reach this point of the script.
  if count > 0 then
    println! "Successfully applied {count} suggestions."
  else
    println! "No edits required."
  return 0
