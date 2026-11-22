# agitate — design record

`agitate` reimplements `lake shake` (Lean `v4.33.1`) so that it works directly from `.olean` files
instead of importing a whole `Environment`, and fixes the performance bottlenecks found along the
way. Upstream sources cited below are at tag `v4.33.1` of `leanprover/lean4`.

## Decisions

| Decision | By | Status |
|---|---|---|
| Toolchain pinned to `leanprover/lean4:v4.33.1`. | Thomas | settled |
| Read modules with `readModuleData`/`readModuleDataParts`, never `importModules(Core)`/`finalizeImport`. | Thomas | settled, implemented (`Agitate/Index.lean`) |
| Correctness criterion: byte-identical stdout and exit code to `lake shake` from the same toolchain, except for deliberate fixes recorded here. Each fix keeps an upstream-compatible flag so the strict comparison stays mechanical (`scripts/compare.sh`). | Claude, after Thomas asked for fixes over parity | open |
| Fix the two reserved-name quirks rather than reproduce them; `--upstream-reserved` restores upstream behaviour. | Thomas | settled, implemented |
| Count a reference to a reserved name as a reference to the declaration it is regenerated from, instead of dropping it; configurable (`--ignore-reserved-refs`). | Thomas (proposed by Claude) | settled, implemented |
| Indirect module uses depend on their `kind`: configurable per kind (`--ignore-indirect-kind`, `*` for all). The default counts all kinds, as upstream, until data suggests a policy. | Thomas (per-kind); Claude (mechanism, default) | settled, implemented; default open |
| Keep upstream's rule that an indirect use counts only if the module's *original* import closure reaches it. | Claude (Thomas: fine either way) | settled |
| Keep the `calcNeeds`/`getExplanations` discrepancy for indirect uses. | Thomas | settled |
| Do not report the reserved-name quirks upstream for now. | Thomas | deferred (TODO) |
| Count an indirect use when its module is reached through a public import of a privately needed kind (upstream bug, broke `--fix` on the fixture); `--upstream-indirect` restores it. | Claude (Thomas's standing preference for fixes) | implemented |
| Test `shake: keep*`, `--fix` and indirect-use kinds on a fixture workspace (`tests/fixture`, `scripts/test-fixture.sh`); `--fix` results must build. | Thomas (what), Claude (how) | implemented |
| A non-module tool, `agitate-nonmodule`, as a separate executable sharing modules with `agitate` (`Args`, `Bitset`, `Header`, `Index`, `Refs`, `Reserved`). | Thomas | implemented |
| Non-module analysis: one kind of need, plain reachability, a single-kind rewrite of the visit step rather than encoding plain imports as `public import`s. | Claude | implemented |
| In non-module files, `shake: keep-all`/`keep-downstream` may appear in any header comment (there is no `module` token). | Claude | implemented |
| Dependencies invisible in oleans (e.g. `open` of a namespace) are handled with `-- shake: keep`, not code. | Thomas | settled |
| Count `@[implemented_by]` targets as needs, with the declaration's visibility in module mode; `--ignore-implemented-by` restores upstream. | Thomas | implemented |
| Count names preresolved by syntax quotations as ordinary extra module uses of their declarers (non-meta; public if the containing declaration is exported); `--ignore-preresolved` restores upstream. A workaround: the fix belongs in Lean (see "Preresolved names in quotations"). | Thomas (proposal, kind); Claude (details) | implemented |
| `agitate` skips source imports missing from the oleans' closure (stale oleans) instead of panicking. | Thomas | implemented |
| License the repository under Apache 2.0, with copyright headers; files copied or ported from Lean keep their original notices and describe their changes. | Thomas | done |
| Resolve modules through the Lake workspace (root package first, then the toolchain), never `LEAN_PATH`/`LEAN_SRC_PATH`; default to the root's default target roots. | Thomas | implemented |
| For a name declared in several modules, charge a use to the module itself if it declares the name, else to the copy its environment showed (core's last-loaded rule over its own load order); `--upstream-duplicates` restores first-declarer resolution. | Thomas (reported by other sessions; design by Claude, last-loaded rule by Thomas) | implemented |
| `modulate`: from a non-module file's oleans, compute the module-system imports it would need under `@[expose] public section`, and with `--fix` convert it; `--meta GLOB` (Lake globs, module names) for `public meta section`. | Thomas (feature, name, globs), Claude (design) | implemented |
| `--compat` selects every upstream-compatible behaviour at once; the parity checks use it, so new deviations do not break them. | Claude | implemented |
| Port the reserved-name predicates over the olean index rather than approximate them; verify with `agitate-check`. | Claude | implemented, verified |
| Test on Batteries first, Mathlib once things work; use Mathlib's `v4.33.1` tag and its olean cache (it exists), which also brings matching Batteries oleans. | Thomas (order), Claude (setup) | settled |
| Start from a verbatim copy of `Lake/CLI/Shake.lean` and replace its phases one at a time, checking parity after each. | Claude | done; the analysis logic in `Agitate/Shake.lean` is still upstream's apart from the marked changes |
| Skip the `.ir`/`.ir.sig` parts (shake loads them only for `extraConstNames`, compiler auxiliary names that kernel terms never mention). | Claude | verified: `agitate-check` agrees with `getModuleIdxFor?` on every constant, and outputs are identical on core, Batteries and Mathlib |
| Same CLI flags as `lake shake`; modules are passed explicitly for now. | Claude | open |
| `percolate`: for given seed declarations, the project's source items they need, as JSON Lines for a tool that deletes the rest; a separate executable; `--scope` globs select the reported modules. | Thomas (feature, separate executable, globs, deletion tool as consumer); Claude (design) | implemented |
| Needs are what deleting source would break, not kernel references: regeneration counts (a reserved name needs its base) and every recorded need counts ("we really want to record the needs", Thomas). | Thomas | implemented |
| Report source items: maximal full declaration ranges, nested ranges merged, with their ranges ("the range information is in fact necessary", Thomas). Internal names are walked through and left out of the output. | Thomas (ranges, filtering); Claude (merging nested ranges) | implemented |
| The upstreamable part depends only on Lean (`Agitate/ImportGraph`, namespace `Agitate.ImportGraph`, so that upstreaming drops the prefix); the feature is `Agitate/Percolate`, with the executable `percolate`. `Bitset` moved into `Agitate.ImportGraph`. | Thomas (factoring, layout and names); Claude (which parts are upstreamable, the namespace, moving `Bitset`) | implemented |
| Remove the port of ImportGraph's `RequiredModules` (it was the wrong code: Thomas meant `ImportGraph/Shake/` and `WorkspaceModel/` at upstream `HEAD`). Revisit how agitate and `percolate` relate to those. | Thomas | removed; relation open |
| Uses that Lean records only per module, or not at all, give two weaker statuses (`candidate`, `moduleUse`) rather than one coarse flag. | Claude | implemented; open |
| JSON Lines, with records written one at a time, rather than one `Json` value. | Claude (agreed by Thomas) | implemented |
| Recreate ImportGraph's declaration-needs model in agitate (no dependency; stay on `v4.33.1`), for performance, with upstreamable parts in `Agitate/ImportGraph`; exercise it through `percolate`, then bench and iterate. No syntax needs (syntax is an extra module use); no build-time recording (a limitation). | Thomas (direction, constraints); Claude (representations) | steps A and B implemented |

## Results

Benchmarks: `Lean` from the toolchain itself (2322 modules in the closure, 206 647 constants),
Batteries (1372 / 136 864) and Mathlib (10 498 / 771 129), all at `v4.33.1`, on a 14-core Apple
Silicon machine with 48 GiB. Reproduce with `scripts/compare-core.sh --profile` and
`scripts/compare.sh --profile <workspace> <module>`. Outputs are byte-identical to `lake shake` with
`--compat` on all three, also with `--explain`, `--add-public --keep-prefix`,
`--keep-implied --keep-public` and `--gh-style` (core and Batteries).

| wall time | `lake shake` | agitate |
|---|---|---|
| core (`Lean`) | 4.5 s | 0.8–1.0 s |
| Batteries | 2.9 s | 0.9 s |
| Mathlib | 120–144 s | 9.4–12.4 s |

Mathlib phases (`--profile` runs the phases one after another; ranges are warm vs. partly cold page
cache, which this machine evicts aggressively between runs):

| phase | baseline (env-based copy) | now |
|---|---|---|
| read oleans | 4.1 s (`importModulesCore`, 5 parts) | 0.6–1.0 s (3 parts, parallel) |
| build constant maps | 5.3 s (`finalizeImport`) | 0.3–2.2 s |
| reserved names, `transDeps` | 1.3 s | 0.07 s (reserved names are lazy) |
| `calcNeeds` | 8.8 s (all modules) | 4.7–6.3 s (selected modules) |
| header parsing | 0.5 s | 0.7–1.0 s |
| `visitModule` loop | 82 s | 2.7 s |

## Bottlenecks and their fixes

### B1. `Bitset` was a `Nat`; every membership test allocated (dominant: 82 s of 105 s on Mathlib)

`Bitset.has` was `Nat.testBit`, defined as `1 &&& (m >>> n) != 0`
(`Init/Data/Nat/Bitwise/Basic.lean:147`) with no native implementation. On a bignum, `>>>` copies the
number into a fresh mpz (`lean_nat_big_shiftr`). A `sample` profile put ~2/3 of the main thread
there. `visitModule` scanned all `N` modules × 4 kinds three times per selected module, so the loop
was roughly cubic in project size.

Fixes, in `Agitate/Shake.lean`:

* A `ByteArray` bitset. `has` is O(1). `insert`/`erase` don't build singletons. `∪`, `∩` and `\`
  work in place. `∪` mutates the longer operand, so nothing grows byte by byte; growth otherwise
  copies from a zero block with `copySlice`. A profile showed byte-wise `push` growth as the next
  hot spot after the first version.
* The four loops in `visitModule` iterate over the set bits of `deps` (or of `preserve`) instead of
  all modules. Why that is equivalent is argued at each loop: they only remove from `deps`, or only
  insert at indices already visited.

Mathlib loop: 82 s → 16 s (bitset) → 5 s (set-bit iteration) → 2.7 s (no byte-wise growth).

### B2. `calcNeeds` did redundant work

* It ran for every module in the closure, although `visitModule` only uses the needs of modules in
  the selected packages. Now it only runs for those (Batteries: 690 ms → 64 ms).
* It resolved every constant *occurrence* again: reserved-ness, module, `isDeclMeta'`, indirect
  uses. Now `resolveRef` runs once per distinct name per module, memoised in the fold. Only the
  `NeedsKind` bookkeeping and the `transDeps[i]` filter for indirect uses stay per occurrence.
* Extension lookups scanned a module's ~40 `entries` comparing names structurally (`lean_name_eq` +
  `memcmp` were a third of `calcNeeds` samples). Now the entries of the dozen extensions agitate uses
  are resolved into slots once per module (`Module.extEntries`).

What remains in `calcNeeds` is mostly `Expr.foldConsts` itself: its pointer-set cache is rebuilt
for every type and value. See TODO for a shared per-module traversal.

### B3. Environment loading

`finalizeImport` built three hash maps over all constants single-threaded, after
`importModulesCore` had read five files per module sequentially. Then it marked everything
persistent. `Agitate/Index.lean` reads three parts per module (`.olean`, `.server` as a dependency
region, `.private`), level by level over the import DAG with one task per module. It builds the same
two constant maps plus `const2ModIdx`, and none of the extension states. The read tasks also touch
each module's constant names and constant headers. Map building dereferences exactly those, so on a
cold page cache the faults happen in parallel instead of one region at a time. Cold
`Index.build` went from 11 s to ~2 s.

### B4. Reserved names: a global scan

Upstream runs every reserved-name predicate on every constant up front. agitate evaluates them
lazily, once per distinct referenced name per module (B2).

### Not bottlenecks

Header parsing (parallel). `--explain` recomputes needs via `getExplanations`, but only when
requested. The `--fix` rewriting is linear.

## Architecture

1. **`readModules`** (`Agitate/Index.lean`). Discovers the import closure level by level, reading
   each module with `readModuleDataParts #[olean, olean.server, olean.private]`. The private region
   points into the other two, so they must be read together, which three independent
   `readModuleData` calls cannot do. Afterwards the modules are put in `ModuleIdx` order: the DFS
   post-order (imports in declared order, first visit only) in which `importModulesCore` pushes to
   `moduleNames`. Output depends on that order: `toAdd` is built in descending index order, and
   duplicate constants resolve to the first module. Regions are never freed, as with
   `leakEnv := true`.
2. **`Index.build`**. Builds the private and public constant maps and `const2ModIdx` exactly as
   `finalizeImport` does, including `subsumesInfo` for theorems realised in several modules. It also
   builds the imported matcher names and the indirect-use map, and pre-resolves the extension slots.
   Lookups such as `isMarkedMeta`, `isDeclMeta`, `getExtraModUses`, `MapDeclarationExtension.find?`
   and `ParametricAttribute.getParam?` mirror core's code on an environment that imported every
   module with `import all`, which is what shake's is. Extension entries come from each module's
   private part by extension name and are `unsafeCast` to the toolchain's entry types. Core's
   private extensions (`metaExt`, `declMetaExt`, `extraModUses`, `structureExt`, …) are reached with
   `import all`, which works across packages and links.
3. **`Reserved`** (`Agitate/Reserved.lean`). The 13 reserved-name predicates, ported (see below).
4. **`calcNeeds`** for the selected modules, in parallel (B2).
5. **`visitModule`**, sequential: each module's result updates `transDeps` for its importers. It runs
   on the new bitsets (B1); the logic is otherwise upstream's.

`agitate-check` (`AgitateCheck.lean`) loads the same modules the way `lake shake` does. It then
compares every index query with core's answer, for every imported constant, under both reserved-name
semantics. On Mathlib that is 5.4M checks, all passing.

Where the entries live (checked by dumping `Lean.Elab.Command`): `extraModUses`, `declMetaExt` and
`*.eqnInfoExt` appear only in `.olean.private`. `metaExt`, `structureExt`, `sparseCasesOn*` and
`Match.Extension` appear at all levels, with more entries in `.private`. Shake reads every module's
private part (`globalLevel = .private` forces `importAll`), so that part is the source for all of
them.

## Reserved names

`lake shake` ignores references to reserved names ("they can be re-generated in-place",
`getDepConstName?`). Reserved-ness is `isReservedName env c` (`Lean/ResolveName.lean:52`). It runs
the predicates that `builtin_initialize` registered in the running binary: 13 at `v4.33.1`, namely
Eqns, MatchEqs ×2, CongrTheorems, CtorIdxHInj, Injective, SparseCasesOnEq, MethodSpecs, BVDecide
Enums, FunInd ×2 and PartialFixpoint ×2. A runtime probe mapped each registered closure to one of
them, and `agitate-check` checks the count. A binary registers the full set only if its `main` calls
`lean_initialize()`, which runs `initialize_Lean(builtin)` (`src/initialize/init.cpp:37`). The
emitted `main` does so whenever the program uses the Lean API.

Upstream, they run against shake's half-initialised environment (`loadExts := false`). Two quirks
follow, both verified on core:

* **`mainModule` is anonymous**, so `mkPrivateName env n` never matches a real private name. Private
  equation lemmas are never reserved (0 of 4167 private eq-like constants are).
* **`isMatcherCore` is always false**: `Match.Extension.getMatcherInfo?` reads the extension *state*,
  which only `addImportedFn` fills. The matcher-equation predicates never fire, and the generic Eqns
  predicate treats matchers as ordinary definitions.

All other predicate inputs come from imported entries by binary search, or from `env.find?`, and are
unaffected.

### Fixes (Thomas: fix rather than reproduce)

`Agitate/Reserved.lean` ports each predicate from its `v4.33.1` source. The ports replace
environment queries with the index lookups that mirror them, and take a `Ctx`. With
`upstream := false` (the default), `mainModule` is the module that declared the name being tested,
and `isMatcherCore` sees all imported matchers. With `upstream := true` (`--upstream-reserved`), they
reproduce the quirks. `agitate-check` compares both against core's `isReservedName`, on shake's
environment and on that environment with the matcher state loaded and `mainModule` set.

Effects of the fixes:

* **Core.** The reserved set grows from 3628 to 8312 names. All 4684 added names are private
  equation/matcher lemmas, and none are removed. 89 cross-module references hit newly reserved
  names, but suggestions are unchanged.
* **Batteries.** No change.
* **Mathlib.** One suggestion changes: `Mathlib/Data/List/Find.lean` no longer gets
  `import Batteries.Data.List.Lemmas` added. `--explain` shows the only reason: the proof
  `List.find?_congr._proof_1_4` refers to `List.filter.match_1.congr_eq_1`, a matcher congruence
  equation that happens to have been realised in that Batteries module. Upstream misses that it is
  reserved, because `isMatcherCore` is false. A file importing only core can `#check` it (Lean
  realises it on demand), so the import really is unnecessary. Its base declaration
  `List.filter.match_1` is in core, so the redirect proposal below would not change this case.

### References to reserved names count as references to their base (Thomas)

Shake *ignores* a reference to a reserved name. But regenerating that name in place needs its base
declaration, and for a non-exposed definition its body. Nothing guarantees that the referencing term
mentions the base declaration elsewhere. The `_simp_` rule in `getDepConstName?` already redirects
to the base declaration instead of dropping. agitate now does the same for reserved names, keeping
the reference's `NeedsKind`; `--ignore-reserved-refs` restores dropping.

`Reserved.reservedBase?` names the base:

* equation lemmas: `declFromEqLikeName`'s definition;
* matcher equations: the matcher (user name);
* method specs: the instance;
* everything else: the name's prefix (constructor, inductive, function, matcher, …).

If that is not an imported constant, its nearest prefix that is.

Effect: none on core, Batteries or Mathlib. With and without `--ignore-reserved-refs` the suggestions
are identical, so in practice the base declaration is always needed for other reasons. This is a
safety measure: it can only add needs, never remove them.

## Indirect module uses

`indirectModUseExt` maps a declaration `c` to the modules that recorded an indirect use of it.
Currently that means modules that applied an attribute to `c` where `c` is not declared in that
module. In `calcNeeds`, a reference from module `i` to `c` (defined elsewhere) also adds each such
module `m`, but only if `i` *already* transitively imports `m` at kind `k`. Observations:

* The check uses `transDeps[i]` from the state captured **before** the visit loop. Because `needs`
  are spawned up front, they effectively use `transDepsOrig`, not the post-edit closure. agitate
  keeps this. `resolveRef` caches each name's indirect modules, and the `transDeps[i]` filter stays
  per occurrence.
* `calcNeeds` and `getExplanations` disagree slightly. `calcNeeds` only considers indirect uses
  inside `if j != i`, with the meta-adjusted `k`. `getExplanations` considers them for every resolved
  `c` and uses the unadjusted `k`. So `--explain` can attribute a need that `calcNeeds` did not
  count, or the reverse. This is kept for parity; it is a candidate fix.
* Uses are kept only if already in the closure, so shake can never add an import for one. Since the
  filter uses the original closure, the result also depends on what upstream modules imported
  before shaking.

**Where indirect uses are recorded, and who else records.** Core records an indirect use in exactly
one place: `attribute [A] c` on an *imported* `c` records `(kind := A, c)` in the current module
(`Lean/Elab/Declaration.lean:340`). Separately, some attribute *consumers* record precise extra
module uses at use time through `recordExtraModUseFromDecl`, which also records every module with an
indirect use of the declaration (`Lean/ExtraModUses.lean:117`). `simp` does this for every lemma it
used (`recordSimpUses`, `Lean/Meta/Tactic/Simp/Main.lean:738`). Instance resolution does not.
`grind` records at attribute time, not at use. So, for kinds consumed by `simp`, the indirect rule in
`calcNeeds` is redundant for real uses; it fires only on references that did not come through
`simp`, e.g. an explicit `rw [c]`, where the attribute is irrelevant. For `instance`, it is the only
thing keeping the import. The fixture shows both (`tests/fixture`, `scripts/test-fixture.sh`). With
`--ignore-indirect-kind simp` the `--fix` result still builds (`Fixture/SimpUse.lean`); with
`--ignore-indirect-kind instance` it does not (`Fixture/InstUse.lean`).

**Bug fix: indirect uses through public imports (Claude; Thomas's standing preference for fixes).**
Upstream checks `transDeps[i].has k m`, with `k` the kind of the reference. A private use (for example
in a non-exposed body) of `c`, whose attribute module `m` is imported *publicly*, therefore fails the
check: public imports land only in `transDeps[i].pub`. So the import is dropped and the `--fix` result
does not build. `lake shake` itself breaks the fixture that way (`Fixture/InstUse.lean`: "failed to
synthesize instance"). Everywhere else shake accepts the public version of a kind (cf. the `toAdd`
loop's `has k j || has {k with isExported := true} j`). `reachesForIndirect` does the same;
`--upstream-indirect` restores the upstream check. Effect: on core, 26 modules keep an import upstream drops (none lose one); on Mathlib,
366 modules keep an import that upstream drops (none lose one). Those are the cases where
`lake shake --fix` removes an import that an indirect use needs, as in `Fixture/InstUse.lean`.

Settled:

* **Per-kind configuration (Thomas).** A use's kind is the attribute that recorded it. Across
  Mathlib's closure there are ~30 kinds and ~700 entries. Examples are simp sets (`mfld_simps`,
  `bv_normalize`, `pushAttr`, …), `aesop`, `grind`, `to_additive`, `gcongrAttr` and
  `notation_class`. The `Index` keeps each use's kind, and `--ignore-indirect-kind <kind>`
  (repeatable, `*` = all) drops uses of that kind. The default counts all kinds, as upstream does:
  the data does not yet suggest a better policy. Before the public-import fix,
  `--ignore-indirect-kind '*'` changed the suggestions for 1121 of 8296 reported Mathlib modules
  (only 50 of them got more removals). Per-kind data (`scripts/indirect-kinds.sh mathlib4 Mathlib`, relative to the
  current default, with the public-import fix) gives, for each kind, the reported modules whose
  suggestions change when that kind is ignored:

  | kind | uses | modules changed (more removals / fewer additions) |
  |---|---|---|
  | `bound` | 52 | 595 (0 / 93) |
  | `mfld_simps` | 18 | 308 (2 / 51) |
  | `aesop` | 43 | 258 (8 / 157) |
  | `ppWithUnivAttr` | 7 | 103 (1 / 101) |
  | `to_additive_do_translate` | 4 | 86 (14 / 69) |
  | `notation_class` | 25 | 65 (3 / 5) |
  | `to_additive` | 31 | 55 (6 / 14) |
  | `to_dual_do_translate` | 4 | 44 (8 / 29) |
  | `to_additive_dont_translate` | 2 | 35 (1 / 26) |
  | `to_set_notation` | 51 | 34 (0 / 30) |
  | `to_dual` | 35 | 19 (2 / 16) |
  | `gcongrAttr` | 24 | 16 (0 / 16) |
  | `zify_simps` | 4 | 15 (0 / 15) |
  | `spec`, `to_additive_ignore_args`, `elementwise`, `coe`, `instance` | | 8–13 each |
  | `ext`, `mon_tauto`, `mono`, `norm_cast`, `pushAttr`, `rclike_simps`, `refl`, `symm`, `trans` | | 1–3 each |
  | `simp`, `grind`, `bv_normalize` and 18 other kinds | | 0 |

  Reading: the impact is concentrated in a few kinds whose tagged declarations are ubiquitous. For
  example, `bound` tags `le_refl` in `Mathlib.Tactic.Bound`, and `to_additive` tags `One` in
  `Mathlib.Tactic.ToAdditive`. Every reference to them then keeps that module whenever it is in the
  closure. Whether that is needed depends on the consumer. Ignoring a kind is justified by
  mechanism only when its consumer records its own uses: `simp` and simp sets such as `mfld_simps`
  and `zify_simps`. There, the changed modules are ones that reference a tagged lemma explicitly,
  where the attribute is irrelevant. For the others (`bound` and `aesop`, whose consumers record
  nothing; pretty-printing kinds like `ppWithUnivAttr`, which can change `#guard_msgs` output;
  `to_additive`), only a build can tell.

  Policy (Claude, pending validation): the default stays "all kinds count" until a Mathlib build
  with `--fix` applied shows which ignores are safe. Which attribute names are simp sets is not
  recoverable from the oleans generically: the simp extension is named after its declaration, not
  the attribute. So a simp-set ignore list would be per project (`--ignore-indirect-kind`).
* **Original closure (Claude, Thomas: fine).** The "already imported" condition keeps using the
  closure before shaking. That is the conservative choice. An indirect dependency present before
  shaking survives: if edits upstream remove the path to it, shake adds a direct import. Judging by
  the post-edit closure could silently drop it.
* **`--explain` discrepancy (Thomas: fine).** Kept as is.

## Non-module code (`agitate-nonmodule`)

`lake shake` refuses non-module code. `agitate-nonmodule` handles it, based on two facts:

* **Oleans.** A non-module file is written as a single `.olean` at the `.private` level, extension
  entries included (`Lean/Environment.lean:1916-1917`). `readModules (allowNonModule := true)` uses it
  as both views. Module-system imports in the closure (e.g. core) are read as usual.
* **Visibility.** Non-module files are elaborated at the `.private` level
  (`Lean/Elab/Import.lean:147-153`), so every import behaves like `import all` and re-exports
  everything. There is a single kind of need, and import closure is plain reachability.

`Agitate/NonModule.lean` follows `Shake.visitModule` step by step with one bitset instead of four
(keep markers, preserve, transitive reduction, folder-nested, additions in descending order,
`--keep-prefix`, removals). It shares reference resolution (`Agitate/Refs.lean`, including the
reserved-name base redirect) and indirect uses with `agitate`. One encoding detail: non-module
oleans store `import X` with `isExported := true`, plus two implicit `Init` imports
(`Lean/Elab/Import.lean:28-40`). Decoding the source gives `{ module := X, isExported := false }`.
So the tool works with module indices and prints and edits the latter, which is what `--fix` matches.

**Testing without an oracle.**

* **Fixture.** `tests/fixture-nonmodule` mirrors the module fixture. Golden outputs are reviewed by
  hand. `--fix` results must build, and a second run must suggest nothing.
* **Converted Batteries.** `scripts/test-batteries-nonmodule.sh` converts Batteries mechanically
  (`scripts/demodularize.py`) with three documented patches. It builds 190 non-module modules.
  agitate-nonmodule suggests edits for 70 of them in ~2 s, the `--fix` result builds, and a second
  run suggests nothing.

The first attempt failed in one file, `Batteries/Recycling/MonadSatisfying/Lean.lean`. Its content
is commented out except `open Lean Elab Term Tactic Command`, which needs the namespaces to exist,
while nothing references a constant. `lake shake` suggests the same removal on the original module
file. Thomas's decision: such cases get `-- shake: keep`, not code.

## Known blind spots

**Fixed: duplicate declarations (reported by another session exercising agitate's results).**
Lean lets imports merge identical theorems declared in unrelated modules (`subsumesInfo`,
`Lean/Environment.lean:2268-2273`; definitions cannot be duplicated). Shake records only the first
declaring module per name (`insertIfNew`). Every reference was charged to that module, with only
`j != i` checked. So a module's use of *its own* theorem could be charged to an earlier,
unrelated module that also declares it. That module was then added, although it was not even in
the module's imports. In the module fixture, upstream's `--fix` then fails with "already declared".

`Index.dupDecls` records all declaring modules, but only for duplicated names (it is filled in the
branch that already handles duplicates). `const2ModIdx` stays as in core, so `agitate-check` is
unaffected. `resolveRef` returns them in `Resolved.decls`. `Resolved.forModule` then specialises a
resolution to the referencing module `i`, once per distinct name per module:

* if `i` itself declares the name, the use is local and needs nothing;
* otherwise, the use is charged to the declarer whose copy `i`'s environment showed
  (`Index.visibleDeclarer`). This replays core's rule (`Lean/Environment.lean:2340-2341`): a later
  copy replaces the current one if it subsumes it, so among copies identical up to binder
  annotations the last loaded wins. It runs over `i`'s own load order (`Index.loadOrder`), which
  replicates `importModulesCore`'s traversal over the import lists in the index (including which
  olean part each module contributes) and can differ from `ModuleIdx` order.

**Why the copy matters (second report, Thomas: "just the last-loaded").** A first version charged the
first declarer reached by `i`'s imports, assuming copies are interchangeable. They are only for the
kernel. `subsumesInfo` compares types with `==`, which is `Expr.eqv` and ignores binder annotations
(`Lean/Expr.lean:804-812`). Another project declared `umat_mem_UJset` with `ε` explicit in one module
and implicit in another; the file relied on the explicit copy, which loaded last. Keeping the other
copy broke `umat_mem_UJset ε g`. The fixtures' `BinderA`/`BinderB`/`BinderUse` reproduce it:
`--compat` (and the first version) keep `BinderA`, whose `--fix` result fails to build.

**Cost.** Nothing is loaded: `loadOrder` walks the import lists already read from the oleans, and
`visibleDeclarer` compares the few declaring copies with core's `subsumesInfo`. Unique names pay
one `isEmpty` test per occurrence. A module that uses a duplicated name pays one traversal of its
import closure, memoised with a `Thunk`, plus one pass over that order per such name. Both happen
inside the parallel `calcNeeds`. Worst case, measured on Mathlib's import graph (as if every one
of its 10 498 modules used a duplicated name; Mathlib itself avoids duplicates): `loadOrder` for all
modules takes 13.3 s sequentially and 1.8 s in parallel, i.e. ~1.3 ms per module, over 23M
load-order entries (largest closure 10 496 modules).

Both tools and `--explain` use this. `--upstream-duplicates` (part of `--compat`) restores upstream.
The fixtures' `DupA`/`DupB`/`DupUse` reproduce the first report: upstream adds `DupA` to `DupB`, and
replaces `DupUse`'s import of `DupB` by `DupA`. No change on core.

Duplicated *equation lemmas*, which are realised routinely in several modules, are reserved names.
By default a use counts as one to the base declaration (see "Reserved names"), whichever copy it
refers to. The rule above covers them under `--ignore-reserved-refs`/`--compat`.

### Preresolved names in quotations (worked around; the real fix belongs in Lean)

**Problem.** A syntax quotation resolves its global identifiers when it is elaborated and stores
the candidates in the syntax (`quoteSyntax`, `Lean/Elab/Quotation.lean:127-143`). The compiled term
holds them as `Name` literals, e.g. `Syntax.Preresolved.decl `quotTarget []`, not as constants, so
`Expr.foldConsts` does not see them. Lean records no extra module use for them either: no
`recordExtraModUse*` call site is in `Quotation.lean` or `ResolveName.lean`. So if a quotation is
the only use of an import, shake removes the import. The quotation's own module still
builds, because preresolution simply finds nothing. The breakage shows up at every expansion site.
With no preresolved candidates, `resolveName` falls back to `realizeGlobalName`
(`Lean/Elab/Term/TermElabM.lean:2189-2192`). That lookup puts the macro scopes back onto the name
(`Lean/ResolveName.lean:196-201`), so no global matches: ``Unknown identifier `quotTarget✝` ``.
It fails even where shake added a direct import of the declaring module (verified on the fixture
with `lake shake --fix`, `v4.33.1`). `notation` happens to be covered: its generated
`@[app_unexpander a]` records `a` through the attribute key (`Lean/KeyedDeclsAttribute.lean:35`).
`macro`, `macro_rules`, `elab` and hand-written metaprograms are not covered.

**Workaround (Thomas: "an ordinary extra mod use, for now"), `Agitate/Preresolved.lean`.** Both
tools synthesize the extra module use that Lean does not record:

* For every `Syntax.Preresolved.decl n _` in a declaration's value whose `n` is a closed `Name`
  term, the declarer of `n` becomes a need of the module. The name is resolved like a constant
  reference (`resolveRef`, `Resolved.forModule`), so reserved names and duplicates behave the same.
* **Kind (Thomas):** public if the declaration containing the quotation is exported, private
  otherwise; never meta. The reasoning, summarized from Thomas: unlike a name literal in general,
  the purpose of a preresolved name is known. It is there so that the quoted syntax resolves to it
  wherever that syntax is elaborated, i.e. in the modules that run the macro or elaborator. Whether
  other modules can run it is what the declaration's visibility says. The name is data to the
  metaprogram, not code it runs, and those modules elaborate it in the regular phase. A macro's
  auxiliary definition counts as exported even without `public macro`, so `QuotMacro` in the
  fixture keeps a public import.
* **Limitation: private helpers (noted by Thomas; summarized).** The declaration's own visibility
  only approximates "other modules run this quotation". A private `meta def` that builds syntax
  for a public macro or elaborator in the same file runs wherever that macro is used, yet its
  quotation gets a private import. The exact rule would make the need public if any exported meta
  declaration reaches the helper through a chain of references. That is beyond this workaround.
  The fixture's `QuotHelper` is exactly this case and gets a private import. Its `--fix` result
  still builds: expansion sites refer to the declaration as a constant, so shake gives them a
  direct import of it. So a private import never breaks a build. It only falls short of the
  intent that a macro's users should not have to import what its expansion needs.
* **Possible restriction, not implemented (suggested by Thomas; summarized).** Count only
  quotations in declarations with the `@[macro]` attribute. Of the hits traced with
  `--explain` (below), only `json%` in `Lean/Data/Json/Elab.lean` is such a declaration. The
  others are `elab_rules` elaborators (`Mathlib/Util/Notation3.lean`,
  `Mathlib/Util/ParseCommand.lean`), plain helpers (`elabElabRulesAux` in
  `Lean/Elab/ElabRules.lean`, `doSeqToCode` in `Lean/Elab/Do/Legacy.lean`) and the fixture's
  private `meta def` helper. The restriction would miss all of these.
* **Not followed (Claude):** the declarer's indirect module uses, which `recordExtraModUseFromDecl`
  would add. They are needs of expansion sites, and expansion sites reference the declaration as a
  constant and get them that way. The quotation's module only needs the name to resolve.
* **Scope:** in `calcNeeds`, only modules whose terms mention `Syntax.Preresolved.decl` are scanned,
  using the resolution cache's keys. `--explain` names the declaration and the preresolved name.
* **Overcounting.** Preresolution keeps every candidate of `resolveGlobalName`, and binder
  identifiers in a quotation are preresolved too: in `` `(fun x => …) `` with a global `x` in
  scope, `x` is preresolved as well. The rule is "this import changes the compiled quotation", which
  is broader than "expansion needs it".
* **Impact (measured).** `--compat` stays identical to `lake shake` on core, Batteries and an early
  Mathlib slice. Default-mode changes, against `--ignore-preresolved`:
  * Batteries: none.
  * Core `Lean`: 15 modules. Examples: `Lean/Data/Json/Elab.lean` (`json%` quotes `toJson`)
    keeps `Lean.Data.Json.FromToJson.Basic`. `Lean/Elab/ElabRules.lean` (`elab_rules` quotes
    `Tactic` and `DoElab` for the definitions it generates) keeps `Lean.Elab.Do.Basic` and adds
    `Lean.Elab.Tactic.Basic`. `Lean/Elab/Do/Legacy.lean` (quotes `Loop.mk`) adds
    `public import Init.While`.
  * Mathlib `v4.33.1`, roots `Mathlib.Algebra.Group.Defs`, `Mathlib.Order.Notation`,
    `Mathlib.Util.Notation3` and `Mathlib.Logic.Basic` (70 modules reported): 2 modules.
    `Mathlib/Util/Notation3.lean` keeps `public import Lean.PrettyPrinter.Delaborator.Builtins`
    (its generated delaborators quote `withOverApp`) where upstream substitutes
    `public import Lean.SubExpr`. `Mathlib/Util/ParseCommand.lean` adds `public import Lean.Log`
    and `Lean.Exception` (its `elab_rules` quotes `logInfo`, `ofExcept`). Elaborators often quote
    core API, and their declarations are exported, so a public import of a core module can
    appear where a meta import used to be enough.
  * Cost: `calcNeeds` on core 275–282 ms with and without the scan (`--profile`, two runs each).
* `--ignore-preresolved` (part of `--compat`) restores upstream. Tests:
  `QuotTarget`/`QuotMacro`/`QuotHelperTarget`/`QuotHelper`/`QuotUse` in the module fixture,
  `QuotTarget`/`QuotMacro`/`QuotUse` in the non-module one. With `--ignore-preresolved`, the
  `--fix` result fails at `QuotUse`.

**The ideal solution, in Lean.** Two parts:

1. `quoteSyntax` records an extra module use for each preresolved declaration, at the export level
   of the declaration being elaborated. That is all the workaround emulates,
   and agitate would then need no special code: delete `Agitate/Preresolved.lean`.
2. Under the module system, a macro's users need the preresolved declarations as well, and a
   private import in the macro's module does not reach them. The natural carrier is an indirect
   use, as Thomas proposed (summarized): references to macro `m` also need module `F`. Expanding a
   macro already calls
   `recordExtraModUseFromDecl` on its declaration (`Lean/Elab/Util.lean:160-162, 214-215`; tactics
   at `Lean/Elab/Tactic/Basic.lean:255, 315`). That call also records the declaration's indirect
   uses, non-meta, at the use site's export level (`Lean/ExtraModUses.lean:111-118`), which is
   exactly the right kind. But an `IndirectModUse` holds only `{kind, declName}`, and its target is
   implicitly the module that stored it (`Lean/ExtraModUses.lean:20-34, 43-49`). `m`'s module can
   only say "users of `m` need me", which is already true, and `F`, compiled earlier, cannot
   mention `m`. Lean would need an entry that names its target module. Two gaps remain even then:
   term and command elaborators do not record their own declaration at use sites (only the syntax
   kinds, `Lean/Elab/Command.lean:625`), and indirect uses are not transitive, so a quotation in a
   helper such as `mkFoo : MetaM Syntax` would be filed under the helper, not the macro calling it.
   Agitate cannot emulate this part per declaration: a use site's recorded `ExtraModUse` has no
   declaration name (`Lean/ExtraModUses.lean:56`), only a module.

Still open:

Shared by both tools and by `lake shake`:

* **Opened namespaces.** `open X` needs declarations in `X` to exist, but leaves no trace in terms
  or recorded uses. Handled with `-- shake: keep` (Thomas).
* **Constants named only in attribute arguments.** For example `@[implemented_by gImpl] def f`:
  nothing records `gImpl`. On scratch copies of both fixtures, agitate-nonmodule and `lake shake`
  both suggest removing the import that provides `gImpl`; after `--fix` the build fails with
  "Unknown constant `gImpl`".
  * **Fixed for `implemented_by` (Thomas).** Both tools count the target as a need of the
    declaring module, read exactly from the attribute's entries (`Index.implementedBy?`,
    `implementedByTarget?`). `--ignore-implemented-by` (included in `--compat`) restores upstream
    behaviour.
  * **Import kind in module mode.** An experiment settles it. A *private* import of the
    implementation lets the declaring module compile, but a downstream module compiling a call of
    `f` fails with "Unknown constant `gImpl`". So the need takes the declaration's visibility:
    public for an exported declaration. This is the `IbDecl`/`IbUse` case in both fixtures.
  * **Impact.** None on core, Batteries or Mathlib (their targets are referenced anyway or live in
    the same module). It matters for code like the fixture's, where nothing else mentions the
    target.
  * **Rarer attributes** with constant arguments get annotations.

Within the module system, the compiler records IR-level uses (`checkTemplateVisibility`,
`Lean/Compiler/LCNF/Visibility.lean:132`, module-only). Non-module code does not need this, because
imports re-export: a module that inlines a function reaches whatever that function's own module
imports. Tactics, macros, notation, syntax, elaborators and `simp` lemmas record their uses in
non-module code too, since none of those recording sites is gated on the module system.

**Freshness.** Neither tool checks that oleans are up to date; both trust them (`--force` is
accepted and ignored). Source headers are still read, for `shake:` markers and `--fix`. On a source
import missing from the olean's closure, agitate-nonmodule skips it, while `agitate` panics in
upstream's `getModuleIdx? … |>.get!` and continues with a wrong module index. Now `agitate` skips
it too (Thomas). Upstream never reaches this without `--force`, because it refuses stale oleans,
so this needs no `--compat` switch. `scripts/test-fixture.sh` checks it with an import of a module
outside the closure, where `lake shake --force` panics with `Option.get!`.

**Module-name shadowing across packages (open, Thomas to decide).** A session that `require`d
agitate from another project got agitate's `Main` instead of the project's own `Main`. The causes:

* `ws.packages` lists the root package first, then dependencies in `require` order
  (`Lake/Config/Workspace.lean:50-54`). `leanPath`/`leanSrcPath` fold `::` over it, which
  reverses it (`:356-366`). So every dependency's build directory and source directories come
  *before* the project's own on `LEAN_PATH`/`LEAN_SRC_PATH`.
* Module names are global. agitate's executable roots (`Main`, `NonModuleMain`) are built into its
  library directory (`.lake/build/lib/lean/Main.olean`). Its `lean_lib`'s source directory is the
  package root, so `Main.lean` is a source too.
* Hence, under `require agitate`, `Main` resolved to agitate's olean (it clashed with the project's
  declarations), and `--fix` would have edited agitate's `Main.lean`.

This is not specific to agitate: any required package with a module of the same name (an
executable root called `Main` is common) shadows the project's module for every tool that resolves
modules by name.

**Decision (Thomas), implemented:** do not use `LEAN_PATH`/`LEAN_SRC_PATH` at all. Load the Lake
workspace and resolve modules through it, starting from the root package, as Lake's own builds do.
`Agitate/Workspace.lean`:

* **Loading.** `Resolver.load` loads the workspace in the working directory with `loadWorkspace`
  (no dependency updates). Lean is the installation the project's `lean` resolves to; Lake is the
  one shipped with it (`LakeInstall.ofLean`). `findLakeInstall?` would look next to agitate's own
  executable. Loading a `lakefile.lean` evaluates it in-process, so the executables use
  `supportInterpreter`. On Mathlib, loading takes 0.6–0.9 s.
* **Resolution.** `Workspace.findTargetModule?` covers library modules and executable roots, root
  package first (`Lake/Config/Workspace.lean:287-288`). Otherwise the toolchain's `lib/lean` and
  `src/lean` (and `src/lean/lake`) serve `Init`, `Std`, `Lean` and `Lake`. Oleans, sources for
  headers and `--fix`, and reported paths all come from here. Reported paths are unchanged, which
  the `--compat` comparisons on core, Batteries and Mathlib confirm.
* **Default roots.** Without modules on the command line, the root package's default target roots
  are checked (`Workspace.defaultTargetRoots`), as `lake shake` does.
* **Checker.** `agitate-check` passes explicit `ImportArtifacts` for every module of the closure to
  `importModulesCore`, so its reference environment does not use a search path either.
* **Test.** `scripts/test-require.sh` builds a project that `require`s agitate and has its own
  `Main`. Agitate must analyse the project's `Main`, both directly and under `lake env`. The
  pre-change binary fails it: without `LEAN_PATH` it finds no `Main`; under `lake env` it reads
  agitate's own non-module `Main.olean`.

The options considered before that decision:

1. Usage: do not `require` agitate; run it with `lake env <path>/agitate…`.
2. Make agitate safe to `require`: namespaced executable roots (e.g. `Agitate.Main`), and delete
   the stale oleans.
3. Detect the hazard generally. If a selected module's olean or source resolves in more than one
   search-path entry, error out (or refuse `--fix`) rather than silently analysing or editing the
   wrong one.

## Converting non-module files: `modulate`

A non-module olean records every import as `isExported := true` (`Lean/Elab/Import.lean:38`), so in
module terms a non-module file already looks like a module whose imports are all `public import`s.
`modulate` (`ModulateMain.lean`) therefore runs `agitate`'s module-system analysis
(`Agitate/Shake.lean`) on non-module oleans (`Args.toModule`, `State.converting`), with these
changes:

* **Hypothetical visibility** (`State.convertedVisibility`), as under `@[expose] public section`:
  non-private declarations are exported; definitions are exposed, and so are the proofs
  abstracted from them (`d._proof_N`), since the module system checks those as part of the exposed
  body; theorem proofs and `opaque` values are private. For `--meta` files (`public meta section`)
  every declaration counts as exported and exposed, private ones included. Importers evaluating a
  public meta definition need the code of everything it calls, so Lean requires
  `public meta import` even for what only private helpers reference (over-approximates for
  unreachable private helpers).
* **Meta.** Declarations of `--meta` files count as meta for their users (`RefCtx.metaModules`).
  References to them need no `meta import`, and a compile-time extra use of such a file needs
  none either. Macros, elaborators and syntax made by the `macro`/`elab`/`syntax` commands are
  recorded as meta even in non-module oleans, so their compile-time uses already come out as
  `meta import`s. `--meta` is for metaprograms nothing records, e.g. `@[macro …] def`.
* **Extra module uses** recorded in non-module elaboration carry no exporting context, so they count
  as public (conservative). On the converted fixture, module-mode `agitate` then finds exactly one
  import that could be private (`Fixture/SimpUse.lean`); everything builds.
* **Closure.** A module cannot import a non-module file, so a file is converted only if every
  non-module file it imports is converted in the same run (`State.notConverted`).
* **Markers.** `shake: keep-all`/`keep-downstream` are read from header comments (there is no
  `module` token) and written onto the `module` line.
* **`--fix`** (`convertToModuleText`). Layout as in core's `script/Modulize.lean`: `module` after
  the header comments; the computed imports; the section below an initial module docstring if any,
  else below the imports; no section without commands. Kept imports keep their trailing comments.

**Tests.** `scripts/test-fixture-nonmodule.sh` converts the non-module fixture. It checks that the
result builds with `--meta Fixture.MetaMacro` (an `@[macro …] def`) and fails without it, and keeps
golden files of `modulate`'s suggestions and of module-mode `agitate` on the converted result.

**Batteries round trip** (by hand). The converted non-module Batteries (see
`test-batteries-nonmodule.sh`) was converted back with `modulate`, `--meta` for the 31 files the
original Batteries has `public meta section` in, and built. Core's `script/Modulize.lean` with the
same sections, which keeps every import and makes it public, served as the comparison.
* **Initially** `modulate` failed in 5 files `modulize` did not. Both causes were import kinds,
  fixed by the visibility rules above: proofs abstracted from exposed definitions, and private
  helpers of public meta code.
* **Now** `modulate` fails in 16 files, a subset of `modulize`'s 17, so none of its failures are
  its own. The remaining failures are conversion semantics no import set fixes: proofs unfolding
  non-exposed definitions (`import all`), `private` declarations in exposed bodies, and files
  mixing meta and non-meta code. Lake skips dependents of failed modules, so these are lower
  bounds.

## Declaration needs: `percolate`

**The question.** Thomas: "how could we change the repo source and still have it work out", "namely
how could we prune declarations". So the graph is over *source items*, the spans that
deleting a declaration removes, and its edges are whatever deleting the source would break.
Claude first proposed kernel-level dependency. Thomas disagreed ("I'm not sure I agree re: ignoring
regeneration"): an equation lemma is not in the source, while the definition it is regenerated from
is.

**Items** (`Agitate/Percolate/Items.lean`). `declRangeExt` stores a range for each declaration written
in the source. Its entries are in `.olean.server` and `.olean.private`, not in `.olean`
(`Lean/DeclarationRange.lean`), so the index's private part has them. Elaborators also give
generated declarations the range of the syntax that made them: constructors
(`Lean/Elab/Inductive.lean:81`), structure fields (`Lean/Elab/Structure.lean:454`), `let rec` and
`where` helpers (`Lean/Elab/LetRec.lean:63`), `deriving` instances
(`Lean/Elab/Deriving/Basic.lean:272`) and `@[ext]` lemmas (`Lean/Elab/Tactic/Ext.lean:128`). Merging
nested ranges therefore groups exactly what cannot be deleted separately. The range is the full one,
docstring and attributes included (checked on the fixture). A constant without a range maps to its
parent: the reserved-name base, else the name's prefix. That parent can be in another module, as for
an equation lemma realised downstream. *Found on Mathlib:* auxiliary lemmas such as `foo._simp_1_3`
are private (`_private.M.0.foo._simp_1_3`) even when `foo` is public, so a private prefix that is not
a constant stands for its public name. Before that fix, 69 413 of 332 993 Mathlib items were
unranged. After it, 1 613 of 265 193 are, mostly `_auto` (742) and realised equation lemmas whose
base has no range (open, TODO).

**Needs** (`Agitate/Percolate/Needs.lean`). An item needs what its constants need: the constants in
their types and values; for an inductive its constructors and for a recursor its mutual block (as
`ConstantInfo.getUsedConstantsAsSet`); `@[implemented_by]` targets; and names preresolved in
quotations. References are resolved with `resolveRef`/`Resolved.forModule`, so reserved names count
as their base, and a duplicated theorem as the copy the module saw. Mutual inductives make the item
graph cyclic, hence strongly connected components (`Agitate.ImportGraph`).

**Unrecorded uses.** `ExtraModUse` stores `{module, isExported, isMeta}` only.
`recordExtraModUseFromDecl` receives the used declaration but passes it to `recordExtraModUseCore`
only as a trace hint (`Lean/ExtraModUses.lean:56-63, 87-93, 111-118`). Uses inside a module record
nothing at all, since `getModuleIdxFor?` is `none` there. A first version (Claude) treated every
item of a used module as possibly needed. On the fixture, `seed2`'s `simp [double]` then marked
every declaration of `Fixture.Base`, used or not, because `simp` records the module of every lemma it
used. Lean says why it records them (`recordSimpUses`, `Lean/Meta/Tactic/Simp/Main.lean:735-743`):
"For `rfl` theorems and simprocs, there might not be an explicit reference in the proof term". So
the result has three levels (Claude, open to revisiting):
* `needed`: recorded needs between declarations;
* `candidate`: also the declarations such a use can name without leaving a term:
  * for a meta use, metaprograms (meta, or a type mentioning `Lean`, which covers non-module code
    and simprocs; a heuristic that errs towards keeping);
  * for a non-meta use, rfl theorems (`@[backward_defeq]`, a superset of `@[defeq]`) as well;
  * inside a module, both, of the module itself.
* `moduleUse`: any item of a used module. This covers the other recorders of non-meta uses
  (coercions, docstrings, delaborators, the deprecation linter, …), whose declarations usually
  also appear in terms.

The fixture test pins this down. Deleting `unused`, and then `moduleUse` as well, still builds, and
a second run reports neither status. Deleting `candidate` as well does not build: there the
notation, the local macros and the rfl lemma used by `dsimp` are all needed. The real fix is in
Lean: store the hint, and the using declaration (TODO).

**Boundaries.** The walk stops at the root package (`Package.isLocalModule`): dependency packages
cannot import it. `--scope` globs only filter the output, since a needed item outside them can need
one inside. Only modules in the seeds' import closure can contain needed items, so needs are computed
for those modules only, in parallel per module.

**Output.** JSON Lines, one `ToJson`-derived record per item, written as computed. A record's
statuses are known only after percolation, so nothing can be streamed earlier. A single `Json`
value would hold a `Std.TreeMap.Raw String Json` of all items and then one huge string
(`Lean/Data/Json/Basic.lean:186`, `Printer.lean:167`).

**Measurements.** Mathlib `v4.33.1`, all of `Mathlib`, seeds `Real.pi_gt_three`,
`fermatLastTheoremFour` and `ZMod.pow_card_sub_one_eq_one`. Two runs back to back (cold, then warm
page cache):
* wall time 8.9 s and 4.5 s; peak RSS 6.4 GB;
* phases: `readModules` 2.4/1.2 s, `Index.build` 2.1/0.2 s, items 0.2 s, needs (2 245 modules in
  the closure) 0.6–0.7 s, graph assembly 0.09 s, percolation (three levels) 0.25 s, output 1.2–1.3 s
  (117 MB);
* result: 9 490 needed, 26 046 candidate, 50 750 moduleUse and 178 907 unused items, out of 265 193.

## `Agitate.ImportGraph`

**Scope (Thomas, "nicely factored so that upstreamable bits are upstreamable, and adapted bits to
our purposes are not baked into our project").** `Agitate/ImportGraph/` imports only Lean, never
the rest of agitate. It holds the parts of the declaration-needs model below that are independent
of how needs are read: `Graph` (graphs in compressed sparse row form, Tarjan components, label
propagation, breadth-first search trees), `NeedKinds`, `SourceItems` and `Bitset` (moved from
`Agitate`; `Agitate.Bitset` is an alias). Producers that read the olean index (`Agitate/DeclNeeds.lean`)
and `percolate` itself stay in agitate.

**Layout and names.** The first version was a separate library, `Percolate`, after Thomas's "Let's
call it Percolate", which Claude applied to the library. Then Thomas: "We should structure this as
Agitate/ImportGraph for the upstreamable content, and Agitate/Percolate and `percolate` for the
functionality here and the executable." The namespace `Agitate.ImportGraph` (Claude) cannot clash
with ImportGraph's own declarations when both are loaded, and upstreaming drops the prefix.

**Removed: a port of `RequiredModules`.** Asked to "depend on or adapt ImportGraph tooling"
(Thomas), Claude read the ImportGraph that Mathlib `v4.33.1` pins (`16f02aa`, 2026-08-10). Its
only constant-dependency code was `ImportGraph/Imports/RequiredModules.lean`, so Claude ported that
(`transitivelyUsedConstants`, `transitivelyRequiredModules'`) and verified the port against it.
Thomas had meant his newer `ImportGraph/Shake/` and `ImportGraph/WorkspaceModel/` work at upstream
`HEAD` (`b9ec7f6`, 2026-11-20), which that commit predates ("Absolutely, I did not want you to port
RequiredModules"). The port, its differential test and the traversals only it used
(`Graph.explore`, `Graph.flowBackward`) are gone. *Lesson:* read a dependency at upstream `HEAD`
before porting from it, not only at the version a downstream project pins.

**`Bitset` against `Nat`.** Lake's shake and ImportGraph's `ImportGraph.Shake.Bitset`
(`ImportGraph/Shake/Core.lean:41-42` at `HEAD`) use a `Nat`. Measured, compiled, on 20 000 sets of
30 elements over 10 000 indices (two runs): singleton `insert` 7–8 ms against 246–330 ms (`Nat`:
`||| (1 <<< i)`); membership of every index for 200 sets 5–6 ms against 633–800 ms (`Nat.testBit`);
but union into an accumulator 27–67 ms against 5–17 ms, and union with a large shared set 47–115 ms
against 5–10 ms. `Bitset.union` loops over bytes in Lean, while `Nat.lor` is GMP's word-wise
`lean_nat_big_lor` (`lean.h:1648-1652`). So the `ByteArray` bitset is not better across the board.
An earlier version of this record said it was (Claude, unmeasured). A word-wise union would
likely close the gap (TODO).

**Tests.** `AgitateTest/ImportGraph.lean` covers cycles, the forward flow, and a 100 000-vertex
chain without stack overflow. On a 1M-vertex chain in the interpreter, components and the forward
flow scale linearly (2.5 s and 4.7 s at 1M). *Pitfall found while testing:* labelling every vertex
`v` with `{v}` makes bitsets of `v/8` bytes, which is quadratic in space. Seeds are few, so
`percolate` does not hit this.

## Declaration needs: recreating ImportGraph's model

**Thomas's constraints.**
* Do not depend on ImportGraph: "we do need to stay on 4.33.1 for now". Copy its types under
  `Agitate/ImportGraph/Copied` if sharing them, or recreate them from scratch for performance.
* "port things in the most performant way we can", in clearly marked upstreamable parts.
* Then use `percolate` to exercise the abstractions, and "make decisions there, then bench and
  iterate".
* Build the "most conceptually elegant approach" rather than only what `percolate` uses so far.

Claude recreates rather than copies (nothing is under `Copied`), choosing representations for speed:
* flags in a byte instead of `DeclDeclNeedsKind` sets (`Std.TreeSet`);
* edge lists sorted into compressed sparse rows instead of nested `NameMap`s;
* dense item ids.

**Syntax and per-command needs (Thomas).** "the syntax needs might not be necessary for this
purpose. Syntax is recorded as an extra mod use." So nothing like ImportGraph's `calcSyntaxNeeds`
is recreated. Attributing extra module uses to commands or declarations would need data recorded
while elaborating. Thomas: "You would need to override the command elaborator for declarations, I
believe, and that would only help sometimes. Linters and such can't persist anything." *Limitation*
(Thomas: "Something that doesn't require a source build opt-in is better for now, but let's note
this as a limitation"): without such an opt-in, extra module uses stay per module, hence the
`candidate` and `moduleUse` approximations. Declaration ranges (`declRangeExt`) stand in for
command ranges where ranges are needed (Thomas: "We might be able to get at least (most of the)
ranges from the declaration range extension").

**Step A: typed needs and `why` (implemented).**
* `NeedKinds` records where in the user a reference sits (`type`, `value`) and how it arises
  (`implementedBy`, `preresolved`, `structural`, `regenerated`). Code needs are next (step C).
* `Agitate.constRefs` and `Agitate.resolveDecl` produce each constant's needs from the index.
* `percolate` builds a labelled graph between items: each constant's needs are merged per needed
  item by sorting `item * 256 + kinds` (no tuples, no hash map), and the whole graph by
  `LGraph.dedup`, which is linear (a marker per vertex).
* A breadth-first tree per level gives each item its `why`. Recorded needs are explained at the
  declaration level by resolving the predecessor item's constants again, batched per module, in
  parallel. The first, unbatched version searched for each item's module and rescanned its
  constants per item, and took the output phase on Mathlib from 1.3 s to 10 s.
* Mathlib (seeds as in "Declaration needs: `percolate`", two runs): wall time 10.5 s (cold)
  and 5.0 s (warm), against 8.9 and 4.5 before.
  * Phases: needs 0.6–0.7 s; graph assembly 0.06–0.07 s for 1 845 579 merged needs; percolation
    0.3 s; search trees 0.02 s; `why` 0.2 s; output 1.4 s.
  * Statuses identical to before.

**Step B: stances, the import algebra, and imports after deletion (implemented).**
* `Agitate.ImportGraph.Imports` recreates ImportGraph's algebra on `Bitset`: `ImportKind` (six kinds),
  `Needs`/`Provides`, composition (`andThen?`, as ImportGraph's `NeedsKind.andThen`), `linearize`,
  `Hierarchy`, and `ImportNeeds.reduce`. The reduction is ImportGraph's `reduceBy`: start from all
  phased needs, keep each need not yet implied, and drop what its closure implies. A first version
  (Claude) checked every chosen import against all others, which is quadratic.
* `Agitate.ImportGraph.Stance` gives a declaration's visibility, exposure and phase, and
  `Stance.importNeeds` turns one need into imports.
* `percolate` exercises both. Its module records give each project module's imports once the items
  of the `--delete` statuses are gone: per-module needs in parallel, then a reduction in
  `ModuleIdx` order over the hierarchy of the new imports.
* Code references are approximated by the value references of declarations that have code, until
  step C reads the IR.

**What the large test found (Claude).** `scripts/test-percolate-batteries.sh` applies the imports
for `--delete none` to a copy of Batteries and builds it. Each failure exposed a need that terms
do not show:
1. *`import all`.* It serves unfolding non-exposed definitions (`Batteries.Control.Lemmas`), which
   leaves no reference. Existing `import all`s are kept, as shake keeps them
   (`Agitate/Shake.lean:533`).
2. *Abstracted proofs.* A proof in an exposed definition is elaborated in its public value, then
   abstracted into `foo._proof_N`, a theorem whose proof is private (`Batteries.Data.Fin.Basic`,
   `Nat.mul_add_lt_mul_of_lt_of_lt`). An auxiliary declaration (no range of its own) counts as being
   where its parent uses it: in the parent's type (public if the parent is), or in its value
   (public if exposed). Its phase is the parent's if it has none itself.
3. *Code references to constructors.* Lean's `checkMeta` (`Lean/Compiler/LCNF/Visibility.lean`)
   checks every declaration code uses, constructors included: anything not marked meta is available
   to code only in the phase it was imported in (`proof_wanted` placeholders,
   `ProofWanted.mk`). So the phase a code reference needs depends on whether the used declaration
   is marked meta, not on whether it has code.
4. *Attributes registered by `initialize`.* `@[tactic_code_action]` was "Unknown" after
   `public meta import Batteries.CodeAction.Attr` became a plain import. Its extension
   (`Batteries.CodeAction.tacticCodeActionExt`) is registered by a runtime `initialize`, which runs
   while elaborating only under a `meta import`. The applying module has entries in that
   extension, so: entries in an extension registered by a regular `initialize` (`regularInitAttr`)
   need its module, meta-imported if the initializer is runtime code. The toolchain's initializers
   are in `lean` and always run. An earlier version without these two refinements added
   `meta import Lean.Compiler.ModPkgExt` to every module, and `meta import
   Batteries.Util.LibraryNote` where a plain import builds.

Result: the suggested imports build, a second run suggests no change, and 139 of 192 modules get
the same imports as `agitate --fix` (shake). The others differ in which module provides a need,
public against private, or `meta`. In 17 cases `percolate` keeps a public import that shake does
not, which is more conservative (likely rule 2). Mathlib (three seeds, two runs): 12.1 s cold and
6.7 s warm. Imports after deletion take 1.2 s: original hierarchy 0.1 s, needs 0.8–0.9 s in
parallel, reduction 0.27 s. The byte-wise `Bitset` does not matter here.

**Limitations of the imports (open).**
* `-- shake: keep` annotations are not read.
* Options registered by `register_option` and used by `set_option` leave no entries, so their
  modules can be dropped.
* Non-module files get plain reachability and are untested.

**Iterating on speed (Claude; Mathlib, three seeds, warm).**
* *Rendering records by hand.* Deriving `ToJson` builds a `Json` tree per record, with objects as
  sorted maps. Rendering the same text directly with `Json.renderString` took the output phase from
  1.6–1.9 s to 0.95–1.3 s, and the whole run to 5.6 s. The Mathlib output is byte for byte the
  same.
* *Modules emptied by the deletion.* Their constants are skipped. That includes constants they
  realised for kept items of other modules (equation lemmas, say): with every command of the
  module gone, nothing realises them. This changed 406 Mathlib module records. Modules that keep
  some items still keep such constants, since which command realised them is unknown.
* *Not yet profiled.* The import needs (0.8 s) did not get faster. Where the time goes needs a
  `sample` profile, not a guess (TODO).

**Step C, reading code references from the IR: not done (Claude, open to revisiting).** Lean
checks phases (`checkMeta`, `Lean/Compiler/LCNF/Visibility.lean`) on a declaration's initial LCNF,
before inlining and specialisation. The `.ir` files hold IR after both: they contain the calls of
other modules' inlined bodies (some private, which would demand `import all`) and lack the inlined
functions themselves. Those are exactly the `@[inline]`/`@[specialize]` effects to be ignored for
now (Thomas). The oleans keep base LCNF only for template-like declarations (`baseExt`). The value
references of a declaration with code are a superset of its base LCNF references, apart from
compiler substitutions: `@[implemented_by]` is handled, `@[csimp]` is not. So code needs stay
approximated by value references. Their only excess is references in erased parts (proofs inside
definitions), which may demand a runtime import where a `meta import` alone exists. The Batteries
test builds with this.

**Meta code (Thomas: read the module system quickstart, ignoring `@[inline]` and `@[specialize]`
for now).** From "Quickstart: The Module System" (leanprover-community.github.io/extras), the rules
step C must model:
* Code has a phase. Meta code may reference only meta code, runtime code only runtime code, and
  types and proofs are ignored.
* `meta import` lifts the imported runtime code to the meta phase, and nothing lowers meta code.
  Intrinsically meta code arrives as meta under any import.
* Meta code is presentable (usable downstream) or not, inferred from what it references.
  * Presentable code may reference only presentable code, and a public meta def must be
    presentable.
  * A private meta def may serve a public one only if its own references are presentable.
  * `public (meta) import` provides presentable code as presentable, a plain `(meta) import` as
    unpresentable.

## ImportGraph at `HEAD`

Findings from reading upstream ImportGraph at `b9ec7f6` (2026-11-20, toolchain `v4.37.0-rc1`),
mostly Thomas's `ImportGraph/Shake/` and `ImportGraph/WorkspaceModel/`. Facts only; how agitate
relates to them is open (TODO). Paths are in that repository.

* **Needs algebra.** `Shake/Core.lean` copies shake's types and adds `privOfPriv` kinds (`import
  all` as an arrow, not a special case). `Shake/Algebra.lean` composes them: `Hierarchy` (a
  `Provides` per module), `≫` (composition), `𝓘⟦n⟧` (transitive closure), `linearize`
  (`public` ⊆ `private`), and `Needs.reduce` (minimal imports). `ImportNeeds`
  (`Shake/DeclNeeds.lean:178-196`) splits each visibility by phase: runtime, meta or phaseless.
* **Declaration needs.** `DeclNeeds` (`Shake/DeclNeeds.lean:569-661`) maps each declaration to
  typed needs (`DeclDeclNeedsKind`, `:460-501`): `expr` (type or value), `runtimeIR`, `metaIR`, or
  `comptime` (syntax kinds with source ranges, or indirect module uses).
  * Same-module uses are kept apart from imported ones (`freeDecls` and `fixedDecls`), and
    auto-generated declarations are linked to their parents (`isDeclNeedsAutoDecl`, `:818-825`: a
    `_` component and no declaration range, the same signal agitate's items use).
  * `Stance` (`:530-551`) and `Stance.toImportNeedsKind` (`:762-790`) turn a need into an import
    kind.
  * The needs are computed in an elaborated environment: from terms (`calcDeclConstInfoNeeds`), from
    the command's syntax (`calcSyntaxNeeds`) and from LCNF (`calcIRNeeds`). Extra module uses are
    captured per command (`withElabCommandCapturingNeeds`, `:952-974`), which is finer than per
    module but still names no declaration.
  * Reserved names are dropped as in shake (`getDepConstName?`, `:87-93`), not redirected as in
    agitate.
* **Hierarchies.** Two sources:
  * `Shake/Environment.lean` builds one from the loaded environment's imports (`mkTransDeps`). The
    file notes that this sees only what is loaded.
  * `WorkspaceModel` (`WorkspaceModel/Model.lean`, `Build.lean`) parses every source header of the
    workspace and the toolchain into modules, libraries and packages, with `transDeps`, `prevs` and
    depths. A `lake` subprocess produces a summary, cached as JSON. Its future work lists "reading
    oleans when available instead of re-parsing imports" (`Build.lean`, module docstring).
* **Tools.** `#min_imports` and `#show_imports` use the environment hierarchy. `#find_home` and
  `#import_diff` use `WorkspaceModel` with `ImportNeeds.providersByLib`. All of them work on one
  file or one command, interactively.
* **`Bitset`** is shake's `Nat` (`Shake/Core.lean:41-65`). Iteration takes `log2` and clears the bit
  per element (`Shake/Basic.lean:72-95`).

## Rejected / deferred

* **Assembling a real `Environment` from `readModuleData` output in order to call core's
  `isReservedName`.** Rejected. It would rebuild `finalizeImport`'s maps and depend on
  `Environment`'s private fields, i.e. `finalizeImport` in disguise. The port plus `agitate-check`
  gives the same exactness, verified.
* **A best-effort, suffix-based approximation of reserved names.** Rejected. The exact port was not
  much more work and keeps the differential test meaningful.
* **Encoding non-module imports as `public import`s to reuse `Shake.visitModule`.** Rejected: plain
  imports decode as private and would stop the closure after one hop, and every place that cares
  (printing, `--fix` matching, meta inference) would need patching. The single-kind visit step is
  shorter and clearer.
* **Preresolved names as indirect uses of the macro's declaration (proposed by Thomas;
  summarized).** Deferred until Lean
  can express it. With today's `IndirectModUse`, the macro's module can only name itself as the
  target (see "Preresolved names in quotations", part 2 of the ideal solution).
* **Agitate emulating those indirect uses per module (Claude).** Not pursued. A use site's recorded
  uses name only the macro's module, not the macro. So agitate would have to charge every user of
  that module with every name preresolved anywhere in it: sound, but coarse. The extra module use
  in the macro's own module covers non-module code completely, because imports re-export.
* **Native (C) bitset helpers via `extern`.** Deferred. The `ByteArray` bitset brought the loop
  from 82 s to 2.7 s; revisit if the loop matters again.
* **Porting ImportGraph's `RequiredModules` for `percolate` (Claude).** Done, then removed: Thomas
  meant ImportGraph's newer `Shake/` and `WorkspaceModel/` code (see "`Agitate.ImportGraph`").
  Depending on or adapting that code is open.
* **One coarse "unattributed" status for module-level uses (Claude).** Replaced by `candidate`
  and `moduleUse`: on the fixture it marked every declaration of a module used once by `simp`.
