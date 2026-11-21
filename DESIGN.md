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
`recordExtraModUse*` call site is in `Quotation.lean` or `ResolveName.lean`. Compare `` ``foo ``,
whose elaborator records a private non-meta use (`Lean/Elab/BuiltinTerm.lean:258-263`). So if a
quotation is the only use of an import, shake removes the import. The quotation's own module still
builds, because preresolution simply finds nothing. The breakage shows up at every expansion site.
With no preresolved candidates, `resolveName` falls back to `realizeGlobalName`
(`Lean/Elab/Term/TermElabM.lean:2189-2192`). That lookup puts the macro scopes back onto the name
(`Lean/ResolveName.lean:196-201`), so no global matches: ``Unknown identifier `quotTarget✝` ``.
It fails even where shake added a direct import of the declaring module (verified on the fixture
with `lake shake --fix`, `v4.33.1`). `notation` happens to be covered: its generated
`@[app_unexpander a]` records `a` through the attribute key (`Lean/KeyedDeclsAttribute.lean:35`).
`macro`, `macro_rules`, `elab` and hand-written metaprograms are not covered.

**Workaround (Thomas: "an ordinary extra mod use, for now"), `Agitate/Preresolved.lean`.** Both
tools synthesize the extra module use that Lean would record if `quoteSyntax` behaved like
`` ``foo ``:

* For every `Syntax.Preresolved.decl n _` in a declaration's value whose `n` is a closed `Name`
  term, the declarer of `n` becomes a need of the module. The name is resolved like a constant
  reference (`resolveRef`, `Resolved.forModule`), so reserved names and duplicates behave the same.
* **Kind (Thomas):** public if the declaration containing the quotation is exported, private
  otherwise; never meta. The name is data to the metaprogram, not code it runs, and expansion
  sites elaborate it in the regular phase. A macro's auxiliary definition counts as exported even
  without `public macro`. In the fixture, `QuotMacro` keeps a public import and `QuotHelper`, whose
  quotation is in a private `meta def`, a private one.
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
   of the declaration being elaborated, as `` ``foo `` does. That is all the workaround emulates,
   and agitate would then need no special code: delete `Agitate/Preresolved.lean`.
2. Under the module system, a macro's users need the preresolved declarations as well, and a
   private import in the macro's module does not reach them. The natural carrier is an indirect
   use: "references to macro `m` also need module `F`". Expanding a macro already calls
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
* **Native (C) bitset helpers via `extern`.** Deferred. The `ByteArray` bitset brought the loop
  from 82 s to 2.7 s; revisit if the loop matters again.
