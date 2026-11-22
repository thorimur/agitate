# `agitate` (`shake` faster)

> [!WARNING]
> This is a small, temporary, **vibe-coded** project to make `lake shake` much faster by avoiding the environment construction and reading directly from oleans. It also shakes non-modules, and does *not* do up-to-date checking for speed.

This part was written by me (Thomas R. Murrills). The rest is Claude, under supervision.

---

A Lean import minimizer: a reimplementation of `lake shake` (Lean `v4.33.1`). It reads `.olean`
files directly instead of importing the whole environment, and it is much faster. On Mathlib it
takes ~12 s where `lake shake` takes ~140 s; on core's `Lean` library, ~1 s instead of 4.5 s.

Its output is byte-identical to `lake shake`'s, except that agitate fixes two bugs in how reserved
names are recognised, and by default it counts references to reserved names as references to the
declaration they are regenerated from. `--compat` restores `lake shake`'s behaviour exactly. See `DESIGN.md` for the design,
measurements and open questions, and `TODO.md` for open work.

`agitate-nonmodule` does the same for code that does *not* use the module system, which
`lake shake` refuses.

## Usage

Build with `lake build`, then run it in the root directory of the project to be checked:

```
/path/to/agitate/.lake/build/bin/agitate [OPTIONS] [MODULE...]
```

agitate loads that Lake workspace itself and resolves modules as Lake's builds do: through the
workspace's packages, root package first, then the toolchain. It does not use `LEAN_PATH` or
`LEAN_SRC_PATH`, so running it under `lake env`, or `require`-ing agitate from the project, makes no
difference. Without modules, the root package's default targets are checked, as `lake shake` does.

The options match `lake shake`: `--keep-implied`, `--keep-prefix`, `--keep-public`, `--add-public`,
`--gh-style`, `--explain`, `--trace`, `--fix` and `--only <MODULE>`. agitate adds:

* `--profile`: print per-phase timings to stderr (runs the phases one after another).
* `--compat`: behave exactly like `lake shake`: `--upstream-reserved`, `--ignore-reserved-refs`,
  `--ignore-implemented-by`, `--upstream-duplicates`, `--ignore-preresolved` and
  `--upstream-indirect`, with no ignored indirect kinds.
* `--upstream-reserved`: compute reserved names exactly as `lake shake` does, quirks included.
* `--ignore-reserved-refs`: drop references to reserved names, as `lake shake` does, instead of
  counting them as references to the declaration they are regenerated from.
* `--ignore-indirect-kind <KIND>`: ignore indirect module uses recorded by attribute `KIND`
  (repeatable; `*` for all). By default all kinds count, as in `lake shake`.
* `--upstream-duplicates`: charge every use of a name declared in several modules (identical
  theorems up to binder annotations) to the first declarer, as `lake shake` does. By default a
  module's own declaration wins, then the copy its environment showed (the last loaded); upstream
  can add an import from outside the module's closure, or keep a copy that elaborates differently.
* `--ignore-preresolved`: do not count names that syntax quotations preresolved, as `lake shake`
  does. By default, `` `(foo) `` in a macro or other metaprogram needs `foo`'s module: non-meta,
  and public if the declaration containing the quotation is exported. Lean records nothing for it,
  so upstream can remove the import, after which every expansion fails with
  ``Unknown identifier `foo✝` `` (see `DESIGN.md`, "Preresolved names in quotations").
* `--upstream-indirect`: count an indirect module use only when the recording module is reached
  through an import of exactly the needed kind, as `lake shake` does. By default a public import
  also satisfies a private need.
* `--list-indirect-kinds`: print the kinds of indirect module uses in the import closure, then exit.

Unlike `lake shake`, at least one module must be given, and there is no check that oleans are up to
date. The exit code is 1 if any edits are suggested (without `--fix`), and 0 otherwise.

## Non-module code: `agitate-nonmodule`

```
/path/to/agitate/.lake/build/bin/agitate-nonmodule [OPTIONS] [MODULE...]
```

Non-module imports re-export everything, so there is one kind of need and no `public`/`meta`:
needed modules are the declarers of referenced constants and of names preresolved by quotations,
recorded extra uses (notation, `simp` lemmas, …) and reachable indirect uses. It takes the options above except `--keep-public`,
`--add-public`, `--upstream-indirect` and `--compat`. `shake: keep` goes on an import line as
usual; `shake: keep-all` and `shake: keep-downstream` go in any comment in the header, since there
is no `module` token to attach them to. Imports of module-system code (such as core) work as usual.

Shake cannot see dependencies that leave no trace in the oleans, such as `open` of a namespace
whose declarations are otherwise unused. Mark such imports `-- shake: keep`. `lake shake` has the
same blind spot.

## Converting to the module system: `modulate`

```
/path/to/agitate/.lake/build/bin/modulate [OPTIONS] [--meta GLOB]... [MODULE...]
```

For each selected non-module file, `modulate` computes from the oleans the imports it would need
as a `module` with `@[expose] public section`, and with `--fix` converts it:
* `module` goes before the imports (with any `shake: keep-all`/`keep-downstream` marker);
* the imports are rewritten in module syntax (`public import`, `import`, `public meta import`, …);
* `@[expose] public section` goes after them, or after an initial module docstring.

`--meta GLOB` (repeatable; Lake globs: `Foo`, `Foo.*` for `Foo` and its submodules, `Foo.+` for
its submodules only) converts the matching files with `public meta section` instead. Use it for
files of metaprograms whose meta-ness nothing records, such as `@[macro …] def` (the `macro`,
`elab` and `syntax` commands are recognised without it). Like core's `script/Modulize.lean`, but
with computed imports and module names instead of paths.

A file can only be converted together with every non-module file it imports. Conversion can still
fail where a module needs more than imports:
* `import all`, for proofs that unfold another module's non-exposed definitions;
* no `private` declarations in exposed bodies;
* split meta and non-meta sections, for files that mix both.

The options above for import analysis also apply, except `--keep-public`, `--add-public`,
`--upstream-indirect` and `--compat`.

## Declaration needs: `percolate`

```
/path/to/agitate/.lake/build/bin/percolate [OPTIONS] (--seed <NAME> | --seeds <FILE>)... [MODULE...]
```

For some seed declarations, `percolate` finds which source declarations of the project
they need, and which they do not, for a tool that deletes the rest. The project is the root
package's modules. Its other options are `--scope <GLOB>` (report only the matching modules; Lake
globs, repeatable), `-o <FILE>` and `--profile`.

It reports **source items**: the span of a source file that deleting a declaration removes. An
item is a maximal declaration range, including its docstring and attributes. It contains every
declaration whose range lies inside it: a structure with its fields and derived instances, a
definition with its `where` helpers. Generated constants (equation lemmas, `_proof_`s, recursors, …)
belong to the item they are generated from, even when they are realised in another module.

An item needs what its constants need, as recorded in the oleans: the constants their types and
values mention, `@[implemented_by]` targets and names preresolved in quotations. These are resolved
as `agitate` resolves them: reserved names to the declaration they are regenerated from, and
duplicated theorems to the copy that was seen. Lean records some uses only per module (notation,
tactics, macros, the lemmas `simp` and `dsimp` used), and uses inside a module not at all. These
give the weaker statuses:

* `needed`: a seed needs it through recorded needs;
* `candidate`: a seed may need it through such a use, and it is of a kind such uses can name
  without leaving a term: a metaprogram (meta, or its type mentions `Lean`), or for non-meta uses
  also an rfl theorem (`@[backward_defeq]`, used by `dsimp`);
* `moduleUse`: a seed may need it only because its module is used;
* `unused`: no seed needs it.

Output is JSON Lines. The first line is a header, `{"format":"percolate/1","seeds":[...]}`; then
there is one line per item of the project's loaded modules, in module order and then source order:

```
{"module":"Fixture.Base","file":"/…/Fixture/Base.lean",
 "range":{"start":{"line":11,"column":0},"end":{"line":15,"column":13}},
 "names":["Point","Point.mk","Point.x","Point.y","instReprPoint.repr","instReprPoint"],
 "status":"needed","usedBy":[0,6],"candidateFor":[1,2,3,4,5],"moduleUseFor":[],
 "attributeCmds":[{"module":"Fixture.Notation","kind":"simp","decl":"Point.sum"}]}
```

* **Range:** lines count from 1 and columns from 0 in codepoints (`Lean.Position`), with `end`
  exclusive. It is `null` for constants with no declaration range.
* **Seed fields:** `usedBy`, `candidateFor` and `moduleUseFor` list seed indices by the level that
  first reaches the item.
* **`attributeCmds`:** the `attribute [kind] decl` commands on the item's declarations in other
  modules. A deletion tool must delete these too. Their ranges are not recorded.

Commands that declare nothing (`open`, `variable`, `example`, …) leave no trace in the oleans and
are the deletion tool's business. `scripts/delete-items.py` is a minimal reference consumer.

## Code for upstream: `Agitate.ImportGraph`

`Agitate/ImportGraph/` depends only on Lean, so that it can move upstream to ImportGraph by
dropping the `Agitate.` prefix from its module and namespace names. It holds:
* strongly connected components, by an iterative Tarjan with no recursion (`Graph.components`);
* label propagation along the edges, over the components (`Graph.flowForward`);
* `Agitate.ImportGraph.Bitset`, the `ByteArray` bitset that agitate uses throughout.

`percolate` uses it.

## Layout

* `Agitate/ImportGraph/` (with `Agitate/ImportGraph.lean`): the upstreamable graph library above;
  `AgitateTest/ImportGraph.lean` holds its unit tests.
* Shared by both tools:
  * `Agitate/Args.lean`: options and the CLI driver.
  * `Agitate/Index.lean`: reads the modules' oleans and answers the queries shake needs.
  * `Agitate/Reserved.lean`: the reserved-name predicates, ported from core.
  * `Agitate/Refs.lean`: resolving referenced constants to modules.
  * `Agitate/Preresolved.lean`: needs from names preresolved by syntax quotations, a workaround
    for uses Lean does not record.
  * `Agitate/Bitset.lean` (an alias of `Agitate.ImportGraph.Bitset`), `Agitate/Header.lean`: module sets,
    and source headers and `--fix`.
* `Agitate/Shake.lean` (with `Main.lean`): `agitate`'s analysis, adapted from upstream
  `Lake/CLI/Shake.lean`. Changes are marked `agitate`.
* `Agitate/NonModule.lean` (with `NonModuleMain.lean`): `agitate-nonmodule`'s single-kind analysis.
* `ModulateMain.lean`: `modulate`, which runs `agitate`'s analysis on non-module oleans
  (`State.converting`).
* `Agitate/Percolate/` (with `PercolateMain.lean`): `percolate`. `Items.lean` groups constants into source
  items, `Needs.lean` computes needs and percolates the seeds, and `Main.lean` holds the CLI and
  output.
* `AgitateCheck.lean`: `agitate-check`, the differential checker for the index (below).
* `tests/fixture`, `tests/fixture-nonmodule`, `tests/fixture-percolate`: small workspaces whose
  modules each exercise one behaviour (comments say which). `tests/fixture-nonmodule.expected` and
  `tests/fixture-percolate.expected` hold golden outputs.
* `scripts/`: the checks below, and `indirect-kinds.sh` (measures how much each indirect-use kind
  changes the suggestions) with its helper `diff-suggestions.py`.

## Checking

* `scripts/compare.sh [--profile] <workspace> [OPTIONS] <MODULE>...` runs `lake shake --force` and
  agitate in a workspace built with this toolchain. It fails unless `agitate --compat`
  matches `lake shake` exactly (stdout and exit code), then shows how agitate's default mode
  differs. Set `AGITATE=<binary>` to test a frozen binary while rebuilding.
* `scripts/compare-core.sh [--profile]` does the same on the toolchain's own `Lean` library, with no
  downloads.
* `scripts/test-fixture.sh` runs the comparison on `tests/fixture` for a matrix of flags, and tests
  `--fix`. `lake shake --fix` and `agitate --compat --fix` must leave identical sources. agitate's
  default `--fix` result must build, while upstream's is known not to (an upstream bug, see
  `DESIGN.md`). Ignoring the `simp` kind must still build; ignoring the `instance` kind must not.
  With `--ignore-preresolved`, the result must fail at `Fixture/QuotUse.lean`.
* `scripts/test-fixture-nonmodule.sh` tests `agitate-nonmodule` without an oracle, and `modulate`.
  Without `--meta`, the converted fixture must fail at `Fixture/MetaMacro.lean`; with
  `--meta Fixture.MetaMacro`, it must build. It checks
  golden outputs (`UPDATE=1` rewrites them; review the diff). The `--fix` results must build, and a
  second run must suggest nothing. Ignoring `simp` indirect uses must still build; ignoring
  `instance` must not, and neither must `--ignore-preresolved` (at `Fixture/QuotUse.lean`).
* `scripts/test-batteries-nonmodule.sh <batteries-dir>` converts a copy of Batteries to non-module
  code (`demodularize.py` plus three documented patches), then checks that it builds, that the
  `--fix` result builds, and that a second run suggests nothing.
* `scripts/test-require.sh` builds a scratch project that `require`s agitate and has its own
  `Main` executable root, and checks that agitate analyses the project's `Main`, both run directly
  and under `lake env`. Before modules were resolved through the workspace, agitate's own `Main`
  shadowed it.
* `scripts/test-percolate.sh` tests `percolate` on `tests/fixture-percolate`:
  * golden outputs (`UPDATE=1` rewrites them);
  * deleting the `unused` items, then also the `moduleUse` ones (`scripts/delete-items.py`), must
    leave a fixture that builds, and a second run must report neither status;
  * deleting the `candidate` items as well must not build.
* `scripts/test-importgraph.sh` builds `AgitateTest.ImportGraph`, whose `#guard`s test
  `Agitate.ImportGraph`.
* `.lake/build/bin/agitate-check <MODULE>...` (run in the workspace) compares every index query with core's answer
  on an environment loaded the way `lake shake` loads it, for every imported constant.

## License

Apache 2.0; see `LICENSE`. Parts are copied or ported from Lean 4 (also Apache 2.0): the analysis
from Lake's `shake` (`Lake/CLI/Shake.lean`), the olean index and reserved-name predicates from
Lean core. Those files keep the original copyright notices and describe their changes.
