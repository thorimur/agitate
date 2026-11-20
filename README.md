# `agitate` (`shake` faster)

⚠️ This is a small, temporary, **vibe-coded** project to make `lake shake` much faster by avoiding the environment construction and reading directly from oleans. It also shakes non-modules, and does *not* do up-to-date checking for speed.

This part was written by me (Thomas R. Murrills). The rest is Claude.

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
* `--compat`: behave exactly like `lake shake` (the next three options combined).
* `--upstream-reserved`: compute reserved names exactly as `lake shake` does, quirks included.
* `--ignore-reserved-refs`: drop references to reserved names, as `lake shake` does, instead of
  counting them as references to the declaration they are regenerated from.
* `--ignore-indirect-kind <KIND>`: ignore indirect module uses recorded by attribute `KIND`
  (repeatable; `*` for all). By default all kinds count, as in `lake shake`.
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
needed modules are the declarers of referenced constants, recorded extra uses (notation, `simp`
lemmas, …) and reachable indirect uses. It takes the options above except `--keep-public`,
`--add-public`, `--upstream-indirect` and `--compat`. `shake: keep` goes on an import line as
usual; `shake: keep-all` and `shake: keep-downstream` go in any comment in the header, since there
is no `module` token to attach them to. Imports of module-system code (such as core) work as usual.

Shake cannot see dependencies that leave no trace in the oleans, such as `open` of a namespace
whose declarations are otherwise unused. Mark such imports `-- shake: keep`. `lake shake` has the
same blind spot.

## Layout

* Shared by both tools:
  * `Agitate/Args.lean`: options and the CLI driver.
  * `Agitate/Index.lean`: reads the modules' oleans and answers the queries shake needs.
  * `Agitate/Reserved.lean`: the reserved-name predicates, ported from core.
  * `Agitate/Refs.lean`: resolving referenced constants to modules.
  * `Agitate/Bitset.lean`, `Agitate/Header.lean`: module sets, and source headers and `--fix`.
* `Agitate/Shake.lean` (with `Main.lean`): `agitate`'s analysis, adapted from upstream
  `Lake/CLI/Shake.lean`. Changes are marked `agitate`.
* `Agitate/NonModule.lean` (with `NonModuleMain.lean`): `agitate-nonmodule`'s single-kind analysis.
* `AgitateCheck.lean`: `agitate-check`, the differential checker for the index (below).
* `tests/fixture`, `tests/fixture-nonmodule`: small workspaces whose modules each exercise one
  behaviour (comments say which). `tests/fixture-nonmodule.expected` holds the non-module golden
  outputs.
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
* `scripts/test-fixture-nonmodule.sh` tests `agitate-nonmodule` without an oracle. It checks
  golden outputs (`UPDATE=1` rewrites them; review the diff). The `--fix` results must build, and a
  second run must suggest nothing. Ignoring `simp` indirect uses must still build; ignoring
  `instance` must not.
* `scripts/test-batteries-nonmodule.sh <batteries-dir>` converts a copy of Batteries to non-module
  code (`demodularize.py` plus three documented patches), then checks that it builds, that the
  `--fix` result builds, and that a second run suggests nothing.
* `scripts/test-require.sh` builds a scratch project that `require`s agitate and has its own
  `Main` executable root, and checks that agitate analyses the project's `Main`, both run directly
  and under `lake env`. Before modules were resolved through the workspace, agitate's own `Main`
  shadowed it.
* `.lake/build/bin/agitate-check <MODULE>...` (run in the workspace) compares every index query with core's answer
  on an environment loaded the way `lake shake` loads it, for every imported constant.

## License

Apache 2.0; see `LICENSE`. Parts are copied or ported from Lean 4 (also Apache 2.0): the analysis
from Lake's `shake` (`Lake/CLI/Shake.lean`), and the olean index and reserved-name predicates from
Lean core. Those files keep the original copyright notices and describe their changes.
