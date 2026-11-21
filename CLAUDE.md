# Working agreements for agitate

* Thomas owns this project; record decisions, measurements and their reasons in `DESIGN.md`, open
  work in `TODO.md`, current behaviour in `README.md`, updated in the same commit as the change.
* Parity with `lake shake` (same toolchain) is the correctness bar, except for deliberate fixes,
  which Thomas prefers over reproducing upstream bugs. Each fix must be recorded in DESIGN.md and
  must keep an upstream-compatible flag.
* After changes to shared code (`Agitate/{Args,Bitset,Header,Index,Refs,Reserved}.lean`), to
  `Agitate/NonModule.lean`, or to `modulate` (conversion code in `Agitate/Shake.lean`), run `scripts/test-fixture-nonmodule.sh` and
  `scripts/test-batteries-nonmodule.sh <mathlib4>/.lake/packages/batteries`.
* After changes to module resolution (`Agitate/Workspace.lean`, `Agitate/Args.lean`), also run
  `scripts/test-require.sh`.
* After any change to the analysis, run `scripts/test-fixture.sh`, `scripts/compare-core.sh` and
  `scripts/compare.sh` on Batteries; both must report IDENTICAL for the `--compat` run. Every new deviation from `lake shake` must be
  switched off by `--compat`. After changes to
  `Agitate/Index.lean` or `Agitate/Reserved.lean`, also run `agitate-check`. Move to Mathlib only
  once those pass (Thomas's order: Batteries first, Mathlib when everything works).
* Commit regularly (Thomas): after each completed and tested change, with its record updates in
  the same commit.
* Every new source file (Lean, scripts, fixtures) gets the Apache 2.0 copyright header. Code
  copied or ported from Lean keeps the original copyright lines and authors, adds Thomas's, and
  says what changed.
* Back performance claims with `--profile` numbers or a `sample` profile, not reasoning alone.

## Benchmark setup

* Mathlib `v4.33.1` (shallow clone plus `lake exe cache get`) lives in the session scratchpad as
  `mathlib4/`. Batteries is tested from inside it (`.lake/packages/batteries`), since Batteries has
  no `v4.33.1` tag but Mathlib pins a matching commit. The scratchpad can be wiped; re-clone if it
  is gone.
* This machine evicts the page cache aggressively: run Mathlib profiles twice back to back and
  report ranges. Cold-cache behaviour matters too (CI starts cold).
* Run long Mathlib comparisons on a copied binary (`AGITATE=…`) in the background, so rebuilding does
  not change the binary mid-run.

## Pitfalls

* Oleans are version-locked: benchmarks need projects built with exactly `v4.33.1`.
* Upstream source for comparison is the `v4.33.1` tag of the local Lean checkout
  (`git show v4.33.1:src/lake/Lake/CLI/Shake.lean`), not its working tree.
* `.olean.private` points into the `.olean` and `.olean.server` regions: read the three together
  with `readModuleDataParts`, not separately with `readModuleData`. Never map the same `.olean`
  twice: the second mapping misses its fixed base address and falls back to `read()` plus
  relocation.
* Reserved-name predicates come from `builtin_initialize`; they are registered only because the
  emitted `main` calls `lean_initialize()` (all of `Lean`). Keep `Main` using the Lean API.
* `lake shake`'s `augmentedLeanSrcPath` does not include the toolchain's `src/lean`; set
  `LEAN_SRC_PATH` explicitly when running `lake shake` on core (the compare script does). agitate
  itself never reads `LEAN_PATH`/`LEAN_SRC_PATH`: it resolves modules through the Lake workspace.
* The Bash tool's shell is zsh: unquoted `$flags` is not word-split (use `${=flags}`), and
  `2>&1 >/dev/null` behaves differently from bash (wrap the command in a subshell).
* `x matches p` inside a `match` arm swallows the following arms; parenthesise it.
* `agitate-check` is a default target so that `lake build` keeps it current. A stale checker run
  under `lake env` once still passed through `LEAN_PATH` after module resolution had moved to the
  Lake workspace. Run the checker directly, not under `lake env`.
* `--profile` serialises phases, so its total exceeds the normal wall time.
