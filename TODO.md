# TODO

* `calcNeeds` (now the largest phase on Mathlib, ~5 s parallel). Try one `foldConsts`-style traversal
  per module with a visited set shared across its constants (per `NeedsKind`), instead of a fresh
  pointer-set cache per type and value. Measure first how much sharing there is between constants.
* `visitModule` loop (~2.7 s on Mathlib, sequential). Profile again. Remaining candidates are the
  byte-wise loops in `Bitset.union`/`inter`/`diff` (8-byte words would cut them 8×) and
  `addTransitiveImps` allocating fresh `Needs`.
* Overlap `calcNeeds` with loading: start a module's `calcNeeds` as soon as the index is built,
  rather than after all headers are requested (check what the critical path is).
* Indirect mod uses: choose a default per-kind policy (DESIGN.md, "Indirect module uses"). The
  principled candidate is to ignore kinds whose consumer records its own uses (`simp` and simp sets).
  Validating it needs a Mathlib build with `--fix` applied (see next item).
* End-to-end validation on Mathlib: apply `agitate --fix` to a copy of Mathlib `v4.33.1` and build
  it. This checks that the suggestions actually compile, which no test has done at Mathlib scale.
  It takes hours of machine time, so ask Thomas before running it.
* Report the two reserved-name quirks upstream, and possibly the reserved-reference redirect.
  Deferred: Thomas does not want anything reported for now.
* `agitate-nonmodule`: test on a real non-module project once one on `v4.33.1` is at hand (so far
  only the fixture and a converted Batteries); time it on something Mathlib-sized.
* CLI: decide whether to offer `lake shake`'s up-to-date check as an option (the default trusts
  the oleans, as Thomas wants).
* Later: per-module needs cache keyed by olean hash (incremental runs). `resolveRef` is a pure
  function of the referenced name and the index, which makes this straightforward apart from the
  `transDeps` filter on indirect uses.
