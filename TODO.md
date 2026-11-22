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
* End-to-end validation on Mathlib: apply `agitate --fix` to a copy of Mathlib `v4.36.0` and build
  it. This checks that the suggestions actually compile, which no test has done at Mathlib scale.
  It takes hours of machine time, so ask Thomas before running it.
* Preresolved names: propose the Lean-side fix (DESIGN.md, "Preresolved names in quotations"):
  `quoteSyntax` records extra module uses, plus indirect uses that name their target module. Once
  Lean records them, delete `Agitate/Preresolved.lean` and `--ignore-preresolved`. Ask Thomas
  before reporting anything upstream. Before proposing it, measure the default-mode change on all
  of Mathlib (so far only a 70-module slice), in particular how many new public imports of core
  modules elaborators bring in.
* Report the two reserved-name quirks upstream, and possibly the reserved-reference redirect.
  Deferred: Thomas does not want anything reported for now.
* `modulate`: automate the Batteries round trip (DESIGN.md, "Converting non-module files"),
  checking that its failing files stay a subset of core `Modulize.lean`'s. Consider detecting the
  conversion-semantics failures up front: `private` declarations used in exposed bodies are visible
  in the oleans; needs for `import all` are not.
* `modulate`: per-declaration publicity of extra module uses (now all public), if the oleans allow
  it.
* `agitate-nonmodule`: test on a real non-module project once one on `v4.36.0` is at hand (so far
  only the fixture and a converted Batteries); time it on something Mathlib-sized.
* CLI: decide whether to offer `lake shake`'s up-to-date check as an option (the default trusts
  the oleans, as Thomas wants).
* Later: per-module needs cache keyed by olean hash (incremental runs). `resolveRef` is a pure
  function of the referenced name and the index, which makes this straightforward apart from the
  `transDeps` filter on indirect uses.
* `percolate`: the remaining unranged items on Mathlib (1 613, mostly `_auto` and realised
  equation lemmas whose base has no range; DESIGN.md, "Declaration needs").
* `percolate`: ranges of `attribute [kind] decl` commands are not in the oleans; the deletion
  tool has to find them in the source (the records name module, kind and declaration).
* `percolate`: validate on Mathlib by deleting the `unused` (and `moduleUse`) items for some
  seeds and building. That takes hours of machine time, so ask Thomas first.
* Unrecorded uses: propose the Lean-side fix, i.e. keep the declaration that
  `recordExtraModUseFromDecl` already receives, and the using declaration (DESIGN.md, "Declaration
  needs"). It would replace the `candidate` and `moduleUse` approximations. Ask Thomas before
  reporting anything upstream.
* Relate agitate and `percolate` to upstream ImportGraph's `Shake/` and `WorkspaceModel/` (at
  `HEAD`, toolchain `v4.37.0-rc1`): read them fully, then propose to Thomas what to depend on,
  adapt or contribute (DESIGN.md, "`Agitate.ImportGraph`").
* `Bitset.union` (and `∩`, `\`): work on 8-byte words. Unions are 3–20× slower than `Nat.lor`
  (DESIGN.md, "`Agitate.ImportGraph`"); measure before and after.
* `percolate` imports: `@[csimp]` substitutions are code references that terms do not show.
* `percolate` imports: read `-- shake: keep` annotations (`Agitate/Header.lean`); `set_option` of
  options from `register_option` leaves no trace; test non-module files.
* `percolate`: per-declaration extension lookups go through `Index.rawEntries`, whose slot search is
  linear (about 1 000 samples in a Mathlib `sample` profile, via `isDeclMeta'` and `implementedBy?`).
  `Index` is shared code (run `agitate-check`). Stances of used declarations could also be cached per
  module.
* Upstream locations (`.value`): the olean producer always records `.type`. Signals for unfolding
  (`@[defeq]` theorems in other modules, equation lemmas realised downstream) are not pursued for
  now (Thomas: "We don't need to work on measuring unfolding here, though").
* `percolate`: profile the imports' needs phase (0.8 s on Mathlib with three seeds) with `sample`
  before optimizing it.

