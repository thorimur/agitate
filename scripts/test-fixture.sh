#!/usr/bin/env bash
# Copyright (c) 2026 Thomas Murrills. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Differential and `--fix` tests on the fixture workspace `tests/fixture` (see its modules' comments
# for what each one exercises). Works on fresh copies, so the fixture in the repo is never modified.
#
# 1. `scripts/compare.sh` for a matrix of flag sets (agitate `--compat` must match `lake shake`).
# 2. `--fix`: `lake shake --fix` and `agitate --compat --fix` must print the same and leave identical
#    sources. agitate's default-mode `--fix` result must build; upstream's must not (known bug in its
#    indirect-use check, `Fixture/InstUse.lean`), so that a change there is noticed.
# 3. Indirect-use kinds: with `--ignore-indirect-kind simp` the `--fix` result must still build
#    (`simp` records its own extra module uses, `Fixture/SimpUse.lean`); with
#    `--ignore-indirect-kind instance` it must fail (`Fixture/InstUse.lean`: instance resolution
#    records nothing, so only the indirect use keeps the import).
# 4. Preresolved names: with `--ignore-preresolved` the `--fix` result must fail at
#    `Fixture/QuotUse.lean` (a quotation's only use of an import, `Fixture/QuotMacro.lean`).
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
(cd "$root" && lake build agitate >/dev/null)
agitate="$root/.lake/build/bin/agitate"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
fresh() { # fresh <dir>: a built copy of the fixture
  mkdir -p "$1"; cp -R "$root/tests/fixture/." "$1/"
  (cd "$1" && lake build >/dev/null 2>&1) || { echo "fixture copy failed to build"; exit 1; }
}
fail=0
fresh "$work/base"

echo "== differential runs"
for flags in "" "--explain" "--add-public" "--keep-prefix" "--add-public --keep-prefix" \
    "--keep-implied" "--keep-public" "--gh-style" "--only Fixture.Unused" "--explain --add-public"; do
  printf '%-28s ' "${flags:-(default)}"
  # shellcheck disable=SC2086
  if r=$("$root/scripts/compare.sh" "$work/base" $flags Fixture 2>&1); then
    echo "$r" | grep '^IDENTICAL'
  else
    echo "MISMATCH"; echo "$r" | tail -20; fail=1
  fi
done

echo "== --fix"
for d in lake compat default noSimp noInstance noPreresolved; do cp -R "$work/base" "$work/$d"; done
norm() { sed "s#$1/##g"; }
(cd "$work/lake" && lake shake --force --fix Fixture 2>&1 | norm "$work/lake") > "$work/lake.out" || true
(cd "$work/compat" && lake env "$agitate" --compat --fix Fixture 2>&1 | norm "$work/compat") > "$work/compat.out" || true
(cd "$work/default" && lake env "$agitate" --fix Fixture 2>&1 | norm "$work/default") > /dev/null || true
(cd "$work/noSimp" && lake env "$agitate" --ignore-indirect-kind simp --fix Fixture 2>&1 | norm "$work/noSimp") > /dev/null || true
(cd "$work/noInstance" && lake env "$agitate" --ignore-indirect-kind instance --fix Fixture 2>&1 | norm "$work/noInstance") > /dev/null || true
(cd "$work/noPreresolved" && lake env "$agitate" --ignore-preresolved --fix Fixture 2>&1 | norm "$work/noPreresolved") > /dev/null || true
if cmp -s "$work/lake.out" "$work/compat.out"; then echo "fix output: identical"
else echo "fix output: DIFFERENT"; diff "$work/lake.out" "$work/compat.out" | head; fail=1; fi
if diff -r -x .lake "$work/lake" "$work/compat" > "$work/fix.diff"; then echo "fixed sources: identical"
else echo "fixed sources: DIFFERENT"; head -30 "$work/fix.diff"; fail=1; fi
if (cd "$work/default" && lake build > "$work/default.build" 2>&1); then echo "default --fix result: builds"
else echo "default --fix result: BUILD FAILED"; grep -m5 error "$work/default.build"; fail=1; fi
# Upstream's result is known not to build: its indirect-use check misses uses through public imports
# (`Fixture/InstUse.lean`, DESIGN.md "Indirect module uses"). Report it, but only fail if that changes.
if (cd "$work/compat" && lake build > "$work/compat.build" 2>&1); then
  echo "lake shake (= --compat) --fix result: builds (UNEXPECTED: has the upstream bug been fixed?)"; fail=1
else
  echo "lake shake (= --compat) --fix result: fails to build, as expected ($(grep -m1 -o 'Fixture/[A-Za-z/]*\.lean' "$work/compat.build"); upstream bug)"
fi
if (cd "$work/noSimp" && lake build > "$work/noSimp.build" 2>&1); then
  echo "--ignore-indirect-kind simp --fix result: builds, as expected"
else
  echo "--ignore-indirect-kind simp --fix result: BUILD FAILED (unexpected)"; grep -m5 error "$work/noSimp.build"; fail=1
fi
if (cd "$work/noInstance" && lake build > "$work/noInstance.build" 2>&1); then
  echo "--ignore-indirect-kind instance --fix result: builds (UNEXPECTED)"; fail=1
else
  echo "--ignore-indirect-kind instance --fix result: fails to build, as expected ($(grep -m1 -o 'Fixture/[A-Za-z/]*\.lean' "$work/noInstance.build"))"
fi
if (cd "$work/noPreresolved" && lake build Fixture.QuotUse > "$work/noPreresolved.build" 2>&1); then
  echo "--ignore-preresolved --fix result: Fixture/QuotUse.lean builds (UNEXPECTED)"; fail=1
else
  echo "--ignore-preresolved --fix result: Fixture/QuotUse.lean fails to build, as expected"
fi
echo "== stale sources (oleans are trusted, not checked)"
cp -R "$work/base" "$work/stale"
# An import added to the source after the build, of a module outside the oleans' import closure.
# Upstream panics here (`Option.get!`); agitate must skip it and say nothing about `Fixture/A.lean`.
sed -i.bak 's/^module$/module\n\npublic import Lean.Data.Json/' "$work/stale/Fixture/A.lean"
rm -f "$work/stale/Fixture/A.lean.bak"
(cd "$work/stale" && lake env "$agitate" Fixture > stale.out 2> stale.err) || true
if grep -q PANIC "$work/stale/stale.err"; then
  echo "stale source import: PANIC"; grep -m3 PANIC "$work/stale/stale.err"; fail=1
elif grep -q 'Fixture/A.lean:' "$work/stale/stale.out"; then
  echo "stale source import: suggestions for Fixture/A.lean (UNEXPECTED)"; fail=1
else echo "stale source import: skipped without a panic"; fi
exit $fail
