#!/usr/bin/env bash
# Copyright (c) 2026 Thomas Murrills. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Tests of `agitate-nonmodule` on `tests/fixture-nonmodule` (see its modules' comments). There is no
# oracle (`lake shake` refuses non-module code), so:
# 1. golden outputs for several flag sets (`tests/fixture-nonmodule.expected/`; `UPDATE=1` rewrites
#    them, review the diff before committing);
# 2. `--fix` results (default and `--keep-prefix`) must build, and a second run must suggest nothing;
# 3. with `--ignore-indirect-kind simp` the `--fix` result must build, with `instance` it must not.
# Works on fresh copies, so the fixture in the repo is never modified.
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
(cd "$root" && lake build agitate-nonmodule >/dev/null)
tool="$root/.lake/build/bin/agitate-nonmodule"
expected="$root/tests/fixture-nonmodule.expected"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
fresh() { mkdir -p "$1"; cp -R "$root/tests/fixture-nonmodule/." "$1/"
  (cd "$1" && lake build >/dev/null 2>&1) || { echo "fixture copy failed to build"; exit 1; }; }
run() { # run <dir> <args...>: tool output with the workspace path removed
  local d; d="$(cd "$1" && pwd -P)"; shift
  (cd "$d" && lake env "$tool" "$@" 2>&1 | sed "s#$d/##g") || true; }
fail=0
fresh "$work/base"

echo "== golden outputs"
mkdir -p "$expected"
for flags in "" "--explain" "--keep-prefix" "--keep-implied" "--gh-style" "--only Fixture.Unused"; do
  name="$(echo "${flags:-default}" | sed 's/^--//; s/ --/_/g; s/ /_/g')"
  # shellcheck disable=SC2086
  run "$work/base" $flags Fixture > "$work/$name.out"
  if [[ -n "${UPDATE:-}" ]]; then cp "$work/$name.out" "$expected/$name.out"; fi
  if cmp -s "$work/$name.out" "$expected/$name.out"; then printf '%-24s matches\n' "$name"
  else printf '%-24s DIFFERS\n' "$name"; diff "$expected/$name.out" "$work/$name.out" | head -20 || true; fail=1; fi
done

echo "== --fix"
for flags in "" "--keep-prefix"; do
  d="$work/fix$(echo "$flags" | tr -d ' -')"; cp -R "$work/base" "$d"
  # shellcheck disable=SC2086
  run "$d" $flags --fix Fixture > /dev/null
  label="--fix${flags:+ $flags}"
  if (cd "$d" && lake build > build.log 2>&1); then echo "$label result: builds"
  else echo "$label result: BUILD FAILED"; grep -m5 error "$d/build.log" || true; fail=1; fi
  # shellcheck disable=SC2086
  again="$(run "$d" $flags Fixture)"
  if [[ -z "$again" ]]; then echo "$label result: a second run suggests nothing"
  else echo "$label result: a second run STILL SUGGESTS:"; echo "$again" | head; fail=1; fi
done

echo "== indirect-use kinds"
for kind in simp instance; do
  d="$work/no$kind"; cp -R "$work/base" "$d"
  run "$d" --ignore-indirect-kind "$kind" --fix Fixture > /dev/null
  if (cd "$d" && lake build > build.log 2>&1); then built=yes; else built=no; fi
  case "$kind:$built" in
    simp:yes) echo "--ignore-indirect-kind simp --fix result: builds, as expected" ;;
    instance:no) echo "--ignore-indirect-kind instance --fix result: fails to build, as expected ($(grep -m1 -o 'Fixture/[A-Za-z/]*\.lean' "$d/build.log"))" ;;
    *) echo "--ignore-indirect-kind $kind --fix result: UNEXPECTED (builds: $built)"; fail=1 ;;
  esac
done
exit $fail
