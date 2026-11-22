#!/usr/bin/env bash
# Copyright (c) 2026 Thomas Murrills. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Tests of `percolate` on `tests/fixture-percolate` (see its modules' comments):
# 1. golden outputs (`tests/fixture-percolate.expected/`; `UPDATE=1` rewrites them, review the diff);
# 2. deleting the `unused` items, then also the `moduleUse` ones (`scripts/delete-items.py`), must
#    leave a fixture that builds, and a second run must report neither status;
# 3. deleting the `candidate` items as well must not build: in this fixture they are all needed.
# Works on fresh copies, so the fixture in the repo is never modified.
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
(cd "$root" && lake build percolate >/dev/null)
tool="$root/.lake/build/bin/percolate"
expected="$root/tests/fixture-percolate.expected"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
fresh() { mkdir -p "$1"; cp -R "$root/tests/fixture-percolate/." "$1/"
  (cd "$1" && lake build >/dev/null 2>&1) || { echo "fixture copy failed to build"; exit 1; }; }
printf '%s\n' seed1 seed2 seedTree seed3 seed4 seed5 seed6 > "$work/seeds"
run() { # run <dir> <args...>: JSON Lines with the workspace path removed
  local d; d="$(cd "$1" && pwd -P)"; shift
  (cd "$d" && "$tool" --seeds "$work/seeds" "$@" | sed "s#$d/##g"); }
fail=0
fresh "$work/base"

echo "== golden outputs"
mkdir -p "$expected"
for flags in "" "--scope Fixture.Base"; do
  name="$(echo "${flags:-default}" | sed 's/^--//; s/ /_/g')"
  # shellcheck disable=SC2086
  run "$work/base" $flags > "$work/$name.jsonl"
  if [[ -n "${UPDATE:-}" ]]; then cp "$work/$name.jsonl" "$expected/$name.jsonl"; fi
  if cmp -s "$work/$name.jsonl" "$expected/$name.jsonl"; then printf '%-24s matches\n' "$name"
  else printf '%-24s DIFFERS\n' "$name"; diff "$expected/$name.jsonl" "$work/$name.jsonl" | head -20 || true; fail=1; fi
done

echo "== deleting items"
for statuses in "unused" "unused moduleUse" "unused moduleUse candidate"; do
  d="$work/del-$(echo "$statuses" | tr ' ' '-')"; cp -R "$work/base" "$d"
  dd="$(cd "$d" && pwd -P)"
  (cd "$dd" && "$tool" --seeds "$work/seeds" > "$work/out.jsonl")
  # shellcheck disable=SC2086
  python3 -I "$root/scripts/delete-items.py" "$work/out.jsonl" $statuses > /dev/null
  if (cd "$d" && lake build > build.log 2>&1); then built=yes; else built=no; fi
  case "$statuses:$built" in
    *candidate:no) echo "deleting $statuses: does not build (as expected)";;
    *candidate:yes) echo "deleting $statuses: BUILDS, but candidates were needed"; fail=1;;
    *:yes) echo "deleting $statuses: builds"
      again="$(cd "$dd" && "$tool" --seeds "$work/seeds" | python3 -I -c '
import json, sys
print(sorted({json.loads(l).get("status") for l in sys.stdin} - {None}))')"
      echo "  second run statuses: $again"
      for s in $statuses; do
        if [[ "$again" == *"'$s'"* ]]; then echo "  second run STILL REPORTS $s"; fail=1; fi
      done;;
    *) echo "deleting $statuses: BUILD FAILED"; grep -m5 error "$d/build.log" || true; fail=1;;
  esac
done
exit $fail
