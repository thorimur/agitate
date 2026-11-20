#!/usr/bin/env bash
# Copyright (c) 2026 Thomas Murrills. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Differential test against `lake shake` in an arbitrary workspace built with this toolchain.
#
#   scripts/compare.sh [--profile] <workspace-dir> <module>...
#
# 1. `agitate --compat` must match `lake shake --force` byte for byte (stdout + exit code).
# 2. Report how agitate's default mode (with its documented fixes) differs from `lake shake`.
# Wall-clock times of both tools are printed; `--profile` also prints agitate's phase timings.
# Outputs are kept in $OUT (default: a fresh temp dir), whose path is printed.
# Set AGITATE=<binary> to test a specific (e.g. frozen) agitate binary instead of building this one.
set -euo pipefail
profile=0
if [[ "${1:-}" == "--profile" ]]; then profile=1; shift; fi
ws="$(cd "$1" && pwd)"; shift
root="$(cd "$(dirname "$0")/.." && pwd)"
if [[ -n "${AGITATE:-}" ]]; then
  agitate="$(cd "$(dirname "$AGITATE")" && pwd)/$(basename "$AGITATE")"
else
  (cd "$root" && lake build agitate >/dev/null)
  agitate="$root/.lake/build/bin/agitate"
fi
out="${OUT:-$(mktemp -d)}"
mkdir -p "$out"
echo "outputs in $out"
cd "$ws"
timed() { # timed <name> <cmd...>: run, keep stdout in $out/<name>.out, report wall time, return exit code
  local name="$1"; shift
  local t0 t1 rc=0
  t0=$(python3 -c 'import time; print(time.time())')
  "$@" > "$out/$name.out" 2> "$out/$name.err" || rc=$?
  t1=$(python3 -c 'import time; print(time.time())')
  printf '%-16s exit %d  %6.2fs\n' "$name" "$rc" "$(python3 -c "print($t1-$t0)")"
  return $rc
}
lake_rc=0; compat_rc=0
timed lake-shake lake shake --force "$@" || lake_rc=$?
timed agitate-compat lake env "$agitate" --compat "$@" || compat_rc=$?
timed agitate lake env "$agitate" "$@" || true
if [[ $profile -eq 1 ]]; then
  lake env "$agitate" --profile "$@" 2>&1 >/dev/null | grep '^\[profile\]' || true
fi
if [[ $lake_rc -eq $compat_rc ]] && cmp -s "$out/lake-shake.out" "$out/agitate-compat.out"; then
  echo "IDENTICAL with --compat ($(grep -c ':$' "$out/agitate-compat.out" || true) modules reported)"
  if cmp -s "$out/lake-shake.out" "$out/agitate.out"; then
    echo "default mode: identical to lake shake"
  else
    echo "default mode: differs from lake shake (agitate's documented deviations, see DESIGN.md):"
    diff "$out/lake-shake.out" "$out/agitate.out" | head -"${DIFF_LINES:-40}" || true
  fi
else
  echo "DIFFERENT (lake exit $lake_rc, agitate exit $compat_rc)"
  diff "$out/lake-shake.out" "$out/agitate-compat.out" | head -40
  exit 1
fi
