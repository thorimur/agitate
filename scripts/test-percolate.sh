#!/usr/bin/env bash
# Copyright (c) 2026 Thomas Murrills. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Tests of the `Percolate` library:
# 1. builds `PercolateTest`, whose `#guard`s are the unit tests;
# 2. with an ImportGraph checkout built with this toolchain (e.g. `<mathlib4>/.lake/packages/importGraph`),
#    compares `Percolate.Environment` with ImportGraph's own functions on the same environment
#    (`tests/percolate/VsImportGraph.lean`).
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$root"
lake build Percolate PercolateTest >/dev/null && echo "PercolateTest: passed"
if [[ $# -ge 1 ]]; then
  ig="$(cd "$1" && pwd)"
  [[ -f "$ig/.lake/build/lib/lean/ImportGraph/Imports/RequiredModules.olean" ]] \
    || { echo "no ImportGraph build in $ig (run \`lake build\` there)"; exit 1; }
  LEAN_PATH="$root/.lake/build/lib/lean:$ig/.lake/build/lib/lean" lean tests/percolate/VsImportGraph.lean
fi
