#!/usr/bin/env bash
# Copyright (c) 2026 Thomas Murrills. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Tests of `Agitate.ImportGraph`:
# 1. builds `AgitateTest.ImportGraph`, whose `#guard`s are the unit tests;
# 2. with an ImportGraph checkout built with this toolchain (e.g. `<mathlib4>/.lake/packages/importGraph`),
#    compares `Agitate.ImportGraph.Environment` with ImportGraph's own functions on the same environment
#    (`tests/importgraph/VsImportGraph.lean`).
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$root"
lake build Agitate.ImportGraph AgitateTest.ImportGraph >/dev/null && echo "AgitateTest.ImportGraph: passed"
if [[ $# -ge 1 ]]; then
  ig="$(cd "$1" && pwd)"
  [[ -f "$ig/.lake/build/lib/lean/ImportGraph/Imports/RequiredModules.olean" ]] \
    || { echo "no ImportGraph build in $ig (run \`lake build\` there)"; exit 1; }
  LEAN_PATH="$root/.lake/build/lib/lean:$ig/.lake/build/lib/lean" lean tests/importgraph/VsImportGraph.lean
fi
