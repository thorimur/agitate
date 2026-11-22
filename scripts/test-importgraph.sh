#!/usr/bin/env bash
# Copyright (c) 2026 Thomas Murrills. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Tests of `Agitate.ImportGraph`: builds `AgitateTest.ImportGraph`, whose `#guard`s are the tests.
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$root"
lake build Agitate.ImportGraph AgitateTest.ImportGraph >/dev/null && echo "AgitateTest.ImportGraph: passed"
