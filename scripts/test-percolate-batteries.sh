#!/usr/bin/env bash
# Copyright (c) 2026 Thomas Murrills. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Tests `percolate`'s imports at scale: on a copy of Batteries (module system), the imports it
# suggests when nothing is deleted (`--delete none`), applied with `scripts/apply-imports.py`, must
# build, and a second run must suggest no further change. Also counts how the suggestions compare
# with `agitate --fix` (shake) on the same copy.
# Usage: test-percolate-batteries.sh <batteries-dir>   (e.g. <mathlib4>/.lake/packages/batteries)
set -euo pipefail
src="$(cd "$1" && pwd)"
root="$(cd "$(dirname "$0")/.." && pwd)"
(cd "$root" && lake build percolate agitate >/dev/null)
tool="$root/.lake/build/bin/percolate"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
mkdir "$work/b" && cp -R "$src/Batteries" "$src/Batteries.lean" "$work/b/"
cd "$work/b"
cp "$root/lean-toolchain" .
printf 'name = "batteries"\n\n[[lean_lib]]\nname = "Batteries"\n' > lakefile.toml
lake build Batteries > build.log 2>&1 || { echo "copy does not build:"; grep -m10 error build.log; exit 1; }
echo "copy builds ($(find .lake/build/lib/lean -name '*.olean' | wc -l | tr -d ' ') oleans)"
seed=List.takeDTR_go_eq
"$tool" --seed "$seed" --delete none Batteries > first.jsonl
# for comparison: the imports `agitate --fix` (shake) gives, on a second copy
cp -R "$work/b" "$work/s" && (cd "$work/s" && "$root/.lake/build/bin/agitate" --fix Batteries > /dev/null 2>&1 || true)
python3 -I - "$work/s" first.jsonl <<'PY'
import json, re, sys
imp = re.compile(r"^(public\s+)?(meta\s+)?import\b")
same = total = 0
for line in open(sys.argv[2]):
    r = json.loads(line)
    if "imports" not in r: continue
    total += 1
    path = sys.argv[1] + "/" + r["module"].replace(".", "/") + ".lean"
    shake = {l.strip().split(" --")[0].strip() for l in open(path) if imp.match(l.strip())}
    same += shake == set(r["imports"])
print(f"same imports as agitate --fix in {same} of {total} modules")
PY
python3 -I "$root/scripts/apply-imports.py" first.jsonl > applied.txt
echo "percolate --delete none: imports change in $(wc -l < applied.txt | tr -d ' ') modules"
if lake build Batteries > fixed.log 2>&1; then echo "result: builds"
else echo "result: BUILD FAILED"; grep -m10 error fixed.log; exit 1; fi
again="$("$tool" --seed "$seed" --delete none Batteries | python3 -I -c '
import json, sys
print([r["module"] for r in map(json.loads, sys.stdin) if r.get("importsChanged")])')"
if [[ "$again" == "[]" ]]; then echo "a second run suggests no change"
else echo "a second run STILL CHANGES: $again" | head -c 600; echo; exit 1; fi
