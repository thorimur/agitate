#!/usr/bin/env bash
# Copyright (c) 2026 Thomas Murrills. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Real-world test of `agitate-nonmodule`: a non-module conversion of Batteries.
#
#   scripts/test-batteries-nonmodule.sh <batteries-dir>
#
# <batteries-dir> is a Batteries checkout matching the toolchain (e.g. Mathlib v4.36.0's
# `.lake/packages/batteries`). The script converts a copy with `demodularize.py` and applies three
# test-data patches. Two modules reach private core declarations through `import all`, which a
# non-module import cannot, so they are dropped. `Batteries.lean` is marked `shake: keep-all`, so the
# rebuild still covers every module. In Batteries before 2026-10-05, one import gets `shake: keep`,
# because its file only `open`s namespaces, which shake cannot see (`lake shake` suggests the same
# removal on the original). Then:
# the copy must build, the `--fix` result must build, and a second run must suggest nothing.
set -euo pipefail
src="$(cd "$1" && pwd)"
root="$(cd "$(dirname "$0")/.." && pwd)"
(cd "$root" && lake build agitate-nonmodule >/dev/null)
tool="$root/.lake/build/bin/agitate-nonmodule"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
mkdir "$work/b" && cp -R "$src/Batteries" "$src/Batteries.lean" "$work/b/"
cd "$work/b"
cp "$root/lean-toolchain" .
printf 'name = "batteries"\n\n[[lean_lib]]\nname = "Batteries"\n' > lakefile.toml
python3 -I "$root/scripts/demodularize.py" . Batteries
rm Batteries/Lean/Meta/Simp.lean Batteries/Tactic/Lint/Simp.lean
sed -i.bak '/^import Batteries.Lean.Meta.Simp$/d; /^import Batteries.Tactic.Lint.Simp$/d' \
  Batteries.lean Batteries/Tactic/Lint.lean Batteries/Data/DList/Basic.lean
sed -i.bak '1s/^.*$/-- shake: keep-all/' Batteries.lean
# (Batteries before 2026-10-05 only: the file then moved to `batteries-recycling`.)
if [[ -f Batteries/Recycling/MonadSatisfying/Lean.lean ]]; then
  sed -i.bak 's/^import Lean.Elab.Command$/import Lean.Elab.Command -- shake: keep (for `open`)/' \
    Batteries/Recycling/MonadSatisfying/Lean.lean
fi
find . -name '*.bak' -delete
lake build Batteries > build.log 2>&1 || { echo "converted copy does not build:"; grep -m10 error build.log; exit 1; }
echo "converted copy builds ($(find .lake/build/lib/lean -name '*.olean' | wc -l | tr -d ' ') modules)"
lake env "$tool" Batteries > first.out || true
echo "suggestions for $(grep -c ':$' first.out || true) modules"
lake env "$tool" --fix Batteries | tail -1
if lake build Batteries > fixed.log 2>&1; then echo "--fix result: builds"
else echo "--fix result: BUILD FAILED"; grep -m10 error fixed.log; exit 1; fi
again="$(lake env "$tool" Batteries || true)"
if [[ -z "$again" ]]; then echo "a second run suggests nothing"
else echo "a second run STILL SUGGESTS:"; echo "$again" | head; exit 1; fi
