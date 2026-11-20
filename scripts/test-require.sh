#!/usr/bin/env bash
# Copyright (c) 2026 Thomas Murrills. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Regression test: a project that `require`s agitate and has its own `Main` executable root.
# Lake puts dependencies before the root package on LEAN_PATH/LEAN_SRC_PATH, so resolving modules
# through those paths made the project's `Main` resolve to agitate's own `Main`. agitate resolves
# modules through the Lake workspace, root package first; it must analyse the project's `Main`
# (and only report the project's files), both run directly and through `lake env`.
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
(cd "$root" && lake build agitate >/dev/null)
agitate="$root/.lake/build/bin/agitate"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
cd "$work"
cp "$root/lean-toolchain" .
cat > lakefile.toml <<EOT
name = "clash"
defaultTargets = ["Clash", "clash"]

[[require]]
name = "agitate"
path = "$root"

[[lean_lib]]
name = "Clash"

[[lean_exe]]
name = "clash"
root = "Main"
EOT
printf 'module\n\npublic def clash : Nat := 1\n' > Clash.lean
printf 'module\n\n-- `Clash` is used; `Init.Data.List.Basic` is not.\npublic import Clash\npublic import Init.Data.List.Basic\n\npublic def main : IO Unit := IO.println clash\n' > Main.lean
lake build > build.log 2>&1 || { echo "scratch project failed to build"; tail build.log; exit 1; }
fail=0
for how in direct "lake env"; do
  if [[ "$how" == direct ]]; then out="$("$agitate" Main Clash 2>&1 || true)"
  else out="$(lake env "$agitate" Main Clash 2>&1 || true)"; fi
  if echo "$out" | grep -q "^$(pwd -P)/Main.lean:" && echo "$out" | grep "remove #\[" | grep -q "Init.Data.List.Basic" \
      && ! echo "$out" | grep -q "$root"; then
    echo "$how: analyses the project's own Main"
  else
    echo "$how: WRONG MODULE OR ERROR:"; echo "$out" | head -10; fail=1
  fi
done
exit $fail
