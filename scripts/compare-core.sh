#!/usr/bin/env bash
# Differential test on the toolchain's own `Lean` library (no downloads needed); see compare.sh.
#   scripts/compare-core.sh [--profile]
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
cp "$root/lean-toolchain" "$work/"
printf 'name = "shakebench"\n' > "$work/lakefile.toml"
# `lake shake`'s source search path does not include the toolchain's own sources.
export LEAN_SRC_PATH="$(cd "$root" && lean --print-prefix)/src/lean"
"$root/scripts/compare.sh" "$@" "$work" Lean
