#!/usr/bin/env bash
# For each kind of indirect module use in the closure of the given modules, measure how much the
# suggestions change when that kind is ignored (`--ignore-indirect-kind`), relative to the default.
#
#   scripts/indirect-kinds.sh <workspace-dir> <module>...
#
# Prints one TSV line per kind: kind, uses, modules recording it, reported modules whose suggestions
# change, and how many of those get more imports removed / fewer imports added. Outputs go to $OUT.
set -euo pipefail
ws="$(cd "$1" && pwd)"; shift
root="$(cd "$(dirname "$0")/.." && pwd)"
if [[ -n "${AGITATE:-}" ]]; then agitate="$AGITATE"; else
  (cd "$root" && lake build agitate >/dev/null); agitate="$root/.lake/build/bin/agitate"; fi
out="${OUT:-$(mktemp -d)}"; mkdir -p "$out"
cd "$ws"
lake env "$agitate" "$@" > "$out/default.out" 2>/dev/null || true
lake env "$agitate" --list-indirect-kinds "$@" > "$out/kinds.tsv"
printf 'kind\tuses\tmodules\tchanged\tmore_removed\tfewer_added\n'
while IFS=$'\t' read -r kind uses mods; do
  lake env "$agitate" --ignore-indirect-kind "$kind" "$@" > "$out/ignore-$kind.out" 2>/dev/null || true
  stats=$(python3 -I "$root/scripts/diff-suggestions.py" "$out/default.out" "$out/ignore-$kind.out")
  printf '%s\t%s\t%s\t%s\n' "$kind" "${uses% uses}" "${mods% modules}" "$stats"
done < "$out/kinds.tsv"
