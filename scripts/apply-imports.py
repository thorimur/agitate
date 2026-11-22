#!/usr/bin/env python3
# Copyright (c) 2026 Thomas Murrills. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
"""Reference consumer of `percolate` module records, for the tests: replaces the import lines of each
module whose imports change by the suggested ones.

Usage: apply-imports.py <percolate.jsonl>

The header is everything before the first line of code: blank lines, comments (block comments
included), `module`, and import lines. The import lines are removed, and the new imports go where
the first one was, or else after `module` (or after the leading comments of a non-module file).
"""
import json
import re
import sys

IMPORT = re.compile(r"^(public\s+)?(meta\s+)?import\b")


def header(lines):
    """The index of the `module` line (or None), the indices of the import lines, and the index of
    the last leading comment line before anything else."""
    module, imports, last_comment, depth = None, [], -1, 0
    for i, line in enumerate(lines):
        s = line.strip()
        if depth > 0 or s.startswith("/-"):
            depth += s.count("/-") - s.count("-/")
            if module is None and not imports:
                last_comment = i
            continue
        if not s or s.startswith("--"):
            continue
        if s == "module" and module is None and not imports:
            module = i
        elif IMPORT.match(s):
            imports.append(i)
        else:
            break
    return module, imports, last_comment


def main():
    for line in open(sys.argv[1]):
        rec = json.loads(line)
        if "imports" not in rec or not rec.get("importsChanged") or not rec.get("file"):
            continue
        lines = open(rec["file"], encoding="utf-8").read().split("\n")
        module, imports, last_comment = header(lines)
        if imports:
            at = imports[0]
            lines = [l for i, l in enumerate(lines) if i not in set(imports[1:])]
            lines[at:at + 1] = rec["imports"]
        else:
            at = (module if module is not None else last_comment) + 1
            lines[at:at] = ([""] + rec["imports"]) if rec["imports"] else []
        open(rec["file"], "w", encoding="utf-8").write("\n".join(lines))
        print(f"{rec['file']}: {len(rec['imports'])} imports")


if __name__ == "__main__":
    main()
