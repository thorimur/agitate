#!/usr/bin/env python3
# Copyright (c) 2026 Thomas Murrills. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
"""Reference consumer of `percolate` output, for the tests: deletes the declaration ranges of the
items with the given statuses from their source files.

Usage: delete-items.py <percolate.jsonl> <status>...

Ranges are `Lean.Position`s: lines from 1, columns from 0 in codepoints, `end` exclusive. Items
without a range are left alone, and so are `attribute` commands on deleted declarations
(`attributeCmds`): a real removal tool must delete those too.
"""
import json
import sys
from collections import defaultdict


def main():
    path, statuses = sys.argv[1], set(sys.argv[2:])
    cuts = defaultdict(list)
    with open(path) as f:
        for line in f:
            rec = json.loads(line)
            if rec.get("status") in statuses and rec.get("range") and rec.get("file"):
                cuts[rec["file"]].append(rec["range"])
    for file, ranges in cuts.items():
        with open(file, encoding="utf-8") as f:
            text = f.read()
        lines = text.split("\n")
        starts = [0]
        for l in lines:
            starts.append(starts[-1] + len(l) + 1)

        def offset(p):
            return starts[p["line"] - 1] + p["column"]

        for r in sorted(ranges, key=lambda r: offset(r["start"]), reverse=True):
            text = text[: offset(r["start"])] + text[offset(r["end"]) :]
        with open(file, "w", encoding="utf-8") as f:
            f.write(text)
        print(f"{file}: deleted {len(ranges)} items")


if __name__ == "__main__":
    main()
