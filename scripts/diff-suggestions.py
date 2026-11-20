# Copyright (c) 2026 Thomas Murrills. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
"""Compare two agitate/lake-shake outputs module by module.

Usage: diff-suggestions.py BASE OTHER [--list]
Prints `changed<TAB>more_removed<TAB>fewer_added`: reported modules whose suggestions differ, and
how many of those have more removals / fewer additions in OTHER. With --list, also prints the
changed modules' section headers.
"""
import re
import sys


def sections(path):
    out, cur = {}, None
    for line in open(path):
        if line.endswith(':\n') and not line.startswith(' '):
            cur = line.rstrip(':\n')
            out[cur] = {'remove': set(), 'add': set()}
        elif cur is not None:
            m = re.match(r'  (remove|add) #\[(.*)\]$', line.rstrip('\n'))
            if m:
                out[cur][m.group(1)] |= {x.strip() for x in m.group(2).split(',') if x.strip()}
    return out


base, other = sections(sys.argv[1]), sections(sys.argv[2])
empty = {'remove': set(), 'add': set()}
changed = [k for k in base.keys() | other.keys() if base.get(k, empty) != other.get(k, empty)]
more_removed = sum(len(other.get(k, empty)['remove']) > len(base.get(k, empty)['remove']) for k in changed)
fewer_added = sum(len(other.get(k, empty)['add']) < len(base.get(k, empty)['add']) for k in changed)
print(f'{len(changed)}\t{more_removed}\t{fewer_added}')
if '--list' in sys.argv:
    for k in sorted(changed):
        print(k)
