# Copyright (c) 2026 Thomas Murrills. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
"""Convert a copy of a module-system Lean library to non-module code (test data for
`agitate-nonmodule`).

Usage: demodularize.py DIR ROOT

Rewrites every `.lean` file under DIR/ROOT and DIR/ROOT.lean in place:
* `module -- comment` becomes `-- comment` (so `shake:` markers survive);
* `public`/`meta`/`all` are dropped from imports;
* `public section`, `@[expose] public section` and `public meta section` become `section` (some
  are closed by an `end`);
* `public`/`meta` declaration modifiers and the `expose` attribute are dropped.

This is mechanical and only meant for libraries as regular as Batteries; private declarations that
were reached through `import all` need manual handling (see `test-batteries-nonmodule.sh`).
"""
import os
import re
import sys


def convert(s):
    s = re.sub(r'^module[ \t]*(--.*)?$', lambda m: m.group(1) or '', s, count=1, flags=re.M)
    s = re.sub(r'^(public )?(meta )?import (all )?', 'import ', s, flags=re.M)
    s = re.sub(r'^(@\[expose\] )?public (meta )?section[ \t]*$', 'section', s, flags=re.M)
    s = re.sub(r'\bpublic (meta )?(?=(def|theorem|instance|structure|inductive|abbrev|class|opaque'
               r'|axiom|partial|unsafe|noncomputable)\b)', '', s)
    s = re.sub(r'(?m)^(\s*)meta (?=def\b)', r'\1', s)
    s = re.sub(r'@\[expose\]\s*', '', s)
    s = re.sub(r',\s*expose\b', '', s)
    s = re.sub(r'\bexpose,\s*', '', s)
    return s


def main(d, root):
    paths = [os.path.join(d, root + '.lean')]
    for dp, _, fs in os.walk(os.path.join(d, root)):
        paths += [os.path.join(dp, f) for f in fs if f.endswith('.lean')]
    for p in paths:
        with open(p) as f:
            s = f.read()
        t = convert(s)
        if t != s:
            with open(p, 'w') as f:
                f.write(t)
    print(f'converted {len(paths)} files')


if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2])
