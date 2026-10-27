#!/usr/bin/env python3
"""gen_setup_v4.py NAME OUT.json BASE.json [--full DIR]... [DIR...] (v4 = v3 + --full DIR: modules found
under such a DIR get every olean part present next to their .olean ([.olean, .olean.server, .olean.private]), e.g. the
start-record data module that the root imports with `import all`; modules under a plain DIR get the public .olean only).
Starts from BASE.json's importArts; a later DIR overrides an earlier entry for the same module only if it is --full
(public-only entries never replace anything). Module name = path relative to its DIR, '/' -> '.', minus .olean."""
import json, os, sys
name, out, base, rest = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4:]
arts = json.load(open(base))['importArts']
nb, full_n = len(arts), 0
i = 0
while i < len(rest):
    full = rest[i] == '--full'
    d = os.path.abspath(rest[i + 1] if full else rest[i])
    i += 2 if full else 1
    for root, _, files in os.walk(d):
        for f in files:
            if not f.endswith('.olean'):
                continue
            p = os.path.join(root, f)
            m = os.path.relpath(p, d)[:-len('.olean')].replace(os.sep, '.')
            if full:
                parts = [p] + [p + e for e in ('.server', '.private') if os.path.exists(p + e)]
                if len(parts) != 3:
                    sys.exit('ERROR: --full module %s lacks a part: %s' % (m, parts))
                arts[m] = [parts]; full_n += 1
            elif m not in arts:
                arts[m] = [[p]]
            elif arts[m][0][0] != p:
                sys.exit('ERROR: module %s at two paths: %s %s' % (m, arts[m][0][0], p))
with open(out, 'w') as fh:
    json.dump({'name': name, 'isModule': True, 'importArts': arts, 'dynlibs': [], 'plugins': [], 'options': {}}, fh)
print('setup %s: %d modules (%d from base; %d with all 3 parts)' % (out, len(arts), nb, full_n))
