#!/usr/bin/env python3
"""gen_setup_v3.py NAME OUT.json BASE.json [DIR...] (v3 = gen_setup_v2 plus a BASE: start from the
importArts of BASE.json, e.g. lib + data publics made once by gen_setup_v2, and add the public .olean of every module under
the DIRs, e.g. one part's ingested units). Module name = path relative to its DIR, '/' -> '.', minus .olean. Exits non-zero
if one module name maps to two different paths."""
import json, os, sys
name, out, base, dirs = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4:]
arts = json.load(open(base))['importArts']
nb = len(arts)
for d in dirs:
    d = os.path.abspath(d)
    for root, _, files in os.walk(d):
        for f in files:
            if f.endswith('.olean'):
                p = os.path.join(root, f)
                m = os.path.relpath(p, d)[:-len('.olean')].replace(os.sep, '.')
                if m in arts and arts[m][0][0] != p:
                    sys.exit('ERROR: module %s at two paths: %s %s' % (m, arts[m][0][0], p))
                arts[m] = [[p]]
with open(out, 'w') as fh:
    json.dump({'name': name, 'isModule': True, 'importArts': arts, 'dynlibs': [], 'plugins': [], 'options': {}}, fh)
print('setup %s: %d modules (%d from base, public .olean only)' % (out, len(arts), nb))
