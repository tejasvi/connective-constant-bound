#!/usr/bin/env python3
"""gen_setup_v2.py (v2 = v1 + the required empty dynlibs/plugins/options fields) NAME OUT.json DIR...: a `lean --setup` file for module NAME whose importArts give
ONLY the public .olean of every module found under the DIRs (module name = path relative to its DIR, '/' -> '.', minus
.olean), so imports never map .olean.server/.olean.private parts. Modules not listed (Lean core) load from the search
path as usual. Exits non-zero if one module name is found at two different paths."""
import json, os, sys
name, out, dirs = sys.argv[1], sys.argv[2], sys.argv[3:]
arts = {}
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
print('setup %s: %d modules (public .olean only)' % (out, len(arts)))
