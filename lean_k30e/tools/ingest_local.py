#!/usr/bin/env python3
"""ingest_local.py: verified ingest of the units' public oleans from a local copy of the run directory (the local-only
form of the ingest step used for the assembly; same checks).

usage: python3 -I ingest_local.py SRC DEST [--items ITEMS.tsv] [--work DIR]
  SRC   a directory with done/P<item> markers and pub/P<item>.<w>.tar parts (w = the builder's name in the marker)
  DEST  assembly unit root: X.olean lands at DEST/<path relative to the build root>
  --items  item map TSV (item, unit module): every listed item needs a marker and exactly these units
A marker counts only if it reads "<w> <time> <n> units olsha <64 hex> out/P<item>.<w>.tar.gz" (7 fields, n > 0, item =
the marker's own name). The part tar must hold exactly the n listed .olean files plus P<item>.olean.sha256; sha256 of
that list must equal the marker's olsha, the list must give .olean/.olean.server/.olean.private for each of the n units,
and every .olean must match its line. An item passes only as a whole; its .olean files are then moved into DEST (an
existing different file there is a conflict). Anything else is a FAILURE: empty, short, malformed or sha-less markers,
missing tar or list, sha mismatches, missing or extra files, count or item mismatches.
Writes DEST/INGEST_MANIFEST.tsv (item, w, module, olean sha256, olsha), DEST/olsha/P<item>.olean.sha256 (the 3-part
lists), WORK/failures.tsv (item, reason). Exit 0 iff no failure."""
import argparse, hashlib, os, re, shutil, sys, tarfile

ap = argparse.ArgumentParser()
ap.add_argument('src'); ap.add_argument('dest')
ap.add_argument('--items', default='')
ap.add_argument('--work', default='')
a = ap.parse_args()
work = os.path.abspath(a.work or os.path.join(a.dest, '..', 'ingest_work'))
os.makedirs(work, exist_ok=True); os.makedirs(os.path.join(a.dest, 'olsha'), exist_ok=True)

def list_done():
    d = os.path.join(a.src, 'done')
    return sorted(os.listdir(d)) if os.path.isdir(d) else []

def read_marker(name):
    p = os.path.join(a.src, 'done', name)
    return open(p, 'rb').read() if os.path.isfile(p) else None

def fetch_part(rel, to):
    p = os.path.join(a.src, rel)
    if not os.path.isfile(p):
        return False
    shutil.copyfile(p, to); return True

sha = lambda b: hashlib.sha256(b).hexdigest()
MK = re.compile(r'^(\S+) (\S+) ([1-9][0-9]*) units olsha ([0-9a-f]{64}) out/(P[^ /]+)\.([^ /]+)\.tar\.gz$')
expect = {}
if a.items:
    for line in open(a.items):
        f = line.rstrip('\n').split('\t')
        if len(f) >= 2 and f[0] and not f[0].startswith('#'):
            expect.setdefault(f[0], set()).add(f[1])
fails, man = [], []

def check(item):
    raw = read_marker(item)
    if raw is None: return 'marker-unreadable'
    if len(raw) == 0: return 'marker-empty'
    if len(raw) < 16: return 'marker-short (%d bytes)' % len(raw)
    txt = raw.decode('utf-8', 'replace').strip()
    if ' olsha ' not in ' %s ' % txt: return 'marker-no-olsha'
    m = MK.match(txt)
    if not m: return 'marker-malformed: %r' % txt[:80]
    w, _, n, olsha, pitem, pw = m.groups()
    n = int(n)
    if pitem != item or pw != w: return 'marker-item-mismatch (%s/%s vs %s/%s)' % (pitem, pw, item, w)
    wd = os.path.join(work, item)
    if os.path.exists(wd): shutil.rmtree(wd)
    os.makedirs(wd)
    tp = os.path.join(wd, 'part.tar')
    if not fetch_part('pub/%s.%s.tar' % (item, w), tp): return 'tar-missing'
    try:
        with tarfile.open(tp) as tf:
            mem = tf.getmembers()
            names = [x.name for x in mem]
            if any(x.name.startswith('/') or '..' in x.name.split('/') or not x.isfile() for x in mem):
                return 'tar-unsafe-member'
            tf.extractall(os.path.join(wd, 'x'), filter='data')
    except (tarfile.TarError, OSError) as e:
        return 'tar-unreadable: %s' % str(e)[:80]
    lname = '%s.olean.sha256' % item
    if lname not in names and './' + lname not in names: return 'list-missing'
    lname_in = lname if lname in names else './' + lname
    lb = open(os.path.join(wd, 'x', lname_in), 'rb').read()
    if sha(lb) != olsha: return 'list-sha-mismatch'
    lines = [l.split() for l in lb.decode().splitlines() if l.strip()]
    if any(len(l) != 2 or not re.fullmatch(r'[0-9a-f]{64}', l[0]) for l in lines): return 'list-malformed'
    norm = lambda q: q[2:] if q.startswith('./') else q
    lst = {norm(l[1]): l[0] for l in lines}
    oleans = sorted(p for p in lst if p.endswith('.olean'))
    for p in oleans:
        for ext in ('.server', '.private'):
            if p + ext not in lst: return 'list-lacks %s%s' % (p, ext)
    if len(oleans) != n or len(lst) != 3 * n: return 'count-mismatch (marker %d, list %d oleans / %d lines)' % (n, len(oleans), len(lst))
    got = sorted(norm(x) for x in names if norm(x) != lname)
    if got != oleans:
        miss = sorted(set(oleans) - set(got)); extra = sorted(set(got) - set(oleans))
        return 'olean-%s' % ('missing ' + miss[0] if miss else 'extra ' + extra[0])
    for p in oleans:
        b = open(os.path.join(wd, 'x', p), 'rb').read()
        if len(b) == 0: return 'olean-empty %s' % p
        if sha(b) != lst[p]: return 'olean-sha-mismatch %s' % p
    mods = {p[:-len('.olean')].replace('/', '.') for p in oleans}
    if expect and item in expect and mods != expect[item]:
        return 'item-mismatch (%d expected, %d in part)' % (len(expect[item]), len(mods))
    for p in oleans:
        t = os.path.join(a.dest, p)
        if os.path.exists(t) and sha(open(t, 'rb').read()) != lst[p]: return 'dest-conflict %s' % p
    for p in oleans:
        t = os.path.join(a.dest, p)
        os.makedirs(os.path.dirname(t), exist_ok=True)
        shutil.move(os.path.join(wd, 'x', p), t)
        man.append((item, w, p[:-len('.olean')].replace('/', '.'), lst[p], olsha))
    open(os.path.join(a.dest, 'olsha', lname), 'wb').write(lb)
    shutil.rmtree(wd)
    return None

markers = list_done()
for item in markers:
    r = check(item)
    if r: fails.append((item, r))
for item in sorted(set(expect) - set(markers)):
    fails.append((item, 'no-marker'))
mp = os.path.join(a.dest, 'INGEST_MANIFEST.tsv')
old_rows = [l.rstrip('\n') for l in open(mp)] if os.path.exists(mp) else []
seen = set(old_rows)
with open(mp, 'a') as fh:
    for row in man:
        line = '\t'.join(row)
        if line not in seen:
            fh.write(line + '\n'); seen.add(line)
with open(os.path.join(work, 'failures.tsv'), 'w') as fh:
    for row in fails:
        fh.write('\t'.join(row) + '\n')
print('markers %d, items ingested %d, units %d, failures %d%s' % (len(markers), len(set(r[0] for r in man)), len(man),
      len(fails), (': ' + '; '.join('%s %s' % f for f in fails[:12])) if fails else ''))
sys.exit(1 if fails else 0)
