# regen_check_k26f.py CERT_PREFIX SCRATCH M1 M2 ...: regenerate the packed data modules M1, M2, ... from the certificate
# with tools/mkdata_k26f.py's own pack function (into SCRATCH/data) and compare their sha256 with data/MANIFEST.tsv.
import hashlib, os, runpy, sys
cert, scratch, mods = sys.argv[1], sys.argv[2], [int(x) for x in sys.argv[3:]]
man = {}
for line in open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "data", "MANIFEST.tsv")):
    p = line.rstrip("\n").split("\t"); man[int(p[0])] = p[5]
os.makedirs(os.path.join(scratch, "data"), exist_ok=True)
sys.argv = ["mkdata_k26f.py", cert, scratch, "1"]
g = runpy.run_path(os.path.join(os.path.dirname(os.path.abspath(__file__)), "mkdata_k26f.py"), run_name="regen")
bad = 0
for m in mods:
    row = g["pack"](m)
    ok = row[5] == man[m]; bad += not ok
    print("module %d records %d..%d sha256 %s %s" % (m, row[1], row[1] + row[2] - 1, row[5], "MATCH" if ok else "DIFF"))
print("regen check: %d modules, %d differ" % (len(mods), bad))
sys.exit(1 if bad else 0)
