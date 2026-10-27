#!/bin/bash
# dbuild30e_m4.sh R P: build the K30E data modules in module-system form, P at a time (2026-10-25).
# Uses gen_data30e_m4.py (hidden bodies) and kbuild_v1.sh from this directory. Resumable: modules with an "rc=0" line
# in R/logs/dbuild.txt are not rebuilt, and new lines are appended.
# R holds data/ (the export: m%05d.bin + MANIFEST.tsv) and src/ with the library sources Saw38aCore/Check.lean and
# Saw38aK/{CheckK,Lit,LitBin}.lean (copies of ../../../src). Oleans go to R/build (the only search root).
#  1. library modules; 2. gen_data30e_m4.py (sources K30EData.M%05d, and Top.lean, which is NOT built here);
#  3. every data module not yet built, P at a time (one line per module in R/logs/dbuild.txt; all must be rc=0);
#  4. R/build/DATA_OLEAN_SHA256SUMS: sha256 of every K30EData olean and ilean.
set -euo pipefail
R=${1:?R}; P=${2:?P}
D=$(cd "$(dirname "$0")" && pwd)
bash "$D/kbuild_v1.sh" "$R" Saw38aCore.Check Saw38aK.CheckK Saw38aK.Lit Saw38aK.LitBin
python3 "$D/gen_data30e_m4.py" "$R/data/MANIFEST.tsv" "$R/src" --top
NM=$(wc -l < "$R/data/MANIFEST.tsv")
touch "$R/logs/dbuild.txt"
awk '$2 == "rc=0" {sub("K30EData.M", "", $1); print $1 + 0}' "$R/logs/dbuild.txt" | sort -u > "$R/logs/dbuild_done.txt"
seq 0 $((NM - 1)) | sort | comm -23 - "$R/logs/dbuild_done.txt" | sort -n > "$R/logs/dbuild_todo.txt"
echo "already built: $(wc -l < "$R/logs/dbuild_done.txt"); to build: $(wc -l < "$R/logs/dbuild_todo.txt")"
xargs -P "$P" -I{} sh -c "bash $D/kbuild_v1.sh $R K30EData.M\$(printf %05d {}) | tail -1" < "$R/logs/dbuild_todo.txt" \
  >> "$R/logs/dbuild.txt"
ok=$(awk '$2 == "rc=0" {print $1}' "$R/logs/dbuild.txt" | sort -u | wc -l)
[ "$ok" -eq "$NM" ] || { echo "data modules built: $ok of $NM"; exit 1; }
(cd "$R/build" && find K30EData -name "M*.olean*" -o -name "M*.ilean" | sort | xargs sha256sum) > "$R/build/DATA_OLEAN_SHA256SUMS"
echo "data modules: $ok; sums: $(wc -l < "$R/build/DATA_OLEAN_SHA256SUMS") files"
