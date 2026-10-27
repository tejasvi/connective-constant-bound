#!/bin/bash
# build_part.sh P: build part P (units 256P.., items 16P..min(16P+15, 62218)) from the units' public oleans only.
# Checks and extracts the part's items from a local copy of the run directory (ingest_local.py), writes the part source
# (gen_asm.py part mode) and builds it with `lean --setup` (gen_setup_v3.py: library and data publics + this part's
# units, public .olean files only). Last line: PART p rc stage wall_s rss_mb olean_sha server_sha private_sha
# Environment: LEAN (default: lean); K30E_RUN (local run copy: done/, pub/); K30E_ASM (work directory with
# lists/units_partNNNN.txt from gen_partlists_v1.awk and base_setup.json from gen_setup_v2.py over K30E_LIB and the
# data publics); K30E_ITEMS (default: ../data/items.tsv next to this script).
set -u
p=${1:?P}; P=$(printf %04d "$p"); T=$(cd "$(dirname "$0")" && pwd)
LEAN=${LEAN:-lean}; RUN=${K30E_RUN:?}; A=${K30E_ASM:?}; ITEMS=${K30E_ITEMS:-$T/../data/items.tsv}
u=$A/units/$P; w=$A/work/$P; L=$A/logs/P$P.log
fin() { echo "PART $p $1 $2 ${3:-0} ${4:-0} ${5:--} ${6:--} ${7:--}"; exit 0; }
mkdir -p "$u" "$w" "$A/src/K30EP" "$A/build/K30EP" "$A/setup" "$A/logs"
a=$((16 * p)); b=$((16 * p + 15)); [ $b -gt 62218 ] && b=62218
awk -v a=$a -v b=$b '$1 >= a && $1 <= b {for (s = $2; s < $2 + $3; s++) printf "P%d\tK30ES.D%04d.S%06d\n", $1, int(s / 1000), s}' "$ITEMS" > "$w/items.tsv"
mkdir -p "$w/src/done" "$w/src/pub"
for i in $(seq $a $b); do
  m=$RUN/done/P$i; [ -s "$m" ] || fin 2 nomarker
  cp "$m" "$w/src/done/" || fin 3 copy
  rel=$(awk '{print $NF}' "$m"); x=${rel#out/P$i.}; x=${x%.tar.gz}
  [ -n "$x" ] && [ "$rel" = "out/P$i.$x.tar.gz" ] || fin 4 marker-form
  cp "$RUN/pub/P$i.$x.tar" "$w/src/pub/" || fin 5 nopub
done
python3 -I "$T/ingest_local.py" "$w/src" "$u" --items "$w/items.tsv" --work "$w/ingest" > "$L" 2>&1 || fin 6 ingest
python3 -I "$T/gen_asm.py" part K30EP.P$P K30EData K30EData.Top K30EData.Params "$A/lists/units_part$P.txt" "$A/src/K30EP/P$P.lean" >> "$L" 2>&1 || fin 7 gen
python3 -I "$T/gen_setup_v3.py" K30EP.P$P "$A/setup/P$P.json" "$A/base_setup.json" "$u" >> "$L" 2>&1 || fin 8 setup
r=$(python3 -I "$T/rtime.py" "$LEAN" --setup "$A/setup/P$P.json" -DElab.async=false -j1 -o "$A/build/K30EP/P$P.olean" "$A/src/K30EP/P$P.lean" 2>&1 | tee -a "$L" | grep '^RTIME')
wall=$(echo "$r" | sed -n 's/.*wall=\([0-9.]*\)s.*/\1/p'); rss=$(echo "$r" | sed -n 's/.*rss=\([0-9]*\)MB.*/\1/p'); rc=$(echo "$r" | sed -n 's/.*rc=\([0-9]*\).*/\1/p')
B=$A/build/K30EP/P$P
[ "$rc" = "0" ] && [ -s "$B.olean" ] && [ -s "$B.olean.server" ] && [ -s "$B.olean.private" ] || fin 9 build "$wall" "$rss"
fin 0 ok "$wall" "$rss" "$(sha256sum < "$B.olean" | cut -c1-64)" "$(sha256sum < "$B.olean.server" | cut -c1-64)" "$(sha256sum < "$B.olean.private" | cut -c1-64)"
