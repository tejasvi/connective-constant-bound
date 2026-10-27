#!/bin/bash
# k30unit_v1.sh S LO CNT MODS: one K30E unit on a fleet node. Started by k30node_v1.py inside a
# systemd scope with a memory cap. Environment: W (node root: build/ = the only Lean search root, holding lib v1, Params
# and the data oleans; data/ = the bins), LEAN, G, NOC ("noc" or empty), NT, NUM, DEN. Steps:
#   1. k30hint: compiled checkState3cL pre-check + hint rows (a failing state stops the unit here, before kernel time);
#   2. gen_asm.py unit mode (the frozen template) -> src/K30ES/Dxxxx/Sxxxxxx.lean;
#   3. lean (the kernel checks every group theorem) -> build/K30ES/Dxxxx/Sxxxxxx.{olean,olean.server,olean.private,ilean}.
# Writes one line to res/Sxxxxxx.res: "S rc stage ms_hint ms_gen ms_lean peak_rss_kb hints_sha256 src_sha256".
set -u
S=$1; LO=$2; CNT=$3; ML=$4
D=$(printf "D%04d" $((S / 1000))); U=$(printf "S%06d" $S)
NAME=K30ES.$D.$U; REL=K30ES/$D/$U
mkdir -p $W/src/K30ES/$D $W/build/K30ES/$D $W/hints $W/res $W/log/u
H=$W/hints/$U.txt
res() { echo "$S $1 $2 $3 $4 $5 $6 $7 $8" > $W/res/$U.res.tmp && mv $W/res/$U.res.tmp $W/res/$U.res; }
ms() { echo $(( ($2 - $1) / 1000000 )); }
t0=$(date +%s%N)
$W/kit/tools/k30hint $W/data $NT $NUM $DEN $LO $CNT "$ML" $H > $W/log/u/$U.hint 2>&1; rc=$?
t1=$(date +%s%N)
[ $rc -eq 0 ] || { res $rc hint $(ms $t0 $t1) 0 0 0 - -; exit $rc; }
HS=$(sha256sum < $H | cut -c1-64)
MSARG=$(echo "$ML" | tr ',' '\n' | cut -d: -f1 | awk '{printf "%s%d:K30EData.M%05d:K30EData.M%05d", (NR > 1 ? "," : ""), $1, $1, $1}')
python3 -I $W/kit/tools/gen_asm.py unit $NAME K30EData K30EData.Params "$MSARG" $LO $H $G $W/src/$REL.lean ${NOC:-} > $W/log/u/$U.gen 2>&1; rc=$?
t2=$(date +%s%N)
[ $rc -eq 0 ] || { res $rc gen $(ms $t0 $t1) $(ms $t1 $t2) 0 0 $HS -; exit $rc; }
SS=$(sha256sum < $W/src/$REL.lean | cut -c1-64)
cd $W/src || exit 3
out=$(python3 -I -c '
import resource, subprocess, sys
p = subprocess.run(sys.argv[2:], stdout=open(sys.argv[1], "w"), stderr=subprocess.STDOUT)
print(p.returncode, resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss)' $W/log/u/$U.lean \
  $LEAN -DElab.async=false -j1 --root=. -o $W/build/$REL.olean -i $W/build/$REL.ilean $REL.lean)
t3=$(date +%s%N)
rc=${out%% *}; rss=${out##* }
res $rc lean $(ms $t0 $t1) $(ms $t1 $t2) $(ms $t2 $t3) $rss $HS $SS
exit $rc
