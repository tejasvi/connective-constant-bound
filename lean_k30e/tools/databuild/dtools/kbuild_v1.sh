#!/bin/bash
# kbuild_v1.sh ROOT MOD...: build Lean modules in order (cwd ROOT/src, so bt_bin% paths ../data/... resolve to
# ROOT/data; oleans in ROOT/build, which is also the only search root). Prints rc, wall ms and peak RSS per module;
# stops at the first failure (log in ROOT/logs/b_MOD.log).
set -u
R=${1:?root}; shift
LEAN=${LEAN:-lean}
export LEAN_PATH=$R/build
mkdir -p "$R/build" "$R/logs"
cd "$R/src" || exit 2
for m in "$@"; do
  f=$(echo "$m" | tr . /).lean; o=$R/build/$(echo "$m" | tr . /)
  mkdir -p "$(dirname "$o")"
  s=$(date +%s%N)
  KB_LOG="$R/logs/b_$m.log" python3 -c '
import os, resource, subprocess, sys
p = subprocess.run(sys.argv[1:], stdout=open(os.environ["KB_LOG"], "w"), stderr=subprocess.STDOUT)
ru = resource.getrusage(resource.RUSAGE_CHILDREN)
print("rss_mb=%d" % (ru.ru_maxrss // 1024), file=sys.stderr)
sys.exit(p.returncode)' "$LEAN" -DElab.async=false -j1 --root=. -o "$o.olean" -i "$o.ilean" "$f" 2> "$R/logs/rss_$m.txt"
  rc=$?
  e=$(date +%s%N)
  echo "$m rc=$rc $(( (e - s) / 1000000 )) ms $(cat "$R/logs/rss_$m.txt")"
  [ $rc -eq 0 ] || { grep -v '^warning' "$R/logs/b_$m.log" | head -30; exit $rc; }
done
