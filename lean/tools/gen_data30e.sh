#!/bin/bash
# gen_data30e.sh [PREFIX]: check the sha256 of PREFIX.{keys,chosen,v} (the certificate of order 30, file prefix k30e;
# default PREFIX ~/l38/cert/k30e), convert it into 11497 chunk files data/cNNNNN.s7 (32 chars per state) and write
# L38Data/ChunkNNNNN.lean, L38Data/All.lean and the root L38Data.lean.
set -euo pipefail
cd "$(dirname "$0")/.."
P=${1:-$HOME/l38/cert/k30e}; B=2164802; NCH=11497; N=24887440008
sha256sum -c - <<SUMS
7a244666900ae95d404550871de6c076fcb57d75baa5dbf68d6af6c798bf64b8  $P.keys
c786235e644c5c547d5be02510561e3263baa55402c3042b676dffcdcc9700fa  $P.chosen
fc4151469c10771fabc2605eb58db96390c15a2a42113c84d068dd5b2267e351  $P.v
SUMS
mkdir -p data L38Data pins
seq 0 $((NCH - 1)) | xargs -P 200 -I{} bash -c 'i={}; f=$(printf "%05d" $i); python3 -I tools/mkchunk30e.py '"$P"' $((i * '"$B"')) '"$B"' data/c$f.s7 > pins/$f.txt'
for i in $(seq 0 $((NCH - 1))); do
  f=$(printf "%05d" $i); read -r len h < pins/$f.txt
  printf 'import L38Loader\n\n/-! Chunk %d of the k30e certificate (%s characters, 32 per state). -/\n\nload_cert_chunk L38.Data.chunk%s "data/c%s.s7" %s\n' $i $len $f $f $h > L38Data/Chunk$f.lean
done
{
  for i in $(seq 0 $((NCH - 1))); do printf 'import L38Data.Chunk%05d\n' $i; done
  printf '\nset_option maxRecDepth 100000\n\nnamespace L38.Data\n\n/-- States per chunk. -/\ndef chunkStates : Nat := %d\n\n/-- The number of states. -/\ndef numStates : Nat := %d\n\n/-- The chunks of the k30e certificate, in order. -/\ndef chunks : Array String := #[\n' $B $N
  for i in $(seq 0 $((NCH - 1))); do sep=","; [ $i -eq $((NCH - 1)) ] && sep=""; printf '  chunk%05d%s\n' $i "$sep"; done
  printf ']\n\nend L38.Data\n'
} > L38Data/All.lean
printf 'import L38Data.All\n' > L38Data.lean
cat pins/*.txt | awk '{s += $1} END {print "chars", s}'
