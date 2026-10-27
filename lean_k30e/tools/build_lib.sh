#!/bin/bash
# build_lib.sh [OUT]: build the 13 library modules (src/Saw38aCore, src/Saw38aK, src/K30B) in dependency order into OUT
# (default: build_lib), one `lean -DElab.async=false -j1` per module, as for the proof. Run from lean_k30e/.
# Environment: LEAN (default: lean on PATH; v4.35.0-rc3). No Mathlib is needed.
set -eu
LEAN=${LEAN:-lean}
OUT=$(mkdir -p "${1:-build_lib}" && cd "${1:-build_lib}" && pwd)
export LEAN_PATH=$OUT
for m in Saw38aCore.Check Saw38aK.CheckK Saw38aK.CheckB Saw38aK.CheckB2 Saw38aK.Lit Saw38aK.LitBin K30B.Check30 \
    K30B.Check3a K30B.Check3b K30B.Look K30B.Check3c K30B.Local K30B.LocalProofs; do
  f=src/$(echo $m | tr . /).lean; o=$OUT/$(echo $m | tr . /).olean; mkdir -p "$(dirname "$o")"
  "$LEAN" -DElab.async=false -j1 -R src -o "$o" "$f"
  echo "built $m"
done
