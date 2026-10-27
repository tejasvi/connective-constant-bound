# gen_partlists_v1.awk: from the kit's shards.tsv ("S LO CNT nmods k:reads,...", S = 0..995497 in
# order) write one gen_asm unit list per part of 256 consecutive units: OUTDIR/units_part%04d.txt with rows
# "K30ES.D%04d.S%06d LO CNT k1,k2,..." (module ids in the shard's order). Usage: awk -v OUT=DIR -f gen_partlists_v1.awk shards.tsv
{ s = $1 + 0
  if (s != NR - 1) { printf "ERROR: row %d has S=%s (expected %d)\n", NR, $1, NR - 1 | "cat 1>&2"; bad = 1; exit 1 }
  p = int(s / 256)
  if (p != cur) { if (f != "") close(f); cur = p; f = sprintf("%s/units_part%04d.txt", OUT, p); np++ }
  n = split($5, a, ","); ks = ""
  if (n != $4 + 0) { printf "ERROR: S=%d nmods %s but %d pairs\n", s, $4, n | "cat 1>&2"; bad = 1; exit 1 }
  for (i = 1; i <= n; i++) { split(a[i], b, ":"); ks = ks (i > 1 ? "," : "") b[1] }
  printf "K30ES.D%04d.S%06d %s %s %s\n", int(s / 1000), s, $2, $3, ks > f; nu++ }
BEGIN { cur = -1; f = "" }
END { if (!bad) printf "parts %d units %d\n", np, nu }
