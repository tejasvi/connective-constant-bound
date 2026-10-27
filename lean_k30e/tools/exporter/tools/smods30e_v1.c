// smods30e_v1.c: shard lists of the K30E data (untrusted helper; a wrong list only makes a shard fail in Lean).
//   smods30e_v1 DATADIR NT B S0 S1
// Shard s = states [s B, min(NT, (s + 1) B)). For s in [S0, S1) prints "s lo cnt k m_1:u_1,...,m_k:u_k": the modules
// (2^20 records each, DATADIR/m%05d.bin as written by pack30e_v1) holding the shard's states and all their children
// (K30B.checkState3cL needs modIn of the state's module and kidIn of each child), with u = the number of record reads
// in that module (state + children), in decreasing u (then increasing m): the order for the shard's module list,
// so that findMod's linear search usually stops early.
#define _FILE_OFFSET_BITS 64
#include <errno.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#define NONE35 ((1ULL << 35) - 1)
#define RECB 28
#define RBITS 20

static void die(const char *m, unsigned long long a) {
  fprintf(stderr, "smods30e_v1: %s %llu\n", m, a);
  exit(2);
}

static unsigned long long num(const char *s) {
  char *e;
  errno = 0;
  unsigned long long x = strtoull(s, &e, 10);
  if (errno || *s == 0 || *e != 0) die("bad number", 0);
  return x;
}

static void rdrange(const char *dir, uint64_t a, uint64_t b, unsigned char *buf) {
  // records [a, b) (b - a <= 2^20, possibly spanning two modules) into buf
  while (a < b) {
    uint64_t m = a >> RBITS, e = (m + 1) << RBITS;
    if (e > b) e = b;
    char fn[4096];
    snprintf(fn, sizeof fn, "%s/m%05llu.bin", dir, (unsigned long long)m);
    int fd = open(fn, O_RDONLY);
    if (fd < 0) die("cannot open module", m);
    size_t n = (size_t)(e - a) * RECB, got = 0;
    off_t off = (off_t)((a & ((1ULL << RBITS) - 1)) * RECB);
    while (got < n) {
      ssize_t r = pread(fd, buf + got, n - got, off + (off_t)got);
      if (r <= 0) die("short read in module", m);
      got += (size_t)r;
    }
    close(fd);
    buf += n;
    a = e;
  }
}

int main(int argc, char **argv) {
  if (argc != 6) {
    fprintf(stderr, "usage: smods30e_v1 DATADIR NT B S0 S1\n");
    return 2;
  }
  const char *dir = argv[1];
  uint64_t NT = num(argv[2]), B = num(argv[3]), s0 = num(argv[4]), s1 = num(argv[5]);
  if (B == 0 || B > (1ULL << RBITS) || NT == 0 || NT >= NONE35) die("bad B or NT", B);
  uint64_t NS = (NT + B - 1) / B, NM = (NT + (1ULL << RBITS) - 1) >> RBITS, NW = (NM + 63) / 64;
  if (s1 > NS || s0 >= s1) die("bad shard range", s0);
  unsigned char *buf = malloc(B * RECB);
  uint64_t *bits = malloc(8 * NW), *use = calloc(NM, 8), *ord = malloc(8 * NM);
  if (!buf || !bits || !use || !ord) die("out of memory", B);
  for (uint64_t s = s0; s < s1; s++) {
    uint64_t lo = s * B, hi = lo + B < NT ? lo + B : NT;
    rdrange(dir, lo, hi, buf);
    memset(bits, 0, 8 * NW);
    for (uint64_t j = 0; j < hi - lo; j++) {
      uint64_t mj = (lo + j) >> RBITS;
      bits[mj >> 6] |= 1ULL << (mj & 63);
      use[mj]++;
      uint64_t w[3];
      memcpy(w, buf + RECB * j, 24);
      uint64_t c[3] = {(w[0] >> 54) | ((w[1] & ((1ULL << 25) - 1)) << 10), (w[1] >> 25) & NONE35,
                       (w[1] >> 60) | ((w[2] & ((1ULL << 31) - 1)) << 4)};
      for (int t = 0; t < 3; t++) {
        if (c[t] == NONE35) continue;
        if (c[t] >= NT) die("child out of range at state", lo + j);
        uint64_t m = c[t] >> RBITS;
        bits[m >> 6] |= 1ULL << (m & 63);
        use[m]++;
      }
    }
    uint64_t k = 0;
    for (uint64_t i = 0; i < NW; i++)
      for (uint64_t x = bits[i]; x; x &= x - 1) ord[k++] = 64 * i + (uint64_t)__builtin_ctzll(x);
    for (uint64_t a = 1; a < k; a++)  // insertion sort by (use desc, m asc); k is small
      for (uint64_t b = a; b > 0 && (use[ord[b]] > use[ord[b - 1]] ||
                                     (use[ord[b]] == use[ord[b - 1]] && ord[b] < ord[b - 1])); b--) {
        uint64_t z = ord[b]; ord[b] = ord[b - 1]; ord[b - 1] = z;
      }
    printf("%llu %llu %llu %llu ", (unsigned long long)s, (unsigned long long)lo, (unsigned long long)(hi - lo),
           (unsigned long long)k);
    for (uint64_t a = 0; a < k; a++) {
      printf(a ? ",%llu:%llu" : "%llu:%llu", (unsigned long long)ord[a], (unsigned long long)use[ord[a]]);
      use[ord[a]] = 0;
    }
    printf("\n");
  }
  return 0;
}
