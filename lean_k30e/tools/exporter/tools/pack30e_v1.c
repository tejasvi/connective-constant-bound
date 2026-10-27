// pack30e_v1.c: pack records [LO, LO + CNT) of the k30e certificate into one K30E data file (untrusted exporter;
// the data only decide which certificate the kernel checks).
//   pack30e_v1 KEYS CHOSEN V LO CNT OUT
// Inputs as published: KEYS uint64 (n << 58 | T), CHOSEN 3 x uint64 per state (all ones = no child), V double.
// Record = K30B.recOf30, 224 bits, 28 bytes little endian: n (6) | T (48) | c0 (35) | c1 (35) | c2 (35) | V (61);
// child all ones -> 2^35 - 1; V = floor(v 2^60). Checks as tools/mkchunk30e.py of the N release: n < 32, T < 2^46,
// child < N, 0 <= v <= 1. Leaves of 64 records (1792 bytes); the last leaf of a short range is zero-padded.
// Prints one line: lo cnt nleaf bytes zeroV none0 none1 none2 n-histogram(n=0..31, comma separated).
#define _FILE_OFFSET_BITS 64
#include <errno.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

#define NONE35 ((1ULL << 35) - 1)
#define RECB 28
#define LEAF 64

static void die(const char *m, unsigned long long a) {
  fprintf(stderr, "pack30e_v1: %s %llu\n", m, a);
  exit(2);
}

static unsigned long long num(const char *s) {
  char *e;
  errno = 0;
  unsigned long long x = strtoull(s, &e, 10);
  if (errno || *s == 0 || *e != 0) die("bad number", 0);
  return x;
}

static void rd(int fd, void *buf, size_t n, off_t off) {
  size_t got = 0;
  while (got < n) {
    ssize_t r = pread(fd, (char *)buf + got, n - got, off + (off_t)got);
    if (r <= 0) die("short read at byte", (unsigned long long)(off + (off_t)got));
    got += (size_t)r;
  }
}

int main(int argc, char **argv) {
  if (argc != 7) {
    fprintf(stderr, "usage: pack30e_v1 KEYS CHOSEN V LO CNT OUT\n");
    return 2;
  }
  int fk = open(argv[1], O_RDONLY), fc = open(argv[2], O_RDONLY), fv = open(argv[3], O_RDONLY);
  if (fk < 0 || fc < 0 || fv < 0) die("cannot open an input", 0);
  struct stat sk, sc, sv;
  if (fstat(fk, &sk) || fstat(fc, &sc) || fstat(fv, &sv)) die("stat", 0);
  uint64_t N = (uint64_t)sk.st_size / 8;
  if ((uint64_t)sk.st_size != 8 * N || (uint64_t)sc.st_size != 24 * N || (uint64_t)sv.st_size != 8 * N)
    die("input sizes disagree, N =", N);
  if (N >= NONE35) die("too many states", N);
  uint64_t lo = num(argv[4]), cnt = num(argv[5]);
  if (cnt == 0 || lo >= N || cnt > N - lo) die("bad range, lo =", lo);
  uint64_t *K = malloc(8 * cnt), *C = malloc(24 * cnt);
  double *V = malloc(8 * cnt);
  uint64_t nleaf = (cnt + LEAF - 1) / LEAF, nb = nleaf * LEAF * RECB;
  unsigned char *out = calloc(nb, 1);
  if (!K || !C || !V || !out) die("out of memory", cnt);
  rd(fk, K, 8 * cnt, (off_t)(8 * lo));
  rd(fc, C, 24 * cnt, (off_t)(24 * lo));
  rd(fv, V, 8 * cnt, (off_t)(8 * lo));
  uint64_t hist[32] = {0}, none[3] = {0}, zeroV = 0;
  for (uint64_t j = 0; j < cnt; j++) {
    uint64_t k = K[j], n = k >> 58, T = k & ((1ULL << 58) - 1);
    if (n >= 32 || T >= (1ULL << 46)) die("bad key at state", lo + j);
    uint64_t c[3];
    for (int t = 0; t < 3; t++) {
      uint64_t x = C[3 * j + t];
      if (x == UINT64_MAX) {
        c[t] = NONE35;
        none[t]++;
      } else {
        if (x >= N) die("child out of range at state", lo + j);
        c[t] = x;
      }
    }
    double v = V[j];
    if (!(v >= 0.0 && v <= 1.0)) die("weight outside [0, 1] at state", lo + j);
    uint64_t W = (uint64_t)(v * 1152921504606846976.0);  // exact scaling by 2^60, then truncation = floor
    if (W == 0) zeroV++;
    hist[n]++;
    uint64_t w[4];
    w[0] = n | (T << 6) | ((c[0] & 0x3FFULL) << 54);
    w[1] = (c[0] >> 10) | (c[1] << 25) | ((c[2] & 0xFULL) << 60);
    w[2] = (c[2] >> 4) | ((W & ((1ULL << 33) - 1)) << 31);
    w[3] = W >> 33;
    memcpy(out + RECB * j, w, RECB);  // little endian: bits 0..223 of the record
  }
  FILE *f = fopen(argv[6], "wb");
  if (!f || fwrite(out, 1, nb, f) != nb || fclose(f)) die("cannot write output", nb);
  printf("%llu %llu %llu %llu %llu %llu %llu %llu ", (unsigned long long)lo, (unsigned long long)cnt,
         (unsigned long long)nleaf, (unsigned long long)nb, (unsigned long long)zeroV, (unsigned long long)none[0],
         (unsigned long long)none[1], (unsigned long long)none[2]);
  for (int i = 0; i < 32; i++) printf("%s%llu", i ? "," : "", (unsigned long long)hist[i]);
  printf("\n");
  return 0;
}
