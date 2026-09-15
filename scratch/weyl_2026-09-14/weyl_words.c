// Shell-resolved Weyl sums of least realizers over c-confined valuation words (mode 0) or over
// all words with total S <= Scap (mode 1, free / critical-tilt ensemble).
// For each final shell s (x = sN - s for mode 0, s itself for mode 1) records:
//   hist[s][a], a = top B bits of r / 2^(s+1)   (a = r >> (s+1-B))
//   W[s][h] = sum_w e(h r_w / 2^(s+1)),  h = 1..HMAX  (exact additive sums, long double)
// usage: ./weyl_words mode c N B [Scap]   -> writes weyl_m{mode}_c{c}_N{N}.bin
#define _GNU_SOURCE
#include <complex.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned __int128 u128;
#define HMAX 64
#define SMAX 128
static int N, c, mode, B, Kb[128], sN, Scap;
static uint64_t *hist[SMAX];
static long double complex W[SMAX][HMAX + 1];
static unsigned long long M[SMAX];
static uint64_t inv3pow[128];
static u128 p3[128];
static void leaf(int S, u128 r) {
  int s = S;
  if (s + 1 >= B) hist[s][(uint64_t)(r >> (s + 1 - B))]++;
  else hist[s][(uint64_t)(r << (B - s - 1))]++;
  M[s]++;
  // exact phase r / 2^(s+1): r < 2^(s+1) <= 2^100; use long double of the top 64 bits
  long double th;
  if (s + 1 > 64) th = (long double)(uint64_t)(r >> (s + 1 - 64)) / 18446744073709551616.0L;
  else th = (long double)(uint64_t)r / ldexpl(1.0L, s + 1);
  long double complex z = cexpl(2.0L * M_PIl * I * th), zz = 1;
  for (int h = 1; h <= HMAX; h++) { zz *= z; if ((h & 7) == 0) zz = cexpl(2.0L * M_PIl * I * fmodl(h * th, 1.0L)); W[s][h] += zz; }
}
static void dfs(int j, int S, u128 r, u128 m) {
  if (j == N) { leaf(S, r); return; }
  int dmax = (mode == 0) ? Kb[j + 1] - S : Scap - S - (N - j - 1);
  u128 A = 3 * m + 1; uint64_t Ah = (uint64_t)(A >> 1);
  for (int d = 1; d <= dmax && d < 60; d++) {
    uint64_t t = (((1ULL << (d - 1)) - Ah) * inv3pow[j + 1]) & ((1ULL << d) - 1);
    u128 z = 3 * (m + 2 * p3[j] * (u128)t) + 1;
    dfs(j + 1, S + d, r + ((u128)t << (S + 1)), z >> d);
  }
}
int main(int argc, char **argv) {
  mode = atoi(argv[1]); c = atoi(argv[2]); N = atoi(argv[3]); B = atoi(argv[4]);
  Scap = argc > 5 ? atoi(argv[5]) : 0;
  const long double A = 1.584962500721156181453738943947816508759814407692481060455L;
  for (int j = 1; j <= N; j++) Kb[j] = (int)floorl(c + j * A);
  sN = Kb[N];
  uint64_t inv3 = 0xAAAAAAAAAAAAAAABULL; inv3pow[0] = 1;
  for (int k = 1; k < 128; k++) inv3pow[k] = inv3pow[k - 1] * inv3;
  p3[0] = 1; for (int k = 1; k < 80; k++) p3[k] = 3 * p3[k - 1];
  int smax = mode == 0 ? sN : Scap;
  for (int s = 0; s <= smax; s++) hist[s] = calloc((size_t)1 << B, 8);
  dfs(0, 0, 1, 1);
  char fn[128]; sprintf(fn, "weyl_m%d_c%d_N%d.bin", mode, c, N);
  FILE *f = fopen(fn, "wb");
  int hdr[5] = {mode, c, N, B, smax}; fwrite(hdr, 4, 5, f);
  for (int s = 0; s <= smax; s++) {
    fwrite(&M[s], 8, 1, f); fwrite(hist[s], 8, (size_t)1 << B, f);
    for (int h = 1; h <= HMAX; h++) { double v[2] = {creall(W[s][h]), cimagl(W[s][h])}; fwrite(v, 8, 2, f); }
  }
  fclose(f);
  unsigned long long tot = 0; for (int s = 0; s <= smax; s++) tot += M[s];
  printf("mode=%d c=%d N=%d sN=%d words=%llu -> %s\n", mode, c, N, sN, tot, fn);
  return 0;
}
