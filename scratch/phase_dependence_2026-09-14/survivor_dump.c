// Exhaustive upper-wall exit times for odd seeds in [2^LO, 2^HI) with a 2-adic sieve (wall U):
//   exit(mu) = first n >= 1 with S_n - n*log2(3) > U.
// Phase 1: odd residues r mod 2^K whose exit is decided by r mod 2^K (exit <= K) are skipped.
// Phase 2: every mu = r + j 2^K in range with r a survivor residue is run in full.
// Outputs: binary file of (uint64 mu, uint32 exit) for exit >= T; per-dyadic-scale histogram
// (mu in [2^k, 2^(k+1))) of exits > K; strict prefix records (in mu order).
// build: gcc -O3 -march=native -fopenmp survivor_dump.c -o survivor_dump -lm
// usage: ./survivor_dump U K LO HI T outfile.bin > log
#include <math.h>
#include <omp.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned __int128 u128;
static const double ALPHA = 1.58496250072115618145;
static int U;
static inline int ctz128(u128 x) {
  uint64_t lo = (uint64_t)x;
  if (lo) return __builtin_ctzll(lo);
  return 64 + __builtin_ctzll((uint64_t)(x >> 64));
}
static int exitU(u128 m) {
  long S = 0;
  int n = 0;
  while (1) {
    u128 x = 3 * m + 1;
    int d = ctz128(x);
    m = x >> d;
    S += d;
    n++;
    if ((double)S - n * ALPHA > U) return n;
    if (m >> 120) return -n;  // overflow guard (never expected)
  }
}
#define EMAX 4096
int main(int argc, char **argv) {
  U = atoi(argv[1]);
  int K = atoi(argv[2]), LO = atoi(argv[3]), HI = atoi(argv[4]), T = atoi(argv[5]);
  FILE *fo = fopen(argv[6], "wb");
  uint64_t M = 1ULL << K;
  uint32_t *surv = malloc(sizeof(uint32_t) * (M / 2));
  uint64_t ns = 0;
  for (uint64_t r = 1; r < M; r += 2) {
    u128 m = r;
    long S = 0;
    int n = 0, decided = 0;
    while (1) {
      u128 x = 3 * m + 1;
      int d = ctz128(x);
      if (S + d + 1 > K) break;
      m = x >> d;
      S += d;
      n++;
      if ((double)S - n * ALPHA > U) { decided = 1; break; }
    }
    if (!decided) surv[ns++] = (uint32_t)r;
  }
  fprintf(stderr, "# U=%d K=%d survivor residues %llu\n", U, K, (unsigned long long)ns);
  uint64_t j0 = (LO == 0) ? 0 : (1ULL << LO) / M, j1 = (1ULL << HI) / M;
  static unsigned long long hist[64][EMAX];
  memset(hist, 0, sizeof(hist));
  int nthreads = omp_get_max_threads();
  unsigned long long nout = 0, bad = 0;
  double t0 = omp_get_wtime();
  uint64_t CH = 16;
  uint64_t nch = (j1 - j0 + CH - 1) / CH;
  // records: per chunk, strict prefix maxima within chunk (merged afterwards)
  typedef struct { uint64_t mu; int e; } cand_t;
  cand_t *cand = calloc(nch * 32, sizeof(cand_t));
  int *cn = calloc(nch, sizeof(int));
#pragma omp parallel
  {
    unsigned long long (*lh)[EMAX] = calloc(64, sizeof(*lh));
    size_t cap = 1 << 16, len = 0;
    uint64_t *bmu = malloc(cap * 8);
    uint32_t *be = malloc(cap * 4);
    unsigned long long lbad = 0;
#pragma omp for schedule(dynamic, 1)
    for (uint64_t c = 0; c < nch; c++) {
      uint64_t ja = j0 + c * CH, jb = ja + CH < j1 ? ja + CH : j1;
      int emax = 0;
      for (uint64_t j = ja; j < jb; j++)
        for (uint64_t s = 0; s < ns; s++) {
          uint64_t mu = surv[s] + j * M;
          if (LO > 0 && mu < (1ULL << LO)) continue;
          int e = exitU(mu);
          if (e < 0) { lbad++; continue; }
          int k = 63 - __builtin_clzll(mu);
          lh[k][e < EMAX ? e : EMAX - 1]++;
          if (e > emax) {
            emax = e;
            if (cn[c] < 32) cand[c * 32 + cn[c]++] = (cand_t){mu, e};
          }
          if (e >= T) {
            if (len == cap) { cap *= 2; bmu = realloc(bmu, cap * 8); be = realloc(be, cap * 4); }
            bmu[len] = mu; be[len] = (uint32_t)e; len++;
          }
        }
    }
#pragma omp critical
    {
      for (int k = 0; k < 64; k++)
        for (int e = 0; e < EMAX; e++) hist[k][e] += lh[k][e];
      for (size_t i = 0; i < len; i++) { fwrite(&bmu[i], 8, 1, fo); fwrite(&be[i], 4, 1, fo); }
      nout += len;
      bad += lbad;
    }
    free(lh); free(bmu); free(be);
  }
  fclose(fo);
  printf("# U=%d K=%d range [2^%d,2^%d) time %.1fs dumped %llu (exit>=%d) overflow %llu threads %d\n",
         U, K, LO, HI, omp_get_wtime() - t0, nout, T, bad, nthreads);
  // merge records: chunks are in increasing mu order
  int g = 0;
  printf("RECORDS:");
  for (uint64_t c = 0; c < nch; c++)
    for (int i = 0; i < cn[c]; i++)
      if (cand[c * 32 + i].e > g) { g = cand[c * 32 + i].e; printf(" %llu:%d", (unsigned long long)cand[c * 32 + i].mu, g); }
  printf("\n");
  for (int k = 0; k < 64; k++) {
    int any = 0;
    for (int e = K + 1; e < EMAX; e++) if (hist[k][e]) any = 1;
    if (!any) continue;
    printf("HIST k=%d:", k);
    for (int e = K + 1; e < EMAX; e++) if (hist[k][e]) printf(" %d:%llu", e, hist[k][e]);
    printf("\n");
  }
  return 0;
}
