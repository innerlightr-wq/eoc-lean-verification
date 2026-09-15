// U = 0 upper-exit (= accelerated glide) records beyond 2^32 by a 2-adic survivor sieve.
// Phase 1: for each odd residue r mod 2^K, follow the orbit of r while the digits are determined by
//          r mod 2^K (S_n + 1 <= K, realizer congruence). If R_n > 0 happens in that determined range,
//          every mu = r (mod 2^K) exits at the same step n <= K: such residues can never set a record
//          beyond exit K and are skipped. Otherwise r is a survivor.
// Phase 2: every mu = r + j 2^K in [2^LO, 2^HI) with r a survivor is run in full; strict prefix
//          maxima of the exit time (in mu order) above the start record are reported. Also a
//          histogram of exit times of survivor seeds (exits of skipped seeds are <= K).
// build: gcc -O3 -march=native -fopenmp glide_sieve.c -o glide_sieve -lm
// usage: ./glide_sieve K LO HI START_RECORD
#include <math.h>
#include <omp.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned __int128 u128;
static const double ALPHA = 1.58496250072115618145;
static inline int ctz128(u128 x) {
  uint64_t lo = (uint64_t)x;
  if (lo) return __builtin_ctzll(lo);
  return 64 + __builtin_ctzll((uint64_t)(x >> 64));
}
static int exit0(u128 m, int *flag) {  // first n >= 1 with S_n - n alpha > 0
  long S = 0;
  int n = 0;
  while (1) {
    u128 x = 3 * m + 1;
    int d = ctz128(x);
    m = x >> d;
    S += d;
    n++;
    double z = (double)S - n * ALPHA;
    if (fabs(z) < 1e-9) *flag |= 1;
    if (z > 0) return n;
    if (m >> 120) { *flag |= 2; return n; }
  }
}
int main(int argc, char **argv) {
  int K = atoi(argv[1]), LO = atoi(argv[2]), HI = atoi(argv[3]);
  int start = atoi(argv[4]);
  uint64_t M = 1ULL << K;
  // phase 1
  uint32_t *surv = malloc(sizeof(uint32_t) * (M / 2));
  uint64_t ns = 0;
  for (uint64_t r = 1; r < M; r += 2) {
    u128 m = r;
    long S = 0;
    int n = 0, decided = 0;
    while (1) {
      u128 x = 3 * m + 1;
      int d = ctz128(x);
      if (S + d + 1 > K) break;  // digit not determined by r mod 2^K
      m = x >> d;
      S += d;
      n++;
      if ((double)S - n * ALPHA > 0) { decided = 1; break; }
    }
    if (!decided) surv[ns++] = (uint32_t)r;
  }
  printf("# K=%d survivors %llu of %llu odd residues (%.4f)\n", K, (unsigned long long)ns,
         (unsigned long long)(M / 2), (double)ns / (M / 2));
  // phase 2: j ranges over blocks; mu = r + j*M
  uint64_t j0 = (1ULL << LO) / M, j1 = (1ULL << HI) / M;
  uint64_t nj = j1 - j0;
  int CH = 1 << 5;  // j per chunk
  uint64_t nch = (nj + CH - 1) / CH;
  typedef struct { uint64_t mu; int e; } cand_t;
  cand_t *cand = calloc(nch * 64, sizeof(cand_t));
  int *cn = calloc(nch, sizeof(int));
  unsigned long long hist[4096];
  memset(hist, 0, sizeof(hist));
  unsigned long long flags = 0;
  double t0 = omp_get_wtime();
#pragma omp parallel
  {
    unsigned long long lh[4096];
    memset(lh, 0, sizeof(lh));
    unsigned long long lf = 0;
#pragma omp for schedule(dynamic, 1)
    for (uint64_t c = 0; c < nch; c++) {
      int emax = start;
      uint64_t ja = j0 + c * CH, jb = ja + CH < j1 ? ja + CH : j1;
      for (uint64_t j = ja; j < jb; j++)
        for (uint64_t s = 0; s < ns; s++) {
          uint64_t mu = surv[s] + j * M;
          int fl = 0;
          int e = exit0(mu, &fl);
          if (fl) lf++;
          lh[e < 4096 ? e : 4095]++;
          if (e > emax) {
            emax = e;
            if (cn[c] < 64) cand[c * 64 + cn[c]++] = (cand_t){mu, e};
          }
        }
    }
#pragma omp critical
    {
      for (int h = 0; h < 4096; h++) hist[h] += lh[h];
      flags += lf;
    }
  }
  printf("# phase 2 [2^%d, 2^%d): %.1fs, flagged %llu\n", LO, HI, omp_get_wtime() - t0, flags);
  int g = start;
  printf("RECORDS:");
  for (uint64_t c = 0; c < nch; c++)
    for (int i = 0; i < cn[c]; i++)
      if (cand[c * 64 + i].e > g) {
        g = cand[c * 64 + i].e;
        printf(" %llu:%d", (unsigned long long)cand[c * 64 + i].mu, g);
      }
  printf("\nSURVIVOR_HIST:");
  for (int h = 0; h < 4096; h++) if (hist[h]) printf(" %d:%llu", h, hist[h]);
  printf("\n");
  return 0;
}
