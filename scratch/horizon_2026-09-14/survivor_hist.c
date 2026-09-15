// Complete upper-wall exit-time histograms per dyadic scale (every odd seed counted).
// exit(mu) = first n >= 1 with S_n - n log2 3 > U.  Phase 1: odd residues r mod 2^K whose exit is
// decided by r mod 2^K (all mu = r mod 2^K share it) are counted analytically; the rest are run.
// Modes:
//   full   U K HI           : every odd mu in [1, 2^HI); output HIST k=..: exit counts for mu in [2^k,2^(k+1))
//   sample U K S NB SEED    : NB random full periods mu = r + j 2^K with j uniform, mu in [2^(S-1), 2^S);
//                              output SAMPLE histogram over the NB * 2^(K-1) sampled odd seeds
// build: gcc -O3 -march=native -fopenmp survivor_hist.c -o survivor_hist -lm
#include <math.h>
#include <omp.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned __int128 u128;
static const double ALPHA = 1.58496250072115618145;
static int U;
#define EMAX 4096
static inline int ctz128(u128 x) { uint64_t lo = (uint64_t)x; return lo ? __builtin_ctzll(lo) : 64 + __builtin_ctzll((uint64_t)(x >> 64)); }
static int exitU(u128 m) {
  long S = 0; int n = 0;
  while (1) {
    u128 x = 3 * m + 1; int d = ctz128(x); m = x >> d; S += d; n++;
    if ((double)S - n * ALPHA > U) return n;
    if (m >> 124) return -1;
  }
}
static uint64_t splitmix(uint64_t *s) { uint64_t z = (*s += 0x9E3779B97F4A7C15ULL); z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL; z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL; return z ^ (z >> 31); }
int main(int argc, char **argv) {
  int sample = !strcmp(argv[1], "sample");
  U = atoi(argv[2]);
  int K = atoi(argv[3]);
  uint64_t M = 1ULL << K;
  uint32_t *surv = malloc(sizeof(uint32_t) * (M / 2));
  uint64_t ns = 0;
  static unsigned long long dec[EMAX];  // decided residues by exit
  uint8_t *decr = malloc(M / 2);        // decided exit per residue (for r < 2^K bookkeeping), 0 = survivor
  for (uint64_t r = 1; r < M; r += 2) {
    u128 m = r; long S = 0; int n = 0, decided = 0;
    while (1) {
      u128 x = 3 * m + 1; int d = ctz128(x);
      if (S + d + 1 > K) break;
      m = x >> d; S += d; n++;
      if ((double)S - n * ALPHA > U) { decided = 1; break; }
    }
    if (decided) { dec[n]++; decr[r / 2] = (uint8_t)n; } else { surv[ns++] = (uint32_t)r; decr[r / 2] = 0; }
  }
  static unsigned long long hist[128][EMAX];
  double t0 = omp_get_wtime();
  unsigned long long bad = 0;
  if (!sample) {
    int HI = atoi(argv[4]);
    // decided residues: mu = r + j 2^K; for j = 0, mu = r in scale floor(log2 r); for j >= 1 whole scales
    for (uint64_t r = 1; r < M; r += 2)
      if (decr[r / 2]) hist[63 - __builtin_clzll(r)][decr[r / 2]]++;
    for (int k = K; k < HI; k++)
      for (int e = 0; e < EMAX; e++) hist[k][e] += dec[e] << (k - K);
    uint64_t j1 = (1ULL << HI) / M;
#pragma omp parallel
    {
      unsigned long long (*lh)[EMAX] = calloc(128, sizeof(*lh));
      unsigned long long lb = 0;
#pragma omp for schedule(dynamic, 64)
      for (uint64_t j = 0; j < j1; j++)
        for (uint64_t s = 0; s < ns; s++) {
          uint64_t mu = surv[s] + j * M;
          int e = exitU(mu);
          if (e < 0) { lb++; continue; }
          lh[63 - __builtin_clzll(mu)][e < EMAX ? e : EMAX - 1]++;
        }
#pragma omp critical
      { for (int k = 0; k < 128; k++) for (int e = 0; e < EMAX; e++) hist[k][e] += lh[k][e]; bad += lb; }
      free(lh);
    }
    printf("# full U=%d K=%d HI=%d time %.1fs overflow %llu\n", U, K, HI, omp_get_wtime() - t0, bad);
    for (int k = 0; k < HI; k++) {
      printf("HIST k=%d:", k);
      for (int e = 0; e < EMAX; e++) if (hist[k][e]) printf(" %d:%llu", e, hist[k][e]);
      printf("\n");
    }
  } else {
    int Sb = atoi(argv[4]), NB = atoi(argv[5]);
    uint64_t seed = strtoull(argv[6], 0, 10);
    uint64_t jlo = (1ULL << (Sb - 1)) >> K, jn = jlo;  // j in [jlo, 2 jlo)
    uint64_t *js = malloc(8 * NB);
    for (int b = 0; b < NB; b++) js[b] = jlo + splitmix(&seed) % jn;
    unsigned long long H[EMAX]; memset(H, 0, sizeof(H));
    for (int e = 0; e < EMAX; e++) H[e] = dec[e] * (unsigned long long)NB;
#pragma omp parallel
    {
      unsigned long long lh[EMAX]; memset(lh, 0, sizeof(lh)); unsigned long long lb = 0;
#pragma omp for schedule(dynamic, 1)
      for (int b = 0; b < NB; b++)
        for (uint64_t s = 0; s < ns; s++) {
          u128 mu = (u128)surv[s] + (u128)js[b] * M;
          int e = exitU(mu);
          if (e < 0) { lb++; continue; }
          lh[e < EMAX ? e : EMAX - 1]++;
        }
#pragma omp critical
      { for (int e = 0; e < EMAX; e++) H[e] += lh[e]; bad += lb; }
    }
    printf("# sample U=%d K=%d scale 2^%d blocks %d seeds %llu time %.1fs overflow %llu\n", U, K, Sb, NB,
           (unsigned long long)NB << (K - 1), omp_get_wtime() - t0, bad);
    printf("SAMPLE S=%d:", Sb);
    for (int e = 0; e < EMAX; e++) if (H[e]) printf(" %d:%llu", e, H[e]);
    printf("\n");
  }
  return 0;
}
