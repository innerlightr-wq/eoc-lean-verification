// list odd mu < 2^L with U=0 exit >= T (sieve with K bits as in glide_sieve.c)
// build: gcc -O3 -march=native -fopenmp long_survivors.c -o long_survivors -lm
#include <math.h>
#include <omp.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
typedef unsigned __int128 u128;
static const double ALPHA = 1.58496250072115618145;
static inline int ctz128(u128 x) { uint64_t lo = (uint64_t)x; return lo ? __builtin_ctzll(lo) : 64 + __builtin_ctzll((uint64_t)(x >> 64)); }
static int exit0(u128 m) { long S = 0; int n = 0; while (1) { u128 x = 3 * m + 1; int d = ctz128(x); m = x >> d; S += d; n++; if ((double)S - n * ALPHA > 0) return n; } }
int main(int argc, char **argv) {
  int K = atoi(argv[1]), L = atoi(argv[2]), T = atoi(argv[3]);
  uint64_t M = 1ULL << K; uint32_t *surv = malloc(4 * (M / 2)); uint64_t ns = 0;
  for (uint64_t r = 1; r < M; r += 2) { u128 m = r; long S = 0; int n = 0, dec = 0;
    while (1) { u128 x = 3 * m + 1; int d = ctz128(x); if (S + d + 1 > K) break; m = x >> d; S += d; n++; if ((double)S - n * ALPHA > 0) { dec = 1; break; } }
    if (!dec) surv[ns++] = r; }
  uint64_t nj = (1ULL << L) / M;
#pragma omp parallel for schedule(dynamic, 1)
  for (uint64_t j = 0; j < nj; j++)
    for (uint64_t s = 0; s < ns; s++) { uint64_t mu = surv[s] + j * M; if (mu < 3) continue; int e = exit0(mu);
      if (e >= T) {
#pragma omp critical
        printf("%llu %d\n", (unsigned long long)mu, e);
      } }
  return 0;
}
