// Per-step survivor statistics for all odd mu < 2^HI (wall U), with a 2-adic sieve.
//  n[j][s]       : #{mu : R_i <= U for i <= j, S_j = s}                      (j <= JM)
//  nd[j][s][d]   : among those, #{next digit d_{j+1} = d}                      (d < DM)
//  st[jj][h][b][a]: for survivors at selected steps J[jj]: headroom h = K_j - S_j (<16),
//                  b = mu mod 16 (odd -> 8 classes), a = T^j(mu) mod 2^10 (odd -> 512 classes)
// Skipped sieve residues (exit decided within the first K bits) contribute their exact paths with
// multiplicity 2^(HI-K).   usage: ./step_stats U K HI out.bin
#include <math.h>
#include <omp.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned __int128 u128;
#define JM 260
#define SM 480
#define DM 24
#define NJ 8
static const int J[NJ] = {20, 30, 40, 60, 80, 100, 130, 160};
static int U, Kb[JM + 2];
static inline int ctz128(u128 x) { uint64_t lo = (uint64_t)x; return lo ? __builtin_ctzll(lo) : 64 + __builtin_ctzll((uint64_t)(x >> 64)); }
typedef struct { unsigned long long n[JM + 1][SM], nd[JM + 1][SM][DM], st[NJ][16][8][512]; } acc_t;
static void walk(u128 m, unsigned long long w, acc_t *A, int maxsteps, uint64_t mu16) {
  // records survivor-at-step-j statistics along the path of the seed with state m (= mu)
  long S = 0;
  A->n[0][0] += w;
  u128 m0 = m;
  for (int j = 0; j < maxsteps && j < JM; j++) {
    u128 x = 3 * m + 1; int d = ctz128(x);
    if (S < SM) A->nd[j][S][d < DM ? d : DM - 1] += w;
    // selected-step state statistics (state before the (j+1)-th digit)
    for (int jj = 0; jj < NJ; jj++) if (J[jj] == j) {
      int h = Kb[j] - (int)S; if (h < 0) h = 0; if (h > 15) h = 15;
      A->st[jj][h][(mu16 & 15) >> 1][(int)((uint64_t)m & 1023) >> 1] += w;
    }
    m = x >> d; S += d;
    if (S > Kb[j + 1]) return;  // exits at step j+1
    if (S < SM) A->n[j + 1][S] += w;
    (void)m0;
  }
}
int main(int argc, char **argv) {
  U = atoi(argv[1]); int K = atoi(argv[2]), HI = atoi(argv[3]);
  const long double AL = 1.584962500721156181453738943947816508759814407692481060455L;
  Kb[0] = 1 << 30;
  for (int j = 1; j <= JM + 1; j++) { long s = (long)floorl(U + j * AL); Kb[j] = (int)s; }
  uint64_t M = 1ULL << K;
  uint32_t *surv = malloc(sizeof(uint32_t) * (M / 2)); uint64_t ns = 0;
  acc_t *G = calloc(1, sizeof(acc_t));
  // phase 1: decided residues -> exact path with multiplicity 2^(HI-K); survivors -> list
  for (uint64_t r = 1; r < M; r += 2) {
    u128 m = r; long S = 0; int n = 0, decided = 0;
    while (1) {
      u128 x = 3 * m + 1; int d = ctz128(x);
      if (S + d + 1 > K) break;
      m = x >> d; S += d; n++;
      if (S > Kb[n]) { decided = 1; break; }
    }
    if (decided) walk(r, 1ULL << (HI - K), G, n, r);   // path fully determined by r mod 2^K
    else surv[ns++] = (uint32_t)r;
  }
  uint64_t j1 = (1ULL << HI) / M;
  double t0 = omp_get_wtime();
  int nth = omp_get_max_threads();
  acc_t **L = malloc(sizeof(acc_t *) * nth);
  for (int t = 0; t < nth; t++) L[t] = calloc(1, sizeof(acc_t));
#pragma omp parallel
  {
    acc_t *A = L[omp_get_thread_num()];
#pragma omp for schedule(dynamic, 16)
    for (uint64_t j = 0; j < j1; j++)
      for (uint64_t s = 0; s < ns; s++) {
        uint64_t mu = surv[s] + j * M;
        walk(mu, 1, A, JM, mu);
      }
  }
  for (int t = 0; t < nth; t++) {
    unsigned long long *a = (unsigned long long *)G, *b = (unsigned long long *)L[t];
    for (size_t i = 0; i < sizeof(acc_t) / 8; i++) a[i] += b[i];
  }
  fprintf(stderr, "U=%d HI=%d time %.1fs\n", U, HI, omp_get_wtime() - t0);
  FILE *f = fopen(argv[4], "wb"); fwrite(G, sizeof(acc_t), 1, f); fclose(f);
  return 0;
}
