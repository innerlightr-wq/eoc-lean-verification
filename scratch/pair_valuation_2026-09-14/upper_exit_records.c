// Upper-exit records U_U(mu) = min{ n >= 1 : R_n(mu) > U } for every odd mu in [3, LIMIT).
// R_n = S_n - n log2(3). Orbit values in unsigned __int128 (overflow flagged); drift tests in double
// with a tie margin (|S - U - n*alpha| < 1e-9 is flagged; for n <= 10^5 the true gap is >> 1e-9).
// Records (strict prefix maxima in mu order) are exact: chunks run in parallel, then merged in order.
//
// build: gcc -O3 -march=native -fopenmp upper_exit_records.c -o upper_exit_records -lm
// usage: ./upper_exit_records LOG2_LIMIT
#include <math.h>
#include <omp.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef unsigned __int128 u128;
#define NU 5
static const int Us[NU] = {0, 1, 2, 4, 8};
static const double ALPHA = 1.58496250072115618145;
#define HIST 4096
#define CAND 256
#define CHUNK_LOG 20

static inline int ctz128(u128 x) {
  uint64_t lo = (uint64_t)x;
  if (lo) return __builtin_ctzll(lo);
  return 64 + __builtin_ctzll((uint64_t)(x >> 64));
}

static void exits(uint64_t mu, int *ex, int *flag) {
  u128 m = mu;
  long S = 0;
  int n = 0, pending = 0;
  for (int k = 0; k < NU; k++) ex[k] = -1;
  *flag = 0;
  while (pending < NU) {
    u128 x = 3 * m + 1;
    int d = ctz128(x);
    m = x >> d;
    S += d;
    n++;
    double R = (double)S - n * ALPHA;
    for (int k = pending; k < NU; k++) {
      double z = R - Us[k];
      if (fabs(z) < 1e-9) *flag |= 1;
      if (z > 0) {
        if (ex[k] < 0) ex[k] = n;
      }
    }
    while (pending < NU && ex[pending] >= 0) pending++;
    if (m >> 120) { *flag |= 2; break; }
    if (n > 100000) { *flag |= 4; break; }
  }
}

typedef struct { uint64_t mu; int val; } cand_t;
typedef struct { double mu_d; uint64_t mu; double val; int ex; } rcand_t;

int main(int argc, char **argv) {
  int L = argc > 1 ? atoi(argv[1]) : 28;
  uint64_t limit = 1ULL << L;
  uint64_t nodd = limit / 2;                 // odd mu = 2i+1, i in [1, nodd)
  uint64_t chunk = 1ULL << CHUNK_LOG;
  uint64_t nchunks = (nodd + chunk - 1) / chunk;
  cand_t *ec = calloc(nchunks * NU * CAND, sizeof(cand_t));
  int *ecn = calloc(nchunks * NU, sizeof(int));
  rcand_t *rc = calloc(nchunks * NU * CAND, sizeof(rcand_t));
  int *rcn = calloc(nchunks * NU, sizeof(int));
  unsigned long long hist[NU][HIST];
  memset(hist, 0, sizeof(hist));
  unsigned long long flags[3] = {0, 0, 0};
  double t0 = omp_get_wtime();
#pragma omp parallel
  {
    unsigned long long lh[NU][HIST];
    memset(lh, 0, sizeof(lh));
    unsigned long long lf[3] = {0, 0, 0};
#pragma omp for schedule(dynamic, 1)
    for (uint64_t c = 0; c < nchunks; c++) {
      int emax[NU];
      double rmax[NU];
      for (int k = 0; k < NU; k++) { emax[k] = -1; rmax[k] = -1; }
      uint64_t i0 = c * chunk, i1 = i0 + chunk < nodd ? i0 + chunk : nodd;
      if (i0 == 0) i0 = 1;
      for (uint64_t i = i0; i < i1; i++) {
        uint64_t mu = 2 * i + 1;
        int ex[NU], fl;
        exits(mu, ex, &fl);
        if (fl & 1) lf[0]++;
        if (fl & 2) lf[1]++;
        if (fl & 4) lf[2]++;
        double lg = log2((double)mu);
        for (int k = 0; k < NU; k++) {
          int e = ex[k];
          if (e < 0) continue;
          lh[k][e < HIST ? e : HIST - 1]++;
          if (e > emax[k]) {
            emax[k] = e;
            int *cn = &ecn[c * NU + k];
            if (*cn < CAND) ec[(c * NU + k) * CAND + (*cn)++] = (cand_t){mu, e};
          }
          if (mu >= 1024) {
            double r = e / lg;
            if (r > rmax[k]) {
              rmax[k] = r;
              int *cn = &rcn[c * NU + k];
              if (*cn < CAND) rc[(c * NU + k) * CAND + (*cn)++] = (rcand_t){lg, mu, r, e};
            }
          }
        }
      }
    }
#pragma omp critical
    {
      for (int k = 0; k < NU; k++)
        for (int h = 0; h < HIST; h++) hist[k][h] += lh[k][h];
      for (int f = 0; f < 3; f++) flags[f] += lf[f];
    }
  }
  double t1 = omp_get_wtime();
  printf("# limit 2^%d, odd seeds %llu, time %.1fs, flags: near-tie %llu overflow %llu cap %llu\n", L,
         (unsigned long long)(nodd - 1), t1 - t0, flags[0], flags[1], flags[2]);
  for (int k = 0; k < NU; k++) {
    double sum = 0, cnt = 0;
    int mx = 0;
    for (int h = 0; h < HIST; h++) {
      sum += (double)h * hist[k][h];
      cnt += hist[k][h];
      if (hist[k][h]) mx = h;
    }
    printf("U=%d mean_exit %.4f max_exit %d\n", Us[k], sum / cnt, mx);
    printf("  HIST U=%d:", Us[k]);
    for (int h = 0; h < HIST; h++) if (hist[k][h]) printf(" %d:%llu", h, hist[k][h]);
    printf("\n");
    int gmax = -1;
    printf("  EXIT_RECORDS U=%d:", Us[k]);
    for (uint64_t c = 0; c < nchunks; c++)
      for (int j = 0; j < ecn[c * NU + k]; j++) {
        cand_t v = ec[(c * NU + k) * CAND + j];
        if (v.val > gmax) { gmax = v.val; printf(" %llu:%d", (unsigned long long)v.mu, v.val); }
      }
    printf("\n");
    double rmax = -1;
    printf("  RATIO_RECORDS(mu>=1024) U=%d:", Us[k]);
    for (uint64_t c = 0; c < nchunks; c++)
      for (int j = 0; j < rcn[c * NU + k]; j++) {
        rcand_t v = rc[(c * NU + k) * CAND + j];
        if (v.val > rmax) { rmax = v.val; printf(" %llu:%d:%.3f", (unsigned long long)v.mu, v.ex, v.val); }
      }
    printf("\n");
  }
  return 0;
}
