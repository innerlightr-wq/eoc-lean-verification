// End-to-end check of the prefix/suffix bilinear decomposition at depth N, cutoff 2^K, split j0.
// For each prefix shell sigma (<= K-1) and word shell s (>= K):
//   L      = #{(P,v): r_{Pv} < 2^K} computed exactly from the prefix-state histogram N(x), x = m_P mod 2^(t+1)
//   Haar   = |P||V| 2^(K-1-s)
//   bound  = Haar * (1 + sqrt(2^t delta_X / |V|)),  delta_X = 2^t sum N^2/|P|^2 - 1   (t = s - sigma)
// usage: ./bilinear_check pstate_file N K
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
typedef unsigned __int128 u128;
static uint64_t inv3pow[128]; static u128 p3[128]; static int Kb[128];
static void realize(const int *dd, int L, u128 *r, int *S) {
  u128 rr = 1, mm = 1; int SS = 0;
  for (int j = 0; j < L; j++) { int d = dd[j]; u128 A = 3 * mm + 1; uint64_t Ah = (uint64_t)(A >> 1);
    uint64_t t = (((1ULL << (d - 1)) - Ah) * inv3pow[j + 1]) & ((1ULL << d) - 1);
    u128 z = 3 * (mm + 2 * p3[j] * (u128)t) + 1; rr += (u128)t << (SS + 1); mm = z >> d; SS += d; }
  *r = rr; *S = SS;
}
int main(int argc, char **argv) {
  FILE *f = fopen(argv[1], "rb"); int N = atoi(argv[2]), K = atoi(argv[3]); int hdr[4]; fread(hdr, 4, 4, f);
  int c = hdr[0], J = hdr[1], B = hdr[2], smaxP = hdr[3];
  const long double A = 1.584962500721156181453738943947816508759814407692481060455L;
  for (int j = 1; j < 128; j++) Kb[j] = (int)floorl(c + j * A);
  uint64_t inv3 = 0xAAAAAAAAAAAAAAABULL; inv3pow[0] = 1; for (int k = 1; k < 128; k++) inv3pow[k] = inv3pow[k - 1] * inv3;
  p3[0] = 1; for (int k = 1; k < 80; k++) p3[k] = 3 * p3[k - 1];
  uint64_t *H[128]; uint64_t P[128];
  for (int s = 0; s <= smaxP; s++) { H[s] = malloc(8ULL << B); fread(&P[s], 8, 1, f); fread(H[s], 8, 1ULL << B, f); }
  int L = N - J, sN = Kb[N]; double totL = 0, totH = 0, totB = 0;
  printf("c=%d j0=%d N=%d K=%d (A=%.3f) sN=%d\n", c, J, N, K, (double)N / K, sN);
  for (int sg = 0; sg <= smaxP && sg <= K - 1; sg++) {
    if (!P[sg]) continue;
    for (int s = K; s <= sN; s++) {
      int t = s - sg; if (t + 1 > B || t < L) continue;
      // enumerate suffix words v: length L, total t, shifted barrier sg + S_i(v) <= Kb[J+i]
      int v[64]; for (int i = 0; i < L; i++) v[i] = 1; long long nV = 0; double Lc = 0;
      int Lm = 1 << t; uint64_t cinv = inv3pow[J] & (Lm - 1); uint64_t Mc = 1ULL << (K - sg - 1);
      // histogram mod 2^(t+1)
      int L1 = 1 << (t + 1); double *Nx = calloc(L1, 8);
      for (uint64_t x = 0; x < (1ULL << B); x++) Nx[x & (L1 - 1)] += H[sg][x];
      double s2 = 0; for (int x = 1; x < L1; x += 2) s2 += Nx[x] * Nx[x];
      double delta = (double)Lm * s2 / ((double)P[sg] * P[sg]) - 1;
      for (;;) {
        int ok = 1, SS = sg; for (int i = 0; i < L; i++) { SS += v[i]; if (SS > Kb[J + i + 1]) { ok = 0; break; } }
        if (ok && SS == s) {
          u128 rv; int Sv; realize(v, L, &rv, &Sv); nV++;
          uint64_t r = (uint64_t)rv;
          for (int x = 1; x < L1; x += 2) { if (Nx[x] == 0) continue;
            uint64_t k = ((((r - (uint64_t)x) & (L1 - 1)) >> 1) * cinv) & (Lm - 1); if (k < Mc) Lc += Nx[x]; }
        }
        int i = L - 1; while (i >= 0) { v[i]++; int S2 = sg; for (int q = 0; q <= i; q++) S2 += v[q]; if (S2 <= Kb[J + i + 1] && S2 + (L - 1 - i) <= s) break; v[i] = 1; i--; }
        if (i < 0) break;
      }
      if (!nV) { free(Nx); continue; }
      double haar = (double)P[sg] * nV * ldexp(1.0, K - 1 - s), eps = sqrt(ldexp(delta, t) / nV);
      totL += Lc; totH += haar; totB += haar * (1 + eps);
      if (s >= sN - 2 && sg >= smaxP - 2) printf("  sigma=%d s=%d t=%d |P|=%llu |V|=%lld L/Haar=%.4f  eps_bound=%.4f  delta=%.2e\n", sg, s, t, (unsigned long long)P[sg], nV, Lc / haar, eps, delta);
      free(Nx);
    }
  }
  printf(" TOTAL post-fresh: L=%.0f Haar=%.1f L/Haar=%.4f  bilinear bound/Haar=%.4f\n", totL, totH, totL / totH, totB / totH);
  return 0;
}
