// Word-level least-realizer statistics for Parts VIII, IX, XIII.
// Enumerates positive words of length N with least realizers r(D) mod 2^{S+1} (lift recursion),
// either c-confined (mode 0) or terminal-only S_N <= s_N (mode 1, "unconstrained" prefix).
// For u = r/2^{S+1}: Fourier coefficients nu^(m), local counts #{u < 2^-j}, 4096-bin histogram
// (star discrepancy at resolution 1/4096), per shell x = s_N - S (x<=2) and total.
// Transfer rule: for the final digit d, the lift digit t in [0,2^d) (top d bits of u): counts.
// usage: ./word_fourier mode c N
#include <complex.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned __int128 u128;
#define NS 4
static const int MS[] = {1, 2, 3, 4, 5, 7, 8, 16, 64, 256, 1024, 4096, 65536, 1048576};
#define NM 14
static int N, c, mode, Kb[128], sN;
static double cnt[NS];
static double complex F[NS][NM];
static double loc[NS][64];
static unsigned long long hist[NS][4096];
static unsigned long long lift[8][64];
static uint64_t inv3pow[128];
static inline int ctz128(u128 x) { uint64_t lo = (uint64_t)x; return lo ? __builtin_ctzll(lo) : 64 + __builtin_ctzll((uint64_t)(x >> 64)); }
static void rec(int x, double u, int dlast, uint64_t tlast) {
  int sh[2] = {x < NS - 1 ? x : -1, NS - 1};
  for (int k = 0; k < 2; k++) {
    int s = sh[k]; if (s < 0) continue;
    cnt[s] += 1;
    for (int i = 0; i < NM; i++) { double ph = 2 * M_PI * fmod((double)MS[i] * u, 1.0); F[s][i] += cexp(I * ph); }
    for (int j = 1; j < 64; j++) { if (u < ldexp(1.0, -j)) loc[s][j] += 1; else break; }
    int b = (int)(u * 4096); if (b > 4095) b = 4095; hist[s][b]++;
  }
  if (dlast < 8 && dlast >= 1) lift[dlast][tlast & 63]++;
}
static void dfs(int j, int S, u128 r, u128 m, int dlast, uint64_t tlast) {
  if (j == N) { rec(sN - S, (double)r / ldexp(1.0, S + 1), dlast, tlast); return; }
  int dmax = (mode == 0) ? Kb[j + 1] - S : (sN - S) - (N - j - 1);
  u128 A = 3 * m + 1; uint64_t Ah = (uint64_t)(A >> 1);
  u128 p3 = 1; for (int i = 0; i < j; i++) p3 *= 3;
  for (int d = 1; d <= dmax && d < 60; d++) {
    uint64_t mask = (1ULL << d) - 1;
    uint64_t t = (((1ULL << (d - 1)) - Ah) * inv3pow[j + 1]) & mask;
    u128 r2 = r + ((u128)t << (S + 1));
    u128 z = 3 * (m + 2 * p3 * (u128)t) + 1;
    dfs(j + 1, S + d, r2, z >> d, d, t);
  }
}
int main(int argc, char **argv) {
  mode = atoi(argv[1]); c = atoi(argv[2]); N = atoi(argv[3]);
  const long double A = 1.584962500721156181453738943947816508759814407692481060455L;
  for (int j = 1; j <= N; j++) Kb[j] = (int)floorl(c + j * A);
  sN = Kb[N];
  uint64_t inv3 = 0xAAAAAAAAAAAAAAABULL; inv3pow[0] = 1;
  for (int k = 1; k < 128; k++) inv3pow[k] = inv3pow[k - 1] * inv3;
  dfs(0, 0, 1, 1, 0, 0);
  const char *nm[NS] = {"x=0", "x=1", "x=2", "all"};
  printf("mode=%s c=%d N=%d sN=%d phi=%.4f\n", mode ? "terminal-only" : "confined", c, N, sN, fmod((double)N * (double)A, 1.0));
  for (int s = 0; s < NS; s++) {
    double n = cnt[s]; if (n < 1) continue;
    double cum = 0, ds = 0;
    for (int b = 0; b < 4096; b++) { cum += hist[s][b]; double d1 = fabs(cum / n - (b + 1) / 4096.0), d0 = fabs((cum - hist[s][b]) / n - b / 4096.0); if (d1 > ds) ds = d1; if (d0 > ds) ds = d0; }
    printf("  %s n=%.0f Dstar4096=%.3e Dstar*sqrt(n)=%.3f |F(m)|*sqrt(n):", nm[s], n, ds, ds * sqrt(n));
    for (int i = 0; i < NM; i++) printf(" %d:%.2f", MS[i], cabs(F[s][i]) / sqrt(n));
    printf("\n     local z_j=(#u<2^-j - n2^-j)/sqrt(n2^-j):");
    for (int j = 1; j < 64; j++) { double e = n * ldexp(1.0, -j); if (e < 20) break; printf(" %d:%+.2f", j, (loc[s][j] - e) / sqrt(e)); }
    printf("\n");
  }
  printf("  lift-digit uniformity (final digit d, t in [0,2^d)): chi2/dof:");
  for (int d = 1; d < 7; d++) {
    double tot = 0; for (int t = 0; t < (1 << d); t++) tot += lift[d][t];
    if (tot < 100 || d > 6) continue;
    double e = tot / (1 << d), chi = 0; for (int t = 0; t < (1 << d); t++) chi += (lift[d][t] - e) * (lift[d][t] - e) / e;
    printf(" d=%d:%.2f(n=%.0f)", d, chi / ((1 << d) - 1), tot);
  }
  printf("\n");
  return 0;
}
