// Exact split-depth decomposition of the smoothed prefix collision sum
//   sum_{h=1}^{H} |Phi(h)|^2 = H |P| + sum_i sum_h C_i(h),
//   C_i(h) = sum_S pre(i,S) [ |sum_d G_{i+1,S+d}(h)|^2 - sum_d |G_{i+1,S+d}(h)|^2 ]
// (ordered off-diagonal pairs whose first differing digit is at step i), with the backward
// subtree transforms G_{i,S}(h) = e(-h 3^{-(i+1)} 2^S / 2^m) sum_d G_{i+1,S+d}(h), G_{j0,sigma} = 1.
// usage: ./split_dp c j0 sigma m H
#include <complex.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned __int128 u128;
static int Kb[256];
int main(int argc, char **argv) {
  int c = atoi(argv[1]), J = atoi(argv[2]), sg = atoi(argv[3]), m = atoi(argv[4]); long H = atol(argv[5]);
  const long double A = 1.584962500721156181453738943947816508759814407692481060455L;
  for (int j = 0; j < 256; j++) Kb[j] = (int)floorl(c + j * A);
  u128 MASK = (((u128)1) << m) - 1, inv3; { u128 x = 1; for (int k = 0; k < 7; k++) x = x * (2 - 3 * x); inv3 = x; }
  u128 a[256]; a[0] = inv3 & MASK; for (int i = 1; i < J; i++) a[i] = (a[i - 1] * inv3) & MASK;
  int Sm = Kb[J];
  static long double pre[256][256], cnt[256][256];
  memset(pre, 0, sizeof pre); memset(cnt, 0, sizeof cnt); pre[0][0] = 1;
  for (int i = 0; i < J; i++) for (int S = 0; S <= Sm; S++) if (pre[i][S] > 0) for (int d = 1; S + d <= Kb[i + 1]; d++) pre[i + 1][S + d] += pre[i][S];
  cnt[J][sg] = 1;
  for (int i = J - 1; i >= 0; i--) for (int S = 0; S <= Kb[i]; S++) { long double v = 0; for (int d = 1; S + d <= Kb[i + 1]; d++) v += cnt[i + 1][S + d]; cnt[i][S] = v; }
  long double P = pre[J][sg];
  static double complex G[256][256];
  static double Csum[256]; memset(Csum, 0, sizeof Csum);
  static long double pairs[256];
  for (int i = 0; i < J; i++) { long double acc = 0; for (int S = 0; S <= Kb[i]; S++) { if (pre[i][S] == 0) continue; long double s1 = 0, s2 = 0;
      for (int d = 1; S + d <= Kb[i + 1]; d++) { s1 += cnt[i + 1][S + d]; s2 += cnt[i + 1][S + d] * cnt[i + 1][S + d]; } acc += pre[i][S] * (s1 * s1 - s2); } pairs[i] = acc; }
  double totPhi2 = 0;
  for (long h = 1; h <= H; h++) {
    for (int S = 0; S <= Sm; S++) G[J][S] = (S == sg);
    for (int i = J - 1; i >= 0; i--) {
      u128 ha = ((u128)h * a[i]) & MASK;
      for (int S = 0; S <= Kb[i]; S++) {
        double complex v = 0; for (int d = 1; S + d <= Kb[i + 1]; d++) v += G[i + 1][S + d];
        u128 x = (ha << S) & MASK; double th = (double)((long double)x / ldexpl(1.0L, m));
        G[i][S] = v * cexp(-2 * M_PI * I * th);
      }
      for (int S = Kb[i] + 1; S <= Sm; S++) G[i][S] = 0;
    }
    totPhi2 += creal(G[0][0] * conj(G[0][0]));
    for (int i = 0; i < J; i++) for (int S = 0; S <= Kb[i]; S++) { if (pre[i][S] == 0) continue;
      double complex s1 = 0; double s2 = 0; for (int d = 1; S + d <= Kb[i + 1]; d++) { s1 += G[i + 1][S + d]; s2 += creal(G[i + 1][S + d] * conj(G[i + 1][S + d])); }
      Csum[i] += (double)pre[i][S] * (creal(s1 * conj(s1)) - s2); }
  }
  double P2 = (double)(P * P);
  printf("c=%d j0=%d sigma=%d m=%d t=%d H=%ld |P|=%.4Le\n", c, J, sg, m, m - sg - 1, H, P);
  printf("  sum_h |Phi|^2/|P|^2 = %.4e = diag %.4e + offdiag %.4e\n", totPhi2 / P2, H / (double)P, (totPhi2 - H * (double)P) / P2);
  double cum = 0;
  for (int i = 0; i < J; i++) { cum += Csum[i] / P2;
    if (i < 8 || i % 5 == 0 || i == J - 1) printf("  split i=%2d: pair share=%.3e  offdiag contribution=%+.3e (per-pair-normalized %+.3e) cum=%+.3e\n", i, (double)(pairs[i] / (P * (P - 1))), Csum[i] / P2, Csum[i] / (double)pairs[i] / H, cum); }
  return 0;
}
