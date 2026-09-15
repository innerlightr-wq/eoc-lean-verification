// Exact path-product characteristic sums of the Syracuse constant over confined prefixes.
//   Phi(h) = sum_{P in P_{j0,sigma}} e(-h * 3^{-j0} q_P / 2^m),  3^{-j0} q_P = sum_i 3^{-(i+1)} 2^{S_i}  (mod 2^m)
// computed by the transfer recursion in (i, S) (state = cumulative valuation S only).
// Also the rigorous digit-swap bound  |Phi(h)| <= Bsw(h) = sum_classes |C| prod_k |cos(pi theta_k)|
// (pairs (2k+off, 2k+1+off); a pair is swappable iff both orders respect the barrier).
// usage: ./phi_dp c j0 sigma m hmax [off]
//   prints |P|, and for h = 1..hmax: |Phi|/|P|, Bsw/|P|; summary sums.
#include <complex.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
typedef unsigned __int128 u128;
static int Kb[256];
int main(int argc, char **argv) {
  int c = atoi(argv[1]), J = atoi(argv[2]), sg = atoi(argv[3]), m = atoi(argv[4]); long hmax = atol(argv[5]);
  int off = argc > 6 ? atoi(argv[6]) : 0, verbose = argc > 7 ? atoi(argv[7]) : 0;
  const long double A = 1.584962500721156181453738943947816508759814407692481060455L;
  for (int j = 0; j < 256; j++) Kb[j] = (int)floorl(c + j * A);
  u128 MASK = (m >= 128) ? ~(u128)0 : (((u128)1 << m) - 1);
  // a_i = 3^{-(i+1)} mod 2^m
  u128 inv3 = 0; { u128 x = 1; for (int k = 0; k < 7; k++) x = x * (2 - 3 * x); inv3 = x; }  // Newton: 3*inv3 = 1 mod 2^128
  u128 a[256]; a[0] = inv3 & MASK; for (int i = 1; i < J; i++) a[i] = (a[i - 1] * inv3) & MASK;
  int Smax = Kb[J];
  // counts (exact, long double enough for reporting)
  static long double cnt[256][256];
  for (int i = 0; i <= J; i++) for (int S = 0; S <= Smax; S++) cnt[i][S] = 0;
  cnt[0][0] = 1;
  for (int i = 0; i < J; i++) for (int S = 0; S <= Smax; S++) if (cnt[i][S] > 0)
    for (int d = 1; S + d <= Kb[i + 1]; d++) cnt[i + 1][S + d] += cnt[i][S];
  long double P = cnt[J][sg];
  printf("c=%d j0=%d sigma=%d (top %d) m=%d t=m-sigma-1=%d |P|=%.6Le log2|P|=%.3f\n", c, J, sg, Smax, m, m - sg - 1, P, (double)log2l(P));
  if (P == 0) return 0;
  static double complex f[256], g[256];
  static double bf[256], bg[256];
  double sumPhi2 = 0, sumB2 = 0, maxPhi = 0, maxB = 0; double sumlogPhi = 0, sumlogB = 0; long hmaxB = 0, hmaxP = 0;
  for (long h = 1; h <= hmax; h++) {
    // exact Phi via one-step transfer
    for (int S = 0; S <= Smax; S++) f[S] = 0; f[0] = 1;
    for (int i = 0; i < J; i++) {
      for (int S = 0; S <= Smax; S++) g[S] = 0;
      u128 ha = ((u128)h * a[i]) & MASK;
      for (int S = 0; S <= Smax; S++) { if (f[S] == 0) continue;
        u128 x = (ha << S) & MASK; double th = (double)((long double)x / ldexpl(1.0L, m));
        double complex ph = cexp(-2 * M_PI * I * th); double complex v = f[S] * ph;
        for (int d = 1; S + d <= Kb[i + 1]; d++) g[S + d] += v; }
      for (int S = 0; S <= Smax; S++) f[S] = g[S];
    }
    double ph2 = cabs(f[sg]) / (double)P;
    // swap bound: process singles before offset, then pairs
    for (int S = 0; S <= Smax; S++) bf[S] = 0; bf[0] = 1;
    int i = 0;
    while (i < J) {
      for (int S = 0; S <= Smax; S++) bg[S] = 0;
      if (i < off || i + 1 >= J) {  // single step, weight 1
        for (int S = 0; S <= Smax; S++) if (bf[S] > 0) for (int d = 1; S + d <= Kb[i + 1]; d++) bg[S + d] += bf[S];
        i += 1;
      } else {  // pair (i, i+1): phase at step i+1 depends on S_{i+1}
        for (int S = 0; S <= Smax; S++) { if (bf[S] == 0) continue;
          for (int d = 1; S + d <= Kb[i + 1]; d++) for (int e = 1; S + d + e <= Kb[i + 2]; e++) {
            if (d == e) { bg[S + d + e] += bf[S]; continue; }
            int swappable = (S + e <= Kb[i + 1]);
            if (!swappable) { bg[S + d + e] += bf[S]; continue; }
            if (d > e) continue;  // count unordered swappable pair once (d < e)
            u128 ha = ((u128)h * a[i + 1]) & MASK;
            u128 x1 = (ha << (S + d)) & MASK, x2 = (ha << (S + e)) & MASK;
            long double diff = ((long double)x1 - (long double)x2) / ldexpl(1.0L, m);
            double w = 2 * fabs(cos(M_PI * (double)diff));
            bg[S + d + e] += bf[S] * w; }
        }
        i += 2;
      }
      for (int S = 0; S <= Smax; S++) bf[S] = bg[S];
    }
    double bsw = bf[sg] / (double)P;
    sumPhi2 += ph2 * ph2; sumB2 += bsw * bsw; if (ph2 > maxPhi) { maxPhi = ph2; hmaxP = h; } if (bsw > maxB) { maxB = bsw; hmaxB = h; } sumlogPhi += log2(ph2 + 1e-300); sumlogB += log2(bsw);
    if (verbose) printf("  h=%ld |Phi|/|P|=%.3e  Bsw/|P|=%.3e\n", h, ph2, bsw);
  }
  printf("  h=1..%ld: sum|Phi/P|^2=%.3e (random %.3e)  max|Phi/P|=%.3e @h=%ld  mean log2|Phi/P|=%.2f (random %.2f)\n", hmax, sumPhi2, (double)(hmax / P), maxPhi, hmaxP, sumlogPhi / hmax, -0.5 * (double)log2l(P) - 0.36);
  printf("  swap bound: max=%.3e @h=%ld (log2 %.2f) rms=%.3e mean log2=%.2f  sum^2=%.3e  per-step rates: max %.4f rms %.4f\n", maxB, hmaxB, log2(maxB), sqrt(sumB2 / hmax), sumlogB / hmax, sumB2, -log2(maxB) / J, -0.5 * log2(sumB2 / hmax) / J);
  return 0;
}
