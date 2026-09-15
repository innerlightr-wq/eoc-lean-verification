// Block transfer operators of the q_P path product: T_l(h) = A_l D_l(h), D_l = diag_S e(-h 3^{-(l+1)} 2^S / 2^m),
// A_l : S -> S+d (d = 1..b(l+1)-S).  Reports rho_L(h) = ||T_{i0+L-1}...T_{i0}(h)||_2 / ||A_{i0+L-1}...A_{i0}||_2
// (spectral norms by power iteration), for L = 1..Lmax, averaged/maxed over h = 1..H and start i0 in a range.
// usage: ./block_norm c j0 m Lmax H i0min i0max
#include <complex.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned __int128 u128;
static int Kb[256], D;
static double specnorm(double complex *M, int n, int k) {  // M is n x k (rows = out, cols = in)
  static double complex v[256], w[256]; for (int j = 0; j < k; j++) v[j] = 1.0 + 0.1 * j + 0.01 * I * (j % 3);
  double lam = 0;
  for (int it = 0; it < 400; it++) {
    for (int r = 0; r < n; r++) { double complex s = 0; for (int j = 0; j < k; j++) s += M[r * k + j] * v[j]; w[r] = s; }
    for (int j = 0; j < k; j++) { double complex s = 0; for (int r = 0; r < n; r++) s += conj(M[r * k + j]) * w[r]; v[j] = s; }
    double nv = 0; for (int j = 0; j < k; j++) nv += creal(v[j] * conj(v[j])); nv = sqrt(nv);
    if (nv == 0) return 0; lam = nv; for (int j = 0; j < k; j++) v[j] /= nv;
  }
  return sqrt(lam);
}
int main(int argc, char **argv) {
  int c = atoi(argv[1]), J = atoi(argv[2]), m = atoi(argv[3]), Lmax = atoi(argv[4]); long H = atol(argv[5]);
  int i0min = atoi(argv[6]), i0max = atoi(argv[7]);
  const long double A = 1.584962500721156181453738943947816508759814407692481060455L;
  for (int j = 0; j < 256; j++) Kb[j] = (int)floorl(c + j * A);
  u128 MASK = (((u128)1) << m) - 1, inv3; { u128 x = 1; for (int k = 0; k < 7; k++) x = x * (2 - 3 * x); inv3 = x; }
  u128 a[256]; a[0] = inv3 & MASK; for (int i = 1; i < J; i++) a[i] = (a[i - 1] * inv3) & MASK;
  D = Kb[J] + 1;
  double *sumr = calloc(Lmax + 1, 8), *maxr = calloc(Lmax + 1, 8); long cntr = 0;
  double complex *M = malloc(16 * D * D), *T = malloc(16 * D * D), *M0 = malloc(16 * D * D), *T0 = malloc(16 * D * D);
  for (int i0 = i0min; i0 <= i0max; i0++) for (long h = 1; h <= H; h++) {
    // M = identity restricted to states S <= Kb[i0]
    for (int x = 0; x < D * D; x++) { M[x] = 0; M0[x] = 0; } for (int S = 0; S <= Kb[i0]; S++) { M[S * D + S] = 1; M0[S * D + S] = 1; }
    for (int L = 1; L <= Lmax; L++) {
      int l = i0 + L - 1; u128 ha = ((u128)h * a[l]) & MASK;
      for (int x = 0; x < D * D; x++) { T[x] = 0; T0[x] = 0; }
      for (int Sp = 0; Sp < D; Sp++) for (int col = 0; col < D; col++) {  // T = A_l D_l M
        double complex s = 0, s0 = 0;
        for (int d = 1; d <= Sp; d++) { int S = Sp - d; if (Sp > Kb[l + 1]) break;
          u128 xx = (ha << S) & MASK; double th = (double)((long double)xx / ldexpl(1.0L, m));
          s += cexp(-2 * M_PI * I * th) * M[S * D + col]; s0 += M0[S * D + col]; }
        T[Sp * D + col] = s; T0[Sp * D + col] = s0; }
      memcpy(M, T, 16 * D * D); memcpy(M0, T0, 16 * D * D);
      double r = specnorm(M, D, D) / specnorm(M0, D, D);
      sumr[L] += log2(r); if (r > maxr[L]) maxr[L] = r;
    }
    cntr++;
  }
  printf("c=%d j0=%d m=%d H=%ld i0 in [%d,%d]: block norm ratios ||T_L(h)||/||A^L||\n", c, J, m, H, i0min, i0max);
  for (int L = 1; L <= Lmax; L++) printf("  L=%2d  mean log2 ratio=%+.4f (per step %+.4f)  max ratio=%.4f\n", L, sumr[L] / cntr, sumr[L] / cntr / L, maxr[L]);
  return 0;
}
