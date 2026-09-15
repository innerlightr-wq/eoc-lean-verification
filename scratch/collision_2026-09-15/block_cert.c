// Rigorous block-norm certificate: |Phi(h)| <= prod_b ||T_b(h)||_2 where the prefix path is cut
// into consecutive blocks of length L (T_b = product of one-step operators A_l D_l(h) in block b,
// restricted to reachable states).  Reports log2(prod_b ||T_b(h)|| / |P|) (a valid upper bound on
// log2 |Phi(h)|/|P|) and the h=0 loss log2(prod_b ||A_b|| / |P|).
// usage: ./block_cert c j0 sigma m L H
#include <complex.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned __int128 u128;
static int Kb[256], D;
static double specnorm(double complex *M, int n) {
  static double complex v[256], w[256]; for (int j = 0; j < n; j++) v[j] = 1.0 + 0.37 * j + 0.11 * I * (j % 5);
  double lam = 0, prev = -1;
  for (int it = 0; it < 2000; it++) {
    for (int r = 0; r < n; r++) { double complex s = 0; for (int j = 0; j < n; j++) s += M[r * n + j] * v[j]; w[r] = s; }
    for (int j = 0; j < n; j++) { double complex s = 0; for (int r = 0; r < n; r++) s += conj(M[r * n + j]) * w[r]; v[j] = s; }
    double nv = 0; for (int j = 0; j < n; j++) nv += creal(v[j] * conj(v[j])); nv = sqrt(nv);
    if (nv == 0) return 0; lam = nv; for (int j = 0; j < n; j++) v[j] /= nv;
    if (fabs(lam - prev) < 1e-13 * lam) break; prev = lam;
  }
  return sqrt(lam) * (1 + 1e-9);   // power iteration converges from below; small safety factor
}
int main(int argc, char **argv) {
  int c = atoi(argv[1]), J = atoi(argv[2]), sg = atoi(argv[3]), m = atoi(argv[4]), L = atoi(argv[5]); long H = atol(argv[6]);
  const long double A = 1.584962500721156181453738943947816508759814407692481060455L;
  for (int j = 0; j < 256; j++) Kb[j] = (int)floorl(c + j * A);
  u128 MASK = (((u128)1) << m) - 1, inv3; { u128 x = 1; for (int k = 0; k < 7; k++) x = x * (2 - 3 * x); inv3 = x; }
  u128 a[256]; a[0] = inv3 & MASK; for (int i = 1; i < J; i++) a[i] = (a[i - 1] * inv3) & MASK;
  D = Kb[J] + 1;
  // reachable-and-coreachable states: need count to (J, sg)
  static long double cnt[256][256], pre[256][256]; memset(cnt, 0, sizeof cnt); memset(pre, 0, sizeof pre);
  cnt[J][sg] = 1; for (int i = J - 1; i >= 0; i--) for (int S = 0; S <= Kb[i]; S++) { long double v = 0; for (int d = 1; S + d <= Kb[i + 1]; d++) v += cnt[i + 1][S + d]; cnt[i][S] = v; }
  pre[0][0] = 1; for (int i = 0; i < J; i++) for (int S = 0; S <= Kb[i]; S++) if (pre[i][S] > 0) for (int d = 1; S + d <= Kb[i + 1]; d++) pre[i + 1][S + d] += pre[i][S];
  long double P = cnt[0][0];
  double complex *M = malloc(16 * D * D), *T = malloc(16 * D * D);
  double worst = -1e9, sumlog = 0, loss0 = 0;
  for (long h = 0; h <= H; h++) {
    double logb = 0;
    for (int i0 = 0; i0 < J; i0 += L) {
      int i1 = i0 + L < J ? i0 + L : J;
      for (int x = 0; x < D * D; x++) M[x] = 0;
      for (int S = 0; S < D; S++) if (pre[i0][S] > 0 && cnt[i0][S] > 0) M[S * D + S] = 1;
      for (int l = i0; l < i1; l++) {
        u128 ha = ((u128)h * a[l]) & MASK;
        for (int x = 0; x < D * D; x++) T[x] = 0;
        for (int Sp = 0; Sp < D; Sp++) { if (!(pre[l + 1][Sp] > 0 && cnt[l + 1][Sp] > 0)) continue;
          for (int d = 1; d <= Sp && d <= Kb[l + 1]; d++) { int S = Sp - d; if (Sp > Kb[l + 1]) continue;
            u128 xx = (ha << S) & MASK; double th = (double)((long double)xx / ldexpl(1.0L, m)); double complex ph = cexp(-2 * M_PI * I * th);
            for (int col = 0; col < D; col++) T[Sp * D + col] += ph * M[S * D + col]; } }
        memcpy(M, T, 16 * D * D);
      }
      logb += log2(specnorm(M, D));
    }
    double rel = logb - (double)log2l(P);
    if (h == 0) loss0 = rel; else { sumlog += rel; if (rel > worst) worst = rel; }
  }
  printf("c=%d j0=%d sigma=%d m=%d L=%d H=%ld: h=0 loss log2(prod||A_b||/|P|)=%+.2f;  h>0: mean log2 bound=%+.2f (per step %+.4f)  worst=%+.2f (per step %+.4f)\n",
         c, J, sg, m, L, H, loss0, sumlog / H, sumlog / H / J, worst, worst / J);
  return 0;
}
