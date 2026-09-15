// Exact low-frequency spacing diagnostics for the prefix phase points zeta_P = 3^{-j0} q_P / 2^m (A=0.7 geometry, c=0).
// Phi(lam)/|P| computed exactly (O(j0*D) backward DP per lam, 320-bit phases) for 1 <= lam < 2^U.
// Outputs per u <= U:
//   Fejer pair count  E(u)/|P|^2 = 2^-u [1 + 2 sum_{0<lam<2^u} (1-lam/2^u)|Phi/P|^2]  (triangle-weighted pairs at scale 2^-u)
//   theta_eff(u) = -log2(E(u)/|P|^2)/u ;  excess(u) = 2^u E(u)/|P|^2 - 1  (0 for Haar-at-scale; floor 2^u/|P|)
//   shell average a_u = mean_{2^u <= lam < 2^{u+1}} |Phi/P|^2 and its exponent -log2(a_u)/u
// plus gamma_1 = -log2|Phi(1)/P| / j0.     usage: spacing j0 sigma t U
#include <complex.h>
#include <quadmath.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned __int128 u128;
#define NL 10
typedef struct { uint64_t w[NL]; } Ub;
static Ub mulU(Ub a, Ub b) { Ub r; memset(&r, 0, sizeof r); for (int i = 0; i < NL; i++) { u128 c = 0; for (int j = 0; i + j < NL; j++) { u128 x = (u128)a.w[i] * b.w[j] + r.w[i + j] + c; r.w[i + j] = (uint64_t)x; c = x >> 64; } } return r; }
static uint64_t b64(Ub a, int lo) { if (lo >= 0) { int q = lo >> 6, s = lo & 63; uint64_t x0 = q < NL ? a.w[q] : 0, x1 = q + 1 < NL ? a.w[q + 1] : 0; return s ? (x0 >> s) | (x1 << (64 - s)) : x0; } int sh = -lo; return sh >= 64 ? 0 : a.w[0] << sh; }
int main(int argc, char **argv) {
  int J = atoi(argv[1]), sg = atoi(argv[2]), t = atoi(argv[3]), U = atoi(argv[4]), m = sg + t + 1, Kb[1024];
  for (int j = 0; j < 1024; j++) Kb[j] = (int)floorl(j * 1.584962500721156181453738943947816508759814407692481060455L);
  int D = Kb[J] + 3; double **cnt = malloc(sizeof(double *) * (J + 2)); for (int i = 0; i <= J + 1; i++) cnt[i] = calloc(D, 8);
  cnt[J][sg] = 1; for (int i = J - 1; i >= 0; i--) for (int S = 0; S <= Kb[i] && S < D; S++) { double v = 0; for (int d = 1; S + d <= Kb[i + 1] && S + d < D; d++) v += cnt[i + 1][S + d]; cnt[i][S] = v; }
  double P = cnt[0][0];
  Ub inv3; static Ub a[1024]; for (int k = 0; k < NL; k++) inv3.w[k] = 0xAAAAAAAAAAAAAAAAULL; inv3.w[0] = 0xAAAAAAAAAAAAAAABULL;
  a[0] = inv3; for (int i = 1; i < J + 2; i++) a[i] = mulU(a[i - 1], inv3);   // a[i] = 3^{-(i+1)}
  __complex128 *f = malloc(sizeof(__complex128) * D), *g = malloc(sizeof(__complex128) * D);
  long H = 1L << U; double *ph = malloc(8 * H);
  for (long lam = 1; lam < H; lam++) {
    Ub L; memset(&L, 0, sizeof L); L.w[0] = (uint64_t)lam;
    for (int S = 0; S < D; S++) f[S] = (S == sg) ? 1 : 0;
    for (int i = J - 1; i >= 0; i--) {
      Ub ha = mulU(a[i], L); __complex128 suf = 0;
      for (int S = D - 1; S >= 0; S--) {  // suf = sum_{S' > S, S' <= b(i+1)} cnt[i+1][S'] f[S']
        g[S] = 0;
        if (S <= Kb[i] && cnt[i][S] > 0) { __float128 x = (__float128)b64(ha, m - S - 64) * 0x1p-64Q + (__float128)b64(ha, m - S - 128) * 0x1p-128Q; __complex128 ph; __real__ ph = cosq(2 * M_PIq * x); __imag__ ph = -sinq(2 * M_PIq * x); g[S] = suf / cnt[i][S] * ph; }
        if (S <= Kb[i + 1] && S >= 1) suf += cnt[i + 1][S] * f[S];
      }
      memcpy(f, g, sizeof(__complex128) * D); }
    ph[lam] = (double)(crealq(f[0]) * crealq(f[0]) + cimagq(f[0]) * cimagq(f[0]));
  }
  printf("j0=%d sigma=%d t=%d m=%d log2|P|=%.2f  H2=0.949956  gamma_1=%.4f (|Phi(1)/P|^2=%.3e)\n", J, sg, t, m, log2(P), -0.5 * log2(ph[1]) / J, ph[1]);
  for (int u = 1; u <= U; u++) { long Hu = 1L << u; double ex = 0, lo = 0; for (long l = 1; l < Hu; l++) { ex += 2 * (1 - (double)l / Hu) * ph[l]; lo += ph[l]; } double s = 1 + ex;
    double E = s / Hu, sh = 0; long n = 0; if (u < U) for (long l = Hu; l < 2 * Hu; l++) { sh += ph[l]; n++; }
    printf(" u=%2d E/P^2=%.4e theta_eff=%.5f margin=%+.5f excess=%.3e excess*|P|/2^u=%.3f mean_{0<l<2^u}|Phi/P|^2=%.3e", u, E, -log2(E) / u, -log2(E) / u - 0.949956, ex, ex * P / Hu, lo / (Hu - 1));
    if (n) printf("  a_u*|P|=%.3f", sh / n * P);
    printf("\n"); }
  return 0; }
