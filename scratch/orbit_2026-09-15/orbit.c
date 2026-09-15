// Parts XXII-XXIII: mean square of orbit sums  M = (1/H) sum_{lam in [H,2H)} |sum_a w_a e(lam r_a / 3^n)|^2 / (sum w)^2,
// H = 3^N, n = N + k (continuation depth beyond the resolved prefix).  Diagonal (no cancellation beyond Renyi) = sum w^2/(sum w)^2.
// families: pow2 r_a = 2^{-(a0+a)}, pow5 r_a = 5^{-(a0+a)}, rand (random units), cons r_a = r0 + a, frozen r_a = r0, and
// "path": pow2 with weights w_a = sum over an m-window of pi_i(S = m - a) from the j0=60 A=0.7 geometry (sigma=95, t=11).
#include <complex.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
typedef unsigned __int128 u128;
static uint64_t mulmod(uint64_t a, uint64_t b, uint64_t q) { return (uint64_t)((u128)a * b % q); }
static uint64_t powmod(uint64_t b, uint64_t e, uint64_t q) { uint64_t r = 1 % q; b %= q; while (e) { if (e & 1) r = mulmod(r, b, q); b = mulmod(b, b, q); e >>= 1; } return r; }
static uint64_t inv(uint64_t a, uint64_t q) { // q = 3^n, phi = 2*3^{n-1}
  uint64_t phi = q / 3 * 2; return powmod(a, phi - 1, q); }
static uint64_t s0 = 88172645463325252ULL; static uint64_t rnd(void) { s0 ^= s0 << 13; s0 ^= s0 >> 7; s0 ^= s0 << 17; return s0; }
static double run(int n, int N, int W, const uint64_t *r, const double *w) {
  uint64_t q = 1; for (int i = 0; i < n; i++) q *= 3; long H = 1; for (int i = 0; i < N; i++) H *= 3;
  double sw = 0, acc = 0; for (int a = 0; a < W; a++) sw += w[a];
  for (long lam = H; lam < 2 * H; lam++) { double complex s = 0;
    for (int a = 0; a < W; a++) if (w[a] > 0) s += w[a] * cexp(2 * M_PI * I * (double)mulmod((uint64_t)lam, r[a], q) / (double)q);
    acc += creal(s * conj(s)); }
  return acc / H / (sw * sw);
}
int main(void) {
  const int W0 = 256; uint64_t r[W0]; double w[W0];
  // path weights: pi_i(S) for j0=60, sigma=95 (A=0.7 geometry), m-window of 16 shells
  int J = 60, sg = 95, Kb[80]; for (int j = 0; j < 80; j++) Kb[j] = (int)floor(j * 1.5849625007211562);
  static double f[61][100], g[61][100]; f[0][0] = 1;
  for (int i = 0; i < J; i++) for (int S = 0; S <= Kb[i]; S++) if (f[i][S] > 0) for (int S2 = S + 1; S2 <= Kb[i + 1] && S2 <= sg; S2++) f[i + 1][S2] += f[i][S];
  g[J][sg] = 1; for (int i = J - 1; i >= 0; i--) for (int S = 0; S <= Kb[i]; S++) for (int S2 = S + 1; S2 <= Kb[i + 1] && S2 <= sg; S2++) g[i][S] += g[i + 1][S2];
  printf("n = N+k; M relative to diagonal (1 = diagonal/Renyi floor; values >> 1 = no cancellation)\n");
  int Ns[] = {8, 11}, ks[] = {1, 3, 6, 12}, Ws[] = {16, 128};
  for (int ni = 0; ni < 2; ni++) for (int ki = 0; ki < 4; ki++) for (int wi = 0; wi < 2; wi++) {
    int N = Ns[ni], k = ks[ki], W = Ws[wi], n = N + k; uint64_t q = 1; for (int i = 0; i < n; i++) q *= 3;
    int a0 = 97; double res[6], diag[6];
    const char *nm[6] = {"pow2", "pow5", "rand", "cons", "frozen", "path"};
    for (int fam = 0; fam < 6; fam++) {
      int WW = W;
      for (int a = 0; a < W0; a++) w[a] = 0;
      if (fam == 5) {  // a = m - S at step i = n-1 (if within path length), m in [107-15, 107]
        int i = n - 1; if (i > J) i = J; WW = 0;
        for (int mm = 107 - 15; mm <= 107; mm++) for (int S = 0; S <= Kb[i] && S <= sg; S++) { double pi = f[i][S] * g[i][S]; if (pi <= 0) continue;
          int a = mm - S - 1 - 40; if (a < 0 || a >= W0) continue; w[a] += pi; if (a + 1 > WW) WW = a + 1; }
        for (int a = 0; a < WW; a++) r[a] = inv(powmod(2, 40 + 1 + a, q), q);  // r_a = 2^{-(a+41)}
      } else for (int a = 0; a < W; a++) { w[a] = 1;
        if (fam == 0) r[a] = inv(powmod(2, a0 + a, q), q);
        else if (fam == 1) r[a] = inv(powmod(5, a0 + a, q), q);
        else if (fam == 2) { uint64_t x; do x = rnd() % q; while (x % 3 == 0); r[a] = x; }
        else if (fam == 3) r[a] = (123456789ULL % q) + a;
        else r[a] = 123456789ULL % q; }
      double sw = 0, sw2 = 0; for (int a = 0; a < WW; a++) { sw += w[a]; sw2 += w[a] * w[a]; }
      diag[fam] = sw2 / (sw * sw); res[fam] = run(n, N, WW, r, w) / diag[fam];
    }
    printf("N=%2d k=%2d W=%3d:", N, k, W); for (int fam = 0; fam < 6; fam++) printf("  %s=%.3f", nm[fam], res[fam]); printf("  (path diag 1/%.1f)\n", 1 / diag[5]);
  }
  return 0; }
