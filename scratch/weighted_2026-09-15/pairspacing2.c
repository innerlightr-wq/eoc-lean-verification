// Pair-spacing statistics of prefix phases zeta_P = y'_P / 2^m, y'_P = 3^{-j0}(2^sigma - q_P) mod 2^m (m = sigma+T+1),
// uniform confined prefixes P in P_{j0,sigma} (sampled via backward counts), 320-bit Horner q_{i+1} = 3 q_i + 2^{S_i}.
// E(q)/Haar = #{sampled pairs with circular distance < 2^-q} / (Ns(Ns-1) 2^-q).   usage: ./pairspacing2 c j0 sigma Ns seed T
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned __int128 u128;
#define NL 5
typedef struct { uint64_t w[NL]; } U;
static U mulU(U a, U b) { U r; memset(&r, 0, sizeof r); for (int i = 0; i < NL; i++) { u128 c = 0; for (int j = 0; i + j < NL; j++) { u128 x = (u128)a.w[i] * b.w[j] + r.w[i + j] + c; r.w[i + j] = (uint64_t)x; c = x >> 64; } } return r; }
static U addU(U a, U b) { U r; u128 c = 0; for (int i = 0; i < NL; i++) { u128 x = (u128)a.w[i] + b.w[i] + c; r.w[i] = (uint64_t)x; c = x >> 64; } return r; }
static U subU(U a, U b) { U r; u128 br = 0; for (int i = 0; i < NL; i++) { u128 x = (u128)a.w[i] - b.w[i] - br; r.w[i] = (uint64_t)x; br = (x >> 64) ? 1 : 0; } return r; }
static U pow2U(int k) { U r; memset(&r, 0, sizeof r); r.w[k >> 6] = 1ULL << (k & 63); return r; }
static uint64_t b64(U a, int lo) { if (lo >= 0) { int q = lo >> 6, s = lo & 63; uint64_t x0 = q < NL ? a.w[q] : 0, x1 = q + 1 < NL ? a.w[q + 1] : 0; return s ? (x0 >> s) | (x1 << (64 - s)) : x0; } int sh = -lo; return sh >= 64 ? 0 : a.w[0] << sh; }
static int Kb[512]; static uint64_t s0, s1;
static inline uint64_t rnd(void) { uint64_t a = s0, b = s1; s0 = b; a ^= a << 23; s1 = a ^ b ^ (a >> 17) ^ (b >> 26); return s1 + b; }
static int cmpd(const void *x, const void *y) { double a = *(const double *)x, b = *(const double *)y; return a < b ? -1 : a > b; }
int main(int argc, char **argv) {
  int c = atoi(argv[1]), J = atoi(argv[2]), sg = atoi(argv[3]); long Ns = atol(argv[4]); s0 = 0x9E3779B97F4A7C15ULL ^ atoll(argv[5]); s1 = 0xD1B54A32D192ED03ULL; int T = atoi(argv[6]);
  int m = sg + T + 1; const long double A = 1.584962500721156181453738943947816508759814407692481060455L;
  for (int j = 0; j < 512; j++) Kb[j] = (int)floorl(c + j * A);
  static double comp[512][520]; memset(comp, 0, sizeof comp); comp[J][sg] = 1;
  for (int i = J - 1; i >= 0; i--) for (int S = 0; S <= Kb[i]; S++) { double v = 0; for (int d = 1; S + d <= Kb[i + 1]; d++) v += comp[i + 1][S + d]; comp[i][S] = v; }
  U inv3; for (int k = 0; k < NL; k++) inv3.w[k] = 0xAAAAAAAAAAAAAAAAULL; inv3.w[0] = 0xAAAAAAAAAAAAAAABULL;
  U i3J = pow2U(0); i3J.w[0] = 1; for (int k = 0; k < J; k++) i3J = mulU(i3J, inv3);
  U three; memset(&three, 0, sizeof three); three.w[0] = 3;
  double *zz = malloc(8 * Ns);
  for (long n = 0; n < Ns; n++) {
    int S = 0; U q; memset(&q, 0, sizeof q);
    for (int j = 0; j < J; j++) {
      q = addU(mulU(q, three), pow2U(S));   // q_{j+1} = 3 q_j + 2^{S_j}
      double tot = comp[j][S], u = (rnd() >> 11) * (1.0 / 9007199254740992.0) * tot, acc = 0; int d = 1;
      for (;; d++) { acc += comp[j + 1][S + d]; if (u < acc || S + d >= Kb[j + 1]) break; }
      S += d;
    }
    U y = mulU(subU(pow2U(sg), q), i3J);   // mod 2^320; read bits below m
    zz[n] = (double)b64(y, m - 64) / 18446744073709551616.0;
  }
  qsort(zz, Ns, 8, cmpd);
  printf("c=%d j0=%d sigma=%d T=%d Ns=%ld  log2|P|=%.1f\n", c, J, sg, T, Ns, log2(comp[0][0]));
  for (int qq = 4; qq <= T; qq += 2) { double w = ldexp(1.0, -qq); long double pairs = 0; long jj = 0;
    for (long i = 0; i < Ns; i++) { if (jj < i + 1) jj = i + 1; while (jj < 2 * Ns && ((jj < Ns ? zz[jj] : zz[jj - Ns] + 1) - zz[i]) < w) jj++; pairs += (jj - i - 1); }
    long double haar = (long double)Ns * (Ns - 1) * w; double se = 1 / sqrt((double)haar);
    printf("  q=%2d E/Haar=%.5f (+-%.5f)\n", qq, (double)(pairs / haar), se); }
  return 0;
}
