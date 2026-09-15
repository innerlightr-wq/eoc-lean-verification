// Exact weighted target of the A=0.7 chain (repo-native, TwistExpansion + WeightedChain):
//   LHS_W = (1 + r/2) * sum_{lambda in Z/2^m, lambda != 0 mod 2^t} cosProd(r,t,lambda) |Phi(lambda)|^2 ,  r = sigma+1, m = sigma+t+1
//   cosProd = prod_{j<r} |cos(pi lambda 2^j / 2^m)| = ||coef||,   Phi(lambda) = sum_P e(-lambda 3^{-j0} q_P / 2^m)  (|Phi| = |Psi|)
//   RHS(eps=1) = |P|^2 |V| / 2^t ;  ratio R = LHS_W / RHS  (need R <= eps^2).
// Dyadic shells in |lambda|_centered: shell u = [2^{t+u}, 2^{t+u+1}) (u = -t.. : shell "low" = [1,2^t)), each mirrored (x2).
// Shells with t+u+1 <= EXH (bits) enumerated exhaustively; higher shells sampled (nsamp uniform lambdas, unbiased).
// Also: A2 = mean_{1<=lambda<2^t} |Phi/P|^2 and its breakdown by v2 and v3.
// usage: ./phi_weighted c j0 sigma t V EXH nsamp seed
#include <complex.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned __int128 u128;
#define NL 5
typedef struct { uint64_t w[NL]; } U;
static U mulU(U a, U b) { U r; memset(&r, 0, sizeof r); for (int i = 0; i < NL; i++) { u128 c = 0; for (int j = 0; i + j < NL; j++) { u128 x = (u128)a.w[i] * b.w[j] + r.w[i + j] + c; r.w[i + j] = (uint64_t)x; c = x >> 64; } } return r; }
static uint64_t b64(U a, int lo) { if (lo >= 0) { int q = lo >> 6, s = lo & 63; uint64_t x0 = q < NL ? a.w[q] : 0, x1 = q + 1 < NL ? a.w[q + 1] : 0; return s ? (x0 >> s) | (x1 << (64 - s)) : x0; } int sh = -lo; return sh >= 64 ? 0 : a.w[0] << sh; }
static double frac(U A, int nb) { return (double)b64(A, nb - 64) / 18446744073709551616.0; }
static int Kb[512], J, sg, t, m, D;
static U a[512];
static double **cnt;
static double complex *f, *g;
static uint64_t s0;
static uint64_t rnd64(void) { s0 ^= s0 << 13; s0 ^= s0 >> 7; s0 ^= s0 << 17; return s0; }
static double phi2(U lam) {  // |Phi(lambda)|^2 / |P|^2
  for (int S = 0; S < D; S++) f[S] = (S == sg) ? 1 : 0;
  for (int i = J - 1; i >= 0; i--) {
    U ha = mulU(a[i], lam);
    for (int S = 0; S <= Kb[i] && S < D; S++) { if (cnt[i][S] == 0) { g[S] = 0; continue; }
      double complex v = 0; for (int d = 1; S + d <= Kb[i + 1] && S + d < D; d++) v += cnt[i + 1][S + d] * f[S + d];
      g[S] = v / cnt[i][S] * cexp(-2 * M_PI * I * frac(ha, m - S)); }
    for (int S = Kb[i] + 1; S < D; S++) g[S] = 0;
    memcpy(f, g, 16 * D);
  }
  return creal(f[0] * conj(f[0]));
}
static double cosprod(U lam) {  // prod_{j<r} |cos(pi lam 2^j / 2^m)|, r = sg+1
  double p = 1; for (int j = 0; j <= sg; j++) { double x = frac(lam, m - j); p *= fabs(cos(M_PI * x)); if (p < 1e-300) return 0; } return p;
}
static U fromu64(uint64_t x) { U r; memset(&r, 0, sizeof r); r.w[0] = x; return r; }
static U randshell(int lo_bits) {  // uniform in [2^lo, 2^{lo+1})
  U r; memset(&r, 0, sizeof r);
  for (int k = 0; k < NL; k++) r.w[k] = rnd64();
  for (int p = lo_bits; p < 64 * NL; p++) r.w[p >> 6] &= ~(1ULL << (p & 63));
  r.w[lo_bits >> 6] |= 1ULL << (lo_bits & 63);
  return r; }
static int divisible_2t(U lam) { for (int p = 0; p < t; p++) if ((lam.w[p >> 6] >> (p & 63)) & 1) return 0; return 1; }
int main(int argc, char **argv) {
  int c = atoi(argv[1]); J = atoi(argv[2]); sg = atoi(argv[3]); t = atoi(argv[4]); double V = atof(argv[5]); int EXH = atoi(argv[6]); long ns = atol(argv[7]); s0 = 88172645463325252ULL ^ atoll(argv[8]);
  m = sg + t + 1; int r = sg + 1;
  const long double A = 1.584962500721156181453738943947816508759814407692481060455L;
  for (int j = 0; j < 512; j++) Kb[j] = (int)floorl(c + j * A);
  U inv3; for (int k = 0; k < NL; k++) inv3.w[k] = 0xAAAAAAAAAAAAAAAAULL; inv3.w[0] = 0xAAAAAAAAAAAAAAABULL;
  a[0] = inv3; for (int i = 1; i < J + 2; i++) a[i] = mulU(a[i - 1], inv3);
  // reduce a_i mod 2^m not needed: frac() reads bits below position m-S only
  D = Kb[J] + 2; cnt = malloc(sizeof(double *) * (J + 1)); for (int i = 0; i <= J; i++) cnt[i] = calloc(D, 8);
  cnt[J][sg] = 1; for (int i = J - 1; i >= 0; i--) for (int S = 0; S <= Kb[i] && S < D; S++) { double v = 0; for (int d = 1; S + d <= Kb[i + 1] && S + d < D; d++) v += cnt[i + 1][S + d]; cnt[i][S] = v; }
  double P = cnt[0][0]; f = malloc(16 * D); g = malloc(16 * D);
  printf("c=%d j0=%d sigma=%d t=%d m=%d |P|=%.4e (log2 %.2f) |V|=%.0f EXH=%d\n", c, J, sg, t, m, P, log2(P), V, EXH);
  // low block [1, 2^t): A2 and breakdown
  double A2 = 0, byv2[64] = {0}, byv3[64] = {0}; long nv2[64] = {0}, nv3[64] = {0}, n = 0; double wtot = 0, lowW = 0;
  double shellsum[400] = {0}; int shellexact[400] = {0};
  long lamexh = (EXH >= 1) ? (1L << EXH) : 1;
  for (long L = 1; L < lamexh; L++) {
    U lam = fromu64((uint64_t)L); if (divisible_2t(lam)) continue;
    double p2 = phi2(lam), w = cosprod(lam);
    int hb = 63 - __builtin_clzl(L); int u = hb - t;  // shell index: 2^{t+u} <= L < 2^{t+u+1}; u<0 -> low block
    int si = u < 0 ? 0 : u + 1; shellsum[si] += 2 * w * p2; shellexact[si] = 1;   // x2 mirror
    if (L < (1L << t)) { A2 += p2; n++; int v2 = __builtin_ctzl(L), v3 = 0; long x = L; while (x % 3 == 0) { x /= 3; v3++; } byv2[v2] += p2; nv2[v2]++; byv3[v3] += p2; nv3[v3]++; }
  }
  // sampled shells: u from (EXH - t) to sg-1 (lambda < 2^{m-1}); the last shell [2^{m-1},2^m) centered is lambda ~ 2^{m-1}: include u = sg as [2^{m-1}, 2^m) once (no mirror)
  for (int u = (EXH - t > 0 ? EXH - t : 0); u <= sg; u++) {
    int lo = t + u; if (lo < EXH) continue; double acc = 0; long cntv = 0;
    for (long k = 0; k < ns; k++) { U lam = randshell(lo); if (divisible_2t(lam)) { cntv++; continue; } acc += cosprod(lam) * phi2(lam); cntv++; }
    double size = ldexp(1.0, lo); double mirror = (u == sg) ? 1 : 2;
    shellsum[u + 1] = mirror * size * acc / cntv;
  }
  double tot = 0; for (int i = 0; i <= sg + 1; i++) tot += shellsum[i];
  double LHS = (1 + r / 2.0) * tot;           // normalized by |P|^2
  double RHS = V / ldexp(1.0, t);             // eps = 1, normalized by |P|^2
  printf("  A2 = mean_{1<=l<2^t} |Phi/P|^2 = %.3e  -> rate (amplitude) %.4f bits/step (need 0.0911 at A=0.7)  [random 1/|P| = %.2e]\n", A2 / n, -log2(A2 / n) / (2.0 * J), 1 / P);
  printf("  by v2: "); for (int v = 0; v < 8 && nv2[v]; v++) printf("v2=%d: %.2e  ", v, byv2[v] / nv2[v]); printf("\n");
  printf("  by v3: "); for (int v = 0; v < 12 && nv3[v]; v++) printf("v3=%d: %.2e(n=%ld)  ", v, byv3[v] / nv3[v], nv3[v]); printf("\n");
  printf("  shell sums (weighted, /|P|^2): low=%.3e", shellsum[0]); for (int u = 0; u <= sg && u < 60; u++) if (u < 6 || u % 8 == 0 || u == sg) printf(" u%d=%.2e%s", u, shellsum[u + 1], shellexact[u + 1] ? "*" : ""); printf("\n");
  printf("  LHS_W/|P|^2 = %.4e   RHS(eps=1)/|P|^2 = %.4e   R = %.4e   (R <= eps^2 needed)\n", LHS, RHS, LHS / RHS);
  return 0;
}
