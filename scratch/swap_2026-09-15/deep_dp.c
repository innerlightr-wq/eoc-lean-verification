// Deep exact path-product DP with 256-bit 2-adic coefficients.
//   Phi(h) = sum_{P in P_{j0,sigma}} e(-h Z_P / 2^m),  Z_P = sum_i 3^{-(i+1)} 2^{S_i} (mod 2^m),  m = sigma+t+1 <= 255
// For each h in [hmin,hmax] reports (all normalized by |P|):
//   phi   = |Phi(h)|/|P|                      (double-precision cancellation floor ~1e-15)
//   swap  = digit-swap bound (pairs (2k,2k+1): |e(a)+e(b)| = 2|cos(pi(a-b))| for admissible transpositions)
//   blk2  = exact 2-step block bound  sum_u |sum_{d: split of u} e(phase_{i+1}(S+d))| (tighter than swap)
//   badfr = path-measure fraction of pair-starts in "bad" states ||theta(i,S)|| < eta,
//           theta(i,S) = h 2^{S+1} 3^{-(i+2)} / 2^m mod 1 (the swap angle of the (1,2)<->(2,1) transposition)
// usage: ./deep_dp c j0 sigma t hmin hmax eta [list_file]
#include <complex.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned __int128 u128;
#ifdef LD
typedef long double complex CT;
#define CEXP cexpl
#define CABS cabsl
#else
typedef double complex CT;
#define CEXP cexp
#define CABS cabs
#endif
#define NL 5
typedef struct { uint64_t w[NL]; } U256;
static U256 mul256(U256 a, U256 b) { U256 r; memset(&r, 0, sizeof r);
  for (int i = 0; i < NL; i++) { u128 carry = 0; for (int j = 0; i + j < NL; j++) { u128 cur = (u128)a.w[i] * b.w[j] + r.w[i + j] + carry; r.w[i + j] = (uint64_t)cur; carry = cur >> 64; } }
  return r; }
static U256 mulsmall(U256 a, uint64_t h) { U256 r; u128 carry = 0; for (int i = 0; i < NL; i++) { u128 cur = (u128)a.w[i] * h + carry; r.w[i] = (uint64_t)cur; carry = cur >> 64; } return r; }
static uint64_t bits64(U256 a, int lo) {  // bits [lo, lo+64) of a (lo may be negative -> zero fill)
  if (lo >= 0) { int q = lo >> 6, sft = lo & 63; uint64_t x0 = q < NL ? a.w[q] : 0, x1 = q + 1 < NL ? a.w[q + 1] : 0;
    return sft ? (x0 >> sft) | (x1 << (64 - sft)) : x0; }
  int sh = -lo; if (sh >= 64) return 0; return a.w[0] << sh; }
// frac( (A mod 2^nb) / 2^nb ) using the top 64 bits below position nb
static double fracmod(U256 A, int nb) { uint64_t top = bits64(A, nb - 64); return (double)top / 18446744073709551616.0; }
static int Kb[512];
static U256 a[512];
int main(int argc, char **argv) {
  int c = atoi(argv[1]), J = atoi(argv[2]), sg = atoi(argv[3]), t = atoi(argv[4]); long hmin = atol(argv[5]), hmax = atol(argv[6]); double eta = atof(argv[7]);
  const char *listf = argc > 8 ? argv[8] : NULL;
  int m = sg + t + 1; if (m > 64 * NL - 1) { fprintf(stderr, "m too large\n"); return 1; }
  const long double A = 1.584962500721156181453738943947816508759814407692481060455L;
  for (int j = 0; j < 512; j++) Kb[j] = (int)floorl(c + j * A);
  U256 inv3; for (int k = 0; k < NL; k++) inv3.w[k] = 0xAAAAAAAAAAAAAAAAULL; inv3.w[0] = 0xAAAAAAAAAAAAAAABULL;
  a[0] = inv3; for (int i = 1; i < J + 2; i++) a[i] = mul256(a[i - 1], inv3);
  int D = Kb[J] + 2;
  // completion counts cnt[i][S] (to (J,sg)) and prefix counts pre[i][S]
  double **cnt = malloc(sizeof(double *) * (J + 1)), **pre = malloc(sizeof(double *) * (J + 1));
  for (int i = 0; i <= J; i++) { cnt[i] = calloc(D, 8); pre[i] = calloc(D, 8); }
  cnt[J][sg] = 1;
  for (int i = J - 1; i >= 0; i--) for (int S = 0; S <= Kb[i] && S < D; S++) { double v = 0; for (int d = 1; S + d <= Kb[i + 1] && S + d < D; d++) v += cnt[i + 1][S + d]; cnt[i][S] = v; }
  pre[0][0] = 1; for (int i = 0; i < J; i++) for (int S = 0; S < D; S++) if (pre[i][S] > 0) for (int d = 1; S + d <= Kb[i + 1] && S + d < D; d++) pre[i + 1][S + d] += pre[i][S];
  double P = cnt[0][0];
  fprintf(stderr, "c=%d j0=%d sigma=%d t=%d m=%d log2|P|=%.2f\n", c, J, sg, t, m, log2(P));
  CT *f = malloc(sizeof(CT) * D), *g = malloc(sizeof(CT) * D); double *sw = malloc(8 * D), *sw2 = malloc(8 * D), *b2 = malloc(8 * D), *b22 = malloc(8 * D);
  double *ang = malloc(8 * D);
  long *hl = NULL; long nh = 0;
  if (listf) { FILE *lf = fopen(listf, "r"); long x; hl = malloc(8 * 1000000); while (fscanf(lf, "%ld", &x) == 1) hl[nh++] = x; fclose(lf); }
  else { nh = hmax - hmin + 1; hl = malloc(8 * nh); for (long k = 0; k < nh; k++) hl[k] = hmin + k; }
  for (long kk = 0; kk < nh; kk++) {
    long h = hl[kk];
    // ---- exact Phi (normalized backward DP: f = F/cnt) ----
    for (int S = 0; S < D; S++) f[S] = (S == sg && cnt[J][S] > 0) ? 1 : 0;
    for (int i = J - 1; i >= 0; i--) {
      U256 ha = mulsmall(a[i], (uint64_t)h);
      for (int S = 0; S < D; S++) g[S] = 0;
      for (int S = 0; S <= Kb[i] && S < D; S++) { if (cnt[i][S] == 0) continue;
        CT v = 0; for (int d = 1; S + d <= Kb[i + 1] && S + d < D; d++) v += cnt[i + 1][S + d] * f[S + d];
        long double th = fracmod(ha, m - S);  // frac(h a_i 2^S / 2^m)
        g[S] = v / cnt[i][S] * CEXP(-2 * 3.14159265358979323846264338327950288L * I * th); }
      memcpy(f, g, sizeof(CT) * D);
    }
    double phi = (double)CABS(f[0]);
    // ---- swap bound and exact 2-block bound (backward over pairs starting at even i) ----
    for (int S = 0; S < D; S++) { sw[S] = (S == sg && cnt[J][S] > 0) ? 1 : 0; b2[S] = sw[S]; }
    int i = J; if (J % 2 == 1) { // leftover single last step: weight = count
      i = J - 1; for (int S = 0; S < D; S++) { double v = 0; if (cnt[i][S] > 0) for (int d = 1; S + d <= Kb[i + 1] && S + d < D; d++) v += cnt[i + 1][S + d] * sw[S + d]; sw2[S] = cnt[i][S] > 0 ? v / cnt[i][S] : 0; b22[S] = sw2[S]; }
      memcpy(sw, sw2, 8 * D); memcpy(b2, b22, 8 * D); }
    double badmass = 0; int npairs = 0;
    for (i = i - 2; i >= 0; i -= 2) {
      npairs++;
      U256 ha = mulsmall(a[i + 1], (uint64_t)h);  // phase at step i+1 depends on S_{i+1}
      for (int S = 0; S < D; S++) ang[S] = fracmod(ha, m - S);
      for (int S = 0; S < D; S++) { sw2[S] = 0; b22[S] = 0; }
      for (int S = 0; S <= Kb[i] && S < D; S++) { if (cnt[i][S] == 0) continue;
        double vs = 0, vb = 0;
        int umax = Kb[i + 2] - S;
        for (int u = 2; u <= umax && S + u < D; u++) { double cu = cnt[i + 2][S + u]; if (cu == 0) continue;
          double complex z = 0; double wsw = 0;
          for (int d = 1; d < u; d++) { int e = u - d; if (S + d > Kb[i + 1]) break;
            z += cexp(-2 * M_PI * I * ang[S + d]);
            if (d < e) { if (S + e <= Kb[i + 1]) wsw += 2 * fabs(cos(M_PI * (ang[S + d] - ang[S + e]))); else wsw += 1; }
            else if (d == e) wsw += 1;
            else { if (!(S + d <= Kb[i + 1] && S + e <= Kb[i + 1])) wsw += 1; /* d>e unpaired only if partner inadmissible: partner e<d always admissible if d is */ }
          }
          vs += cu * wsw * sw[S + u]; vb += cu * cabs(z) * b2[S + u]; }
        sw2[S] = vs / cnt[i][S]; b22[S] = vb / cnt[i][S];
        // bad-state mass for pair start (i,S): theta = h 2^{S+1} 3^{-(i+2)} / 2^m
        double th = ang[S + 1 < D ? S + 1 : S]; double nrm = fmin(th, 1 - th);
        if (nrm < eta) badmass += pre[i][S] * cnt[i][S] / P;
      }
      memcpy(sw, sw2, 8 * D); memcpy(b2, b22, 8 * D);
    }
    printf("h=%ld v2=%d phi=%.3e swap=%.3e blk2=%.3e badfr=%.4f  rates(bits/step): phi %.4f swap %.4f blk2 %.4f\n", h, __builtin_ctzl(h), phi, sw[0], b2[0], badmass / npairs,
           -log2(phi + 1e-300) / J, -log2(sw[0]) / J, -log2(b2[0]) / J);
    fflush(stdout);
  }
  return 0;
}
