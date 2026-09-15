// L=3 block-cube bounds for the WeightedFourier target (A=0.7 geometry), per frequency lambda:
//   phi2 = |Phi/P|^2 (exact),  Q3 = E_P prod_r W_r^2  (rigorous: |Phi|^2/|P|^2 <= Q3 by Cauchy-Schwarz over coarse
//   3-block paths, W_r = |T_r|/|C_r|),  B3 = E_P prod_r W_r (rigorous pointwise: |Phi|/|P| <= B3).
// Blocks = steps (0,1,2),(3,4,5),...; a final partial block of length 1 or 2 is treated exactly the same way.
// Weighted target: R3 = (1+r/2) sum_{lambda != 0 mod 2^t} ||coef(lambda)|| Q3(lambda) / (|V|/2^t); low shells exhaustive
// (lambda < 2^EXH), higher dyadic shells sampled.   usage: ./phi3 c j0 sigma t V EXH nsamp seed
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
static uint64_t s0;
static uint64_t rnd64(void) { s0 ^= s0 << 13; s0 ^= s0 >> 7; s0 ^= s0 << 17; return s0; }
static double complex *f, *g; static double *G2, *G2n, *G1, *G1n; static double complex **E;  // E[l][S] = e(-phase_l(S))
static void eval(U lam, double *phi2, double *Q3, double *B3) {
  for (int l = 0; l < J; l++) { U ha = mulU(a[l], lam); for (int S = 0; S <= Kb[l] && S < D; S++) E[l][S] = cexp(-2 * M_PI * I * frac(ha, m - S)); }
  // exact Phi
  for (int S = 0; S < D; S++) f[S] = (S == sg) ? 1 : 0;
  for (int i = J - 1; i >= 0; i--) {
    for (int S = 0; S < D; S++) { g[S] = 0; if (S > Kb[i] || cnt[i][S] == 0) continue;
      double complex v = 0; for (int d = 1; S + d <= Kb[i + 1] && S + d < D; d++) v += cnt[i + 1][S + d] * f[S + d];
      g[S] = v / cnt[i][S] * E[i][S]; }
    memcpy(f, g, 16 * D); }
  *phi2 = creal(f[0] * conj(f[0]));
  // block DP (backward). Block boundaries: 0,3,6,...,3q, then J.
  int nb = J / 3, rem = J - 3 * nb;
  for (int S = 0; S < D; S++) { G2[S] = (S == sg) ? 1 : 0; G1[S] = G2[S]; }
  int starts[200], lens[200], k = 0; for (int r = 0; r < nb; r++) { starts[k] = 3 * r; lens[k++] = 3; } if (rem) { starts[k] = 3 * nb; lens[k++] = rem; }
  double complex *A = malloc(16 * D), *CB = malloc(16 * D);
  for (int bi = k - 1; bi >= 0; bi--) {
    int i = starts[bi], L = lens[bi];
    for (int S = 0; S < D; S++) { G2n[S] = 0; G1n[S] = 0; }
    for (int S = 0; S <= Kb[i] && S < D; S++) { if (cnt[i][S] == 0) continue;
      double v2 = 0, v1 = 0;
      if (L == 1) { for (int d = 1; S + d <= Kb[i + 1] && S + d < D; d++) { double w = cnt[i + 1][S + d]; v2 += w * G2[S + d]; v1 += w * G1[S + d]; } }
      else if (L == 2) {  // exit S+u, internal S1 in (S, min(b(i+1), S+u-1)]
        for (int u = 2; S + u <= Kb[i + 2] && S + u < D; u++) { double ce = cnt[i + 2][S + u]; if (ce == 0) continue;
          double complex T = 0; int nC = 0; for (int S1 = S + 1; S1 <= Kb[i + 1] && S1 <= S + u - 1; S1++) { T += E[i + 1][S1]; nC++; }
          if (!nC) continue; double at = cabs(T); v2 += ce * at * at / nC * G2[S + u]; v1 += ce * at * G1[S + u]; } }
      else {  // L == 3: internal (S1,S2), S<S1<S2<S+u, S1<=b(i+1), S2<=b(i+2)
        int top = Kb[i + 2] < D - 1 ? Kb[i + 2] : D - 1;
        CB[S] = 0; for (int x = S + 1; x <= top; x++) CB[x] = CB[x - 1] + E[i + 2][x];   // cumulative B over S2
        // prefix sums over S1 of A(S1) and A(S1)*CB(S1), and counts
        double complex PA = 0, PAC = 0; int nA = 0; long nAC = 0;  // nAC = sum_{S1} (#S2 <= S1) -> for counts
        static double complex pa[600], pac[600]; static long na[600], nac[600];
        for (int x = S + 1; x <= Kb[i + 1] && x < D; x++) { PA += E[i + 1][x]; PAC += E[i + 1][x] * CB[x < top ? x : top]; nA++; nAC += (x < top ? x : top) - S; pa[x] = PA; pac[x] = PAC; na[x] = nA; nac[x] = nAC; }
        for (int u = 3; S + u <= Kb[i + 3] && S + u < D; u++) { double ce = cnt[i + 3][S + u]; if (ce == 0) continue;
          int top2 = (Kb[i + 2] < S + u - 1) ? Kb[i + 2] : S + u - 1; int top1 = (Kb[i + 1] < S + u - 2) ? Kb[i + 1] : S + u - 2; if (top1 > top2 - 1) top1 = top2 - 1;
          if (top1 < S + 1) continue;
          double complex T = CB[top2] * pa[top1] - pac[top1];
          long nC = (long)(top2 - S) * na[top1] - nac[top1];
          if (nC <= 0) continue; double at = cabs(T); v2 += ce * at * at / nC * G2[S + u]; v1 += ce * at * G1[S + u]; } }
      G2n[S] = v2 / cnt[i][S]; G1n[S] = v1 / cnt[i][S]; }
    memcpy(G2, G2n, 8 * D); memcpy(G1, G1n, 8 * D);
  }
  free(A); free(CB);
  *Q3 = G2[0]; *B3 = G1[0];
}
static double cosprod(U lam) { double p = 1; for (int j = 0; j <= sg; j++) { p *= fabs(cos(M_PI * frac(lam, m - j))); if (p < 1e-300) return 0; } return p; }
static U fromu64(uint64_t x) { U r; memset(&r, 0, sizeof r); r.w[0] = x; return r; }
static U randshell(int lo) { U r; for (int k = 0; k < NL; k++) r.w[k] = rnd64(); for (int p = lo; p < 64 * NL; p++) r.w[p >> 6] &= ~(1ULL << (p & 63)); r.w[lo >> 6] |= 1ULL << (lo & 63); return r; }
static int div2t(U lam) { for (int p = 0; p < t; p++) if ((lam.w[p >> 6] >> (p & 63)) & 1) return 0; return 1; }
int main(int argc, char **argv) {
  int c = atoi(argv[1]); J = atoi(argv[2]); sg = atoi(argv[3]); t = atoi(argv[4]); double V = atof(argv[5]); int EXH = atoi(argv[6]); long ns = atol(argv[7]); s0 = 88172645463325252ULL ^ atoll(argv[8]);
  m = sg + t + 1; int r = sg + 1;
  const long double Al = 1.584962500721156181453738943947816508759814407692481060455L;
  for (int j = 0; j < 512; j++) Kb[j] = (int)floorl(c + j * Al);
  U inv3; for (int kk = 0; kk < NL; kk++) inv3.w[kk] = 0xAAAAAAAAAAAAAAAAULL; inv3.w[0] = 0xAAAAAAAAAAAAAAABULL;
  a[0] = inv3; for (int i = 1; i < J + 3; i++) a[i] = mulU(a[i - 1], inv3);
  D = Kb[J] + 3; cnt = malloc(sizeof(double *) * (J + 4)); for (int i = 0; i <= J + 3; i++) cnt[i] = calloc(D, 8);
  cnt[J][sg] = 1; for (int i = J - 1; i >= 0; i--) for (int S = 0; S <= Kb[i] && S < D; S++) { double v = 0; for (int d = 1; S + d <= Kb[i + 1] && S + d < D; d++) v += cnt[i + 1][S + d]; cnt[i][S] = v; }
  double P = cnt[0][0];
  f = malloc(16 * D); g = malloc(16 * D); G2 = malloc(8 * D); G2n = malloc(8 * D); G1 = malloc(8 * D); G1n = malloc(8 * D);
  E = malloc(sizeof(double complex *) * (J + 3)); for (int l = 0; l < J + 3; l++) E[l] = calloc(D, 16);
  printf("c=%d j0=%d sigma=%d t=%d m=%d log2|P|=%.2f |V|=%.0f EXH=%d\n", c, J, sg, t, m, log2(P), V, EXH);
  if (EXH < 0) {
    FILE *lf = fopen(argv[9], "r"); char buf[512];
    while (fscanf(lf, "%511s", buf) == 1) { U lam; memset(&lam, 0, sizeof lam);
      for (char *p = buf; *p; p++) { U ten; memset(&ten, 0, sizeof ten); ten.w[0] = 10; lam = mulU(lam, ten); u128 cc = (u128)(*p - '0');
        for (int kk = 0; kk < NL && cc; kk++) { u128 x = (u128)lam.w[kk] + cc; lam.w[kk] = (uint64_t)x; cc = x >> 64; } }
      double p2, q3, b3; eval(lam, &p2, &q3, &b3);
      printf("  lam=%s  phi2=%.3e (rate %.4f)  Q3=%.3e (rate %.4f)  B3=%.3e (rate %.4f)\n", buf, p2, -log2(p2) / (2.0 * J), q3, -log2(q3) / (2.0 * J), b3, -log2(b3) / J); }
    return 0; }
  double sP = 0, sQ = 0, sB = 0, maxQ = 0; long n = 0, worst = 0; double shellQ[400] = {0}, shellP[400] = {0};
  for (long Lm = 1; Lm < (1L << EXH); Lm++) { U lam = fromu64((uint64_t)Lm); if (div2t(lam)) continue;
    double p2, q3, b3; eval(lam, &p2, &q3, &b3); double w = cosprod(lam);
    int hb = 63 - __builtin_clzl(Lm), u = hb - t, si = u < 0 ? 0 : u + 1; shellQ[si] += 2 * w * q3; shellP[si] += 2 * w * p2;
    if (Lm < (1L << t)) { sP += p2; sQ += q3; sB += b3 * b3; n++; if (q3 > maxQ) { maxQ = q3; worst = Lm; } } }
  for (int u = (EXH - t > 0 ? EXH - t : 0); u <= sg; u++) { int lo = t + u; if (lo < EXH) continue; double aQ = 0, aP = 0; long cv = 0;
    for (long kk = 0; kk < ns; kk++) { U lam = randshell(lo); cv++; if (div2t(lam)) continue; double p2, q3, b3; eval(lam, &p2, &q3, &b3); double w = cosprod(lam); aQ += w * q3; aP += w * p2; }
    double mir = (u == sg) ? 1 : 2; shellQ[u + 1] = mir * ldexp(1.0, lo) * aQ / cv; shellP[u + 1] = mir * ldexp(1.0, lo) * aP / cv; }
  double totQ = 0, totP = 0; for (int i = 0; i <= sg + 1; i++) { totQ += shellQ[i]; totP += shellP[i]; }
  double RHS = V / ldexp(1.0, t);
  printf("  low block 1<=l<2^t: mean phi2=%.3e (rate %.4f)  mean Q3=%.3e (rate %.4f)  mean B3^2=%.3e (rate %.4f)  max Q3=%.3e at l=%ld\n",
         sP / n, -log2(sP / n) / (2.0 * J), sQ / n, -log2(sQ / n) / (2.0 * J), sB / n, -log2(sB / n) / (2.0 * J), maxQ, worst);
  printf("  weighted: R_true=%.3e   R3 (rigorous-bound version)=%.3e   [(1+r/2)*sum w*.../(|V|/2^t)]\n", (1 + r / 2.0) * totP / RHS, (1 + r / 2.0) * totQ / RHS);
  printf("  shell Q3 sums: low=%.2e", shellQ[0]); for (int u = 0; u <= sg && u < 40; u++) if (u < 5 || u % 10 == 0) printf(" u%d=%.2e", u, shellQ[u + 1]); printf("\n");
  return 0;
}
