// Shellwise A=0.7 chain constant with the rigorous 3-adic interval-sieve bound (C3), per pair (sigma,s)
// and per centered frequency shell u (H = 2^u):
//   a_u <= min(1, min_N  mu_N (1 + 2*3^N (1+N ln3)/H) * (sum_S g_S^{(N)}) / |P_sigma| * 2^{-2 gd (J-N)} ) / (1-2^-t)
// valid for N <= J with 2*Xmax(N) <= 2^m  (mu_N = ceil(Xmax(N)/3^N), Xmax(N) = sum_{i<N} 2^{b(i)} 3^{N-1-i}).
// gd = hypothetical extra amplitude saving (bits/step) on the uncontrolled steps N..J (gd=0: fully rigorous).
// Weights: crude (Lean interface, 2^t per shell) or refined min(2^{u+1}, 2^t) (needs ||coef|| <= 1).
// Output: chain constant C = sum Haar*min(c_triv, 1+eps) / sum Haar and effective exponent 1 - I0*A + log2(C)/K.
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef long double LD;
static const LD AL = 1.584962500721156181453738943947816508759814407692481060455L;
static int K, J, NT, sN, bb[4096], refined; static LD gd;
static LD *f;  // f[i*W+S] prefix counts
static int W;
#define F(i, S) f[(size_t)(i) * W + (S)]
int main(int argc, char **argv) {
  K = atoi(argv[1]); refined = atoi(argv[2]); gd = argc > 3 ? strtold(argv[3], 0) : 0; int mode = argc > 4 ? atoi(argv[4]) : 0; int MS = argc > 5 ? atoi(argv[5]) : 0, MSS = argc > 6 ? atoi(argv[6]) : 0;
  const LD A = 0.7L, I0 = 0.0793186L; int c = 0;
  J = (int)floorl((K - 1 - c) / AL); NT = (int)floorl(A * K);
  for (int j = 0; j < 4096; j++) bb[j] = (int)floorl(c + j * AL);
  sN = bb[NT]; W = sN + 2; int L = NT - J;
  f = calloc((size_t)(J + 1) * W, sizeof(LD)); F(0, 0) = 1;
  for (int i = 0; i < J; i++) for (int S = 0; S <= bb[i]; S++) if (F(i, S) > 0)
    for (int S2 = S + 1; S2 <= bb[i + 1]; S2++) F(i + 1, S2) += F(i, S);
  // mu_N and log2(2 Xmax(N))
  LD *mu = calloc(J + 1, sizeof(LD)), *l2X = calloc(J + 1, sizeof(LD));
  for (int N = 0; N <= J; N++) { LD r = 0; for (int i = 0; i < N; i++) r += powl(2, bb[i]) / powl(3, i + 1);  // Xmax/3^N
    mu[N] = N ? ceill(r) : 1; l2X[N] = N ? log2l(2 * r) + N * AL : -1e9; }
  LD *g = calloc((size_t)(J + 1) * W, sizeof(LD)), *rho = calloc(J + 1, sizeof(LD)), *V = calloc(W + 1, sizeof(LD));
  LD *PM = calloc((size_t)W * (J + 1), sizeof(LD)); int KG = 4 * (int)(1.6 * J + 8); LD *T = calloc((size_t)(J + 1) * KG, sizeof(LD)); LD *cur = calloc(W + 1, sizeof(LD)), *nw = calloc(W + 1, sizeof(LD));
  LD Htot = 0, Hc = 0, Htriv = 0, worst = 0; int wsig = 0, ws = 0;
  for (int sig = 0; sig < K && sig <= bb[J]; sig++) {
    LD P = F(J, sig); if (P <= 0) continue;
    memset(g, 0, sizeof(LD) * (size_t)(J + 1) * W); g[(size_t)J * W + sig] = 1;
    for (int i = J - 1; i >= 0; i--) { LD acc = 0;  // g[i][S] = sum_{S<S2<=min(b(i+1),sig)} g[i+1][S2]
      int top = bb[i + 1] < sig ? bb[i + 1] : sig;
      for (int S2 = top; S2 >= 1; S2--) { acc += g[(size_t)(i + 1) * W + S2]; if (S2 - 1 <= bb[i]) g[(size_t)i * W + S2 - 1] = acc; } }
    // Minkowski form: sqrt(avg|Phi|^2)/|P| <= sum_S g_S min(p_S, sqrt(kappa p_S)) / |P|, kappa = mu_N (1 + 2*3^N(1+N ln3)/H)
    // T[N][k] = sum_S g_S min(p_S, sqrt(2^{k/4} p_S)) on a kappa grid (kappa rounded up => valid bound)
    for (int N = 0; N <= J; N++) for (int k = 0; k < KG; k++) { LD a = 0, kap = powl(2, k / 4.0L);
      for (int S = 0; S <= bb[N] && S < W; S++) { LD p = F(N, S); if (p <= 0) continue; LD gg = g[(size_t)N * W + S]; if (gg <= 0) continue;
        a += gg * fminl(p, sqrtl(kap * p)); }
      T[(size_t)N * KG + k] = a / P; }
    if (mode == 3 && sig == MS) { int N = MSS; LD tot = 0; for (int S = 0; S <= bb[N]; S++) { LD p = F(N, S), gg = g[(size_t)N * W + S]; if (p > 0 && gg > 0) { tot += p * gg / P;
        printf("N=%d S=%d log2p=%.2f pi=%.3Le\n", N, S, (double)log2l(p), p * gg / P); } } printf("tot=%.4Lf mu=%.0Lf\n", tot, mu[N]); }
    for (int u = 0; u < W; u++) { LD run = 1; for (int N = 0; N <= J; N++) {
      LD kap = mu[N] * (1 + 2 * powl(3, N) * (1 + N * logl(3)) / powl(2, u)); int k = (int)ceill(4 * log2l(kap));
      LD v = k >= KG ? 1 : T[(size_t)N * KG + k]; v = v * v * powl(2, -2 * gd * (J - N));
      if (v < run) run = v; PM[(size_t)u * (J + 1) + N] = run; } }
    // suffix counts V[t]
    int tmax = sN - sig; memset(cur, 0, sizeof(LD) * (W + 1)); cur[0] = 1;
    for (int i = 0; i < L; i++) { memset(nw, 0, sizeof(LD) * (W + 1));
      for (int S = 0; S <= tmax; S++) if (cur[S] > 0) for (int d = 1; S + d <= tmax; d++) { if (sig + S + d > bb[J + i + 1]) break; nw[S + d] += cur[S]; }
      memcpy(cur, nw, sizeof(LD) * (W + 1)); }
    for (int s = K; s <= sN; s++) {
      int t = s - sig; LD Vc = cur[t]; if (Vc <= 0) continue; int m = sig + t + 1;
      LD H = P * Vc * powl(2, K - 1 - s); Htot += H;
      LD ctriv = powl(2, s + 1 - K), sum = 0;
      int Nmax = 0; while (Nmax < J && l2X[Nmax + 1] <= m) Nmax++;
      for (int u = 0; u < m; u++) {
        LD best = PM[(size_t)u * (J + 1) + Nmax];
        best /= (1 - powl(2, -t));
        LD w = refined ? fminl(powl(2, u + 1), powl(2, t)) : powl(2, t);
        sum += w * best;
        if (mode == 2 && sig == MS && s == MSS && u % 8 == 0) printf("u=%d log2a=%.2f log2(w a)=%.2f\n", u, (double)log2l(best), (double)log2l(w*best)); }
      LD eps = sqrtl((1 + (sig + 1) / 2.0L) * sum * powl(2, t) / Vc), cf = 1 + eps;
      Hc += H * fminl(ctriv, cf); Htriv += H * ctriv;
      if (mode) printf("%.3Le sig=%d s=%d t=%d log2V=%.1f log2eps=%.2f log2ctriv=%d Nmax=%d\n", H, sig, s, t, (double)log2l(Vc), (double)log2l(eps), s + 1 - K, Nmax);
      if (cf < ctriv && H * cf > worst) { worst = H * cf; wsig = sig; ws = s; } }
  }
  LD C = Hc / Htot, Ct = Htriv / Htot;
  printf("K=%d j0=%d N=%d refined=%d gd=%.4f: C=%.4Le (log2 %.2f)  exp=%.5f | trivial-only C=%.3Le exp=%.5f | worst Fourier pair (sig,s)=(%d,%d)\n",
         K, J, NT, refined, (double)gd, C, (double)log2l(C), (double)(1 - I0 * A + log2l(C) / K), Ct, (double)(1 - I0 * A + log2l(Ct) / K), wsig, ws);
  return 0;
}
