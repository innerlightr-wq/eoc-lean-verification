// A=0.7 shellwise chain constant from the rigorous 3-adic interval sieve (C3, Minkowski form).
// For pair (sigma,s), t=s-sigma, m=sigma+t+1, centered shell u (H=2^u), any split N<=J with 2*Xmax(N) <= 2^m:
//   a_u <= (1-2^-t)^-1 * ( sum_S g_S min(p_S, sqrt(kappa p_S)) / |P| )^2 * 2^{-2 gd (J-N)},
//   kappa = mu_N (1 + 2*3^N (1+N ln3)/2^u),  mu_N = ceil(Xmax(N)/3^N),  Xmax(N) = sum_{i<N} 2^{b(i)} 3^{N-1-i},
// p_S = #N-step confined prefixes ending at S, g_S = #continuations (S at N) -> (sigma at J).
// gd = hypothetical extra amplitude decay (bits/step) on the uncontrolled steps N..J (gd = 0: rigorous).
// Weights w_u: crude 2^t (current Lean interface) or refined min(2^{u+1}, 2^t) (uses ||coef|| <= 1).
// Chain constant C = sum Haar * min(2^{s+1-K}, 1+eps) / sum Haar, eps^2 = (1+(sigma+1)/2) sum_u w_u a_u 2^t/|V|.
// usage: c3chain3 K refined gd [verbose]
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef long double LD;
static const LD AL = 1.584962500721156181453738943947816508759814407692481060455L;
static int cmpd(const void *a, const void *b) { LD x = ((LD *)a)[0], y = ((LD *)b)[0]; return x < y ? -1 : x > y; }
int main(int argc, char **argv) {
  int K = atoi(argv[1]), refined = atoi(argv[2]); LD gd = strtold(argv[3], 0); int verb = argc > 4 ? atoi(argv[4]) : 0;
  LD A = argc > 5 ? strtold(argv[5], 0) : 0.7L; LD theta = argc > 6 ? strtold(argv[6], 0) : 0; int DS = argc > 7 ? atoi(argv[7]) : -1, DSS = argc > 8 ? atoi(argv[8]) : -1; const LD I0 = 0.0793186L; int c = 0;
  int J = (int)floorl((K - 1 - c) / AL), NT = (int)floorl(A * K), bb[8192];
  for (int j = 0; j < 8192; j++) bb[j] = (int)floorl(c + j * AL);
  int sN = bb[NT], W = sN + 2, L = NT - J;
  LD *f = calloc((size_t)(J + 1) * W, sizeof(LD)); f[0] = 1;
  for (int i = 0; i < J; i++) { LD acc = 0;  // f[i+1][S2] = sum_{S<S2, S<=b(i)} f[i][S]
    for (int S2 = 1; S2 <= bb[i + 1]; S2++) { if (S2 - 1 <= bb[i]) acc += f[(size_t)i * W + S2 - 1]; f[(size_t)(i + 1) * W + S2] = acc; } }
  LD *mu = calloc(J + 1, sizeof(LD)), *l2X = calloc(J + 1, sizeof(LD));
  for (int N = 0; N <= J; N++) { LD r = 0; for (int i = 0; i < N; i++) r += powl(2, bb[i]) / powl(3, i + 1);
    mu[N] = N ? ceill(r) : 1; l2X[N] = N ? log2l(2 * r) + N * AL : -1e9; }
  LD *g = calloc((size_t)(J + 1) * W, sizeof(LD)), *V = calloc((size_t)(K + 1) * (W + 1), sizeof(LD));
  LD *nw = calloc(W + 1, sizeof(LD)), *PM = calloc((size_t)W * (J + 1), sizeof(LD));
  LD *srt = calloc(2 * (size_t)W, sizeof(LD)), *A1 = calloc(W + 1, sizeof(LD)), *A2 = calloc(W + 1, sizeof(LD));
  // suffix counts and per-sigma Haar mass
  LD *hs = calloc(K + 1, sizeof(LD)), hmax = 0;
  for (int sig = 0; sig < K && sig <= bb[J]; sig++) { LD P = f[(size_t)J * W + sig]; if (P <= 0) continue;
    LD *cur = V + (size_t)sig * (W + 1); int tmax = sN - sig; cur[0] = 1;
    for (int i = 0; i < L; i++) { memset(nw, 0, sizeof(LD) * (W + 1));
      for (int S = 0; S <= tmax; S++) if (cur[S] > 0) for (int d = 1; S + d <= tmax; d++) { if (sig + S + d > bb[J + i + 1]) break; nw[S + d] += cur[S]; }
      memcpy(cur, nw, sizeof(LD) * (W + 1)); }
    for (int s = K; s <= sN; s++) if (cur[s - sig] > 0) hs[sig] += P * cur[s - sig] * powl(2, K - 1 - s);
    if (hs[sig] > hmax) hmax = hs[sig]; }
  LD *p3 = calloc(J + 1, sizeof(LD)), *ip2 = calloc(W + 1, sizeof(LD)), *gdf = calloc(J + 1, sizeof(LD));
  for (int N = 0; N <= J; N++) { p3[N] = powl(3, N); gdf[N] = powl(2, -2 * gd * (J - N)); } for (int u = 0; u <= W; u++) ip2[u] = powl(2, -u);
  LD Htot = 0, Hc = 0, Htriv = 0;
  for (int sig = 0; sig < K && sig <= bb[J]; sig++) {
    LD P = f[(size_t)J * W + sig]; if (P <= 0) continue; LD *cur = V + (size_t)sig * (W + 1);
    int heavy = theta > 0 ? 0 : 1;
    if (heavy) {
      memset(g, 0, sizeof(LD) * (size_t)(J + 1) * W); g[(size_t)J * W + sig] = 1;
      for (int i = J - 1; i >= 0; i--) { LD acc = 0; int top = bb[i + 1] < sig ? bb[i + 1] : sig;
        for (int S2 = top; S2 >= 1; S2--) { acc += g[(size_t)(i + 1) * W + S2]; if (S2 - 1 <= bb[i]) g[(size_t)i * W + S2 - 1] = acc; } }
      for (int N = 0; N <= J; N++) {  // sorted-by-p prefix sums: T(kappa) = sum_{p<=kappa} g p + sqrt(kappa) sum_{p>kappa} g sqrt(p)
        int n = 0; for (int S = 0; S <= bb[N] && S < W; S++) { LD p = f[(size_t)N * W + S], gg = g[(size_t)N * W + S];
          if (p > 0 && gg > 0) { srt[2 * n] = p; srt[2 * n + 1] = gg; n++; } }
        qsort(srt, n, 2 * sizeof(LD), cmpd);
        A1[0] = 0; for (int k = 0; k < n; k++) A1[k + 1] = A1[k] + srt[2 * k] * srt[2 * k + 1];
        A2[n] = 0; for (int k = n - 1; k >= 0; k--) A2[k] = A2[k + 1] + sqrtl(srt[2 * k]) * srt[2 * k + 1];
        for (int u = 0; u < W; u++) {
          LD kap = mu[N] * (1 + 2 * p3[N] * (1 + N * logl(3)) * ip2[u]);
          int lo = 0, hi = n; while (lo < hi) { int md = (lo + hi) / 2; if (srt[2 * md] <= kap) lo = md + 1; else hi = md; }
          LD T = (A1[lo] + sqrtl(kap) * A2[lo]) / P, v = T * T * gdf[N];
          LD prev = N ? PM[(size_t)u * (J + 1) + N - 1] : 1; PM[(size_t)u * (J + 1) + N] = v < prev ? v : prev; } }
    }
    for (int s = K; s <= sN; s++) {
      int t = s - sig; LD Vc = cur[t]; if (Vc <= 0) continue; int m = sig + t + 1;
      LD H = P * Vc * powl(2, K - 1 - s), ctriv = powl(2, s + 1 - K); Htot += H; Htriv += H * ctriv;
      
      int Nmax = 0; while (Nmax < J && l2X[Nmax + 1] <= m) Nmax++;
      LD sum = 0;
      for (int u = 0; u < m; u++) { LD a = theta > 0 ? fmaxl(powl(2, -theta * u), 1 / P) : PM[(size_t)u * (J + 1) + Nmax] / (1 - powl(2, -t));
        sum += (refined ? fminl(powl(2, u + 1), powl(2, t)) : powl(2, t)) * a;
        if (sig == DS && s == DSS && u % 10 == 0) { int bn = 0; for (int N = 1; N <= Nmax; N++) if (PM[(size_t)u * (J + 1) + N] < PM[(size_t)u * (J + 1) + bn]) bn = N; printf("  u=%d log2a=%.2f bestN=%d log2(w a)=%.2f\n", u, (double)log2l(a), bn, (double)log2l(a * (refined ? fminl(powl(2, u + 1), powl(2, t)) : powl(2, t)))); } }
      LD eps = sqrtl((1 + (sig + 1) / 2.0L) * sum * powl(2, t) / Vc);
      Hc += H * fminl(ctriv, 1 + eps);
      if (verb) printf("Hc=%.3Le H=%.3Le sig=%d s=%d t=%d log2V=%.1f log2eps=%.2f log2ctriv=%d\n", H * fminl(ctriv, 1 + eps), H, sig, s, t, (double)log2l(Vc), (double)log2l(eps), s + 1 - K);
    }
  }
  LD C = Hc / Htot, Ct = Htriv / Htot;
  printf("A=%.3Lf K=%d j0=%d refined=%d gd=%.4f: C=%.4Le (log2 %.2f, /K %.5f) | eff.exp %.5f | trivial-only log2 C=%.2f (/K %.5f)\n",
         A, K, J, refined, (double)gd, C, (double)log2l(C), (double)(log2l(C) / K), (double)(1 - I0 * A + log2l(C) / K), (double)log2l(Ct), (double)(log2l(Ct) / K));
  return 0;
}
