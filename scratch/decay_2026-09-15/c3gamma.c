// gamma -> exponent: chain constant with per-shell bounds
//  model 1 (plain low-frequency decay):      a_u = max(min(2^{-thM u}, 2^{-gamma j0}), 1/|P|)
//  model 2 (decorrelated continuation decay): a_u = max(2^{-thM u - gamma*max(0, j0 - u/alpha)}, 1/|P|)
// usage: c3gamma K A model gamma1 gamma2 ...
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef long double LD;
static const LD AL = 1.584962500721156181453738943947816508759814407692481060455L;
int main(int argc, char **argv) {
  int K = atoi(argv[1]); LD A = strtold(argv[2], 0); int model = atoi(argv[3]); int ng = argc - 4; LD gm[16]; for (int k = 0; k < ng; k++) gm[k] = strtold(argv[4 + k], 0);
  const LD I0 = 0.0793186L, thM = 0.70516L; int J = (int)floorl((K - 1) / AL), NT = (int)floorl(A * K), bb[16384];
  for (int j = 0; j < 16384; j++) bb[j] = (int)floorl(j * AL);
  int sN = bb[NT], W = sN + 2, L = NT - J;
  LD *f = calloc((size_t)(J + 1) * W, sizeof(LD)); f[0] = 1;
  for (int i = 0; i < J; i++) { LD acc = 0; for (int S2 = 1; S2 <= bb[i + 1]; S2++) { if (S2 - 1 <= bb[i]) acc += f[(size_t)i * W + S2 - 1]; f[(size_t)(i + 1) * W + S2] = acc; } }
  LD *cur = calloc(W + 1, sizeof(LD)), *nw = calloc(W + 1, sizeof(LD));
  LD *au = calloc((size_t)ng * (W + 2), sizeof(LD));
  LD *P1 = calloc((size_t)ng * (W + 3), sizeof(LD)), *P2 = calloc((size_t)ng * (W + 3), sizeof(LD));
  LD Htot = 0, Hc[16] = {0};
  for (int sig = 0; sig < K && sig <= bb[J]; sig++) { LD P = f[(size_t)J * W + sig]; if (P <= 0) continue;
    int tmax = sN - sig; memset(cur, 0, sizeof(LD) * (W + 1)); cur[0] = 1;
    for (int i = 0; i < L; i++) { memset(nw, 0, sizeof(LD) * (W + 1)); LD a = 0; int top = bb[J + i + 1] - sig < tmax ? bb[J + i + 1] - sig : tmax;
      for (int S2 = 1; S2 <= top; S2++) { a += cur[S2 - 1]; nw[S2] = a; } memcpy(cur, nw, sizeof(LD) * (W + 1)); }
    int mmax = sig + tmax + 2;
    for (int k = 0; k < ng; k++) for (int u = 0; u < mmax && u < W + 2; u++) { LD v;
      if (model == 1) v = fminl(powl(2, -thM * u), powl(2, -gm[k] * J));
      else { LD rest = J - u / AL; if (rest < 0) rest = 0; v = powl(2, -thM * u - gm[k] * rest); }
      au[(size_t)k * (W + 2) + u] = fminl(1, fmaxl(v, 1 / P)); }
    for (int k = 0; k < ng; k++) { LD *a_ = au + (size_t)k * (W + 2), *p1 = P1 + (size_t)k * (W + 3), *p2 = P2 + (size_t)k * (W + 3); p1[0] = p2[0] = 0;
      for (int u = 0; u < W + 2; u++) p1[u + 1] = p1[u] + powl(2, u + 1) * a_[u]; p2[W + 2] = 0; for (int u = W + 1; u >= 0; u--) p2[u] = p2[u + 1] + a_[u]; }
    for (int s = K; s <= sN; s++) { int t = s - sig; LD Vc = cur[t]; if (Vc <= 0) continue; int m = sig + t + 1;
      LD H = P * Vc * powl(2, K - 1 - s), ctriv = powl(2, s + 1 - K); Htot += H;
      for (int k = 0; k < ng; k++) { LD *p1 = P1 + (size_t)k * (W + 3), *p2 = P2 + (size_t)k * (W + 3); int mm = m < W + 2 ? m : W + 2, tt = t < mm ? t : mm;
        LD sum = p1[tt] + powl(2, t) * (p2[tt] - p2[mm]);
        LD eps = sqrtl((1 + (sig + 1) / 2.0L) * sum * powl(2, t) / Vc); Hc[k] += H * fminl(ctriv, 1 + eps); } } }
  for (int k = 0; k < ng; k++) printf("K=%d A=%.3Lf model=%d gamma=%.4Lf log2C=%.3f exp=%.6f\n", K, A, model, gm[k], (double)log2l(Hc[k] / Htot), (double)(1 - I0 * A + log2l(Hc[k] / Htot) / K));
  return 0; }
