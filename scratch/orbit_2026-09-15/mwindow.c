// Chain constant for idealized shell averages a_u = max(2^{-theta u}, 1/|P|) (refined weights), several theta at once.
// usage: c3theta K A theta1 theta2 ...   prints log2 C and effective exponent 1 - I0*A + log2(C)/K per theta
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef long double LD;
static const LD AL = 1.584962500721156181453738943947816508759814407692481060455L;
int main(int argc, char **argv) {
  int K = atoi(argv[1]); LD A = strtold(argv[2], 0); int nt = argc - 3; LD th[16]; for (int k = 0; k < nt; k++) th[k] = strtold(argv[3 + k], 0);
  const LD I0 = 0.0793186L; int J = (int)floorl((K - 1) / AL), NT = (int)floorl(A * K), bb[8192];
  for (int j = 0; j < 8192; j++) bb[j] = (int)floorl(j * AL);
  int sN = bb[NT], W = sN + 2, L = NT - J;
  LD *f = calloc((size_t)(J + 1) * W, sizeof(LD)); f[0] = 1;
  for (int i = 0; i < J; i++) { LD acc = 0; for (int S2 = 1; S2 <= bb[i + 1]; S2++) { if (S2 - 1 <= bb[i]) acc += f[(size_t)i * W + S2 - 1]; f[(size_t)(i + 1) * W + S2] = acc; } }
  LD *cur = calloc(W + 1, sizeof(LD)), *nw = calloc(W + 1, sizeof(LD)), *acc = calloc(W + 2, sizeof(LD));
  int MW = W + 8; LD *G1 = calloc((size_t)nt * (MW + 1), sizeof(LD)), *G2 = calloc((size_t)nt * (MW + 1), sizeof(LD));
  for (int k = 0; k < nt; k++) for (int u = 0; u < MW; u++) { G1[(size_t)k * (MW + 1) + u + 1] = G1[(size_t)k * (MW + 1) + u] + powl(2, (1 - th[k]) * u);
    G2[(size_t)k * (MW + 1) + u + 1] = G2[(size_t)k * (MW + 1) + u] + powl(2, -th[k] * u); }
  LD Htot = 0, Hc[16] = {0}; LD *ws = calloc(W + 2, sizeof(LD)); LD Wsum = 0, WHsum = 0, WHsum2 = 0; int nsig = 0;
  for (int sig = 0; sig < K && sig <= bb[J]; sig++) { LD P = f[(size_t)J * W + sig]; if (P <= 0) continue;
    int tmax = sN - sig; memset(cur, 0, sizeof(LD) * (W + 1)); cur[0] = 1;
    for (int i = 0; i < L; i++) {  // nw[S2] = sum_{S<S2} cur[S], S2 <= min(tmax, b(J+i+1)-sig)
      memset(nw, 0, sizeof(LD) * (W + 1)); LD a = 0; int top = bb[J + i + 1] - sig < tmax ? bb[J + i + 1] - sig : tmax;
      for (int S2 = 1; S2 <= top; S2++) { a += cur[S2 - 1]; nw[S2] = a; }
      memcpy(cur, nw, sizeof(LD) * (W + 1)); }
    LD hsum = 0, csum = 0, hent = 0, cent = 0; LD hh[4096], cc[4096]; int ns_ = 0;
    for (int s = K; s <= sN; s++) { int t = s - sig; LD Vc = cur[t]; if (Vc <= 0) continue; int m = sig + t + 1;
      LD H = P * Vc * powl(2, K - 1 - s), ctriv = powl(2, s + 1 - K); Htot += H;
      for (int k = 0; k < nt; k++) { LD *g1 = G1 + (size_t)k * (MW + 1), *g2 = G2 + (size_t)k * (MW + 1);
        int uf = (int)ceill(log2l(P) / th[k]); if (uf > m) uf = m; int a1 = t < uf ? t : uf;
        LD sum = 2 * g1[a1];                                        // u < min(t,uf): 2^{u+1} 2^{-theta u}
        if (uf < t) sum += (powl(2, t + 1) - powl(2, uf + 1)) / P;  // uf <= u < t: 2^{u+1}/P
        int lo = t, hi = uf; if (hi > lo) sum += powl(2, t) * (g2[hi] - g2[lo]);  // t <= u < uf: 2^t 2^{-theta u}
        int lo2 = t > uf ? t : uf; if (m > lo2) sum += powl(2, t) * (m - lo2) / P;  // u >= max(t,uf)
        LD eps = sqrtl((1 + (sig + 1) / 2.0L) * sum * powl(2, t) / Vc); Hc[k] += H * fminl(ctriv, 1 + eps); if (k == 0) { hh[ns_] = H; cc[ns_] = H * fminl(ctriv, 1 + eps); ns_++; } } }
    for (int q = 0; q < ns_; q++) { hsum += hh[q]; csum += cc[q]; }
    for (int q = 0; q < ns_; q++) { if (hh[q] > 0) hent -= hh[q] / hsum * log2l(hh[q] / hsum); if (cc[q] > 0) cent -= cc[q] / csum * log2l(cc[q] / csum); }
    Wsum += csum; WHsum += csum * powl(2, cent); WHsum2 += csum * powl(2, hent); nsig++; }
  printf("K=%d A=%.2Lf: contribution-weighted effective m-window 2^H(s|sigma): %.2Lf (chain-contribution weights), %.2Lf (Haar weights); s-range %d..%d\n", K, A, WHsum / Wsum, WHsum2 / Wsum, K, sN);
  for (int k = 0; k < nt; k++) { LD C = Hc[k] / Htot;
    printf("K=%d A=%.3Lf theta=%.5Lf log2C=%.3f exp=%.5f\n", K, A, th[k], (double)log2l(C), (double)(1 - I0 * A + log2l(C) / K)); }
  return 0; }
