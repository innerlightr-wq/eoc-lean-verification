// Large-deviation loss of the Minkowski (C3) step: T_N = sum_S g_S sqrt(p_S) / |P| (kappa-free),
// h_eff(N) = -2 log2(T_N)/N  (ideal: h = 1.50564, i.e. theta = h/alpha = H2);  theta_C3(N) = h_eff/alpha.
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
typedef long double LD; static const LD AL = 1.584962500721156181453738943947816508759814407692481060455L;
int main(int c, char **v) { int J = atoi(v[1]), gap = atoi(v[2]), bb[8192]; for (int j = 0; j < 8192; j++) bb[j] = (int)floorl(j * AL);
  int sg = bb[J] - gap, W = sg + 2;
  LD *f = calloc((size_t)(J + 1) * W, sizeof(LD)), *g = calloc((size_t)(J + 1) * W, sizeof(LD)); f[0] = 1;
  for (int i = 0; i < J; i++) { LD a = 0; for (int S2 = 1; S2 <= bb[i + 1] && S2 < W; S2++) { if (S2 - 1 <= bb[i]) a += f[(size_t)i * W + S2 - 1]; f[(size_t)(i + 1) * W + S2] = a; } }
  g[(size_t)J * W + sg] = 1;
  for (int i = J - 1; i >= 0; i--) { LD a = 0; int top = bb[i + 1] < sg ? bb[i + 1] : sg; for (int S2 = top; S2 >= 1; S2--) { a += g[(size_t)(i + 1) * W + S2]; if (S2 - 1 <= bb[i]) g[(size_t)i * W + S2 - 1] = a; } }
  LD P = f[(size_t)J * W + sg];
  printf("J=%d sigma=%d (gap %d)  h=1.50564 alpha=1.58496\n", J, sg, gap);
  for (int N = J / 16; N <= J / 2; N += J / 16) { LD T = 0, lt = 0, tot = 0, sh = 0; for (int S = 0; S < W; S++) { LD p = f[(size_t)N * W + S], gg = g[(size_t)N * W + S]; if (p > 0 && gg > 0) { T += gg * sqrtl(p); tot += p; sh += p * gg * gg; } }
    T /= P; LD he = -2 * log2l(T) / N, ht = log2l(tot) / N;
    printf(" N=%4d  h_eff=%.4Lf  theta_C3=%.4Lf  share-rate=%.4Lf  (log2 #N-prefixes / N = %.4Lf)\n", N, he, he / AL, -log2l(sh / (P * P)) / N, ht); }
  return 0; }
