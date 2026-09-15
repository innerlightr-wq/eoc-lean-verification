#include <math.h>
#include <stdio.h>
#include <stdlib.h>
typedef long double LD; static const LD AL = 1.584962500721156181453738943947816508759814407692481060455L;
int main(int c, char **v) { int J = atoi(v[1]), sg = atoi(v[2]), N0 = atoi(v[3]), W = sg + 2, bb[4096];
  for (int j = 0; j < 4096; j++) bb[j] = (int)floorl(j * AL);
  LD *f = calloc((size_t)(J + 1) * W, sizeof(LD)), *g = calloc((size_t)(J + 1) * W, sizeof(LD)); f[0] = 1;
  for (int i = 0; i < J; i++) { LD acc = 0; for (int S2 = 1; S2 <= bb[i + 1] && S2 < W; S2++) { if (S2 - 1 <= bb[i]) acc += f[(size_t)i * W + S2 - 1]; f[(size_t)(i + 1) * W + S2] = acc; } }
  g[(size_t)J * W + sg] = 1;
  for (int i = J - 1; i >= 0; i--) { LD acc = 0; int top = bb[i + 1] < sg ? bb[i + 1] : sg;
    for (int S2 = top; S2 >= 1; S2--) { acc += g[(size_t)(i + 1) * W + S2]; if (S2 - 1 <= bb[i]) g[(size_t)i * W + S2 - 1] = acc; } }
  LD P = f[(size_t)J * W + sg], tot = 0; for (int S = 0; S < W; S++) tot += f[(size_t)N0 * W + S];
  printf("J=%d sigma=%d N=%d b(N)=%d log2 total(N)=%.2Lf  h*N=%.2Lf\n", J, sg, N0, bb[N0], log2l(tot), 1.50564L * N0);
  for (int S = 0; S <= bb[N0]; S++) { LD p = f[(size_t)N0 * W + S], pi = p * g[(size_t)N0 * W + S] / P; if (pi > 1e-3) printf("  S=%d (b-S=%d) log2p=%.2Lf pi=%.4Lf\n", S, bb[N0] - S, log2l(p), pi); }
}
