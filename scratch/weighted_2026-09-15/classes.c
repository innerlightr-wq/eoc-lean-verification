// E_P 2^{-r(P)} = #swap classes / |P| (pairs (2k,2k+1), swappable: d != e and both orders admissible)
// = full-group value of the class-averaged swap-cube L^2 bound -> ideal swap-cube amplitude rate.
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int Kb[2048];
int main(void) {
  const long double A = 1.584962500721156181453738943947816508759814407692481060455L;
  int Js[] = {30, 60, 100, 150, 200, 300, 400, 600}; int cs[] = {0, 1, 2};
  for (int ci = 0; ci < 3; ci++) for (int jj = 0; jj < 8; jj++) {
    int c = cs[ci], J = Js[jj]; if (c > 0 && J != 200) continue;
    for (int j = 0; j < 2048; j++) Kb[j] = (int)floorl(c + j * A);
    int sg = Kb[J], D = sg + 2;
    double *cn = calloc(D, 8), *gn = calloc(D, 8), *cn2 = calloc(D, 8), *gn2 = calloc(D, 8);
    cn[sg] = 1; gn[sg] = 1; int i = J; double logscale = 0;
    if (J % 2) { i = J - 1; for (int S = 0; S <= Kb[i]; S++) { double v = 0; for (int d = 1; S + d <= Kb[J]; d++) v += cn[S + d]; cn2[S] = v; gn2[S] = v; }
      memcpy(cn, cn2, 8 * D); memcpy(gn, gn2, 8 * D); }
    for (i = i - 2; i >= 0; i -= 2) {
      memset(cn2, 0, 8 * D); memset(gn2, 0, 8 * D);
      for (int S = 0; S <= Kb[i]; S++) { double vc = 0, vg = 0;
        for (int d = 1; S + d <= Kb[i + 1]; d++) for (int e = 1; S + d + e <= Kb[i + 2]; e++) {
          double x = cn[S + d + e]; if (x == 0) continue; vc += x;
          int sw = (d != e) && (S + e <= Kb[i + 1]); vg += gn[S + d + e] * (sw ? 0.5 : 1.0); }
        cn2[S] = vc; gn2[S] = vg; }
      double mx = 0; for (int S = 0; S < D; S++) if (cn2[S] > mx) mx = cn2[S];
      for (int S = 0; S < D; S++) { cn[S] = cn2[S] / mx; gn[S] = gn2[S] / mx; } logscale += log2(mx);
    }
    double ratio = gn[0] / cn[0];
    printf("c=%d j0=%d: log2|P|=%.1f  E_P 2^-r = 2^%.2f  -> ideal swap-cube amplitude rate %.4f bits/step\n",
           c, J, logscale + log2(cn[0]), log2(ratio), -log2(ratio) / (2.0 * J));
    free(cn); free(gn); free(cn2); free(gn2);
  }
  return 0;
}
