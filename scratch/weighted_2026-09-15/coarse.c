// Ideal L^2 ceiling of the L-step block-cube route: E_P prod_blocks 1/#(internal completions with same block endpoints)
// = #(coarse paths S_0,S_L,S_2L,...)/|P|  -> rate (log2|P| - log2 #coarse)/(2 j0).
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int Kb[2048];
int main(void) {
  const long double A = 1.584962500721156181453738943947816508759814407692481060455L;
  int Js[] = {60, 150, 300, 600}; int Ls[] = {1, 2, 3, 4, 6, 8};
  for (int j = 0; j < 2048; j++) Kb[j] = (int)floorl(j * A);
  for (int jj = 0; jj < 4; jj++) { int J = Js[jj], sg = Kb[J], D = sg + 2;
    // fine counts cnt[i][S] (completions to (J,sg))
    double **cnt = malloc(sizeof(double *) * (J + 1)); double *scale = calloc(J + 1, 8);
    for (int i = 0; i <= J; i++) cnt[i] = calloc(D, 8);
    cnt[J][sg] = 1; for (int i = J - 1; i >= 0; i--) { double mx = 0; for (int S = 0; S <= Kb[i]; S++) { double v = 0; for (int d = 1; S + d <= Kb[i + 1]; d++) v += cnt[i + 1][S + d]; cnt[i][S] = v; if (v > mx) mx = v; }
      for (int S = 0; S <= Kb[i]; S++) cnt[i][S] /= mx; scale[i] = scale[i + 1] + log2(mx); }
    double log2P = scale[0] + log2(cnt[0][0]);
    printf("j0=%d log2|P|=%.1f:", J, log2P);
    for (int li = 0; li < 6; li++) { int L = Ls[li];
      // reach[i][S'] from S within one block: block transition exists iff a fine path from (i,S) to (i+L',S') respecting barrier
      double *co = calloc(D, 8), *co2 = calloc(D, 8); co[sg] = 1; double cscale = 0;
      int i = J; int first = J % L ? J - J % L : J - L;
      for (i = J; i > 0; ) { int i0 = (i % L) ? i - i % L : i - L; if (i0 < 0) i0 = 0;
        // for each start S at i0, the set of S' reachable at i
        memset(co2, 0, 8 * D);
        char *R = calloc(D, 1), *R2 = calloc(D, 1);
        for (int S = 0; S <= Kb[i0]; S++) { if (cnt[i0][S] == 0) continue; memset(R, 0, D); R[S] = 1;
          for (int k = i0; k < i; k++) { memset(R2, 0, D); for (int x = 0; x < D; x++) if (R[x]) for (int d = 1; x + d <= Kb[k + 1]; d++) R2[x + d] = 1; memcpy(R, R2, D); }
          double v = 0; for (int x = 0; x < D; x++) if (R[x] && cnt[i][x] > 0) v += co[x]; co2[S] = v; }
        double mx = 0; for (int S = 0; S < D; S++) if (co2[S] > mx) mx = co2[S];
        for (int S = 0; S < D; S++) co[S] = co2[S] / mx; cscale += log2(mx); free(R); free(R2); i = i0; }
      double log2C = cscale + log2(co[0]);
      printf("  L=%d: %.4f", L, (log2P - log2C) / (2.0 * J)); free(co); free(co2); (void)first; }
    printf("   (random ceiling h/2=0.7528)\n");
  }
  return 0;
}
