// Across-N summary from weyl_words mode-0 files:
//  (1) confined critical-tilt Fourier expectation  F_N(h) = sum_w 2^-S_w e(h u_w) / sum_w 2^-S_w  (exact)
//  (2) top shell (x=0) and x=1: |W_s(h)|/M and |W_s(h)|/sqrt(M), h = 1..8
// usage: ./weyl_scaling files...
#include <complex.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
int main(int argc, char **argv) {
  for (int a = 1; a < argc; a++) {
    FILE *f = fopen(argv[a], "rb"); int hdr[5]; fread(hdr, 4, 5, f); int c = hdr[1], N = hdr[2], B = hdr[3], smax = hdr[4];
    uint64_t *H = malloc(8ULL << B); double complex F[9] = {0}; double Z = 0; double complex Wt[3][9]; uint64_t Mt[3];
    for (int s = 0; s <= smax; s++) {
      uint64_t M; double Wd[128]; fread(&M, 8, 1, f); fread(H, 8, 1ULL << B, f); fread(Wd, 8, 128, f);
      double w = ldexp(1.0, -s); Z += w * M;
      for (int h = 1; h <= 8; h++) F[h] += w * (Wd[2 * (h - 1)] + I * Wd[2 * (h - 1) + 1]);
      int x = smax - s; if (x <= 2) { Mt[x] = M; for (int h = 1; h <= 8; h++) Wt[x][h] = Wd[2 * (h - 1)] + I * Wd[2 * (h - 1) + 1]; }
    }
    printf("c=%d N=%2d  tilt |F(h)|:", c, N); for (int h = 1; h <= 8; h++) printf(" %.2e", cabs(F[h]) / Z); printf("\n");
    for (int x = 0; x <= 1; x++) { printf("        x=%d M=%11llu |W|/M:", x, (unsigned long long)Mt[x]); for (int h = 1; h <= 8; h++) printf(" %.1e", cabs(Wt[x][h]) / Mt[x]);
      printf("  |W|/sqrtM:"); for (int h = 1; h <= 4; h++) printf(" %5.2f", cabs(Wt[x][h]) / sqrt((double)Mt[x])); printf("\n"); }
    fclose(f); free(H);
  }
  return 0;
}
