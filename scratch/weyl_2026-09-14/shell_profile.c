// Haar mass profile by shell gap x: rho_x = M_{sN-x} 2^x / M_{sN}; compare with (2(alpha-1)/alpha)^x (1+x)
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
int main(int argc, char **argv) {
  for (int a = 1; a < argc; a++) {
    FILE *f = fopen(argv[a], "rb"); int hdr[5]; fread(hdr, 4, 5, f); int c = hdr[1], N = hdr[2], B = hdr[3], smax = hdr[4];
    uint64_t *Ms = calloc(smax + 1, 8); uint64_t *H = malloc(8ULL << B);
    for (int s = 0; s <= smax; s++) { double Wd[128]; fread(&Ms[s], 8, 1, f); fread(H, 8, 1ULL << B, f); fread(Wd, 8, 128, f); }
    double al = log2(3.0), q = 2 * (al - 1) / al;
    printf("c=%d N=%d:", c, N);
    for (int x = 0; x <= 10; x++) printf(" x=%d:%.3f(%.3f)", x, (double)Ms[smax - x] * pow(2, x) / Ms[smax], pow(q, x) * (1 + x));
    printf("\n"); fclose(f);
  }
  return 0;
}
