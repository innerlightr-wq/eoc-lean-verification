// List the largest top-block Fourier coefficients |V(g)|/sqrt(M) at resolution n for shell x.
// usage: ./weyl_peaks file n x top
#include <complex.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
static void fft(double complex *a, int n) {
  for (int i = 1, j = 0; i < n; i++) { int b = n >> 1; for (; j & b; b >>= 1) j ^= b; j ^= b; if (i < j) { double complex t = a[i]; a[i] = a[j]; a[j] = t; } }
  for (int len = 2; len <= n; len <<= 1) { double complex w = cexp(-2 * M_PI * I / len);
    for (int i = 0; i < n; i += len) { double complex u = 1; for (int k = 0; k < len / 2; k++) { double complex x = a[i + k], y = a[i + k + len / 2] * u; a[i + k] = x + y; a[i + k + len / 2] = x - y; u *= w; } } }
}
int main(int argc, char **argv) {
  FILE *f = fopen(argv[1], "rb"); int n = atoi(argv[2]), xx = atoi(argv[3]), top = atoi(argv[4]); int hdr[5]; fread(hdr, 4, 5, f);
  int B = hdr[3], smax = hdr[4]; uint64_t *H = malloc(8ULL << B); double complex *a = malloc(16ULL << B); double *mag = malloc(8ULL << B);
  for (int s = 0; s <= smax; s++) {
    uint64_t M; double Wd[128]; fread(&M, 8, 1, f); fread(H, 8, 1ULL << B, f); fread(Wd, 8, 128, f);
    if (smax - s != xx) continue;
    int L = 1 << n, per = 1 << (B - n);
    for (int i = 0; i < L; i++) { double v = 0; for (int k = 0; k < per; k++) v += H[i * per + k]; a[i] = v; }
    fft(a, L); for (int g = 0; g < L; g++) mag[g] = cabs(a[g]) / sqrt((double)M);
    mag[0] = 0;
    for (int t = 0; t < top; t++) { int bi = 1; for (int g = 1; g < L; g++) if (mag[g] > mag[bi]) bi = g;
      int gs = bi > L / 2 ? bi - L : bi; printf("g=%6d (signed %6d, v2=%2d, g/2^n=%.5f)  |V|/sqrtM=%7.2f\n", bi, gs, __builtin_ctz(bi), (double)bi / L, mag[bi]); mag[bi] = 0; }
  }
  return 0;
}
