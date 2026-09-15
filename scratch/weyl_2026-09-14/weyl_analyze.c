// Analyze weyl_words output. For near-top shells x = sN - s, top-block resolution n (K = s+1-n):
//   Z   = N_0 / (M 2^-n)             exact least-realizer count over Haar share (the quantity to bound)
//   E   = sum_{g!=0 mod 2^n} |V(g)|/M (sufficient condition: E <= C-1 gives Z <= C)
//   chi = chi^2/dof of the 2^n top-block cells (random points: 1)
//   rmsV= rms_{g!=0}|V(g)|/sqrt(M)   (random: ~1)   maxV = max |V(g)|/sqrt(M)
// Additive W_s(h), h=1..64: |W|/sqrt(M) by v2(h).
// usage: ./weyl_analyze file nmax xmax
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
  FILE *f = fopen(argv[1], "rb"); int nmax = atoi(argv[2]), xmax = atoi(argv[3]); int hdr[5]; fread(hdr, 4, 5, f);
  int c = hdr[1], N = hdr[2], B = hdr[3], smax = hdr[4];
  uint64_t *H = malloc(8ULL << B); double complex *a = malloc(16ULL << B);
  printf("c=%d N=%d sN=%d\n", c, N, smax);
  for (int s = 0; s <= smax; s++) {
    uint64_t M; double Wd[128]; fread(&M, 8, 1, f); fread(H, 8, 1ULL << B, f); fread(Wd, 8, 128, f);
    int x = smax - s; if (x > xmax || M < 50) continue;
    printf(" x=%d s=%d M=%llu\n", x, s, (unsigned long long)M);
    for (int n = 1; n <= nmax && n <= s && n <= B; n++) {
      int L = 1 << n, per = 1 << (B - n);
      for (int i = 0; i < L; i++) { double v = 0; for (int k = 0; k < per; k++) v += H[i * per + k]; a[i] = v; }
      double mean = (double)M / L, chi = 0; for (int i = 0; i < L; i++) chi += (creal(a[i]) - mean) * (creal(a[i]) - mean);
      double Z = creal(a[0]) / mean; fft(a, L);
      double E = 0, s2 = 0, mx = 0; for (int g = 1; g < L; g++) { double v = cabs(a[g]); E += v; s2 += v * v; if (v > mx) mx = v; }
      int K = s + 1 - n;
      printf("   n=%2d K=%2d A=%5.3f Z=%6.3f E=%9.3f chi2/dof=%6.3f rmsV=%6.3f maxV=%6.2f\n", n, K, (double)N / K, Z, E / M,
             chi / mean / (L - 1), sqrt(s2 / (L - 1) / M), mx / sqrt(M));
    }
    for (int q = 0; q <= 6; q++) { double mx = 0, sm = 0; int cnt = 0;
      for (int h = 1; h <= 64; h++) if (__builtin_ctz(h) == q) { double v = hypot(Wd[2 * (h - 1)], Wd[2 * (h - 1) + 1]) / sqrt((double)M); sm += v; cnt++; if (v > mx) mx = v; }
      printf("   additive v2(h)=%d: |W|/sqrtM mean=%8.3f max=%8.3f  (max |W|/M=%.2e)\n", q, sm / cnt, mx, mx / sqrt((double)M)); }
  }
  return 0;
}
