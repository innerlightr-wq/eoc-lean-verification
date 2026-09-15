// Collision / Fourier statistics of prefix end states m_P mod 2^b (odd residues, 2^(b-1) classes).
//   delta = 2^(b-1) sum_x N(x)^2 / |P|^2 - 1   (relative collision excess; random: (2^(b-1)-1)/|P|)
//   ratio = delta / random                      (= chi^2/dof)
//   supX  = max over nonzero eta of |Xhat(eta)| / |P|,  also * sqrt|P| (random ~ sqrt(log))
// usage: ./pstate_analyze file bmax
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
  FILE *f = fopen(argv[1], "rb"); int bmax = atoi(argv[2]); int hdr[4]; fread(hdr, 4, 4, f);
  int c = hdr[0], J = hdr[1], B = hdr[2], smax = hdr[3];
  uint64_t *H = malloc(8ULL << B); double complex *a = malloc(16ULL << B);
  printf("c=%d j0=%d\n", c, J);
  for (int s = 0; s <= smax; s++) {
    uint64_t P; fread(&P, 8, 1, f); fread(H, 8, 1ULL << B, f);
    if (P < 1000 || smax - s > 2) continue;
    printf(" sigma=%d (top gap %d) |P|=%llu\n", s, smax - s, (unsigned long long)P);
    for (int b = 2; b <= bmax && b <= B; b++) {
      int L = 1 << b; for (int i = 0; i < L; i++) a[i] = 0;
      for (uint64_t x = 0; x < (1ULL << B); x++) a[x & (L - 1)] += H[x];
      double s2 = 0; for (int i = 1; i < L; i += 2) s2 += creal(a[i]) * creal(a[i]);
      double delta = (L / 2) * s2 / ((double)P * P) - 1, rnd = (L / 2 - 1) / (double)P;
      fft(a, L); double mx = 0; for (int e = 1; e < L; e++) { if (e == L / 2) continue; double v = cabs(a[e]); if (v > mx) mx = v; }
      printf("   b=%2d delta=%.3e random=%.3e ratio=%6.3f  supX/|P|=%.3e  supX/sqrt|P|=%6.2f  need(2^-0.05(b-1))=%.3f\n", b, delta, rnd, delta / rnd,
             mx / P, mx / sqrt((double)P), pow(2, -0.05 * (b - 1)));
    }
  }
  return 0;
}
