// Per-shell contributions to the confined tilt coefficient F_N(h) = sum_s 2^-s W_s(h) / Z
#include <complex.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
int main(int argc, char **argv) {
  FILE *f = fopen(argv[1], "rb"); int h = atoi(argv[2]); int hdr[5]; fread(hdr, 4, 5, f); int N = hdr[2], B = hdr[3], smax = hdr[4];
  uint64_t *H = malloc(8ULL << B); double Z = 0; double complex tot = 0; double complex con[128]; uint64_t Ms[128];
  for (int s = 0; s <= smax; s++) { double Wd[128]; fread(&Ms[s], 8, 1, f); fread(H, 8, 1ULL << B, f); fread(Wd, 8, 128, f);
    double w = ldexp(1.0, -s); Z += w * Ms[s]; con[s] = w * (Wd[2 * (h - 1)] + I * Wd[2 * (h - 1) + 1]); tot += con[s]; }
  printf("N=%d h=%d |F|=%.2e\n", N, h, cabs(tot) / Z);
  for (int s = smax; s >= 0 && s >= smax - 14; s--) if (Ms[s]) printf("  x=%2d M=%10llu mass=%.3f contrib |.|/Z=%.2e  |W|/sqrtM=%.2f\n", smax - s, (unsigned long long)Ms[s], ldexp(1.0, -s) * Ms[s] / Z, cabs(con[s]) / Z, cabs(con[s]) / ldexp(1.0, -s) / sqrt((double)Ms[s]));
  return 0;
}
