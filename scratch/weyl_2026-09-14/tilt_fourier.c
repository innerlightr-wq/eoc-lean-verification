// Critical-tilt (Haar) Fourier expectation of the normalized least realizer:
//   F_N(h) = E_mu[ e(h mu / 2^(S_N(mu)+1)) ] = sum_w 2^-S_w e(h r_w / 2^(S_w+1))   (free, all words)
// estimated by Monte Carlo over uniform odd 128-bit seeds; mu mod 2^(S_N+1) = r_w.
// usage: ./tilt_fourier samples Nmax seed
#include <complex.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
typedef unsigned __int128 u128;
static uint64_t s0, s1;
static inline uint64_t rnd(void) { uint64_t a = s0, b = s1; s0 = b; a ^= a << 23; s1 = a ^ b ^ (a >> 17) ^ (b >> 26); return s1 + b; }
int main(int argc, char **argv) {
  long long ns = atoll(argv[1]); int Nmax = atoi(argv[2]); s0 = 0x9E3779B97F4A7C15ULL ^ atoll(argv[3]); s1 = 0xD1B54A32D192ED03ULL;
  static double complex acc[64][9];
  for (long long t = 0; t < ns; t++) {
    u128 mu = ((u128)rnd() << 64) | rnd(); mu |= 1; u128 x = mu; int S = 0;
    for (int N = 1; N <= Nmax; N++) {
      x = 3 * x + 1; uint64_t lo = (uint64_t)x; int v = lo ? __builtin_ctzll(lo) : 64 + __builtin_ctzll((uint64_t)(x >> 64));
      x >>= v; S += v; if (S + 1 > 120) break;
      // theta = mu / 2^(S+1) mod 1, use top 64 bits of mu mod 2^(S+1)
      u128 r = mu & ((((u128)1) << (S + 1)) - 1);
      long double th = (S + 1 > 64) ? (long double)(uint64_t)(r >> (S + 1 - 64)) / 18446744073709551616.0L : (long double)(uint64_t)r / ldexpl(1.0L, S + 1);
      for (int h = 1; h <= 8; h++) acc[N][h] += cexp(2 * M_PI * I * (double)fmodl(h * th, 1.0L));
    }
  }
  printf("free Haar ensemble, %lld samples (noise ~ %.1e)\n", ns, 1 / sqrt((double)ns));
  for (int N = 1; N <= Nmax; N++) { printf("N=%2d", N); for (int h = 1; h <= 8; h++) printf(" %8.5f", cabs(acc[N][h]) / ns); printf("\n"); }
  return 0;
}
