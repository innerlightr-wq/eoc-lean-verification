// Monte Carlo estimate of the exact prefix end-state collision excess
//   delta_t = 2^t * sum_a mu(a)^2 - 1,  mu = law of m_P mod 2^(t+1) over uniform P in P_{j0,sigma}
// Samples Ns uniform confined prefixes with S_{j0} = sigma (backward completion counts),
// computes r_P, m_P = T^{j0}(r_P) exactly (u128 lift recursion), and estimates the collision
// probability with the unbiased U-statistic (sum n_a^2 - Ns)/(Ns(Ns-1)) for t = 4..tmax.
// usage: ./mc_collide c j0 sigma Ns seed tmax
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned __int128 u128;
static int Kb[256]; static uint64_t inv3pow[128]; static u128 p3[128];
static uint64_t s0, s1;
static inline uint64_t rnd(void) { uint64_t a = s0, b = s1; s0 = b; a ^= a << 23; s1 = a ^ b ^ (a >> 17) ^ (b >> 26); return s1 + b; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static int cmp64(const void *x, const void *y) { uint64_t a = *(const uint64_t *)x, b = *(const uint64_t *)y; return a < b ? -1 : a > b; }
int main(int argc, char **argv) {
  int c = atoi(argv[1]), J = atoi(argv[2]), sg = atoi(argv[3]); long Ns = atol(argv[4]); s0 = 0x9E3779B97F4A7C15ULL ^ atoll(argv[5]); s1 = 0xD1B54A32D192ED03ULL ^ (atoll(argv[5]) << 7);
  int tmax = atoi(argv[6]);
  const long double A = 1.584962500721156181453738943947816508759814407692481060455L;
  for (int j = 0; j < 256; j++) Kb[j] = (int)floorl(c + j * A);
  uint64_t i3 = 0xAAAAAAAAAAAAAAABULL; inv3pow[0] = 1; for (int k = 1; k < 128; k++) inv3pow[k] = inv3pow[k - 1] * i3;
  p3[0] = 1; for (int k = 1; k < 80; k++) p3[k] = 3 * p3[k - 1];
  // completion counts: comp[i][S] = # ways from (i,S) to (J, sg) respecting barrier
  static long double comp[256][256]; memset(comp, 0, sizeof comp);
  comp[J][sg] = 1;
  for (int i = J - 1; i >= 0; i--) for (int S = 0; S <= Kb[i]; S++) { long double v = 0; for (int d = 1; S + d <= Kb[i + 1]; d++) v += comp[i + 1][S + d]; comp[i][S] = v; }
  printf("c=%d j0=%d sigma=%d |P|=%.4Le (log2 %.2f) Ns=%ld\n", c, J, sg, comp[0][0], (double)log2l(comp[0][0]), Ns);
  uint64_t *mm = malloc(8 * Ns);
  for (long n = 0; n < Ns; n++) {
    int S = 0; u128 r = 1, m = 1;
    for (int j = 0; j < J; j++) {
      long double tot = comp[j][S], u = urand() * tot, acc = 0; int d = 1;
      for (;; d++) { acc += comp[j + 1][S + d]; if (u < acc || S + d >= Kb[j + 1]) break; }
      u128 Aa = 3 * m + 1; uint64_t Ah = (uint64_t)(Aa >> 1);
      uint64_t tt = (((1ULL << (d - 1)) - Ah) * inv3pow[j + 1]) & ((1ULL << d) - 1);
      u128 z = 3 * (m + 2 * p3[j] * (u128)tt) + 1;
      r += (u128)tt << (S + 1); m = z >> d; S += d;
    }
    if (S != sg) { fprintf(stderr, "sampling error\n"); return 1; }
    mm[n] = (uint64_t)m;
  }
  for (int t = 4; t <= tmax; t += 2) {
    uint64_t mask = (t + 1 >= 64) ? ~0ULL : ((1ULL << (t + 1)) - 1);
    uint64_t *k = malloc(8 * Ns); for (long n = 0; n < Ns; n++) k[n] = mm[n] & mask;
    qsort(k, Ns, 8, cmp64);
    long double pairs = 0; long run = 1;
    for (long n = 1; n <= Ns; n++) { if (n < Ns && k[n] == k[n - 1]) run++; else { pairs += (long double)run * (run - 1); run = 1; } }
    long double col = pairs / ((long double)Ns * (Ns - 1));
    double delta = (double)(ldexpl(col, t) - 1), se = sqrt(2.0 * ldexp(1.0, t)) / Ns;
    double rnd_delta = (double)(ldexpl(1.0L, t) / comp[0][0]);
    printf("  t=%2d delta=%+.3e (se %.1e)  random %.2e   need(2^-0.05t)=%.3f\n", t, delta, se, rnd_delta, pow(2, -0.05 * t));
    free(k);
  }
  return 0;
}
