// Brute-force checks over all c-confined prefixes of length j0:
//  (1) 2^sigma m_P = 3^j0 r_P + q_P (exact, u128)
//  (2) m_P == 1 - 2*3^j0*B_P (mod 2^(t+1)),  B_P = floor( (3^-j0 (2^sigma - q_P) mod 2^(sigma+t+1)) / 2^(sigma+1) )
//  (3) r_P == 3^-j0 (2^sigma - q_P) mod 2^(sigma+1)
//  (4) Phi(h) by direct summation vs the DP (printed for h=1..3 at sigma = top)
#include <complex.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
typedef unsigned __int128 u128;
static int J, t, Kb[128], topS; static uint64_t inv3pow[128]; static u128 p3[128], inv3;
static long long bad1, bad2, bad3, tot; static double complex phi[4];
static u128 pw(u128 b, int e) { u128 r = 1; while (e--) r *= b; return r; }
static void dfs(int j, int S, u128 r, u128 m, u128 q) {
  if (j == J) {
    tot++;
    u128 lhs = ((u128)1 << S) * m, rhs = p3[J] * r + q; if (lhs != rhs) bad1++;
    int M = S + t + 1; u128 MASK = ((u128)1 << M) - 1;
    u128 i3j = pw(inv3, J) & MASK;
    u128 y = ((((u128)1 << S) - q) * i3j) & MASK;         // 3^-j0 (2^S - q) mod 2^M
    u128 B = y >> (S + 1);
    u128 lhs2 = m & (((u128)1 << (t + 1)) - 1);
    u128 rhs2 = (1 - 2 * p3[J] * B) & (((u128)1 << (t + 1)) - 1);
    if (lhs2 != rhs2) bad2++;
    if ((y & ((((u128)1) << (S + 1)) - 1)) != r) bad3++;
    if (S == topS) for (int h = 1; h <= 3; h++) {
      int m2 = 40; u128 MK = ((u128)1 << m2) - 1; u128 z = (q * (pw(inv3, J) & MK)) & MK;
      phi[h] += cexp(-2 * M_PI * I * (double)((long double)((h * z) & MK) / ldexpl(1.0L, m2))); }
    return;
  }
  int dmax = Kb[j + 1] - S; u128 A = 3 * m + 1; uint64_t Ah = (uint64_t)(A >> 1);
  for (int d = 1; d <= dmax && d < 60; d++) {
    uint64_t tt = (((1ULL << (d - 1)) - Ah) * inv3pow[j + 1]) & ((1ULL << d) - 1);
    u128 z = 3 * (m + 2 * p3[j] * (u128)tt) + 1;
    dfs(j + 1, S + d, r + ((u128)tt << (S + 1)), z >> d, 3 * q + ((u128)1 << S));
  }
}
int main(int argc, char **argv) {
  int c = atoi(argv[1]); J = atoi(argv[2]); t = atoi(argv[3]);
  const long double A = 1.584962500721156181453738943947816508759814407692481060455L;
  for (int j = 0; j < 128; j++) Kb[j] = (int)floorl(c + j * A);
  topS = Kb[J];
  uint64_t i3 = 0xAAAAAAAAAAAAAAABULL; inv3pow[0] = 1; for (int k = 1; k < 128; k++) inv3pow[k] = inv3pow[k - 1] * i3;
  p3[0] = 1; for (int k = 1; k < 80; k++) p3[k] = 3 * p3[k - 1];
  { u128 x = 1; for (int k = 0; k < 7; k++) x = x * (2 - 3 * x); inv3 = x; }
  dfs(0, 0, 1, 1, 0);
  printf("j0=%d t=%d prefixes=%lld  bad(2^s m = 3^j r + q)=%lld  bad(m formula)=%lld  bad(r formula)=%lld\n", J, t, tot, bad1, bad2, bad3);
  for (int h = 1; h <= 3; h++) printf("  direct Phi(%d) (m=40, sigma=top) = %.6e %+.6ei\n", h, creal(phi[h]), cimag(phi[h]));
  return 0;
}
