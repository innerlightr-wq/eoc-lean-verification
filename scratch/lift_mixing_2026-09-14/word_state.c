// Word-ensemble balance of least-realizer orbit states m(D) = T^N(r(D)) mod 2^k (odd residues),
// for c-confined words (mode 0), terminal-only words S_N <= s_N (mode 1), or full fixed-sum shells
// S_N = s_N - x for x in {0,1,2} (mode 1 restricted).  Also the final lift digit tau and the parity
// relation.  usage: ./word_state mode c N
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
typedef unsigned __int128 u128;
static int N, c, mode, Kb[128], sN;
static unsigned long long H[4][256];
static uint64_t inv3pow[128];
static inline int ctz128(u128 x) { uint64_t lo = (uint64_t)x; return lo ? __builtin_ctzll(lo) : 64 + __builtin_ctzll((uint64_t)(x >> 64)); }
static void dfs(int j, int S, u128 r, u128 m) {
  if (j == N) { int x = sN - S; int a = (int)((uint64_t)m & 511) >> 1; if (x < 3) H[x][a]++; H[3][a]++; return; }
  int dmax = (mode == 0) ? Kb[j + 1] - S : (sN - S) - (N - j - 1);
  u128 A = 3 * m + 1; uint64_t Ah = (uint64_t)(A >> 1);
  u128 p3 = 1; for (int i = 0; i < j; i++) p3 *= 3;
  for (int d = 1; d <= dmax && d < 60; d++) {
    uint64_t t = (((1ULL << (d - 1)) - Ah) * inv3pow[j + 1]) & ((1ULL << d) - 1);
    u128 z = 3 * (m + 2 * p3 * (u128)t) + 1;
    dfs(j + 1, S + d, r + ((u128)t << (S + 1)), z >> d);
  }
}
int main(int argc, char **argv) {
  mode = atoi(argv[1]); c = atoi(argv[2]); N = atoi(argv[3]);
  const long double A = 1.584962500721156181453738943947816508759814407692481060455L;
  for (int j = 1; j <= N; j++) Kb[j] = (int)floorl(c + j * A);
  sN = Kb[N];
  uint64_t inv3 = 0xAAAAAAAAAAAAAAABULL; inv3pow[0] = 1;
  for (int k = 1; k < 128; k++) inv3pow[k] = inv3pow[k - 1] * inv3;
  dfs(0, 0, 1, 1);
  const char *nm[4] = {"x=0", "x=1", "x=2", "all"};
  printf("mode=%s c=%d N=%d\n", mode ? "terminal-only" : "confined", c, N);
  for (int s = 0; s < 4; s++) {
    unsigned long long tot = 0; for (int a = 0; a < 256; a++) tot += H[s][a];
    printf("  %s n=%llu:", nm[s], tot);
    for (int k = 2; k <= 9; k++) {
      int nc = 1 << (k - 1); double e = (double)tot / nc, chi = 0; long long mx = -1, mn = -1;
      for (int b = 0; b < nc; b++) { unsigned long long v = 0; for (int a = b; a < 256; a += nc) v += H[s][a];
        chi += (v - e) * (v - e) / e; if (mx < 0 || (long long)v > mx) mx = v; if (mn < 0 || (long long)v < mn) mn = v; }
      printf("  k=%d chi2/dof=%.3f spread=%lld", k, chi / (nc - 1), mx - mn);
    }
    printf("\n");
  }
  return 0;
}
