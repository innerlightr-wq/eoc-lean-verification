// Exact enumeration of c-confined words of length N with their least realizers r(D) (mod 2^{S+1}),
// built along the prefix tree: extending a prefix with least realizer r (orbit state m = T^j(r))
// by digit d lifts r by t 2^{S+1}, t = (2^{d-1} - (3m+1)/2) * 3^{-(j+1)} mod 2^d.
// Per shell gap x = s_N - S_N: count, mean/var of u = r/2^{S+1}, 64-bin histogram of u, top bit,
// r mod 16 distribution, r_min; pair split depth q = v2(r(D)-r(E)) histogram (same-shell pairs and
// all pairs) from the trie (PairValuation: q = S_k + min(a,b)).
// usage: ./word_enum c N
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned __int128 u128;
#define XM 8
#define QM 80
static int N, c, Kb[128], sN;
static double su[XM], su2[XM], cnt[XM];
static unsigned long long hu[XM][64], top[XM], low[XM][16];
static u128 rmin[XM];
static double pairS[XM][QM], pairA[QM];
static uint64_t inv3pow[128];
static inline int ctz128(u128 x) { uint64_t lo = (uint64_t)x; return lo ? __builtin_ctzll(lo) : 64 + __builtin_ctzll((uint64_t)(x >> 64)); }
// returns counts per shell gap (x < XM, lumped XM-1 for larger) in out[]
static void dfs(int j, int S, u128 r, u128 m, double *out) {
  memset(out, 0, sizeof(double) * XM);
  if (j == N) {
    int x = sN - S;
    int xi = x < XM ? x : XM - 1;
    double u = (double)r / ldexp(1.0, S + 1);
    cnt[xi] += 1; su[xi] += u; su2[xi] += u * u;
    int b = (int)(u * 64); if (b > 63) b = 63;
    hu[xi][b]++;
    if (r >> S) top[xi]++;
    low[xi][(int)(r & 15)]++;
    if (rmin[xi] == 0 || r < rmin[xi]) rmin[xi] = r;
    out[xi] = 1;
    return;
  }
  double ch[64][XM];
  int nd = 0, ds[64];
  int dmax = Kb[j + 1] - S;
  u128 A = 3 * m + 1;  // even
  uint64_t Ah = (uint64_t)(A >> 1);
  for (int d = 1; d <= dmax && d < 60; d++) {
    // t = (2^{d-1} - A/2) * inv(3^{j+1}) mod 2^d
    uint64_t mask = (d == 64) ? ~0ULL : ((1ULL << d) - 1);
    uint64_t t = (((1ULL << (d - 1)) - Ah) * inv3pow[j + 1]) & mask;
    u128 r2 = r + ((u128)t << (S + 1));
    u128 p3 = 1; for (int i = 0; i < j; i++) p3 *= 3;
    u128 mm = m + 2 * p3 * (u128)t;
    u128 z = 3 * mm + 1;
    if (ctz128(z) != d) { fprintf(stderr, "lift error\n"); exit(1); }
    dfs(j + 1, S + d, r2, z >> d, ch[nd]);
    ds[nd] = d; nd++;
  }
  for (int a = 0; a < nd; a++) {
    for (int x = 0; x < XM; x++) out[x] += ch[a][x];
    for (int b = a + 1; b < nd; b++) {
      int q = S + (ds[a] < ds[b] ? ds[a] : ds[b]);
      double ta = 0, tb = 0;
      for (int x = 0; x < XM; x++) { pairS[x][q] += ch[a][x] * ch[b][x]; ta += ch[a][x]; tb += ch[b][x]; }
      pairA[q] += ta * tb;
    }
  }
}
int main(int argc, char **argv) {
  c = atoi(argv[1]); N = atoi(argv[2]);
  const long double A = 1.584962500721156181453738943947816508759814407692481060455L;
  for (int j = 1; j <= N; j++) {
    long s = (long)floorl(c + j * A);
    Kb[j] = (int)s;
  }
  sN = Kb[N];
  // inverse of 3^k mod 2^64
  uint64_t inv3 = 0xAAAAAAAAAAAAAAABULL;  // 3 * inv3 = 1 mod 2^64
  inv3pow[0] = 1;
  for (int k = 1; k < 128; k++) inv3pow[k] = inv3pow[k - 1] * inv3;
  double out[XM];
  // root: the empty word, least realizer class of all odd numbers: r = 1 mod 2 (S = 0), m = r = 1
  dfs(0, 0, 1, 1, out);
  double tot = 0; for (int x = 0; x < XM; x++) tot += cnt[x];
  printf("c=%d N=%d sN=%d phi=%.4f words=%.0f\n", c, N, sN, fmod((double)N * (double)A, 1.0), tot);
  for (int x = 0; x < XM - 1; x++) {
    if (cnt[x] < 1) continue;
    double mu = su[x] / cnt[x], var = su2[x] / cnt[x] - mu * mu;
    // KS distance of u from uniform via histogram
    double cum = 0, ks = 0;
    for (int b = 0; b < 64; b++) { cum += hu[x][b]; double d = fabs(cum / cnt[x] - (b + 1) / 64.0); if (d > ks) ks = d; }
    printf("  x=%d count=%.0f mean_u=%.5f var_u=%.5f (unif 0.08333) KS64=%.5f top=%.5f rmin=%.0f low16:",
           x, cnt[x], mu, var, ks, top[x] / cnt[x], (double)rmin[x]);
    for (int k = 1; k < 16; k += 2) printf(" %.4f", low[x][k] / cnt[x]);
    printf("\n");
  }
  // pair split distributions: all pairs and same-shell x=0,1 pairs; normalized
  for (int w = -1; w < 2; w++) {
    double *P = (w < 0) ? pairA : pairS[w];
    double t = 0; for (int q = 0; q < QM; q++) t += P[q];
    if (t <= 0) continue;
    printf("  pairs %s total=%.0f  q:frac", w < 0 ? "all" : (w == 0 ? "x=0" : "x=1"), t);
    for (int q = 1; q < QM && q <= sN; q++) if (P[q] > 0) printf(" %d:%.5f", q, P[q] / t);
    printf("\n");
  }
  return 0;
}
