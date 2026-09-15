// Orbit-merge clusters among deep survivors.  Survivors: seeds mu < 2^HI with exit > N (wall U).
// Two survivors are joined if their orbits share an odd value within the first N steps (both are
// confined there).  Union-find over a hash of orbit values.  For every union (spanning-forest
// edge) the pair features are written: x y i j v2(x-y) k (common word-prefix length) and the
// drift offset R_i(x) - R_j(y); plus exit times.
// usage: ./clusters file.bin HI N U edges_out.txt
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned __int128 u128;
static const double ALPHA = 1.58496250072115618145;
static inline int ctz128(u128 x) {
  uint64_t lo = (uint64_t)x;
  if (lo) return __builtin_ctzll(lo);
  return 64 + __builtin_ctzll((uint64_t)(x >> 64));
}
static long *par;
static long findp(long a) { while (par[a] != a) { par[a] = par[par[a]]; a = par[a]; } return a; }
typedef struct { u128 v; long id; int t; } ent;
int main(int argc, char **argv) {
  FILE *f = fopen(argv[1], "rb");
  int HI = atoi(argv[2]), N = atoi(argv[3]);
  FILE *fe = fopen(argv[5], "w");
  fseek(f, 0, SEEK_END);
  long n = ftell(f) / 12;
  fseek(f, 0, SEEK_SET);
  uint64_t *mu = malloc(n * 8);
  uint32_t *ex = malloc(n * 4);
  long m = 0;
  for (long i = 0; i < n; i++) {
    uint64_t a; uint32_t e;
    fread(&a, 8, 1, f); fread(&e, 4, 1, f);
    if (e > (uint32_t)N && a < (1ULL << HI)) { mu[m] = a; ex[m] = e; m++; }
  }
  // sort by mu so that ids follow seed order
  // (simple insertion via qsort on pairs)
  typedef struct { uint64_t mu; uint32_t e; } rec;
  rec *R = malloc(m * sizeof(rec));
  for (long i = 0; i < m; i++) { R[i].mu = mu[i]; R[i].e = ex[i]; }
  int cmpr(const void *a, const void *b) { uint64_t x = ((rec *)a)->mu, y = ((rec *)b)->mu; return (x > y) - (x < y); }
  qsort(R, m, sizeof(rec), cmpr);
  long cap = 1; while (cap < 2 * m * (long)N) cap <<= 1;
  ent *H = calloc(cap, sizeof(ent));
  par = malloc(m * sizeof(long));
  for (long i = 0; i < m; i++) par[i] = i;
  long edges = 0;
  for (long id = 0; id < m; id++) {
    u128 v = R[id].mu;
    for (int t = 0; t < N; t++) {
      // insert v (value at time t)
      uint64_t h = (uint64_t)(v ^ (v >> 64)) * 0x9E3779B97F4A7C15ULL;
      long pos = h & (cap - 1);
      int found = 0;
      while (H[pos].v) {
        if (H[pos].v == v) { found = 1; break; }
        pos = (pos + 1) & (cap - 1);
      }
      if (found) {
        long other = H[pos].id;
        long ra = findp(other), rb = findp(id);
        if (ra != rb) {
          par[rb] = ra;
          edges++;
          // features: x = earlier seed (other), times H[pos].t (for x) and t (for y)
          uint64_t x = R[other].mu, y = R[id].mu;
          int i = H[pos].t, j = t;
          // words and drift at merge
          u128 a = x, b = y;
          long Sx = 0, Sy = 0;
          int k = -1;
          int kk = 0;
          for (int s = 0; s < (i > j ? i : j); s++) {
            int da = 0, db = 0;
            if (s < i) { u128 z = 3 * a + 1; da = ctz128(z); a = z >> da; Sx += da; }
            if (s < j) { u128 z = 3 * b + 1; db = ctz128(z); b = z >> db; Sy += db; }
            if (k < 0 && (s >= i || s >= j || da != db)) k = s;
            kk = s;
          }
          if (k < 0) k = (i < j ? i : j);
          double off = (Sx - i * ALPHA) - (Sy - j * ALPHA);
          fprintf(fe, "%llu %llu %d %d %d %d %.6f %u %u\n", (unsigned long long)x, (unsigned long long)y,
                  i, j, __builtin_ctzll(x ^ y), k, off, R[other].e, R[id].e);
        }
        break;  // orbit of id now joins an existing value; later values also exist (same orbit)
      }
      H[pos].v = v; H[pos].id = id; H[pos].t = t;
      u128 z = 3 * v + 1;
      v = z >> ctz128(z);
    }
  }
  // cluster sizes
  long *sz = calloc(m, sizeof(long));
  for (long i = 0; i < m; i++) sz[findp(i)]++;
  long ncl = 0, maxs = 0; double s2 = 0;
  long hist[64]; memset(hist, 0, sizeof(hist));
  for (long i = 0; i < m; i++) if (sz[i]) { ncl++; s2 += (double)sz[i] * sz[i]; if (sz[i] > maxs) maxs = sz[i]; hist[sz[i] < 63 ? sz[i] : 63]++; }
  printf("N=%d HI=%d survivors %ld clusters %ld ratio %.3f  palm_mean_size %.3f  max %ld  edges %ld\n",
         N, HI, m, ncl, (double)m / ncl, s2 / m, maxs, edges);
  printf("  size_hist:");
  for (int s = 1; s < 64; s++) if (hist[s]) printf(" %d:%ld", s, hist[s]);
  printf("\n");
  return 0;
}
