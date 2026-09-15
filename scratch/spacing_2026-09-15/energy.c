// Part XXIV: exact additive energy E = #{(P,Q,R,S): y_P + y_Q = y_R + y_S mod 2^m} of the prefix points y_P = 3^{-J} q_P mod 2^m.
// Sidon minimum 2n^2 - n (plus pairs with 2(y_P - y_Q) = 0).  usage: energy J sigma t
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
static int J, sg, m, bb[64]; static uint64_t MASK, inv3p[64], *Y; static long n, cap;
static void dfs(int i, int s, uint64_t z) {
  if (i == J) { if (s != sg) return; if (n == cap) { cap = cap ? 2 * cap : 1024; Y = realloc(Y, cap * 8); } Y[n++] = z & MASK; return; }
  uint64_t z2 = (z + inv3p[i] * (1ULL << s)) & MASK;
  for (int s2 = s + 1; s2 <= bb[i + 1] && s2 <= sg; s2++) dfs(i + 1, s2, z2);
}
static int cmp(const void *a, const void *b) { uint64_t x = *(uint64_t *)a, y = *(uint64_t *)b; return x < y ? -1 : x > y; }
int main(int c, char **v) { J = atoi(v[1]); sg = atoi(v[2]); m = sg + atoi(v[3]) + 1; MASK = (1ULL << m) - 1;
  for (int j = 0; j < 64; j++) bb[j] = (int)floor(j * 1.5849625007211562);
  uint64_t inv3 = 0xAAAAAAAAAAAAAAABULL, p = 1; for (int l = 0; l < 64; l++) { p *= inv3; inv3p[l] = p; }
  dfs(0, 0, 0);  // y = sum inv3^(i+1) 2^{S_i} = 3^{-J} q_P (sign irrelevant for energy)
  uint64_t *s = malloc(sizeof(uint64_t) * n * n); long k = 0;
  for (long a = 0; a < n; a++) for (long b = 0; b < n; b++) s[k++] = (Y[a] + Y[b]) & MASK;
  qsort(s, k, 8, cmp); double E = 0; long run = 1;
  for (long i = 1; i <= k; i++) { if (i < k && s[i] == s[i - 1]) run++; else { E += (double)run * run; run = 1; } }
  printf("J=%d sigma=%d m=%d n=|P|=%ld  E=%.0f  E/(2n^2-n)=%.4f\n", J, sg, m, n, E, E / (2.0 * n * n - n)); return 0; }
