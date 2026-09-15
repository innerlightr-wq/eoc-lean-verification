// Pair statistics of survivor seeds by 2-adic distance.
// Input: binary (uint64 mu, uint32 exit) records; for each threshold N (argv), the survivor set
// {mu < 2^HI : exit > N}; outputs n_N and, for q = 1..HI-1, P_q = #{pairs x<y : v2(x-y) = q}.
// Also the same restricted to pairs whose valuation words share a common prefix of length >= k
// is derivable from q via PairValuation, so only q is recorded here.
// usage: ./pair_v2 file.bin HI N1 N2 ...
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static uint64_t rev(uint64_t x) {
  x = ((x >> 1) & 0x5555555555555555ULL) | ((x & 0x5555555555555555ULL) << 1);
  x = ((x >> 2) & 0x3333333333333333ULL) | ((x & 0x3333333333333333ULL) << 2);
  x = ((x >> 4) & 0x0F0F0F0F0F0F0F0FULL) | ((x & 0x0F0F0F0F0F0F0F0FULL) << 4);
  x = ((x >> 8) & 0x00FF00FF00FF00FFULL) | ((x & 0x00FF00FF00FF00FFULL) << 8);
  x = ((x >> 16) & 0x0000FFFF0000FFFFULL) | ((x & 0x0000FFFF0000FFFFULL) << 16);
  return (x >> 32) | (x << 32);
}
static int cmp(const void *a, const void *b) {
  uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b;
  return (x > y) - (x < y);
}
int main(int argc, char **argv) {
  FILE *f = fopen(argv[1], "rb");
  int HI = atoi(argv[2]);
  fseek(f, 0, SEEK_END);
  long n = ftell(f) / 12;
  fseek(f, 0, SEEK_SET);
  uint64_t *mu = malloc(n * 8);
  uint32_t *ex = malloc(n * 4);
  for (long i = 0; i < n; i++) { fread(&mu[i], 8, 1, f); fread(&ex[i], 4, 1, f); }
  uint64_t *key = malloc(n * 8);
  for (int a = 3; a < argc; a++) {
    int N = atoi(argv[a]);
    long m = 0;
    for (long i = 0; i < n; i++)
      if (ex[i] > (uint32_t)N && mu[i] < (1ULL << HI)) key[m++] = rev(mu[i]);
    qsort(key, m, 8, cmp);
    // lcp of consecutive in reversed order = number of equal low bits of the original values
    unsigned long long ge[65];
    memset(ge, 0, sizeof(ge));
    for (int q = 1; q <= HI; q++) {
      unsigned long long tot = 0, run = 1;
      for (long i = 1; i < m; i++) {
        uint64_t x = key[i - 1] ^ key[i];  // in reversed space: common high bits = common low bits
        int l = x ? __builtin_clzll(x) : 64;
        if (l >= q) run++;
        else { tot += run * (run - 1) / 2; run = 1; }
      }
      tot += run * (run - 1) / 2;
      ge[q] = tot;
    }
    printf("N=%d n=%ld", N, m);
    for (int q = 1; q < HI; q++) printf(" %d:%llu", q, ge[q] - ge[q + 1]);
    printf("\n");
  }
  return 0;
}
