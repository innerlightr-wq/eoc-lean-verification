// Shell-conditioned survivor counts: for survivors (exit > N, mu < 2^HI) in a dump file, the
// histogram of the shell gap x = s_N - S_N(mu).   usage: ./shell_q dump.bin HI N sN
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
typedef unsigned __int128 u128;
int main(int argc, char **argv) {
  FILE *f = fopen(argv[1], "rb"); int HI = atoi(argv[2]), N = atoi(argv[3]), sN = atoi(argv[4]);
  unsigned long long h[64] = {0}, tot = 0;
  uint64_t mu; uint32_t e;
  while (fread(&mu, 8, 1, f) == 1 && fread(&e, 4, 1, f) == 1) {
    if (e <= (uint32_t)N || mu >= (1ULL << HI)) continue;
    u128 m = mu; long S = 0;
    for (int j = 0; j < N; j++) { u128 x = 3 * m + 1; int d = __builtin_ctzll((uint64_t)x) ; if (!(uint64_t)x) d = 64 + __builtin_ctzll((uint64_t)(x >> 64)); m = x >> d; S += d; }
    int x = sN - (int)S; if (x < 0 || x > 63) { fprintf(stderr, "bad x %d\n", x); continue; }
    h[x]++; tot++;
  }
  printf("N=%d HI=%d total %llu :", N, HI, tot);
  for (int x = 0; x < 20; x++) printf(" %d:%llu", x, h[x]);
  printf("\n");
  return 0;
}
