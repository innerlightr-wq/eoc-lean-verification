// Count exact vanishing of top-block Weyl sums V(g) (integers summed against 2^n-th roots of unity)
// V(g) = 0 exactly is decided on the integer cell counts: for g = 2^(n-1) it is N_even - N_odd;
// in general V(g) = 0 iff the pushed-forward counts on Z/2^(n-v2(g)) are constant on cosets of the
// subgroup of order 2 (cyclotomic criterion for 2-power roots of unity).
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
int main(int argc, char **argv) {
  for (int a = 1; a < argc; a++) {
    FILE *f = fopen(argv[a], "rb"); int hdr[5]; fread(hdr, 4, 5, f); int N = hdr[2], B = hdr[3], smax = hdr[4];
    uint64_t *H = malloc(8ULL << B); long long zeros = 0, tested = 0;
    for (int s = 0; s <= smax; s++) {
      uint64_t M; double Wd[128]; fread(&M, 8, 1, f); fread(H, 8, 1ULL << B, f); fread(Wd, 8, 128, f);
      if (smax - s > 3 || M < 100) continue;
      for (int n = 1; n <= 10 && n <= B; n++) {
        int L = 1 << n, per = 1 << (B - n); long long *cells = calloc(L, 8);
        for (int i = 0; i < L; i++) for (int k = 0; k < per; k++) cells[i] += H[i * per + k];
        // g with v2(g) = v: V(g) = sum_a cells[a] zeta^(g a), zeta primitive 2^n-th root; reduce a mod 2^(n-v):
        // character of Z/2^m (m = n - v) with odd multiplier; sum_b c_b zeta_m^(g' b) = 0 iff c_b = c_{b + 2^(m-1)} for all b
        for (int v = 0; v < n; v++) {
          int m = n - v, Lm = 1 << m; long long *c = calloc(Lm, 8);
          for (int i = 0; i < L; i++) c[i & (Lm - 1)] += cells[i];
          int z = 1; for (int b = 0; b < Lm / 2; b++) if (c[b] != c[b + Lm / 2]) { z = 0; break; }
          tested += (1 << (m - 1)); if (z) zeros += (1 << (m - 1));   // all odd g' at this level vanish together
          free(c);
        }
        free(cells);
      }
    }
    printf("N=%d: nonzero frequencies tested %lld, exactly vanishing %lld\n", N, tested, zeros);
    fclose(f); free(H);
  }
  return 0;
}
