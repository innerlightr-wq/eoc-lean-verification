// Bad-cell geometry of the (1,2)<->(2,1) swap angle theta(i,S) = h 2^{S+1} 3^{-(i+2)} / 2^m mod 1 over the reachable
// (i,S) region of c-confined prefixes ending at (J, sigma).  For threshold eta reports:
//   cell bad fraction (uniform over reachable cells and path-weighted), max horizontal run (fixed i),
//   max vertical run (fixed S), and the longest admissible pair-path (pairs i -> i+2, S -> S+u, u>=2 with
//   S+u <= b(i+2)) visiting only bad pair-starts; plus the same statistics for a random-angle control.
// usage: ./bad_geom c J sigma t h eta seed
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned __int128 u128;
#define NL 5
typedef struct { uint64_t w[NL]; } U;
static U mulU(U a, U b) { U r; memset(&r, 0, sizeof r); for (int i = 0; i < NL; i++) { u128 c = 0; for (int j = 0; i + j < NL; j++) { u128 x = (u128)a.w[i] * b.w[j] + r.w[i + j] + c; r.w[i + j] = (uint64_t)x; c = x >> 64; } } return r; }
static U muls(U a, uint64_t h) { U r; u128 c = 0; for (int i = 0; i < NL; i++) { u128 x = (u128)a.w[i] * h + c; r.w[i] = (uint64_t)x; c = x >> 64; } return r; }
static uint64_t b64(U a, int lo) { if (lo >= 0) { int q = lo >> 6, s = lo & 63; uint64_t x0 = q < NL ? a.w[q] : 0, x1 = q + 1 < NL ? a.w[q + 1] : 0; return s ? (x0 >> s) | (x1 << (64 - s)) : x0; } int sh = -lo; return sh >= 64 ? 0 : a.w[0] << sh; }
static double frac(U A, int nb) { return (double)b64(A, nb - 64) / 18446744073709551616.0; }
static int Kb[512];
static uint64_t s0 = 88172645463325252ULL;
static double rnd(void) { s0 ^= s0 << 13; s0 ^= s0 >> 7; s0 ^= s0 << 17; return (s0 >> 11) * (1.0 / 9007199254740992.0); }
int main(int argc, char **argv) {
  int c = atoi(argv[1]), J = atoi(argv[2]), sg = atoi(argv[3]), t = atoi(argv[4]); long h = atol(argv[5]); double eta = atof(argv[6]); s0 ^= atoll(argv[7]);
  int m = sg + t + 1; const long double A = 1.584962500721156181453738943947816508759814407692481060455L;
  for (int j = 0; j < 512; j++) Kb[j] = (int)floorl(c + j * A);
  U inv3; for (int k = 0; k < NL; k++) inv3.w[k] = 0xAAAAAAAAAAAAAAAAULL; inv3.w[0] = 0xAAAAAAAAAAAAAAABULL;
  static U a[512]; a[0] = inv3; for (int i = 1; i < J + 3; i++) a[i] = mulU(a[i - 1], inv3);
  int D = Kb[J] + 3;
  static double cnt[512][260], pre[512][260]; memset(cnt, 0, sizeof cnt); memset(pre, 0, sizeof pre);
  cnt[J][sg] = 1; for (int i = J - 1; i >= 0; i--) for (int S = 0; S <= Kb[i]; S++) { double v = 0; for (int d = 1; S + d <= Kb[i + 1]; d++) v += cnt[i + 1][S + d]; cnt[i][S] = v; }
  pre[0][0] = 1; for (int i = 0; i < J; i++) for (int S = 0; S <= Kb[i]; S++) if (pre[i][S] > 0) for (int d = 1; S + d <= Kb[i + 1]; d++) pre[i + 1][S + d] += pre[i][S];
  double P = cnt[0][0];
  static unsigned char bad[2][512][260];
  for (int ctl = 0; ctl < 2; ctl++) {
    memset(bad[ctl], 0, sizeof bad[ctl]);
    long ncell = 0, nbad = 0; double pw = 0, pwbad = 0;
    for (int i = 0; i + 1 < J; i++) { U ha = muls(a[i + 1], (uint64_t)h);
      for (int S = 0; S <= Kb[i]; S++) { if (!(pre[i][S] > 0 && cnt[i][S] > 0)) continue;
        double th = ctl ? rnd() : frac(ha, m - (S + 1)); double nrm = fmin(th, 1 - th);
        int b = nrm < eta; bad[ctl][i][S] = b; ncell++; nbad += b;
        if (i % 2 == 0) { double w = pre[i][S] * cnt[i][S] / P; pw += w; pwbad += w * b; } } }
    int hmaxr = 0, vmaxr = 0;
    for (int i = 0; i + 1 < J; i++) { int r = 0; for (int S = 0; S <= Kb[i]; S++) { if (bad[ctl][i][S]) { r++; if (r > hmaxr) hmaxr = r; } else r = 0; } }
    for (int S = 0; S < D; S++) { int r = 0; for (int i = 0; i + 1 < J; i++) { if (pre[i][S] > 0 && cnt[i][S] > 0 && bad[ctl][i][S]) { r++; if (r > vmaxr) vmaxr = r; } else r = 0; } }
    // longest admissible pair-path through consecutive bad pair-starts (pairs at even i)
    static int L[512][260]; int best = 0; memset(L, 0, sizeof L);
    for (int i = 0; i + 1 < J; i += 2) for (int S = 0; S <= Kb[i]; S++) {
      if (!(pre[i][S] > 0 && cnt[i][S] > 0)) continue;
      if (!bad[ctl][i][S]) { L[i][S] = 0; continue; }
      int prevbest = 0; if (i >= 2) for (int u = 2; S - u >= 0; u++) { int Sp = S - u; if (S > Kb[i]) break; if (pre[i - 2][Sp] > 0 && cnt[i - 2][Sp] > 0 && L[i - 2][Sp] > prevbest) prevbest = L[i - 2][Sp]; }
      L[i][S] = prevbest + 1; if (L[i][S] > best) best = L[i][S]; }
    printf("%s h=%ld eta=%.3f: bad cells %.4f (path-weighted %.4f; random 2eta=%.3f)  max horiz run %d  max vert run %d  longest all-bad pair-path %d of %d pairs\n",
           ctl ? "control " : "actual  ", h, eta, (double)nbad / ncell, pwbad / pw, 2 * eta, hmaxr, vmaxr, best, J / 2);
  }
  return 0;
}
