// Prefix end states m_P = T^{J0}(r_P) over c-confined prefixes P of length J0, split by sigma = S_P.
// Writes hist[sigma][m_P mod 2^B] (odd residues) and verifies the concatenation formula
//   r(P.v) = r_P + 2^(S_P+1) * ( ((r_v - m_P)/2) * 3^(-J0) mod 2^(S_v) )
// on all confined extensions P.v of length N (for small N) against the direct lift recursion.
// usage: ./prefix_states c J0 B [Ncheck]
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
typedef unsigned __int128 u128;
static int c, J0, B, Nchk, Kb[128];
static uint64_t *hist[128];
static unsigned long long cnt[128], checked, bad;
static uint64_t inv3pow[128];
static u128 p3[128];
// least realizer and end state of an arbitrary word (digits dd[0..L-1]) from scratch
static void realize(const int *dd, int L, u128 *r, u128 *m, int *S) {
  u128 rr = 1, mm = 1; int SS = 0;
  for (int j = 0; j < L; j++) {
    int d = dd[j]; u128 A = 3 * mm + 1; uint64_t Ah = (uint64_t)(A >> 1);
    uint64_t t = (((1ULL << (d - 1)) - Ah) * inv3pow[j + 1]) & ((1ULL << d) - 1);
    u128 z = 3 * (mm + 2 * p3[j] * (u128)t) + 1;
    rr += (u128)t << (SS + 1); mm = z >> d; SS += d;
  }
  *r = rr; *m = mm; *S = SS;
}
static int word[128];
static void dfs(int j, int S, u128 r, u128 m) {
  if (j == J0) {
    hist[S][(uint64_t)m & ((1ULL << B) - 1)]++; cnt[S]++;
    if (Nchk > J0 && (checked < 20000000)) {
      // enumerate confined suffixes v of length Nchk - J0 and check the concatenation formula
      int L = Nchk - J0; int v[64]; for (int i = 0; i < L; i++) v[i] = 1;
      for (;;) {
        int ok = 1, SS = S; for (int i = 0; i < L; i++) { SS += v[i]; if (SS > Kb[J0 + i + 1]) { ok = 0; break; } }
        if (ok) {
          int full[128]; for (int i = 0; i < J0; i++) full[i] = word[i]; for (int i = 0; i < L; i++) full[J0 + i] = v[i];
          u128 rw, mw, rv, mv; int Sw, Sv; realize(full, J0 + L, &rw, &mw, &Sw); realize(v, L, &rv, &mv, &Sv);
          u128 modv = (u128)1 << Sv; u128 diff = (rv - m) & ((modv << 1) - 1);  // (r_v - m_P) mod 2^(Sv+1), even
          uint64_t inv = inv3pow[0]; u128 i3 = 1; for (int k = 0; k < J0; k++) i3 = i3 * (u128)0xAAAAAAAAAAAAAAABULL; // not used
          (void)inv; (void)i3;
          // 3^(-J0) mod 2^Sv via 64-bit inverse (Sv < 64 here)
          uint64_t c3 = inv3pow[J0];
          u128 k = ((diff >> 1) * (u128)c3) & (modv - 1);
          u128 pred = r + (k << (S + 1));
          checked++; if (pred != rw) bad++;
        }
        int i = L - 1; while (i >= 0) { v[i]++; int SS2 = S; for (int t = 0; t <= i; t++) SS2 += v[t]; if (SS2 <= Kb[J0 + i + 1]) break; v[i] = 1; i--; }
        if (i < 0) break;
      }
    }
    return;
  }
  int dmax = Kb[j + 1] - S; u128 A = 3 * m + 1; uint64_t Ah = (uint64_t)(A >> 1);
  for (int d = 1; d <= dmax && d < 60; d++) {
    uint64_t t = (((1ULL << (d - 1)) - Ah) * inv3pow[j + 1]) & ((1ULL << d) - 1);
    u128 z = 3 * (m + 2 * p3[j] * (u128)t) + 1;
    word[j] = d; dfs(j + 1, S + d, r + ((u128)t << (S + 1)), z >> d);
  }
}
int main(int argc, char **argv) {
  c = atoi(argv[1]); J0 = atoi(argv[2]); B = atoi(argv[3]); Nchk = argc > 4 ? atoi(argv[4]) : 0;
  const long double A = 1.584962500721156181453738943947816508759814407692481060455L;
  for (int j = 1; j < 128; j++) Kb[j] = (int)floorl(c + j * A);
  uint64_t inv3 = 0xAAAAAAAAAAAAAAABULL; inv3pow[0] = 1;
  for (int k = 1; k < 128; k++) inv3pow[k] = inv3pow[k - 1] * inv3;
  p3[0] = 1; for (int k = 1; k < 80; k++) p3[k] = 3 * p3[k - 1];
  for (int s = 0; s <= Kb[J0]; s++) hist[s] = calloc((size_t)1 << B, 8);
  dfs(0, 0, 1, 1);
  if (Nchk > J0) printf("concatenation formula: checked %llu pairs, mismatches %llu\n", checked, bad);
  char fn[128]; sprintf(fn, "pstate_c%d_j%d.bin", c, J0); FILE *f = fopen(fn, "wb");
  int hdr[3] = {c, J0, B}; int smax = Kb[J0]; fwrite(hdr, 4, 3, f); fwrite(&smax, 4, 1, f);
  for (int s = 0; s <= smax; s++) { fwrite(&cnt[s], 8, 1, f); fwrite(hist[s], 8, (size_t)1 << B, f); }
  fclose(f);
  for (int s = 0; s <= smax; s++) if (cnt[s]) printf("sigma=%d |P|=%llu\n", s, cnt[s]);
  return 0;
}
