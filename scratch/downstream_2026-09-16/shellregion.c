/* Which prefix shells sigma carry the Haar weight of weighted_phi_decay_implies_exceptional_bound?
   K, A: j0 = max{j : b(j) < K} (hbK), N = ceil(A K), b(i) = floor(i log2 3) (U = 0).
   Haar share H(s,sigma) = |P_sigma| |V_{sigma,s}| 2^(K-1-s) (ShellwiseChain.haarShare_eq); trivial constant
   ctriv(s) = 2^(s+1-K).  x = b(j0) - sigma.  Reports weighted median / 99% quantile of x, and
   x* = least x with sum_{x' > x} H*ctriv <= total mass (trivial branch below x* adds <= 1 to C).
   Exact lattice-path counts; per-row scaling with log2 offsets (long double).
   usage: shellregion K A XMAX */
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef long double LD;
static const LD AL = 1.584962500721156181453738943947816508759814407692481060455L;
static int bb(int i) { return (int)floorl(i * AL); }
static LD lse2(LD a, LD b) { if (a == -INFINITY) return b; if (b == -INFINITY) return a; LD m = a > b ? a : b; return m + log2l(powl(2, a - m) + powl(2, b - m)); }
int main(int argc, char **argv) {
  int K = atoi(argv[1]); LD A = strtold(argv[2], 0); int XMAX = atoi(argv[3]);
  int j0 = 0; while (bb(j0 + 1) < K) j0++;
  int N = (int)ceill(A * K), L = N - j0, top = bb(j0), sN = bb(N), W = sN + 1;
  /* prefix */
  LD *row = calloc(W, sizeof(LD)), *nw = calloc(W, sizeof(LD)); row[0] = 1; LD lg = 0;
  for (int i = 1; i <= j0; i++) { int cap = bb(i); LD acc = 0; memset(nw, 0, sizeof(LD) * W);
    for (int S = 1; S <= cap; S++) { acc += row[S - 1]; nw[S] = acc; }
    LD m = 0; for (int S = 0; S <= cap; S++) if (nw[S] > m) m = nw[S];
    for (int S = 0; S <= cap; S++) nw[S] /= m; lg += log2l(m); LD *t = row; row = nw; nw = t; }
  int nx = top - j0 + 1; if (nx > XMAX + 1) nx = XMAX + 1;
  LD *mass = malloc(sizeof(LD) * nx), *tc = malloc(sizeof(LD) * nx);
  LD *v = calloc(W, sizeof(LD)), *v2 = calloc(W, sizeof(LD));
  for (int x = 0; x < nx; x++) { int sg = top - x; LD logP = row[sg] > 0 ? log2l(row[sg]) + lg : -INFINITY;
    memset(v, 0, sizeof(LD) * W); v[sg] = 1; LD lv = 0;
    for (int i = j0 + 1; i <= N; i++) { int cap = bb(i); LD acc = 0; memset(v2, 0, sizeof(LD) * W);
      for (int S = 1; S <= cap; S++) { acc += v[S - 1]; v2[S] = acc; }
      LD m = 0; for (int S = 0; S <= cap; S++) if (v2[S] > m) m = v2[S];
      if (m <= 0) break; for (int S = 0; S <= cap; S++) v2[S] /= m; lv += log2l(m); LD *t = v; v = v2; v2 = t; }
    LD ms = -INFINITY, tt = -INFINITY;
    for (int s = K; s <= sN; s++) if (v[s] > 0 && logP > -INFINITY) { LD lh = logP + log2l(v[s]) + lv + (K - 1 - s);
      ms = lse2(ms, lh); tt = lse2(tt, lh + (s + 1 - K)); }
    mass[x] = ms; tc[x] = tt; }
  LD tot = -INFINITY, alltc = -INFINITY; for (int x = 0; x < nx; x++) { tot = lse2(tot, mass[x]); alltc = lse2(alltc, tc[x]); }
  LD cum = 0; int xh = -1, x99 = -1; for (int x = 0; x < nx; x++) { cum += powl(2, mass[x] - tot); if (xh < 0 && cum >= 0.5) xh = x; if (x99 < 0 && cum >= 0.99) x99 = x; }
  LD tail = -INFINITY; int xstar = nx - 1; for (int x = nx - 1; x >= 0; x--) { if (tail > tot) break; xstar = x; tail = lse2(tail, tc[x]); }
  /* xstar: least x with tail(x' > x) <= tot */
  { LD tl = -INFINITY; xstar = nx - 1; for (int x = nx - 1; x >= 0; x--) { if (tl <= tot) xstar = x; else break; tl = lse2(tl, tc[x]); } }
  printf("K=%d A=%.3Lf j0=%d N=%d L=%d j0/300=%.1f  x_median=%d x99=%d x*=%d (x*/L=%.2f)  log2(trivial cost everywhere / mass)=%.1Lf  scanned x<=%d%s\n",
         K, A, j0, N, L, j0 / 300.0, xh, x99, xstar, (double)xstar / L, alltc - tot, nx - 1, nx - 1 < top - j0 ? " (truncated)" : "");
  return 0; }
