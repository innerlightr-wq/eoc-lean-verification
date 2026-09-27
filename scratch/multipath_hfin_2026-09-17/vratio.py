"""Part VII: exact |V_{sigma,s}| (positive words, length L, total t, S_i <= b_U(j0+i) - sigma) versus C(t-1,L-1).
Exact integer DP with the exact floor barrier (alpha = log2 3 via integer test 2^p <= 3^i*2^U  <=>  p <= i*alpha + U)."""
from math import comb, log2
def barrier(U, i):
    # floor(i*log2(3) + U) exactly: largest p with 2^p <= 3^i * 2^U
    v = 3 ** i << U
    return v.bit_length() - 1
def countV(U, j0, sigma, L, t):
    K = [barrier(U, j0 + i) - sigma for i in range(L + 1)]
    dist = {0: 1}
    for i in range(1, L + 1):
        nd = {}
        for S, c in dist.items():
            for a in range(1, K[i] - S + 1):
                if S + a <= K[i]:
                    nd[S + a] = nd.get(S + a, 0) + c
        dist = nd
    return dist.get(t, 0)
print(" j0   L   x   t      |V|        C(t-1,L-1)   R=|V|/C    L*R   (t position)")
for j0 in (300,):
    for L in (10, 20, 40, 80):
        for x in (0, 3, 10):
            sigma = barrier(0, j0) - x
            tmax = barrier(0, j0 + L) - sigma
            for t in sorted({L, (L + tmax) // 2, tmax - 3, tmax}):
                if t < L: continue
                v = countV(0, j0, sigma, L, t); c = comb(t - 1, L - 1)
                print(f"{j0:4d} {L:3d} {x:3d} {t:4d} {v:12d} {c:14d}  {v/c:.4f}  {L*v/c:6.2f}  {'top' if t==tmax else ''}")
