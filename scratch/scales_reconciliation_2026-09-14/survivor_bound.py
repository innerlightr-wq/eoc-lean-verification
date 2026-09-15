"""Part XIII: strongest finite-X seed bound obtainable from card_seeds_le_sum,
    #{odd mu < X : R_j(mu) <= U for all j <= N} <= (X/2) p_N(U) + W_U(N)     (every N),
evaluated EXACTLY (integer DP for W_U(N) and p_N(U)) and optimized over N, for X = 2^k.
Reports B(X) = min_N [...] normalized by X^{H2(rho)} and by X^{H2(rho)} (log2 X)^{-3/2}.
usage: python3 survivor_bound.py U NMAX"""
import sys
from math import floor, log2
U = int(sys.argv[1]); NMAX = int(sys.argv[2])
A = log2(3)
H2 = lambda p: -p * log2(p) - (1 - p) * log2(1 - p)
h = H2(1 / A)


def lg(x):
    b = x.bit_length()
    return b - 60 + log2(x >> (b - 60)) if b > 60 else log2(x)


def smax_of(r):
    s = floor(U + r * A)
    while (1 << (s - U)) > 3 ** r:
        s -= 1
    return s


layer = {0: 1}
lW, lP = {}, {}
for r in range(1, NMAX + 1):
    sm = smax_of(r)
    keys = sorted(layer)
    new, acc, idx = {}, 0, 0
    for Sp in range(r, sm + 1):
        while idx < len(keys) and keys[idx] < Sp:
            acc += layer[keys[idx]]
            idx += 1
        if acc:
            new[Sp] = acc
    layer = new
    mS = max(layer)
    lW[r] = lg(sum(layer.values()))
    lP[r] = lg(sum(v << (mS - S) for S, v in layer.items())) - mS


def lsum(x, y):  # log2(2^x + 2^y)
    m = max(x, y)
    return m + log2(2 ** (x - m) + 2 ** (y - m))


print(f"U={U}: B(X) = min_N [(X/2)p_N + W_U(N)],  H2(1/alpha) = {h:.6f}")
print("  log2X   N*   log2B(X)   B/X^H2     B/(X^H2 (log2X)^-1.5)   B/(X^H2 (log2X)^-0.5)")
for k in list(range(100, int(A * NMAX * 0.95), 250)):
    best = min((lsum(k - 1 + lP[N], lW[N]), N) for N in range(1, NMAX + 1))
    lb, N = best
    r0 = lb - h * k
    print(f"  {k:6d}  {N:4d}  {lb:10.2f}  {2 ** r0:.3e}   {2 ** (r0 + 1.5 * log2(k)):8.4f}   "
          f"{2 ** (r0 + 0.5 * log2(k)):9.4f}")
