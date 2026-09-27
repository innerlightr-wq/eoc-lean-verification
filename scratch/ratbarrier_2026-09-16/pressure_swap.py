"""Part XVII/XII: how much of the pressure is barrier-driven?

Swap the TRUE barrier top[i] = floor(i*alpha) for a rational one floor(i*p/q), holding the 3-adic
environment (the black cells) and the chain weights fixed, and compare the exact additive block
weights w_r and the long-run growth rate.  The point: alpha enters the pressure model in three
places -- sg = floor(J*alpha), top[] (barrier), and P = 1/alpha (chain weights) -- but NOT in the
blackness test, whose modulus is 3^(2r+2) and grows with the block index.  This measures whether
rationalising alpha perturbs the observable at all, and where.
usage: python3 pressure_swap.py"""
import sys, math, os
sys.path.insert(0, "/home/elias/GitHub/eoc-lean-verification/scratch/transient_2026-09-16")
import tcommon as T

J = 400
CONV = [(8, 5), (19, 12), (65, 41), (485, 306)]
LAMS = [1, 5, 7, 11]


def geom_with(J, bar):
    G = T.Geom(J)
    G.top = [min(bar(i), G.sg) for i in range(J + 1)]
    return G


def weights(G, lam, s=3.0):
    """exact additive block weights w_r = (a_r - a_{r+1})/2 (same pattern as t4_corpus.py)."""
    Rend = G.R - 1
    env = T.FastEnv(G, lam, s)
    V = env.ones(Rend)
    a = [0.0] * (Rend + 1)
    for r in range(Rend - 1, -1, -1):
        V = env.apply_T(r, V)
        mx = max(V)
        a[r] = math.log2(mx) if mx > 0 else -1e9
    return [(a[r] - a[r + 1]) / 2.0 for r in range(Rend)], Rend


print(f"J = {J}: barrier swap, same 3-adic environment, exact block weights")
print("  lam   p/q       #blocks  max|dw|    mean|dw|   sum|dw|   #blocks changed   rate_alpha  rate_beta")
Ga = geom_with(J, lambda i: math.floor(i * T.AL))
for lam in LAMS:
    wa, Ra = weights(Ga, lam)
    for (p, q) in CONV:
        Gb = geom_with(J, lambda i, p=p, q=q: (p * i) // q)
        try:
            wb, Rb = weights(Gb, lam)
        except Exception as e:
            print(f"  {lam:4d}  {p}/{q:<6}  failed: {e}")
            continue
        n = min(Ra, Rb, len(wa), len(wb))
        d = [wa[r] - wb[r] for r in range(2, n - 20)]
        nz = sum(1 for x in d if abs(x) > 1e-12)
        ra = sum(wa[2:n - 20]) / max(1, len(d))
        rb = sum(wb[2:n - 20]) / max(1, len(d))
        print(f"  {lam:4d}  {p}/{q:<6}  {len(d):6d}   {max(abs(x) for x in d):.5f}   "
              f"{sum(abs(x) for x in d)/len(d):.6f}  {sum(abs(x) for x in d):8.4f}   {nz:6d}"
              f"            {ra:.5f}     {rb:.5f}")
