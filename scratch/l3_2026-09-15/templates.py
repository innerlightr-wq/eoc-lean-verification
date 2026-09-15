"""Exact L=3 block templates.  Block at step i, entry state S, total u = d1+d2+d3, internal sums
S1 = S+d1, S2 = S1+d2.  Block phase = common - h * 3^{-(i+3)} (3*2^{S1} + 2^{S2}) / 2^m, so with
a = S1-S-1, b = S2-S-1 (0 <= a < b <= u-2) the block is the shape set Q_u = {3*2^a + 2^b} scaled by the
single angle beta = h 3^{-(i+3)} 2^{S+1}/2^m mod 1.  Weight W(beta) = |sum_{q in Q} e(q beta)| / |Q|."""
import math, cmath, itertools
al = math.log2(3); p = 1 / al
def Q(u, amax=None, bmax=None):  # admissible: a <= amax (S1 <= b(i+1)), b <= bmax (S2 <= b(i+2))
    return [3 * 2**a + 2**b for a in range(u - 1) for b in range(a + 1, u - 1)
            if (amax is None or a <= amax) and (bmax is None or b <= bmax)]
def v2(x): x = abs(x); return (x & -x).bit_length() - 1
def f(qs, x): return abs(sum(cmath.exp(2j * math.pi * q * x) for q in qs)) ** 2 / len(qs) ** 2
print(" u |Q| distinct  differences: min v2 / max v2   full-group mean f = 1/|Q|   max f on ||x||>=1/27   max f on ||x||>=1/8   peak half-width")
for u in range(3, 11):
    qs = Q(u); n = len(qs)
    dist = len(set(qs)) == n
    diffs = [a - b for a in qs for b in qs if a != b]
    vs = [v2(d) for d in diffs] if diffs else [0]
    grid = [k / 20000 for k in range(1, 10000)]
    m27 = max((f(qs, x) for x in grid if x >= 1 / 27), default=1)
    m8 = max((f(qs, x) for x in grid if x >= 1 / 8), default=1)
    hw = next((x for x in grid if f(qs, x) < 0.5), None) if n > 1 else None
    print(f" {u:2d} {n:3d}  {str(dist):5s}   {min(vs):2d} / {max(vs):2d}                      {1/n:.4f}                    {m27:.4f}              {m8:.4f}            {hw}")
# exact bit-structure argument for distinctness: 3*2^a + 2^b = 2^a + 2^{a+1} + 2^b (b>a+1: 3 bits) or 5*2^a (b=a+1)
# ideal ceilings from critical-tilt entropies: L-block ceiling = (L*h - H(NB(L,p)))/(2L) per step
def H_geom(p): return (-p * math.log2(p) - (1 - p) * math.log2(1 - p)) / p
def H_NB(L, p, umax=400):
    H = 0
    for u in range(L, umax):
        pr = math.comb(u - 1, L - 1) * p**L * (1 - p) ** (u - L)
        if pr > 0: H -= pr * math.log2(pr)
    return H
h = H_geom(p)
print(f"\nper-step entropy h = {h:.5f} (alpha - I0 = 1.50564)")
for L in (1, 2, 3, 4, 6, 8):
    print(f"  L={L}: ideal L2 ceiling (L h - H(NB(L,1/alpha)))/(2L) = {(L*h - H_NB(L, p))/(2*L):.4f} bits/step")
