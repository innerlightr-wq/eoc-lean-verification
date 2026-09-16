"""Explicit super-eigenvector certificate, done correctly: h(v) = lam^v with lam > 1.

The headroom v = top[2r] - S_{2r} must be weighted INCREASINGLY (more headroom = more mass), so the
certificate is h(v) = lam^v with lam > 1.  The row of the tilted block operator at state v, phase r:
    row_r(v) = sum_{u >= 2, v' = v + inc_r - u >= 0}  w * (U if w <= 1 else 1) * lam^{v'},
    w = min(u - 1, inc1_r + v),  inc1_r = top[2r+1]-top[2r], inc_r = top[2r+2]-top[2r].
A certificate is M = max over phases r and all v of row_r(v)/lam^v; then
    Z(U) = ker <= M^R * h(v_start)/h(v_end).
Budget (exact.py): the Lean hypothesis needs  R*log2 M + log2(h0/hend) + log2 J <= log2 C + T log2 U.
usage: python3 cert2.py"""
import math
from math import comb

AL = math.log2(3)
U = 3
VMAX = 400

def budget(J, TR, u=U):
    R = J // 2
    sg = math.floor(J * AL)
    T = int(TR * R)
    lC = math.log2(comb(sg - 1, J - 1))
    return (lC + T * math.log2(u) - math.log2(J)) / R, T, lC, R, sg

def rows(J, lam, u=U):
    """max over phases and v of row/lam^v for the true barrier of length J."""
    sg = math.floor(J * AL)
    top = [min(math.floor(i * AL), sg) for i in range(J + 1)]
    worst = 0.0; arg = None
    for r in range(J // 2 - 1):
        inc1 = top[2 * r + 1] - top[2 * r]
        inc = top[2 * r + 2] - top[2 * r]
        for v in range(0, VMAX + 1):
            tot = 0.0
            for uu in range(2, v + inc + 1):
                vp = v + inc - uu
                if vp < 0: continue
                w = min(uu - 1, inc1 + v)
                if w < 1: continue
                tot += w * (u if w <= 1 else 1) * lam ** (vp - v)
            if tot > worst: worst = tot; arg = (r, v, inc1, inc)
    return worst, arg

for J, TR in ((200, 0.55), (200, 0.60), (200, 0.62)):
    need, T, lC, R, sg = budget(J, TR)
    print(f"\nJ={J}, T/R={TR}: needed log2 M <= {need:.4f} bits/block  (T={T}, log2 C={lC:.2f})")
    best = None
    for lam in (1.6, 1.8, 2.0, 2.1, 2.2, 2.4, 2.8, 3.2):
        M, arg = rows(J, lam)
        l2 = math.log2(M)
        if best is None or l2 < best[1]: best = (lam, l2, arg)
        print(f"   lam = {lam:4.2f}:  log2 M = {l2:7.4f}   margin {need - l2:+7.4f}   worst at "
              f"(r,v,inc1,inc) = {arg}")
    print(f"   best: lam = {best[0]}, log2 M = {best[1]:.4f}, margin {need - best[1]:+.4f}")
