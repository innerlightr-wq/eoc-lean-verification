"""Super-eigenvector certificate for the tilted tight-block operator (the remaining ShapeTail piece).

EOC.LocalWindow.ker_le_of_superEigen: if h > 0 and sum_y w(x,y) h(y) <= M h(x) for every state x and
every layer, then the pinned kernel obeys ker <= M^R h(x0)/h(z).  Applied to the tilted block operator
  state  v = top[2r] - S_{2r}   (headroom),
  step   u >= 2,  v' = v + inc - u >= 0,   inc = top[2r+2]-top[2r],
  weight |B| = min(u-1, inc1 + v),  inc1 = top[2r+1]-top[2r],  tilted by  U  when |B| <= 1,
this gives  Z(U) <= M^R * h(v0)/h(vend).

Needed (from exact.py, J=200, T=0.55R, U=3):  log2 M <= 3.742 bits/block, true growth 3.6253.
This script computes the best M over geometric weights h(v) = lam^v (and over a numerically optimized
h), for the worst phase type (inc1, inc), and reports the margin.
usage: python3 cert.py"""
import math

AL = math.log2(3)
U = 3
VMAX = 60          # headroom truncation for the numerical eigenvector
TYPES = [(1, 3), (2, 3), (1, 4), (2, 4)]   # (inc1, inc) patterns of floor(i*alpha)

def observed_types(J=400):
    """which (inc1, inc) pairs actually occur in top[i] = floor(i*alpha)."""
    sg = math.floor(J * AL)
    top = [min(math.floor(i * AL), sg) for i in range(J + 1)]
    seen = {}
    for r in range(J // 2 - 1):
        inc1 = top[2 * r + 1] - top[2 * r]
        inc = top[2 * r + 2] - top[2 * r]
        seen[(inc1, inc)] = seen.get((inc1, inc), 0) + 1
    return seen

print("phase types (inc1, inc) occurring in the true barrier, with counts:")
for k, v in sorted(observed_types().items()):
    print(f"   {k}: {v}")

def row(v, inc1, inc, lam):
    """sum over u of weight * lam^{v'} for state v under one phase type."""
    tot = 0.0
    for u in range(2, v + inc + 1):
        vp = v + inc - u
        if vp < 0: continue
        w = min(u - 1, inc1 + v)
        if w < 1: continue
        ww = w * (U if w <= 1 else 1)
        tot += ww * lam ** vp
    return tot

print("\ngeometric certificate h(v) = lam^v:  M(lam) = max over types and v<=VMAX of row/lam^v")
print("    lam     M         log2 M     margin vs 3.742")
best = None
for lam in [0.05 * i for i in range(1, 19)]:
    M = 0.0
    for (inc1, inc) in TYPES:
        for v in range(0, VMAX + 1):
            M = max(M, row(v, inc1, inc, lam) / lam ** v)
    l2 = math.log2(M) if M > 0 else float('inf')
    if best is None or l2 < best[1]: best = (lam, l2, M)
    print(f"  {lam:5.2f}   {M:10.4f}   {l2:7.4f}     {3.742 - l2:+7.4f}")
print(f"\nbest geometric: lam = {best[0]:.2f}, log2 M = {best[1]:.4f}, margin {3.742-best[1]:+.4f}")

# power iteration for the optimal h on the truncated state space, worst-type-uniform
print("\npower iteration (uniform over all four types, truncation VMAX =", VMAX, ")")
h = [1.0] * (VMAX + 1)
for it in range(4000):
    new = [0.0] * (VMAX + 1)
    for v in range(VMAX + 1):
        best_row = 0.0
        for (inc1, inc) in TYPES:
            tot = 0.0
            for u in range(2, v + inc + 1):
                vp = v + inc - u
                if vp < 0 or vp > VMAX: continue
                w = min(u - 1, inc1 + v)
                if w < 1: continue
                tot += w * (U if w <= 1 else 1) * h[vp]
            best_row = max(best_row, tot)
        new[v] = best_row
    mx = max(new)
    h = [x / mx for x in new]
    if it > 3990:
        print(f"  iterate {it}: log2(max row growth) = {math.log2(mx):.5f}")
M = mx
print(f"uniform-over-types M: log2 M = {math.log2(M):.5f}, margin vs 3.742 = {3.742 - math.log2(M):+.5f}")
print(f"h profile (first 12): {[round(x,5) for x in h[:12]]}")
