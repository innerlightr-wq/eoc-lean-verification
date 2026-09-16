"""Tight-block statistics of the exact confined ensemble, and the feasible (N0, T, K) region.

EOC/ShapeTail.lean reduces `ShapeTail` to `TightTail`:
  every block is shape-good, tight (|B_r| <= 1) or big (|B_r| > N0);
  the block budget sum_r (|B_r|+1) <= sigma bounds #big <= sigma/(N0+2) DETERMINISTICALLY;
  so  #shapegood < K  =>  #tight >= T  whenever  K + T + sigma/(N0+2) <= R.
Hence we need P_conf(#tight >= T) exponentially small, with T <= R - K - sigma/(N0+2).

This script computes, in the exact confined ensemble (uniform on C_J: compositions d_1..d_J >= 1 with
S_J = sg = floor(J*alpha) and S_i <= top[i] = min(floor(i*alpha), sg)):
  * the exact mean of #tight / R,
  * the exact tilted partition function Z(t) = sum_w t^{#tight(w)} and the Legendre/Chernoff rate for
    P(#tight >= T),
  * the resulting feasible region in (N0, T/R) and the implied margin.
Block r: state S = S_{2r} -> S' = S_{2r+2}; internal choices |B_r| = min(S'-1, top[2r+1]) - S.
usage: python3 tight.py J [N0]"""
import math, sys
from fractions import Fraction

AL = math.log2(3)
J = int(sys.argv[1]) if len(sys.argv) > 1 else 200
N0S = [4, 6, 10, 14, 20, 30, 40]
R = J // 2
sg = math.floor(J * AL)
top = [min(math.floor(i * AL), sg) for i in range(J + 1)]

def blocks(S, r):
    """yield (S2, w) with w = |B_r| >= 1 for transitions out of state S at block r."""
    cap = top[2 * r + 1]
    for S2 in range(S + 2, min(top[2 * r + 2], cap + 1 + (cap + 1 - S)) + 2):
        if S2 > top[2 * r + 2]: break
        w = min(S2 - 1, cap) - S
        if w >= 1:
            yield S2, w

def partition(t):
    """Z(t) = sum over confined words of t^{#tight}, as float logs (scaled to avoid overflow)."""
    # f[S] = weighted count of prefixes reaching S_{2r} = S
    f = {0: 1.0}
    logscale = 0.0
    for r in range(R):
        g = {}
        for S, v in f.items():
            if v == 0.0: continue
            for S2, w in blocks(S, r):
                ww = w * (t if w <= 1 else 1.0)
                g[S2] = g.get(S2, 0.0) + v * ww
        f = g
        mx = max(f.values()) if f else 0.0
        if mx > 0:
            sc = 1.0 / mx
            f = {k: v * sc for k, v in f.items()}
            logscale += math.log2(mx)
        if not f: return float('-inf')
    tot = f.get(sg, 0.0)
    return logscale + math.log2(tot) if tot > 0 else float('-inf')

def mean_tight():
    """exact mean of #tight under the uniform confined law, by differentiating at t=1 numerically."""
    h = 1e-4
    l1 = partition(1.0 + h); l0 = partition(1.0 - h)
    # d/dt log2 Z at t=1 times 1 = E[#tight]/ln2 ... use central difference of log Z (nats)
    return (l1 - l0) / (2 * h) * math.log(2)

logZ1 = partition(1.0)
mt = mean_tight()
print(f"J = {J}, R = {R}, sigma = sg = {sg}, log2|C_J| = {logZ1:.3f}")
print(f"exact mean #tight = {mt:.3f}  ({mt/R:.4f} per block)")

print("\nChernoff rate for P(#tight >= T):  min over t>=1 of  t^{-T} Z(t)/Z(1)")
print("   T/R    best t    log2 P bound    rate (bits per digit J)")
for frac in (0.42, 0.45, 0.48, 0.50, 0.55, 0.60):
    T = frac * R
    best = None
    for t in [1.05, 1.1, 1.2, 1.4, 1.7, 2.0, 2.5, 3.0, 4.0, 6.0]:
        lb = partition(t) - logZ1 - T * math.log2(t)
        if best is None or lb < best[0]: best = (lb, t)
    print(f"  {frac:5.2f}  {best[1]:6.2f}   {best[0]:12.3f}    {-best[0]/J:8.5f}")

print("\nfeasible region: need  K + T + sigma/(N0+2) <= R,  i.e.  T/R <= 1 - K/R - sigma/((N0+2)R)")
print("   N0    sigma/((N0+2)R)    max T/R at K/R = 0.10   margin over mean tight")
for N0 in N0S:
    loss = sg / ((N0 + 2) * R)
    maxT = 1 - 0.10 - loss
    print(f"  {N0:3d}      {loss:.4f}            {maxT:7.4f}              {maxT - mt/R:+.4f}")
