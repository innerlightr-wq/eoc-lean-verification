"""Geometric (killed P*) normalisation of the odd-dark transfer operator, window norms, and one-block certificates.

p' = (j-1)/(sigma-1), q' = 1 - p'.  Block operator on states x in [2r, top(2r)] (even prefix sums):
  Lt_r(x,y) = p'^2 q'^(y-x-2) * W_r(x,y),   W_r(x,y) = (v-x) + (s-1)(H(v-1) - H(x)),  v = min(y-1, cap_r),
for x+2 <= y <= top(2r+2) and x <= cap_r - 1 (else 0).  Untilted row sums are <= 1 (substochastic).
Exact identity on paths 0 -> sigma: every path has geometric factor p'^j q'^(sigma-j), hence
  sum_P s^{N_odd} = ker_count(0 -> sigma) = ker_geo(0 -> sigma) / (p'^j q'^(sigma-j)).
Recurrences (O(sigma) per block, no truncation):  for f on the next layer,
  A(x) = sum_{y=x+2}^{cap+1} q^{y-x-2} f(y),  B(x) = sum_{y=x+2}^{cap+1} q^{y-x-2} (y-1+(s-1)H(y-2)) f(y),
  C(x) = q^{cap-x} * sum_{y>=cap+2} q^{y-cap-2} f(y),
  (Lt f)(x) = p^2 [ B(x) - (x + (s-1)H(x)) A(x) + ((cap-x) + (s-1)(H(cap-1)-H(x))) C(x) ].
"""
import math, random, sys
from pexact import Instance, barrier, log2ratio


def make_ops(I, s=3.0):
    j, sg = I.j, I.sg
    p = (j - 1) / (sg - 1); q = 1 - p
    return p, q


def apply(I, r, f, s, p, q, lo_next):
    """f: list on layer r+1 indexed from lo_next = 2r+2 .. top(2r+2); returns list on layer r (2r .. top(2r))."""
    top = I.top; cap = top[2 * r + 1]; H = I.H[r]
    lo, hi = 2 * r, top[2 * r]
    hi_next = lo_next + len(f) - 1
    out = [0.0] * (hi - lo + 1)
    # C(cap) = sum_{y >= cap+2} q^{y-cap-2} f(y)
    Ccap = 0.0
    for y in range(hi_next, cap + 1, -1):
        if y >= lo_next:
            Ccap = f[y - lo_next] + q * Ccap
    A = 0.0; B = 0.0
    Hc1 = H[cap - 1] if cap >= 1 else 0
    # iterate x downward from min(hi, cap-1)
    xs = min(hi, cap - 1)
    # prime A,B at x = xs: need sums over y in [xs+2, cap+1]
    for y in range(cap + 1, xs + 1, -1):
        fy = f[y - lo_next] if lo_next <= y <= hi_next else 0.0
        A = fy + q * A
        B = fy * (y - 1 + (s - 1) * H[y - 2]) + q * B
    Cx = Ccap * q ** (cap - xs) if xs <= cap else 0.0
    for x in range(xs, lo - 1, -1):
        if x < xs:
            y = x + 2
            fy = f[y - lo_next] if lo_next <= y <= hi_next and y <= cap + 1 else 0.0
            A = fy + q * A
            B = fy * (y - 1 + (s - 1) * H[y - 2]) + q * B
            Cx *= q
        val = B - (x + (s - 1) * H[x]) * A + ((cap - x) + (s - 1) * (Hc1 - H[x])) * Cx
        out[x - lo] = p * p * val
    return out


def window_norms(I, K, s=3.0):
    """log2 sup_x (Lt_{r..r+K-1} 1)(x) for every start r (sup over all states of layer r)."""
    p, q = make_ops(I, s)
    res = []
    for r0 in range(0, I.R - K + 1):
        f = [1.0] * (I.top[2 * (r0 + K)] - 2 * (r0 + K) + 1)
        for r in range(r0 + K - 1, r0 - 1, -1):
            f = apply(I, r, f, s, p, q, 2 * r + 2)
        res.append(math.log2(max(f)))
    return res


def global_geo(I, s=3.0, pinned=True):
    """log2 of e_0^T Lt_0 ... Lt_{R-1} (e_sigma if pinned else 1), with per-layer renormalisation."""
    p, q = make_ops(I, s)
    R = I.R
    if pinned:
        f = [0.0] * (I.top[2 * R] - 2 * R + 1); f[I.sg - 2 * R] = 1.0
    else:
        f = [1.0] * (I.top[2 * R] - 2 * R + 1)
    lg = 0.0
    for r in range(R - 1, -1, -1):
        f = apply(I, r, f, s, p, q, 2 * r + 2)
        mx = max(f)
        if mx > 0:
            lg += math.log2(mx); f = [v / mx for v in f]
    return lg + math.log2(f[0])


def one_block_cert(I, s=3.0):
    """sum_r log2 max_x (Lt_r 1)(x): the h = 1 (state-only) certificate."""
    p, q = make_ops(I, s)
    tot = 0.0
    for r in range(I.R):
        f = [1.0] * (I.top[2 * r + 2] - 2 * r - 2 + 1)
        tot += math.log2(max(apply(I, r, f, s, p, q, 2 * r + 2)))
    return tot
