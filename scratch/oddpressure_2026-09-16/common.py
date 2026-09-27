"""Shared exact setup for the odd-pressure investigation (pure Python, no numpy).

Conventions taken verbatim from scratch/cw2_2026-09-16/cw2env.py and
scratch/oddblack_2026-09-16/{adversary.py,depth_true.py}:

  AL = log2(3), J digits, R = J//2 pair blocks, sg = floor(J*AL), t = J//6, m = sg+t+1
  top[i] = min(floor(i*AL), sg)
  block r owns level b = 2r+2 ; column x -> cell (a,b) = (m-x, 2r+2)
  environment: y = centered(XI * 2^{-(m-x)} mod 3^b),  BLACK  iff  54*|y| < 3^b
  triangle depth of a black cell = ln(eta/|U|) = ln(3^b / (54*|y|)),  eta = 1/54, U = y/3^b
  (T_r f)(S) = sum_{S2} [sum_{x=S+1..min(S2-1,cap)} s^black(x)] * p^2 q^{S2-S-2} * f(S2), cap = top[2r+1]

Floating point is used only for the transfer-operator weights p,q and the log2 of ratios
(exactly as the original scripts do).  All 3-adic arithmetic is exact Python integers.
"""
import math

AL = math.log2(3)
P = 1 / AL
Q_ = 1 - P
UMAX = 30
DMAX = 60
ETA_DEN = 54  # black iff 54|y| < 3^b


class Geom:
    def __init__(self, J):
        self.J = J
        self.R = J // 2
        self.sg = math.floor(J * AL)
        self.t = J // 6
        self.m = self.sg + self.t + 1
        self.top = [min(math.floor(i * AL), self.sg) for i in range(J + 1)]


def centered(v, qb):
    return v if v <= qb // 2 else v - qb


def row_values(G, r, x_lo, x_hi, XI):
    """exact centered residues y(x) for level b = 2r+2, columns x in [x_lo,x_hi]."""
    b = 2 * r + 2
    qb = 3 ** b
    rr = XI * pow(2, -(G.m - x_lo), qb) % qb
    out = {}
    for x in range(x_lo, x_hi + 1):
        out[x] = centered(rr, qb)
        rr = rr * 2 % qb
    return out


def row_black(G, r, x_lo, x_hi, XI):
    b = 2 * r + 2
    qb = 3 ** b
    return {x: (ETA_DEN * abs(y) < qb) for x, y in row_values(G, r, x_lo, x_hi, XI).items()}


def cell_xrange(G, r):
    """columns x of block r that the transfer operator can read (superset over all states)."""
    lo = 2 * r + 1
    hi = min(G.top[2 * r + 1], G.top[2 * r + 2] - 1)
    return lo, hi


class Env:
    """precomputed black rows + transfer operator for one environment XI."""

    def __init__(self, G, XI, s=3.0, rmax=None):
        self.G = G
        self.XI = XI
        self.s = s
        R = G.R if rmax is None else rmax
        self.R = R
        self.blk = [row_black(G, r, 2 * r, G.top[2 * r] + DMAX, XI) for r in range(R)]
        self.wu = [0.0, 0.0] + [P * P * Q_ ** (u - 2) for u in range(2, UMAX + 1)]
        self.cumw = []
        for r in range(R):
            cap = G.top[2 * r + 1]
            row = self.blk[r]
            W = {}
            for S in range(2 * r, G.top[2 * r] + 1):
                run = 0.0
                lst = []
                for x in range(S + 1, min(cap, G.top[2 * r + 2] - 1) + 1):
                    run += s if row.get(x, False) else 1.0
                    lst.append(run)
                W[S] = lst
            self.cumw.append(W)

    def apply_T(self, r, f):
        G = self.G
        cap = G.top[2 * r + 1]
        W = self.cumw[r]
        out = {}
        for S in range(2 * r, G.top[2 * r] + 1):
            lst = W[S]
            acc = 0.0
            for S2 in range(S + 2, min(S + UMAX, G.top[2 * r + 2]) + 1):
                v = f.get(S2)
                if v is None:
                    continue
                k = min(S2 - 1, cap) - S - 1
                if k < 0:
                    continue
                acc += (lst[k] if k < len(lst) else (lst[-1] if lst else 0.0)) * self.wu[S2 - S] * v
            out[S] = acc
        return out

    def MK(self, r0, L):
        G = self.G
        V = {S: 1.0 for S in range(2 * (r0 + L), G.top[2 * (r0 + L)] + 1)}
        for r in range(r0 + L - 1, r0 - 1, -1):
            V = self.apply_T(r, V)
        return V

    def cw_at(self, r0, K):
        """(max CW over states, argmax state, dict S->cw)."""
        V1 = self.MK(r0, K)
        V2 = self.MK(r0, 2 * K)
        best = -1e9
        arg = None
        d = {}
        for S in V1:
            if V1[S] > 0 and V2.get(S, 0) > 0:
                v = math.log2(V2[S] / V1[S]) / (2 * K)
                d[S] = v
                if v > best:
                    best, arg = v, S
        return best, arg, d
