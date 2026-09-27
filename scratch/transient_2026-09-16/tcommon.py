"""Fast list-based re-implementation of scratch/oddpressure_2026-09-16/common.py.

Mathematically IDENTICAL to common.Env (verified bit-for-bit up to float assoc. in
verify_engine.py); the only change is data layout (lists instead of dicts) plus
precomputation of the per-block transfer coefficients, and a sweep that gets
M_K(j) and M_2K(j) for every anchor j in R*2K block applications instead of R*3K.

Conventions (verbatim from common.py):
  AL = log2 3, J digits, R = J//2 pair blocks, sg = floor(J*AL), t = J//6, m = sg+t+1
  top[i] = min(floor(i*AL), sg)
  block r owns level b = 2r+2; column x -> cell (a,b) = (m-x, 2r+2)
  BLACK iff 54*|centered(XI*2^{-(m-x)} mod 3^b)| < 3^b
  (T_r f)(S) = sum_{S2} [sum_{x=S+1..min(S2-1,cap)} s^black(x)] p^2 q^{S2-S-2} f(S2), cap = top[2r+1]

Exact integer arithmetic for everything 3-adic; floats only in the operator, exactly
as the original.
"""
import math

AL = math.log2(3)
P = 1 / AL
Q_ = 1 - P
UMAX = 30
DMAX = 60
ETA_DEN = 54


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
    b = 2 * r + 2
    qb = 3 ** b
    rr = XI * pow(2, -(G.m - x_lo), qb) % qb
    out = {}
    for x in range(x_lo, x_hi + 1):
        out[x] = centered(rr, qb)
        rr = rr * 2 % qb
    return out


def row_black_list(G, r, x_lo, x_hi, XI):
    """list of bools for x = x_lo..x_hi (exact integer test)."""
    b = 2 * r + 2
    qb = 3 ** b
    rr = XI * pow(2, -(G.m - x_lo), qb) % qb
    half = qb // 2
    out = []
    for _ in range(x_lo, x_hi + 1):
        y = rr if rr <= half else rr - qb
        out.append(ETA_DEN * (y if y >= 0 else -y) < qb)
        rr = rr * 2 % qb
    return out


def cell_xrange(G, r):
    lo = 2 * r + 1
    hi = min(G.top[2 * r + 1], G.top[2 * r + 2] - 1)
    return lo, hi


class FastEnv:
    def __init__(self, G, XI, s=3.0, rmax=None):
        self.G = G
        self.XI = XI
        self.s = s
        R = G.R if rmax is None else rmax
        self.R = R
        top = G.top
        wu = [0.0, 0.0] + [P * P * Q_ ** (u - 2) for u in range(2, UMAX + 1)]
        self.wu = wu
        self.blk = []          # blk[r][x-2r] = black?  for x = 2r .. top[2r]+DMAX
        self.coef = []         # coef[r][S-2r] = list over u=2..UMAX of coefficient
        self.slo = []          # 2r
        self.shi = []          # top[2r]
        for r in range(R):
            xlo = 2 * r
            xhi = top[2 * r] + DMAX
            row = row_black_list(G, r, xlo, xhi, XI)
            self.blk.append(row)
            cap = top[2 * r + 1]
            hi_x = min(cap, top[2 * r + 2] - 1)
            # prefix sums Pf[x-xlo+1] = sum_{x'=xlo..x} s^black(x')  -> lst_S[k] = Pf[S+1+k]-Pf[S]
            Pf = [0.0] * (xhi - xlo + 2)
            run = 0.0
            for idx in range(xhi - xlo + 1):
                run += s if row[idx] else 1.0
                Pf[idx + 1] = run
            off = xlo - 1   # Pf index of column x is x - off
            cf = []
            for S in range(2 * r, top[2 * r] + 1):
                nl = hi_x - S            # number of admissible columns x = S+1..hi_x
                kc = cap - S - 1
                base = Pf[S - off]
                cl = []
                for u in range(2, UMAX + 1):
                    k = u - 2
                    if kc < k:
                        k = kc
                    if nl - 1 < k:
                        k = nl - 1
                    cl.append(0.0 if k < 0 else (Pf[S + 1 + k - off] - base) * wu[u])
                cf.append(cl)
            self.coef.append(cf)
            self.slo.append(2 * r)
            self.shi.append(top[2 * r])

    def ones(self, r):
        return [1.0] * (self.shi[r] - self.slo[r] + 1)

    def apply_T(self, r, f):
        """f lives on block r+1 (index S2-slo[r+1]); returns vector on block r."""
        lo = self.slo[r]
        lo2 = self.slo[r + 1]
        hi2 = self.shi[r + 1]
        cf = self.coef[r]
        n = self.shi[r] - lo + 1
        out = [0.0] * n
        for i in range(n):
            S = lo + i
            cl = cf[i]
            acc = 0.0
            umax = hi2 - S
            if umax > UMAX:
                umax = UMAX
            base = S - lo2
            for u in range(2, umax + 1):
                c = cl[u - 2]
                if c:
                    acc += c * f[base + u]
            out[i] = acc
        return out

    def MK(self, r0, L):
        V = self.ones(r0 + L)
        for r in range(r0 + L - 1, r0 - 1, -1):
            V = self.apply_T(r, V)
        return V

    def cw_at(self, r0, K):
        V1 = self.MK(r0, K)
        V2 = self.MK(r0, 2 * K)
        return cw_from(V1, V2, K, self.slo[r0])

    def pressure_sweep(self, K):
        """returns dict j -> (Pbest, Sarg) for every anchor j with j+2K <= R-1.

        One backward sweep of length 2K per endpoint e gives M_K(e-K) and M_2K(e-2K).
        """
        R = self.R
        MKv = {}
        M2Kv = {}
        for e in range(2 * K, R):
            V = self.ones(e)
            r = e - 1
            while r >= e - 2 * K:
                V = self.apply_T(r, V)
                if r == e - K:
                    MKv[r] = V
                if r == e - 2 * K:
                    M2Kv[r] = V
                r -= 1
        out = {}
        for j in sorted(M2Kv):
            if j in MKv:
                out[j] = cw_from(MKv[j], M2Kv[j], K, self.slo[j])
        return out


def cw_from(V1, V2, K, slo):
    best = -1e9
    arg = None
    d = {}
    for i, a in enumerate(V1):
        b = V2[i]
        if a > 0 and b > 0:
            v = math.log2(b / a) / (2 * K)
            d[slo + i] = v
            if v > best:
                best, arg = v, slo + i
    return best, arg, d
