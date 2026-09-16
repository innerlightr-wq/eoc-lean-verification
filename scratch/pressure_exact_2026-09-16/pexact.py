"""Exact odd-dark pressure for the Lean observable, and the old Tao-black surrogate.

Lean objects (EOC/OddBlack.lean, EOC/AverageOddDark.lean):
  shellP b j sigma : words d_1..d_j >= 1, S_i <= b(i) = floor(i alpha), S_j = sigma = b(j)
  pair block r < R = j/2 : class state x = S_{2r}, y = S_{2r+2};
      B_r(x,y) = { z : x < z < y, z <= cap_r },  cap_r = b(2r+1)          (pairB)
      z eligible iff z+1 in B_r(x,y)                                        (Elig)
      Dark(lam, m, d, r, z) iff distZ(lam * u * 2^z / 2^m) < d, u = 3^{-(2r+2)} mod 2^m   (Dark, pairPhase)
  N_odd(P) = #{ r : own odd choice S_{2r+1} eligible and dark },  m = sigma + 1 + t.
  Target: (1/j) log2( sum_P s^{N_odd(P)} / |shellP| ) <= theta   (AverageOddDarkPressure, per lambda;
          SummedOddDarkPressure sums over lambda in the frequency shell).

Two dark predicates are available for a column z of block r (b = 2r+2, a = m - z):
  '2adic' : exact Lean predicate, D * min(v, 2^m - v) < 2^m, v = lam*u*2^z mod 2^m   (d = 1/D)
  '3adic' : D * |centered(xi * 2^{-a} mod 3^b)| < 3^b   (xi = lam gives the Lean predicate up to the
            reciprocity correction lam 2^z / (2^m 3^b);  arbitrary 3-adic xi allowed)
Observables:
  'odd'   : tilt s at eligible dark own choices           (Lean N_odd)
  'black' : tilt s at every own odd choice with dark cell (the surrogate measured in earlier rounds, D=54)

Class DP (exact big integers for integer s): Z_{r+1}(y) = sum_x Z_r(x) W_r(x,y) with
  W_r(x,y) = (v - x) + (s-1)(H(v') - H(x)),  v = min(y-1, cap_r),  v' = v-1 ('odd') or v ('black'),
  H = cumulative dark count, for x <= v-1 (else 0).  Prefix sums make each layer O(b(j)).
Telescoping block observable (floats, per-layer renormalised):
  Phi_r = <f_r, g_r>, f_r = forward tilted through block r-1, g_r = backward UNtilted from block r to the end.
  Phi_0 = |shellP|, Phi_R = sum_P s^{N}, and w_r = log2 Phi_{r+1} - log2 Phi_r >= 0 with sum_r w_r = j * pressure.
"""
import math

AL = math.log2(3)


def barrier(i):
    return (3 ** i).bit_length() - 1          # floor(i log2 3), exact


class Instance:
    def __init__(self, j, t, lam=1, D=108, mode='2adic', obs='odd', xi=None):
        assert j % 2 == 0
        self.j, self.R, self.t, self.D = j, j // 2, t, D
        self.sg = barrier(j)
        self.m = self.sg + 1 + t
        self.top = [min(barrier(i), self.sg) for i in range(j + 1)]
        self.lam, self.mode, self.obs = lam, mode, obs
        self.xi = lam if xi is None else xi
        self.H = [self._cumdark(r) for r in range(self.R)]   # H[r][z] for z in 0..cap_r

    def dark_row(self, r):
        cap = self.top[2 * r + 1]
        b = 2 * r + 2
        out = [False] * (cap + 1)
        lo = 2 * r + 1
        mode = self.mode
        if mode == 'auto':
            # PROVED (MATH): D*|c| != 3^b for even D (parity), so the 3-adic test equals the exact
            # Lean (2-adic) test whenever 2^(m-z) > D*lam for all columns z <= sigma.
            assert self.D % 2 == 0 and self.xi == self.lam
            mode = '3adic' if (1 << (self.m - self.sg)) > self.D * self.lam else '2adic'
        if mode == '2adic':
            M = 1 << self.m
            c = self.lam * pow(3 ** b, -1, M) % M
            for z in range(lo, cap + 1):
                v = (c << z) % M
                out[z] = self.D * min(v, M - v) < M
        else:
            qb = 3 ** b
            rr = self.xi * pow(2, -(self.m - lo), qb) % qb
            half = qb // 2
            for z in range(lo, cap + 1):
                y = rr if rr <= half else qb - rr
                out[z] = self.D * y < qb
                rr = rr * 2 % qb
        return out

    def _cumdark(self, r):
        row = self.dark_row(r)
        H = [0] * len(row)
        acc = 0
        for z, fl in enumerate(row):
            acc += fl
            H[z] = acc
        return H

    # ---------- exact forward DP (integer s) ----------
    def moment(self, s):
        top, R = self.top, self.R
        Z = {0: 1}
        lo = 0
        vec = [1]                                  # indices x = lo .. top[2r]
        for r in range(R):
            cap = top[2 * r + 1]
            H = self.H[r]
            hi = top[2 * r]
            n = hi - lo + 1
            A0 = [0] * (n + 1); A1 = [0] * (n + 1); AH = [0] * (n + 1)
            for i in range(n):
                x = lo + i
                zx = vec[i]
                A0[i + 1] = A0[i] + zx
                A1[i + 1] = A1[i] + x * zx
                AH[i + 1] = AH[i] + zx * (H[x] if x <= cap else H[cap])
            nlo, nhi = 2 * r + 2, top[2 * r + 2]
            out = [0] * (nhi - nlo + 1)
            for y in range(nlo, nhi + 1):
                v = min(y - 1, cap)
                k = min(v - 1, hi) - lo + 1        # number of x in [lo, v-1]
                if k <= 0:
                    continue
                vp = v - 1 if self.obs == 'odd' else v
                hv = H[vp] if vp >= 0 else 0
                out[y - nlo] = v * A0[k] - A1[k] + (s - 1) * (hv * A0[k] - AH[k])
            lo, vec = nlo, out
        return vec[self.sg - lo]

    # ---------- float telescoping decomposition ----------
    def blocks(self, s):
        top, R = self.top, self.R
        # backward untilted g_r on x in [2r, top[2r]], log-scaled
        g = [None] * (R + 1); gs = [0.0] * (R + 1)
        g[R] = {self.sg: 1.0}
        for r in range(R - 1, -1, -1):
            cap = top[2 * r + 1]
            nlo, nhi = 2 * r + 2, top[2 * r + 2]
            gy = g[r + 1]
            # suffix sums over y of g(y), (y-1) g(y)  for y <= cap+1 ; plain g for y >= cap+2
            ys = sorted(gy)
            lo, hi = 2 * r, top[2 * r]
            cur = {}
            # T(x) = sum_{y>=x+2, y<=cap+1} (y-1-x) g(y) + sum_{y>=cap+2} (cap-x) g(y)
            tail = sum(val for y, val in gy.items() if y >= cap + 2)
            pref = {}
            S0 = 0.0; S1 = 0.0
            for y in sorted((y for y in gy if y <= cap + 1), reverse=True):
                S0 += gy[y]; S1 += (y - 1) * gy[y]
                pref[y] = (S0, S1)
            keys = sorted(pref)
            import bisect
            for x in range(lo, hi + 1):
                if x > cap - 1 and x + 2 > cap + 1:
                    val = 0.0
                else:
                    idx = bisect.bisect_left(keys, x + 2)
                    a0, a1 = pref[keys[idx]] if idx < len(keys) else (0.0, 0.0)
                    val = a1 - x * a0 + (cap - x) * tail if x <= cap - 1 else a1 - x * a0
                if val > 0:
                    cur[x] = val
            mx = max(cur.values())
            g[r] = {x: v / mx for x, v in cur.items()}
            gs[r] = gs[r + 1] + math.log2(mx)
        # forward tilted f_r and Phi_r
        f = {0: 1.0}; fs = 0.0
        logphi = [0.0] * (R + 1)
        logphi[0] = fs + gs[0] + math.log2(sum(f[x] * g[0].get(x, 0.0) for x in f))
        for r in range(R):
            cap = top[2 * r + 1]
            H = self.H[r]
            lo, hi = 2 * r, top[2 * r]
            xs = sorted(f)
            A0 = [0.0]; A1 = [0.0]; AH = [0.0]; X = []
            for x in xs:
                X.append(x)
                A0.append(A0[-1] + f[x]); A1.append(A1[-1] + x * f[x])
                AH.append(AH[-1] + f[x] * (H[x] if x <= cap else H[cap]))
            import bisect
            nf = {}
            for y in range(2 * r + 2, top[2 * r + 2] + 1):
                v = min(y - 1, cap)
                k = bisect.bisect_right(X, v - 1)
                if k == 0:
                    continue
                vp = v - 1 if self.obs == 'odd' else v
                hv = H[vp] if vp >= 0 else 0
                val = v * A0[k] - A1[k] + (s - 1) * (hv * A0[k] - AH[k])
                if val > 0:
                    nf[y] = val
            mx = max(nf.values())
            f = {y: val / mx for y, val in nf.items()}
            fs += math.log2(mx)
            dot = sum(f[x] * g[r + 1].get(x, 0.0) for x in f)
            logphi[r + 1] = fs + gs[r + 1] + math.log2(dot)
        w = [logphi[r + 1] - logphi[r] for r in range(R)]
        return w, logphi


def log2ratio(a, b):
    """log2(a/b) for positive big ints, accurate to ~1e-15."""
    sh = max(a.bit_length(), b.bit_length()) - 64
    if sh > 0:
        return math.log2(a >> sh) - math.log2(b >> sh) if (a >> sh) and (b >> sh) else \
            (a.bit_length() - b.bit_length())
    return math.log2(a) - math.log2(b)


def below(a, b, j, num, den):
    """certified: a <= b * 2^{(num/den) j}  (exact integer test a^den <= b^den 2^{num j})."""
    return a ** den <= (b ** den) << (num * j)
