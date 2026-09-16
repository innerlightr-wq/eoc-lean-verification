"""Dangerous-window fractions for logarithmic window sizes K(j) = ceil(A log2 j), disjoint windows from block 0.
Window mass from state x: val(x) = (Lt_{r0} ... Lt_{r0+K-1} 1)(x) in the geometric normalisation p = (j-1)/(sigma-1),
s = 3, d = 1/108 (exact Lean dark predicate via pexact 'auto').  A window is dangerous at theta_d when
max_x log2 val(x) / (2K) > theta_d.
Modes:  float  - fast scan;  exact - integer recurrence G_r(x) = sum_y (j-1)^2 Q^{y-x-2} W(x,y) G_{r+1}(y),
        Q = sigma - j, G_end(y) = D^{T-y}, D = sigma-1, so val(x) = G_r0(x) / D^{T-x}; certified comparison
        val <= 2^{2 K theta_d} with rational theta_d = n/d  <=>  G^d <= 2^{2Kn} D^{d(T-x)}.
usage: python3 logk.py float|exact"""
import json, math, random, sys
from fractions import Fraction
from multiprocessing import Pool
sys.path.insert(0, '../pressure_exact_2026-09-16')
from pexact import Instance, barrier
from geo import apply, make_ops

AS = (1, 2, 3, 4)
THD = [Fraction(k, 100) for k in range(4, 15)]          # 0.04 .. 0.14

def K_of(j, A):
    return math.ceil(A * math.log2(j))

def apply_int(I, r, G, lo_next):
    """exact integer version of geo.apply with p^2 -> (j-1)^2, q -> Q = sigma - j (s = 3)."""
    j, sg = I.j, I.sg; Q = sg - j; P2 = (j - 1) ** 2
    top = I.top; cap = top[2 * r + 1]; H = I.H[r]
    lo, hi = 2 * r, top[2 * r]; hi_next = lo_next + len(G) - 1
    out = [0] * (hi - lo + 1)
    Ccap = 0
    for y in range(hi_next, cap + 1, -1):
        if y >= lo_next: Ccap = G[y - lo_next] + Q * Ccap
    A = 0; B = 0
    Hc1 = H[cap - 1] if cap >= 1 else 0
    xs = min(hi, cap - 1)
    for y in range(cap + 1, xs + 1, -1):
        gy = G[y - lo_next] if lo_next <= y <= hi_next else 0
        A = gy + Q * A; B = gy * (y - 1 + 2 * H[y - 2]) + Q * B
    Cx = Ccap * Q ** (cap - xs) if xs <= cap else 0
    for x in range(xs, lo - 1, -1):
        if x < xs:
            y = x + 2
            gy = G[y - lo_next] if lo_next <= y <= hi_next and y <= cap + 1 else 0
            A = gy + Q * A; B = gy * (y - 1 + 2 * H[y - 2]) + Q * B
            Cx *= Q
        val = B - (x + 2 * H[x]) * A + ((cap - x) + 2 * (Hc1 - H[x])) * Cx
        out[x - lo] = P2 * val
    return out

def scan(args):
    mode, j, t, kind, val, A = args
    I = Instance(j, t, lam=val, D=108, mode='auto') if kind == 'true' else \
        Instance(j, t, D=108, mode='3adic', xi=val)
    K = K_of(j, A); W = I.R // K
    p, q = make_ops(I)
    rates = []; certs = {str(th): 0 for th in THD}; unresolved = 0
    for i in range(W):
        r0, r1 = i * K, (i + 1) * K
        if mode == 'float':
            f = [1.0] * (I.top[2 * r1] - 2 * r1 + 1)
            for r in range(r1 - 1, r0 - 1, -1): f = apply(I, r, f, 3.0, p, q, 2 * r + 2)
            rates.append(math.log2(max(f)) / (2 * K))
        else:
            D = I.sg - 1; T = I.top[2 * r1]
            G = [D ** (T - y) for y in range(2 * r1, T + 1)]
            for r in range(r1 - 1, r0 - 1, -1): G = apply_int(I, r, G, 2 * r + 2)
            lo = 2 * r0
            # exact worst state: compare val(x) = G/D^{T-x} across x via float for reporting, exact for thresholds
            best = max(range(len(G)), key=lambda i2: (math.log2(G[i2]) if G[i2] else -1e18) - (T - lo - i2) * math.log2(D))
            rates.append(((math.log2(G[best]) if G[best] else -1e9) - (T - lo - best) * math.log2(D)) / (2 * K))
            for th in THD:
                n, dd = th.numerator, th.denominator
                if any(G[i2] ** dd > (D ** (dd * (T - lo - i2))) << (2 * K * n) for i2 in range(len(G)) if G[i2]):
                    certs[str(th)] += 1
    frac = {str(th): (sum(1 for v in rates if v > float(th)) / W) if mode == 'float' else certs[str(th)] / W for th in THD}
    return {'mode': mode, 'j': j, 't': t, 'kind': kind, 'lam': val if kind == 'true' else None, 'A': A, 'K': K,
            'W': W, 'max': max(rates), 'mean': sum(rates) / W, 'frac': frac}

if __name__ == '__main__':
    mode = sys.argv[1]
    specs = []
    if mode == 'float':
        for j in (400, 800, 1600, 3200):
            for lam in (1, 3, 5, 17):
                for t in (1, j // 6, j):
                    for A in AS: specs.append((mode, j, t, 'true', lam, A))
            random.seed(7 + j)
            for k in range(2):
                xi = random.randrange(1, 3 ** (j + 2)); xi += (xi % 3 == 0)
                for A in AS: specs.append((mode, j, j // 6, 'haar', xi, A))
        for t in (1, 6400 // 6):
            for A in AS: specs.append((mode, 6400, t, 'true', 1, A))
    else:
        for j in (400, 800, 1600):
            for lam, t in ((1, 1), (1, j // 6), (17, j)):
                for A in (2, 3): specs.append((mode, j, t, 'true', lam, A))
    with Pool(7) as pool:
        res = pool.map(scan, specs, chunksize=1)
    json.dump(res, open(f'logk_{mode}.json', 'w'))
    print('done', len(res))
