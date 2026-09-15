"""Parts V-VIII, XXXI: first-divergence pair diagnostics (A=0.7 geometry, c=0, uniform paths in P_sigma).
(a) closeness given a shared prefix: P uniform, Q = P's first k steps + independent uniform continuation.
    Pr(||zeta_P - zeta_Q|| < 2^-u | share k)  vs Haar 2^{1-u};  k = round(u/alpha) is the H2-saturating family.
(b) odd quotient Delta = (q_P-q_Q)/2^v for fixed first-divergence data (prefix, step k+1 digits d != d'):
    Renyi-2 entropy of Delta mod 2^r (2-adic low bits) and of the top r bits of zeta_P - zeta_Q (archimedean).
usage: python3 pairdiag.py j0 sigma t nsamp seed"""
import math, random, sys
from collections import Counter
AL = math.log2(3)
j0, sg, t, ns, seed = map(int, sys.argv[1:6]); random.seed(seed); m = sg + t + 1; MOD = 1 << m
b = [math.floor(j * AL) for j in range(j0 + 2)]
g = [dict() for _ in range(j0 + 1)]; g[j0][sg] = 1
for i in range(j0 - 1, -1, -1):
    for S in range(0, b[i] + 1):
        v = sum(g[i + 1].get(S2, 0) for S2 in range(S + 1, min(b[i + 1], sg) + 1))
        if v: g[i][S] = v
def extend(S, i0, first=None):  # uniform continuation of partial-sum list S (length i0+1) to j0 steps
    S = S[:i0 + 1]
    for i in range(i0, j0):
        opts = [(S2, g[i + 1][S2]) for S2 in range(S[-1] + 1, min(b[i + 1], sg) + 1) if S2 in g[i + 1]]
        if i == i0 and first is not None: opts = [(S2, w) for S2, w in opts if S2 == S[-1] + first]
        if not opts: return None
        x = random.randrange(sum(w for _, w in opts))
        for S2, w in opts:
            if x < w: S.append(S2); break
            x -= w
    return S
inv = pow(3, -j0, MOD)
def zeta(S):  # y-type point 3^{-j0} q_P mod 2^m, q_P = sum_{i<j0} 3^{j0-1-i} 2^{S_i}
    return (inv * sum(3 ** (j0 - 1 - i) * 2 ** S[i] for i in range(j0))) % MOD
def cd(x): x %= MOD; return min(x, MOD - x)
print(f"j0={j0} sigma={sg} t={t} m={m}")
print("(a) Pr(close at 2^-u | share first k steps) / Haar(2^{1-u}):")
for u in (4, 6, 8, 10, 12):
    row = []
    for k in sorted(set([0, max(1, round(u / AL)), round(u / AL) + 3, round(2 * u / AL)])):
        hits = 0
        for _ in range(ns):
            P = extend([0], 0); Q = extend(P, k)
            if Q is not None and cd(zeta(P) - zeta(Q)) < MOD >> u: hits += 1
        row.append(f"k={k}: {hits / ns / 2.0 ** (1 - u):.2f}")
    print(f"  u={u:2d} (u/alpha={u / AL:.1f}):  " + "  ".join(row))
print("(b) fixed first-divergence data: Renyi-2 entropy deficit (r-1-H2 for Delta mod 2^r; r-H2 for top bits)")
for k in (5, 20, 40):
    base = extend([0], 0)
    for (d, e) in ((1, 2), (1, 3)):
        lowv, topv = [], []
        for _ in range(ns):
            P = extend(base, k, d); Q = extend(base, k, e)
            if P is None or Q is None: continue
            D = sum(3 ** (j0 - 1 - i) * (2 ** P[i] - 2 ** Q[i]) for i in range(j0))
            v = (D & -D).bit_length() - 1; Dl = D >> v
            lowv.append(Dl); topv.append((inv * D) % MOD)
        n = len(lowv)
        def h2(vals):
            c = Counter(vals); col = sum(x * (x - 1) for x in c.values())
            return -math.log2(col / (n * (n - 1))) if col else float('inf')
        out = []
        for r in (4, 8, 12, 16, 20):
            out.append(f"r={r}: {r - 1 - h2([x % (1 << r) for x in lowv]):+.2f}/{r - h2([x >> (m - r) for x in topv]):+.2f}")
        print(f"  k={k:2d} d,d'={d},{e} n={n}: " + "  ".join(out))
