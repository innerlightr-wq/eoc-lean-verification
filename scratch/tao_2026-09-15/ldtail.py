"""Parts XII-XIII, XXXI, XLV: lower tail of the path contraction sum_r Z_r (Z_r = -log2 W_r^2, L=3 blocks) at lambda = 1
(true environment) vs a random high frequency (random-digit control); weak-block (Z<0.1 among u>=4) statistics.
usage: python3 ldtail.py j0 sigma t npaths"""
import math, random, sys
AL = math.log2(3); random.seed(17)
j0, sg, t, npaths = map(int, sys.argv[1:5]); m = sg + t + 1; b = [math.floor(j * AL) for j in range(j0 + 3)]
g = [dict() for _ in range(j0 + 1)]; g[j0][sg] = 1
for i in range(j0 - 1, -1, -1):
    for S in range(0, b[i] + 1):
        v = sum(g[i + 1].get(S2, 0) for S2 in range(S + 1, min(b[i + 1], sg) + 1))
        if v: g[i][S] = v
cum = {}  # sampling tables
def sample_path():
    S = [0]
    for i in range(j0):
        opts = [(S2, g[i + 1][S2]) for S2 in range(S[-1] + 1, min(b[i + 1], sg) + 1) if S2 in g[i + 1]]
        x = random.randrange(sum(w for _, w in opts))
        for S2, w in opts:
            if x < w: S.append(S2); break
            x -= w
    return S
MOD = 1 << m; inv3 = pow(3, -1, MOD); nb = j0 // 3
Qc = {}
def shapes(i, S, u):
    k = (i, S, u)
    if k not in Qc: Qc[k] = [3 * 2 ** a + 2 ** c for c in range(u - 1) for a in range(c) if S + 1 + a <= b[i + 1] and S + 1 + c <= b[i + 2]]
    return Qc[k]
def W2(beta, Q):
    if len(Q) <= 1: return 1.0
    re = sum(math.cos(2 * math.pi * q * beta) for q in Q); im = sum(math.sin(2 * math.pi * q * beta) for q in Q)
    return (re * re + im * im) / len(Q) ** 2
lamR = random.randrange(1, MOD) | 1
for name, lam in (("lambda=1", 1), ("random-freq", lamR)):
    tots = []; weak = []; nontriv = 0
    for _ in range(npaths):
        S = sample_path(); tot = 0; wk = 0
        for r in range(nb):
            Sr = S[3 * r]; M = m - Sr - 1; u = S[3 * r + 3] - Sr; Q = shapes(3 * r, Sr, u)
            x = (lam * pow(inv3, 3 * r + 3, 1 << M)) % (1 << M)
            z = -math.log2(max(W2(x / 2 ** M, Q), 1e-300)); tot += z
            if len(Q) > 1: nontriv += 1; wk += (z < 0.1)
        tots.append(tot / (2 * j0)); weak.append(wk)
    n = len(tots); mean = sum(tots) / n
    tail = {z: sum(v < z for v in tots) / n for z in (0.01, 0.05, 0.1, 0.2, 0.3)}
    mw = sum(weak) / n; vw = sum((w - mw) ** 2 for w in weak) / n; pw = sum(weak) / nontriv
    print(f"j0={j0} {name}: mean amp rate {mean:.3f}, min {min(tots):.3f}; P(rate<z): " + " ".join(f"{z}:{p:.2e}" for z, p in tail.items())
          + f" | weak blocks: P(weak|u>=4)={pw:.4f}, E W={mw:.2f}, Var W/binomial={vw / max(mw * (1 - pw), 1e-9):.2f}")
