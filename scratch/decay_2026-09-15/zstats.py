"""Parts XXV-XXVII: log-product statistics Z_r = -log2 W_r^2 of the L=3 block factors along (lambda, path), low shell.
usage: python3 zstats.py j0 sigma t npaths nlam"""
import math, random, sys, statistics as st
AL = math.log2(3); random.seed(11)
j0, sg, t, npaths, nlam = map(int, sys.argv[1:6]); m = sg + t + 1; b = [math.floor(j * AL) for j in range(j0 + 3)]
g = [dict() for _ in range(j0 + 1)]; g[j0][sg] = 1
for i in range(j0 - 1, -1, -1):
    for S in range(0, b[i] + 1):
        v = sum(g[i + 1].get(S2, 0) for S2 in range(S + 1, min(b[i + 1], sg) + 1))
        if v: g[i][S] = v
def sample_path():
    S = [0]
    for i in range(j0):
        opts = [(S2, g[i + 1][S2]) for S2 in range(S[-1] + 1, min(b[i + 1], sg) + 1) if S2 in g[i + 1]]
        x = random.randrange(sum(w for _, w in opts))
        for S2, w in opts:
            if x < w: S.append(S2); break
            x -= w
    return S
MOD = 1 << m; inv3 = pow(3, -1, MOD)
def W2(beta, i, S, u):
    Q = [3 * 2 ** a + 2 ** c for c in range(u - 1) for a in range(c) if S + 1 + a <= b[i + 1] and S + 1 + c <= b[i + 2]]
    if len(Q) <= 1: return 1.0
    re = sum(math.cos(2 * math.pi * q * beta) for q in Q); im = sum(math.sin(2 * math.pi * q * beta) for q in Q)
    return (re * re + im * im) / len(Q) ** 2
nb = j0 // 3; Z = []  # rows
lams = random.sample(range(1, 1 << t), min(nlam, (1 << t) - 1))
for lam in lams:
    for _ in range(npaths):
        S = sample_path(); row = []
        for r in range(nb):
            Sr = S[3 * r]; M = m - Sr - 1; u = S[3 * r + 3] - Sr
            x = (lam * pow(inv3, 3 * r + 3, MOD)) % (1 << M)
            row.append(-math.log2(max(W2(x / 2 ** M, 3 * r, Sr, u), 1e-300)))
        Z.append(row)
flat = [z for row in Z for z in row]; mean = st.mean(flat); var = st.pvariance(flat)
print(f"j0={j0} blocks={nb} samples={len(Z)}: mean Z={mean:.3f} bits/block ({mean / 6:.3f} amplitude bits/step), var={var:.3f}, P(Z<0.1)={sum(z < 0.1 for z in flat) / len(flat):.3f}, P(Z=0)={sum(z == 0 for z in flat) / len(flat):.3f}")
for lag in (1, 2, 3, 5, 8):
    xs = [row[r] for row in Z for r in range(nb - lag)]; ys = [row[r + lag] for row in Z for r in range(nb - lag)]
    mx, my = st.mean(xs), st.mean(ys); c = sum((a - mx) * (b_ - my) for a, b_ in zip(xs, ys)) / len(xs)
    print(f"  corr(Z_r, Z_r+{lag}) = {c / math.sqrt(st.pvariance(xs) * st.pvariance(ys)):+.4f}")
tot = sorted(sum(row) for row in Z); n = len(tot)
print(f"  per-path total: median {tot[n // 2]:.1f}, 1% quantile {tot[n // 100]:.1f}, min {tot[0]:.1f} bits (mean {mean * nb:.1f});  per-block tail P(Z>8)={sum(z > 8 for z in flat) / len(flat):.3f}")
