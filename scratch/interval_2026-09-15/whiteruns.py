"""Part XXIX: white-run statistics of the L=3 block angles over low frequencies (A=0.7 geometry, c=0).
Block r = steps (3r,3r+1,3r+2); entry S = S_{3r}; angle beta_r = e_r / 2^{M_r}, e_r = cres(lam * 3^{-(3r+3)} mod 2^{M_r}),
M_r = m - S - 1; white_r := 54|e_r| < 2^{M_{r+1}}  (angle < 2^{-u_r}/54).  Rigidity (Lean: WhiteRun.run_dvd): a white run of
length k starting at r forces 27^{k-1} | e_r.  Paths: uniform samples from the prefix shell P_sigma.
usage: python3 whiteruns.py j0 sigma t npaths nlam seed"""
import math, random, sys
from collections import Counter
AL = math.log2(3)
j0, sg, t, npaths, nlam, seed = map(int, sys.argv[1:7]); random.seed(seed)
m = sg + t + 1; b = [math.floor(j * AL) for j in range(j0 + 3)]
# backward counts g[i][S] = #continuations from (i,S) to (j0, sg)
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
paths = [sample_path() for _ in range(npaths)]
MOD = 1 << m; inv3 = pow(3, -1, MOD)
w = [pow(inv3, n, MOD) for n in range(j0 + 4)]
def cres(x, M):
    x %= (1 << M)
    return x - (1 << M) if x > (1 << (M - 1)) else x
def v27(x):
    k = 0
    while x and x % 27 == 0: x //= 27; k += 1
    return k if x else 99
def W2(beta, i, S, u):  # block mean square with admissible shapes
    Q = [3 * 2 ** a + 2 ** bb for bb in range(u - 1) for a in range(bb) if S + 1 + a <= b[i + 1] and S + 1 + bb <= b[i + 2]]
    if len(Q) <= 1: return 1.0
    re = sum(math.cos(2 * math.pi * q * beta) for q in Q); im = sum(math.sin(2 * math.pi * q * beta) for q in Q)
    return (re * re + im * im) / len(Q) ** 2
lams = list(range(1, min(1 << t, 1024)))
if (1 << t) > 1024: lams += random.sample(range(1024, 1 << t), min(nlam, (1 << t) - 1024))
lams = [l for l in lams if l % (1 << t)]
nb = j0 // 3
Rmax = Counter(); runs_tot = 0; white_tot = 0; blocks_tot = 0; viol = 0; startv = Counter(); logQ = []; dv = Counter(); ndeep = 0
for lam in lams:
    for S in paths:
        e = []; Ms = []; whites = []; lq = 0.0
        for r in range(nb):
            Sr = S[3 * r]; M = m - Sr - 1; M2 = m - S[3 * r + 3] - 1; u = S[3 * r + 3] - Sr
            er = cres(lam * w[3 * r + 3], M); e.append(er)
            wh = 54 * abs(er) < (1 << M2); whites.append(wh)
            lq += math.log2(max(W2(er / 2 ** M, 3 * r, Sr, u), 1e-300))
            if 3 ** (3 * r + 3) > (1 << t): ndeep += 1; dv[min(v27(er), 4)] += 1
        blocks_tot += nb; white_tot += sum(whites); logQ.append(lq)
        best = 0; r = 0
        while r < nb:
            if whites[r]:
                k = 1
                while r + k < nb and whites[r + k]: k += 1
                runs_tot += 1; best = max(best, k); startv[min(v27(e[r]), 5)] += 1
                if k >= 2 and e[r] % 27 ** (k - 1): viol += 1
                r += k
            else: r += 1
        Rmax[best] += 1
N = len(lams) * len(paths)
print(f"j0={j0} sigma={sg} t={t} m={m} blocks={nb} lambdas={len(lams)} paths={len(paths)} pairs={N}")
print(f" white fraction per block {white_tot / blocks_tot:.4e}; runs per (lam,path) {runs_tot / N:.4f}; rigidity violations {viol}")
print(" P(Rmax>=k):", {k: f"{sum(v for kk, v in Rmax.items() if kk >= k) / N:.3e}" for k in range(1, 6)})
print(" v27 at run starts:", dict(sorted(startv.items())))
print(" deep blocks (3^{n_r} > 2^t): P(v27(e_r) >= k):", {k: f"{sum(v for kk, v in dv.items() if kk >= k) / ndeep:.3e}" for k in range(1, 4)}, " (27^-k =", [f"{27.0 ** -k:.2e}" for k in (1, 2, 3)], ")")
logQ.sort(); mean = sum(2 ** x for x in logQ) / N
print(f" per-path log2 prod W^2: median {logQ[N // 2]:.1f} (rate {-logQ[N // 2] / (2 * j0):.3f}), max {logQ[-1]:.1f} (rate {-logQ[-1] / (2 * j0):.3f}); log2 mean {math.log2(mean):.1f}")
