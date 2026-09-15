"""Parts II-IX, XXX: per-frequency-shell rigorous savings (log2 of normalized shell average a_u) at one (j0, sigma, t):
  T2(u): 2-adic complete-period block tower   E_P prod_{r: M_r <= u} 1/|C_r|           (Lean: ThreeBlock.sum_Ico_sq_norm_shapeSet)
  T3(u): 3-adic block tower  2 * E_P prod_{r: 3r+3 <= N(u)} rho_r, rho = #{q=q' mod 27}/|Q|^2, 3^{N(u)} <= 2^u
  C3(u): 3-adic interval sieve on the true Phi (Minkowski form, best split N)
  need(u): per-shell budget if the WeightedFourier budget (eps=1) is split evenly over the m shells, refined weights.
usage: python3 shells.py j0 sigma t |V|"""
import math, sys
AL = math.log2(3)
j0, sg, t, V = map(int, sys.argv[1:5]); m = sg + t + 1
b = [math.floor(j * AL) for j in range(j0 + 3)]
f = [dict() for _ in range(j0 + 1)]; f[0][0] = 1
for i in range(j0):
    for S, v in f[i].items():
        for S2 in range(S + 1, b[i + 1] + 1): f[i + 1][S2] = f[i + 1].get(S2, 0) + v
g = [dict() for _ in range(j0 + 1)]; g[j0][sg] = 1
for i in range(j0 - 1, -1, -1):
    for S in range(0, b[i] + 1):
        v = sum(g[i + 1].get(S2, 0) for S2 in range(S + 1, min(b[i + 1], sg) + 1))
        if v: g[i][S] = v
P = f[j0][sg]
def shapes(i, S, u):
    return [3 * 2 ** a + 2 ** c for c in range(u - 1) for a in range(c) if S + 1 + a <= b[i + 1] and S + 1 + c <= b[i + 2]]
def rho(Q):
    if len(Q) <= 1: return 1.0
    return sum(1 for q in Q for q2 in Q if (q - q2) % 27 == 0) / len(Q) ** 2
nb = j0 // 3
def block_dp(weight):  # sum over coarse block paths of prod weight(r,S,u)*... ; blocks r < nb, then remaining steps exact
    cur = {0: 1.0}
    for r in range(nb):
        i = 3 * r; new = {}
        for S, v in cur.items():
            for u in range(3, sg - S + 1):
                S3 = S + u
                if S3 > b[i + 3] or S3 not in g[i + 3]: continue
                Q = shapes(i, S, u)
                if not Q: continue
                new[S3] = new.get(S3, 0) + v * weight(r, S, u, Q)
        cur = new
    return sum(v * g[3 * nb][S] for S, v in cur.items())
def T2(u0): return block_dp(lambda r, S, u, Q: 1.0 if m - S - 1 <= u0 else len(Q)) / P
def T3(u0):
    N = int(u0 / AL)
    return min(1.0, 2 * block_dp(lambda r, S, u, Q: rho(Q) * len(Q) if 3 * r + 3 <= N else len(Q)) / P)
def C3(u0):
    best = 1.0
    for N in range(0, j0 + 1):
        r = sum(2.0 ** b[i] / 3 ** (i + 1) for i in range(N))
        if N and math.log2(2 * r) + N * AL > m: break
        mu = math.ceil(r) if N else 1; kap = mu * (1 + 2 * 3.0 ** N * (1 + N * math.log(3)) / 2.0 ** u0)
        T = sum(g[N][S] * min(p, math.sqrt(kap * p)) for S, p in f[N].items() if S in g[N]) / P
        best = min(best, T * T)
    return best / (1 - 2.0 ** -t)
print(f"j0={j0} sigma={sg} t={t} m={m} log2|P|={math.log2(P):.1f} |V|={V}  (log2 a_u; need = even split of eps=1 budget)")
for u0 in sorted(set(list(range(0, m, max(1, m // 16))) + [t, m - 1])):
    w = min(2 ** (u0 + 1), 2 ** t); need = V / (2 ** t * (1 + (sg + 1) / 2) * m * w)
    print(f" u={u0:3d}  T2={math.log2(T2(u0)):8.1f}  T3={math.log2(T3(u0)):8.1f}  C3={math.log2(C3(u0)):8.1f}  need={math.log2(need):7.1f}")
