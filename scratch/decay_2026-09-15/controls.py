"""Parts VI, XVI: continuation characteristic function Gamma = E_{continuation from (N,S)} e(sum_{i>=N} theta_i(S_i)),
theta_i(S) = (xi 2^S mod 3^{i+1}) / 3^{i+1}  (3-adic reading of the Collatz phase; archimedean correction dropped).
Controls: true xi = lam * 2^{-m} (lam in [2^u, 2^{u+1})), random xi, frozen (continuation high digits zeroed), iid critical-tilt
continuation digits (unconfined) with true xi.  Reports log2 E|Gamma|^2 and amplitude rate per step vs continuation length L.
usage: python3 controls.py j0 sigma t u nsamp"""
import math, random, sys
AL = math.log2(3); random.seed(5)
J, sg, t, u, ns = map(int, sys.argv[1:6]); m = sg + t + 1; b = [math.floor(j * AL) for j in range(J + 2)]
MOD = 3 ** (J + 1); w = pow(2, -m, MOD)
f = [dict() for _ in range(J + 1)]; f[0][0] = 1
for i in range(J):
    for S, v in f[i].items():
        for S2 in range(S + 1, b[i + 1] + 1): f[i + 1][S2] = f[i + 1].get(S2, 0) + v
g = [dict() for _ in range(J + 1)]; g[J][sg] = 1
for i in range(J - 1, -1, -1):
    for S in range(0, b[i] + 1):
        v = sum(g[i + 1].get(S2, 0) for S2 in range(S + 1, min(b[i + 1], sg) + 1))
        if v: g[i][S] = v
def phase(xi, i, S): return (xi * pow(2, S, 3 ** (i + 1)) % 3 ** (i + 1)) / 3 ** (i + 1)
def gamma_conf(xi, N, S0):  # confined continuation (N,S0) -> (J,sg), uniform over continuations
    val = {sg: 1.0 + 0j}  # value at step J (no phase at step J: q uses i < J)
    for i in range(J - 1, N - 1, -1):
        new = {}
        for S in g[i]:
            if i == N and S != S0: continue
            tot = 0j; wt = 0
            for S2, v in val.items():
                if S2 > S and S2 <= b[i + 1]: tot += g[i + 1][S2] * v; wt += g[i + 1][S2]
            if wt: new[S] = tot / wt * complex(math.cos(2 * math.pi * phase(xi, i, S)), math.sin(2 * math.pi * phase(xi, i, S)))
        val = new
    return val[S0]
def gamma_iid(xi, N, S0, L):  # unconfined iid geometric(1/alpha) digits for L steps
    p = 1 / AL; q = 1 - p; dist = {S0: 1.0 + 0j}
    for i in range(N, N + L):
        new = {}
        for S, v in dist.items():
            ph = phase(xi, i, S); v2 = v * complex(math.cos(2 * math.pi * ph), math.sin(2 * math.pi * ph))
            for d in range(1, 30):
                pr = p * q ** (d - 1)
                if pr < 1e-12: break
                new[S + d] = new.get(S + d, 0) + v2 * pr
        dist = new
    return sum(dist.values())
print(f"j0={J} sigma={sg} m={m} u={u}: log2 E|Gamma|^2 (amplitude rate per step)")
for N in (7, 17, 27, 37, 47):
    S0 = max(g[N], key=lambda S: f[N].get(S, 0) * g[N][S]); L = J - N
    lams = random.sample(range(2 ** u, 2 ** (u + 1)), ns)
    res = {}
    for name in ("true", "random", "frozen", "iid"):
        acc = 0
        for lam in lams:
            if name == "true": xi = lam * w % MOD
            elif name == "random": xi = random.randrange(1, MOD)
            elif name == "frozen": x = (lam * w * pow(2, S0, 3 ** (N + 1))) % 3 ** (N + 1); xi = x * pow(2, -S0, MOD) % MOD
            else: xi = lam * w % MOD
            G = gamma_iid(xi, N, S0, L) if name == "iid" else gamma_conf(xi, N, S0)
            acc += abs(G) ** 2
        mv = acc / ns; res[name] = f"{math.log2(mv):7.1f} ({-math.log2(mv) / (2 * L):.3f})"
    print(f" N={N:2d} S={S0} L={L:2d}: " + "  ".join(f"{k}={v}" for k, v in res.items()))
