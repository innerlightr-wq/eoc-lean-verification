"""Uniformity test: -log2|Phi_xi/P| for fixed 3-adic units xi under the critical confined law (sigma = b(J)), vs J."""
import math, random, sys
sys.setrecursionlimit(10000)
AL = math.log2(3); random.seed(9)

def run(J, sg, xis):
    b = [math.floor(j * AL) for j in range(J + 2)]
    g = [dict() for _ in range(J + 1)]; g[J][sg] = 1
    for i in range(J - 1, -1, -1):
        for S in range(0, b[i] + 1):
            v = sum(g[i + 1].get(S2, 0) for S2 in range(S + 1, min(b[i + 1], sg) + 1))
            if v: g[i][S] = v
    out = []
    for xi in xis:
        val = {sg: 1.0 + 0j}
        for i in range(J - 1, -1, -1):
            mod = 3 ** (i + 1); new = {}; S2s = sorted(val); suf = 0j; wt = 0; k = len(S2s)
            for S in sorted(g[i], reverse=True):
                while k > 0 and S2s[k - 1] > S:
                    k -= 1
                    if S2s[k] <= b[i + 1]: suf += g[i + 1][S2s[k]] * val[S2s[k]]; wt += g[i + 1][S2s[k]]
                if wt:
                    x = (xi * pow(2, S, mod) % mod) / mod
                    new[S] = suf / wt * complex(math.cos(2 * math.pi * x), math.sin(2 * math.pi * x))
            val = new
        out.append(-math.log2(abs(val[0])))
    return out
print("J   xi=1  xi=2  xi=-1/2  xi=2^-(t+1) [m=t+1, corner triangle]  xi=2^-(sigma+t+1) [true lambda=1]  random  (bits=-log2|Phi/P|)")
for J in (40, 60, 90, 120, 180, 240):
    MOD = 3 ** (J + 1); sg = math.floor(J * AL); t = J // 6
    xis = [1, 2, (-pow(2, -1, MOD)) % MOD, pow(2, -(t + 1), MOD), pow(2, -(sg + t + 1), MOD), random.randrange(1, MOD)]
    r = run(J, sg, xis); print(f"{J:3d} " + "  ".join(f"{v:7.1f}" for v in r))
