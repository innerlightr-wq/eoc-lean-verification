"""Max depth ln(eta/|U|) of black cells on the confined path support (mass > 1e-15), environment xi (default 1).
usage: python3 depth_true.py J [xi]"""
import math, sys
AL = math.log2(3); J = int(sys.argv[1]); xi = int(sys.argv[2]) if len(sys.argv) > 2 else 1
sg = math.floor(J * AL); t = J // 6; m = sg + t + 1; top = [min(math.floor(i * AL), sg) for i in range(J + 1)]
F = [None] * (J + 1); F[0] = {0: 1}
for i in range(J):
    acc = 0; nx = {}
    for S2 in range(i + 1, top[i + 1] + 1):
        acc += F[i].get(S2 - 1, 0)
        if acc: nx[S2] = acc
    F[i + 1] = nx
G = [None] * (J + 1); G[J] = {sg: 1}
for i in range(J - 1, -1, -1):
    acc = 0; cur = {}
    for S in range(top[i + 1] - 1, i - 1, -1):
        acc += G[i + 1].get(S + 1, 0)
        if acc and S <= top[i]: cur[S] = acc
    G[i] = cur
Z = F[J][sg]; thr = Z >> 50
best = 0.0; nb = 0
for i in range(J):
    b = i + 1; qb = 3 ** b
    for S in F[i]:
        if S in G[i] and F[i][S] * G[i][S] > thr:
            v = xi * pow(2, -(m - S), qb) % qb; y = v if v <= qb // 2 else v - qb
            if 54 * abs(y) < qb:
                nb += 1; best = max(best, math.log(qb / (54 * abs(y))))
print(f"J={J} xi={xi if xi < 10**6 else 'big'}: black support cells {nb}, max depth ln(eta/|U|) = {best:.2f}")
