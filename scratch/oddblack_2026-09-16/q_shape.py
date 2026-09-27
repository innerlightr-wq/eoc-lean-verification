"""Part XXI: what predicts Q_r(S)?  Path-weighted mean of Q by headroom h = top[2r] - S, by position r/R, and by
the local triangle structure: k(S) = length of the run of black cells (m-S-1, 2r+2), (m-S-2, 2r+2), ... starting
at d = 1 (Q >= 1 - q^k exactly when the first k cells are black), and by the colour of the even cell (m-S, 2r+1).
usage: python3 q_shape.py J"""
import math, sys
from collections import defaultdict
AL = math.log2(3); p = 1 / AL; q = 1 - p
J = int(sys.argv[1]); R = J // 2; sg = math.floor(J * AL); t = J // 6; m = sg + t + 1
top = [min(math.floor(i * AL), sg) for i in range(J + 1)]
def blk(a, b):
    qb = 3 ** b; v = pow(2, -a, qb); y = v if v <= qb // 2 else v - qb; return 54 * abs(y) < qb
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
Z = F[J][sg]; sh = Z.bit_length() - 60
byh = defaultdict(lambda: [0.0, 0.0]); byk = defaultdict(lambda: [0.0, 0.0]); bypos = defaultdict(lambda: [0.0, 0.0])
byev = defaultdict(lambda: [0.0, 0.0])
for r in range(1, R):
    i = 2 * r
    for S in F[i]:
        if S not in G[i]: continue
        w = (F[i][S] * G[i][S] >> sh) / (Z >> sh)
        if w < 1e-14: continue
        cells = [blk(m - S - d, 2 * r + 2) for d in range(1, 41)]
        Q = sum(p * q ** (d - 1) for d in range(1, 41) if cells[d - 1])
        k = 0
        while k < 40 and cells[k]: k += 1
        h = top[i] - S; hb = h if h < 3 else (3 if h <= 5 else (6 if h <= 10 else (11 if h <= 20 else 21)))
        for dct, key in ((byh, hb), (byk, min(k, 5)), (bypos, int(10 * r / R)), (byev, blk(m - S, 2 * r + 1))):
            dct[key][0] += w * Q; dct[key][1] += w
fmt = lambda d: "  ".join(f"{k}: {v[0] / v[1]:.4f} (mass {v[1] / R:.3f})" for k, v in sorted(d.items()))
print(f"J={J}: path-weighted mean Q_r(S) by")
print("  headroom bin (0,1,2,3=3-5,6=6-10,11=11-20,21=>20):", fmt(byh))
print("  leading black run k (5 = >=5):                     ", fmt(byk))
print("  position tenth r/R:                                 ", fmt(bypos))
print("  colour of even cell (m-S, 2r+1) (True = black):     ", fmt(byev))
