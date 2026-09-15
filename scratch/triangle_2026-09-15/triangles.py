"""Parts XVII-XXIII, XXXIX-XLIII: Tao-black triangles of the universal array U(a,b) = centered(xi * 2^{-a} mod 3^b)/3^b
along corridors a(b) = m - round(slope * b), b = 1..J, and along sampled confined paths (a = m - S_i, b = i + 1).
Black: |U| < eta.  Apex of the maximal triangle containing a black cell: climb a+1 while black, then b+1 while black
(Tao's up-then-left).  Size s = ln(eta / |U(apex)|).  Height = b_apex - b_entry (levels the monotone path can stay inside).
usage: python3 triangles.py J t eta mode   (mode: corridor | paths)"""
import math, random, sys
from collections import Counter
AL = math.log2(3); random.seed(23)
J, t = int(sys.argv[1]), int(sys.argv[2]); eta = float(sys.argv[3]); mode = sys.argv[4]
sg = math.floor(J * AL); m = sg + t + 1
cache = {}
def U(xi, a, b):
    k = (xi, a, b)
    if k not in cache:
        q = 3 ** b; r = xi * pow(2, -a, q) % q
        if r > q // 2: r -= q
        cache[k] = r / q
    return cache[k]
def apex(xi, a, b):
    while abs(U(xi, a + 1, b)) < eta: a += 1
    while abs(U(xi, a, b + 1)) < eta: b += 1
    return a, b, math.log(eta / abs(U(xi, a, b)))
def corridor(xi, slope, offset=0):
    black = 0; tri = {}; occ = Counter()
    for b in range(1, J + 1):
        a = m - round(slope * b) + offset
        if a < 1: break
        if abs(U(xi, a, b)) < eta:
            black += 1; A = apex(xi, a, b); tri[A[:2]] = A[2]; occ[A[:2]] += 1
    sizes = sorted(tri.values(), reverse=True)
    big = lambda R: sum(occ[k] for k, s in tri.items() if s >= R) / J
    return black / J, sizes[:3], len(tri), big(3), big(6), big(10)
rxi = [random.randrange(1, 3 ** (J + 5)) for _ in range(3)]
rxi = [x if x % 3 else x + 1 for x in rxi]
if mode == "corridor":
    print(f"J={J} t={t} m={m} eta={eta}: black fraction | top-3 sizes | #triangles | occupation by size>=3,6,10")
    conv = [(19, 12), (65, 41), (84, 53), (485, 306)]
    for name, xi, slope in ([("true alpha", 1, AL), ("true alpha-0.05", 1, AL - 0.05), ("true alpha+0.05", 1, AL + 0.05)]
                            + [(f"true p/q={p}/{q}", 1, p / q) for p, q in conv]
                            + [(f"random{k} alpha", rxi[k], AL) for k in range(3)]):
        res = [corridor(xi, slope, off) for off in (0, 7, 23)]
        bf = sum(r[0] for r in res) / 3; top = max(max(r[1] or [0]) for r in res); nt = sum(r[2] for r in res) / 3
        o3, o6, o10 = (sum(r[i] for r in res) / 3 for i in (3, 4, 5))
        print(f"  {name:22s} black={bf:.4f} max size={top:5.2f} #tri={nt:6.1f} occ>=3:{o3:.4f} >=6:{o6:.4f} >=10:{o10:.4f}")
else:
    W = sg + 2; g = [None] * (J + 1); g[J] = [0] * W; g[J][sg] = 1
    b_ = [math.floor(j * AL) for j in range(J + 2)]
    for i in range(J - 1, -1, -1):
        row = [0] * W; acc = 0; top = min(b_[i + 1], sg)
        for S2 in range(top, 0, -1):
            acc += g[i + 1][S2]
            if S2 - 1 <= b_[i]: row[S2 - 1] = acc
        g[i] = row
    def path():
        S = [0]
        for i in range(J):
            s0 = S[-1]; top = min(b_[i + 1], sg); tot = sum(g[i + 1][s0 + 1: top + 1]); x = random.randrange(tot)
            for S2 in range(s0 + 1, top + 1):
                if x < g[i + 1][S2]: S.append(S2); break
                x -= g[i + 1][S2]
        return S
    for name, xi in (("true", 1), ("random", rxi[0])):
        blk = 0; steps = 0; ratios = Counter(); visits = 0; sizes = []
        for _ in range(int(sys.argv[5]) if len(sys.argv) > 5 else 40):
            S = path(); cur = None; enter = None
            for i in range(J):
                a, b = m - S[i], i + 1; steps += 1
                if abs(U(xi, a, b)) < eta:
                    blk += 1; A = apex(xi, a, b)
                    if cur != A[:2]:
                        if cur is not None: visits += 1
                        cur = A[:2]; enter = i; hgt = A[1] - b + 1; sizes.append(A[2])
                    last = i
                else:
                    if cur is not None:
                        dur = last - enter + 1
                        for R, lab in ((3, "s<3"), (6, "3-6"), (10, "6-10"), (1e9, ">10")):
                            if sizes[-1] < R: ratios[(lab, round(min(dur / max(hgt, 1), 1.0), 1))] += 1; break
                    cur = None
        print(f"{name}: black step fraction {blk / steps:.4f}; triangle visits {len(sizes)}; size quantiles "
              f"{[round(q, 2) for q in (sorted(sizes)[len(sizes) // 2], sorted(sizes)[int(0.9 * len(sizes))], max(sizes))] if sizes else []}")
        for lab in ("s<3", "3-6", "6-10", ">10"):
            tot = sum(v for (l, r), v in ratios.items() if l == lab)
            if tot:
                full = sum(v for (l, r), v in ratios.items() if l == lab and r >= 0.75) / tot
                print(f"   size {lab:5s}: visits {tot:5d}, fraction staying >= 0.75 of available height: {full:.3f}")
