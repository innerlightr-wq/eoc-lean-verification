"""Copy of scratch/triangle_2026-09-15/rmax.py (left unmodified) with one bug fix and extra columns.

Bug in rmax.py: the random control unit xi = randrange(1, 3^(J+3)) | 1 may be divisible by 3 (seed 41:
J = 800 and J = 6400).  Then U(a, 1) = 0 for every a, the first corridor cell is 'black', and the apex
climb `while |U(aa+1, bb)| < eta` never terminates.  Fix (as in triangles.py): xi -> xi + 1 when 3 | xi
(the draw sequence is unchanged, so every other row reproduces rmax.py exactly), plus a climb cap.
The true (xi = 1) column is unaffected by the bug.

Extra columns: R_max/J, R_max/ln J, apex (a*, b*) of the maximal triangle, and s*/D* with
D* = a* ln2 + b* ln3 (the quantity Ridout / the p-adic Subspace Theorem forces to 0).
usage: python3 rmax_fixed.py J1 J2 ..."""
import math, random, sys, time
AL = math.log2(3); eta = 1 / 54; random.seed(41); CAP = 10 ** 6


def run(J, xi, offs=4):
    t = J // 6; m = math.floor(J * AL) + t + 1; best = (0.0, 0, 0); nb = 0; cells = 0; cache = {}

    def U(a, b):
        k = (a, b)
        if k not in cache:
            q = 3 ** b; r = xi * pow(2, -a, q) % q
            if r > q // 2: r -= q
            cache[k] = r / q
        return cache[k]
    for off in range(offs):
        for b in range(1, J + 1):
            a = m - round(AL * b) + off
            if a < 1: break
            cells += 1
            if abs(U(a, b)) < eta:
                nb += 1; aa, bb = a, b; n = 0
                while abs(U(aa + 1, bb)) < eta and n < CAP: aa += 1; n += 1
                while abs(U(aa, bb + 1)) < eta and n < CAP: bb += 1; n += 1
                assert n < CAP, "climb did not terminate"
                s = math.log(eta / abs(U(aa, bb)))
                if s > best[0]: best = (s, aa, bb)
    return cells, nb, best


print("J      cells  black   Rmax(true)  Rmax/J    Rmax/lnJ  apex(a*,b*)     s*/D*   | Rmax(rand) Rmax/lnJ  time")
for J in [int(x) for x in sys.argv[1:]]:
    t0 = time.time()
    c, nb, (rt, aa, bb) = run(J, 1)
    x = random.randrange(1, 3 ** (J + 3)) | 1
    x = x if x % 3 else x + 1
    _, _, (rr, _, _) = run(J, x)
    D = aa * math.log(2) + bb * math.log(3)
    print(f"{J:6d} {c:6d} {nb / c:.4f}  {rt:8.2f}   {rt / J:.5f}  {rt / math.log(J):.3f}    ({aa:5d},{bb:5d})  "
          f"{rt / D:.5f}  | {rr:8.2f}   {rr / math.log(J):.3f}   ({time.time() - t0:.0f}s)", flush=True)
