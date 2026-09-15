"""Parts XXX-XXXII: R_max along the critical corridor band (offsets 0..3), eta = 1/54, true (xi=1) vs random unit.
size of a black cell's maximal triangle = ln(eta/|U(apex)|); R_max - ln(#cells) as Gumbel check (random model: ~ ln(2 eta) + Gumbel)."""
import math, random, sys, time
AL = math.log2(3); eta = 1 / 54; random.seed(41)
def run(J, xi, offs=4):
    t = J // 6; m = math.floor(J * AL) + t + 1; best = 0; nb = 0; cells = 0; cache = {}
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
                nb += 1; aa, bb = a, b
                while abs(U(aa + 1, bb)) < eta: aa += 1
                while abs(U(aa, bb + 1)) < eta: bb += 1
                best = max(best, math.log(eta / abs(U(aa, bb))))
    return cells, nb, best
print("J      cells  black   Rmax(true)  Rmax-ln(cells)   | Rmax(random) Rmax-ln(cells)   Rmax/lnJ(true)")
for J in [int(x) for x in sys.argv[1:]]:
    t0 = time.time(); c, nb, rt = run(J, 1); _, _, rr = run(J, random.randrange(1, 3 ** (J + 3)) | 1)
    print(f"{J:6d} {c:6d} {nb/c:.4f}  {rt:8.2f}   {rt - math.log(c):+7.2f}        | {rr:8.2f}   {rr - math.log(c):+7.2f}     {rt / math.log(J):.3f}   ({time.time() - t0:.0f}s)", flush=True)
