"""STEP 6 (concatenation) -- can the worst unit's DRIVER follow itself along ONE 3-adic phase?

The driver of the CW = 0.374 unit is the deep triangle occupying blocks 5..10: the readable rows
begin with all-black prefixes of lengths 6,7,8,9,10,12.  We ask EXACTLY, with the same level-by-level
sieve, whether there is a 3-adic xi whose pattern has that driver repeated with period P blocks,
i.e. blocks r0+P k + j (j = 0..5) begin with an all-black prefix of length L_j, all other cells FREE.
A nonempty answer means the high-pressure unit is self-concatenable by a genuine environment, so the
compatibility graph has a cycle of mean >= the periodic environment's long-product growth, which we
then measure.

usage: python3 step6b_periodic.py [P] [NREP] [CAP]
"""
import json, math, sys
from common import Geom, Env, cell_xrange, ETA_DEN

P = int(sys.argv[1]) if len(sys.argv) > 1 else 6
NREP = int(sys.argv[2]) if len(sys.argv) > 2 else 20
CAP = int(sys.argv[3]) if len(sys.argv) > 3 else 20_000_000

J, SV = 400, 3.0
G = Geom(J)
U = json.load(open("unit.json"))
r0 = U["r0"]
PREF = [6, 7, 8, 9, 10, 12]     # leading all-black prefix lengths of blocks 5..10

# target rows: -1 = free
targ = {}
rmax = r0 + P * (NREP - 1) + 5
if rmax >= G.R - 1:
    NREP = (G.R - 2 - r0 - 5) // P + 1
    rmax = r0 + P * (NREP - 1) + 5
for k in range(NREP):
    for j in range(6):
        r = r0 + P * k + j
        lo, hi = cell_xrange(G, r)
        n = hi - lo + 1
        row = [-1] * n
        for i in range(min(PREF[j], n)):
            row[i] = 1
        targ[r] = (lo, row)
print(f"period P={P}, {NREP} repetitions, blocks {r0}..{rmax}, levels {2*r0+2}..{2*rmax+2}")
print(f"constrained cells: {sum(sum(1 for t in v[1] if t>=0) for v in targ.values())}")


def filt(b, lo, row, cands):
    qb = 3 ** b
    half = qb // 2
    inv = pow(2, -(G.m - lo), qb)
    out = []
    n = len(row)
    for v in cands:
        rr = v * inv % qb
        ok = True
        for i in range(n):
            t = row[i]
            if t >= 0:
                y = rr if rr <= half else rr - qb
                if (ETA_DEN * (y if y >= 0 else -y) < qb) != t:
                    ok = False
                    break
            rr += rr
            if rr >= qb:
                rr -= qb
        if ok:
            out.append(v)
    return out


b0 = 2 * r0 + 2
cands = [v for v in range(3 ** b0) if v % 3]   # 3-adic UNITS only (v=0 blackens every cell trivially)
prev = 0
hist = []
dead = None
for r in range(r0, rmax + 1):
    b = 2 * r + 2
    if prev:
        qp = 3 ** prev
        step = b - prev
        if len(cands) * 3 ** step > CAP:
            print(f"  !! level {b}: {len(cands)*3**step} lifts exceed CAP; abort")
            dead = "cap"
            break
        cands = [v + j * qp for v in cands for j in range(3 ** step)]
    if r in targ:
        lo, row = targ[r]
        cands = filt(b, lo, row, cands)
    hist.append((r, b, len(cands)))
    prev = b
    if r in targ and (r - r0) % P == 0:
        print(f"  after driver copy #{(r-r0)//P}: level b={b:3d} survivors {len(cands)}", flush=True)
    if not cands:
        print(f"  *** EMPTY at block r={r} (level b={b}): the driver CANNOT repeat at period {P}")
        dead = "empty"
        break

print(f"\nfinal: {len(cands)} surviving residues mod 3^{prev}  (density {len(cands)/3**prev:.3e})")
if cands and dead is None:
    xi = cands[0]
    print(f"  explicit periodic-driver phase xi mod 3^{prev} = {xi}")
    env = Env(G, xi, SV)
    v32, S32, _ = env.cw_at(r0, 32)
    print(f"  CW(r0={r0},K=32) of this periodic environment = {v32:.4f}   (theta_max 0.137)")
    for L in (16, 32, 64, 96, 128):
        if r0 + L < G.R - 1:
            V = env.MK(r0, L)
            print(f"    Lambda(r0,{L}) = (1/2L)log2 max_S M_L = {math.log2(max(V.values()))/(2*L):.4f}")
    # verify the driver really repeats
    okrep = all(all(t < 0 or ((ETA_DEN * abs(y) < 3 ** (2 * r + 2)) == bool(t))
                    for t, y in zip(targ[r][1],
                                    [((xi * pow(2, -(G.m - targ[r][0] - i), 3 ** (2 * r + 2))) % 3 ** (2 * r + 2))
                                     for i in range(len(targ[r][1]))]))
                for r in targ)
    print(f"  (driver-repetition re-verified independently: {okrep})")
json.dump({"P": P, "NREP": NREP, "hist": hist, "n_final": len(cands),
           "xi": str(cands[0]) if cands else None, "b_final": prev}, open(f"per_{P}.json", "w"))
