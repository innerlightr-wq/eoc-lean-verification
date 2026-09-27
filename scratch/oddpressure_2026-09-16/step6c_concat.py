"""STEP 6 (concatenation, depth-capped) -- can the worst unit's driver follow ITSELF along one
genuine 3-adic phase, with the triangle depth still capped?

The driver is the exact 6-row core of the CW = 0.374 unit (blocks 5..10 of XI_adv):
  1111110 / 11111110 / 111111110 / 1111111110 / 111111111100 / 1111111111110
The terminating WHITE cells are part of the target: they are what caps the triangle depth at ~8.
We sieve exactly for a 3-adic unit whose pattern carries this core at blocks r0+Pk+j (all other
cells free), for k = 0..NREP-1.  Free levels are lifted exhaustively while the candidate list fits
in CAP; above CAP the list is randomly subsampled -- any survivor is then still a *genuine* phase
(existence stays exact, only the counts become lower bounds).

usage: python3 step6c_concat.py P NREP [CAP] [SEED]
"""
import json, math, random, sys
from common import Geom, Env, cell_xrange, row_values, ETA_DEN

P = int(sys.argv[1]); NREP = int(sys.argv[2])
CAP = int(sys.argv[3]) if len(sys.argv) > 3 else 4_000_000
random.seed(int(sys.argv[4]) if len(sys.argv) > 4 else 12345)

J, SV = 400, 3.0
G = Geom(J)
U = json.load(open("unit.json"))
r0 = U["r0"]
CORE = [p[4] for p in U["pattern"][:6]]          # exact rows of blocks 5..10 (incl. terminating whites)
print("driver core rows (blocks %d..%d):" % (r0, r0 + 5))
for j, c in enumerate(CORE):
    print(f"   j={j}: {''.join(map(str,c))}")

targ = {}
k = 0
while True:
    r = r0 + P * k + 5
    if r >= G.R - 2:
        break
    for j in range(6):
        rr_ = r0 + P * k + j
        lo, hi = cell_xrange(G, rr_)
        n = hi - lo + 1
        row = [-1] * n
        for i in range(min(len(CORE[j]), n)):
            row[i] = CORE[j][i]
        targ[rr_] = (lo, row)
    k += 1
    if k >= NREP:
        break
NREP = k
rmax = max(targ)
ncon = sum(sum(1 for t in v[1] if t >= 0) for v in targ.values())
print(f"\nperiod P={P}, {NREP} driver copies, blocks {r0}..{rmax}, levels {2*r0+2}..{2*rmax+2}, "
      f"{ncon} constrained cells")


def filt(b, lo, row, cands):
    qb = 3 ** b; half = qb // 2; inv = pow(2, -(G.m - lo), qb); out = []
    n = len(row)
    for v in cands:
        rr = v * inv % qb; ok = True
        for i in range(n):
            t = row[i]
            if t >= 0:
                y = rr if rr <= half else rr - qb
                if (ETA_DEN * (y if y >= 0 else -y) < qb) != t:
                    ok = False; break
            rr += rr
            if rr >= qb: rr -= qb
        if ok: out.append(v)
    return out


b0 = 2 * r0 + 2
cands = [v for v in range(3 ** b0) if v % 3]
logdrop = 0.0            # log3 of (sampled fraction) accumulated, for a density lower bound
prev = 0
for r in range(r0, rmax + 1):
    b = 2 * r + 2
    if prev:
        qp = 3 ** prev; step = b - prev
        cands = [v + j * qp for v in cands for j in range(3 ** step)]
        if len(cands) > CAP:
            f = CAP / len(cands)
            cands = random.sample(cands, CAP)
            logdrop += math.log(f)
    if r in targ:
        cands = filt(b, *targ[r], cands)
    prev = b
    if r in targ and (r - r0) % P == 0:
        print(f"  after driver copy #{(r-r0)//P:2d}: level b={b:3d}  survivors {len(cands)}", flush=True)
    if not cands:
        print(f"  *** EMPTY at block r={r} (level b={b}): driver cannot repeat at period {P}")
        break

print(f"\nsurvivors mod 3^{prev}: {len(cands)}  (subsampling factor applied: e^{logdrop:.1f})")
if not cands:
    sys.exit(0)
xi = random.choice(cands)
print(f"explicit repeating phase xi (unit, xi mod 3 = {xi%3}), {len(str(xi))} decimal digits")

# ---- independent re-verification with CENTERED residues ----------------------
bad = []
for r, (lo, row) in sorted(targ.items()):
    b = 2 * r + 2; qb = 3 ** b
    vals = row_values(G, r, lo, lo + len(row) - 1, xi)
    for i, t in enumerate(row):
        if t < 0: continue
        if (ETA_DEN * abs(vals[lo + i]) < qb) != bool(t):
            bad.append((r, lo + i))
print(f"independent verification of all {ncon} constrained cells: "
      f"{'OK - the driver really repeats' if not bad else 'MISMATCH ' + str(bad[:5])}")

# ---- depth and pressure of the repeating environment -------------------------
env = Env(G, xi, SV)
md = 0.0; nbl = 0; ncell = 0
for r in range(r0, min(rmax, G.R - 2) + 1):
    lo, hi = cell_xrange(G, r); b = 2 * r + 2; qb = 3 ** b
    for x, y in row_values(G, r, lo, hi, xi).items():
        ncell += 1
        if ETA_DEN * abs(y) < qb:
            nbl += 1
            md = max(md, math.log(qb / (ETA_DEN * abs(y))))
print(f"black fraction over blocks {r0}..{rmax}: {nbl}/{ncell} = {nbl/ncell:.4f}; "
      f"max triangle depth = {md:.2f}")
v32, S32, _ = env.cw_at(r0, 32)
print(f"CW(r0={r0},K=32) = {v32:.4f}   (theta_max = 0.137; adversary's single unit {U['CW']:.4f})")
out = []
for L in (16, 32, 64, 96, 128, 160, 190):
    if r0 + L < G.R - 1:
        V = env.MK(r0, L)
        out.append((L, math.log2(max(V.values())) / (2 * L)))
print("long-product growth Lambda(r0,L) = " + "  ".join(f"L={L}:{v:.4f}" for L, v in out))
print(f"MAX CYCLE MEAN estimate for this periodic unit: Lambda -> {out[-1][1]:.4f} bits/step")
json.dump({"P": P, "NREP": NREP, "n": len(cands), "b": prev, "xi": str(xi),
           "cw32": v32, "lambda": out, "maxdepth": md, "blackfrac": nbl / ncell},
          open(f"concat_{P}.json", "w"))
