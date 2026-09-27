"""STEP 1 -- reproduce the greedy adversarial unit and dump its full local data.
usage: python3 step1_unit.py
Writes UNIT.txt (human) and unit.json-ish (pattern) for later steps."""
import json, math, sys
from common import Geom, Env, cell_xrange, row_values, ETA_DEN

J, K, SV = 400, 32, 3.0
XI = int(open("ADV_xi_400_8.txt").read().split()[0])
G = Geom(J)
print(f"J={J} R={G.R} sg={G.sg} t={G.t} m={G.m}  s={SV}  K={K}")
print(f"adversarial XI mod 3^{J} has {len(str(XI))} decimal digits; XI mod 3 = {XI % 3} (3-adic unit: {XI%3!=0})")

env = Env(G, XI, SV)
# full anchor scan (stride 1 over the range used by denseenv) to confirm the worst unit
worst = (-1e9, None)
for r0 in range(1, G.R - 2 * K, 4):
    v, S, _ = env.cw_at(r0, K)
    if v > worst[0]:
        worst = (v, (r0, S))
print(f"stride-4 anchor scan, K={K}: max CW = {worst[0]:.4f} at (r0,S) = {worst[1]}")
r0, S0 = worst[1]
# refine locally at stride 1
for rr in range(max(1, r0 - 6), r0 + 7):
    v, S, _ = env.cw_at(rr, K)
    if v > worst[0]:
        worst = (v, (rr, S))
r0, S0 = worst[1]
CWV = worst[0]
print(f"local stride-1 refinement: max CW = {CWV:.6f} at (r0,S) = ({r0},{S0})")

blocks = list(range(r0, r0 + 2 * K))
bmin, bmax = 2 * blocks[0] + 2, 2 * blocks[-1] + 2
print(f"window blocks r = {blocks[0]}..{blocks[-1]}, 3-adic levels b = {bmin}..{bmax} (step 2)")

# exact cells + depths
cells = []          # (a, b, black, depth, r, x)
perblock = []
for r in blocks:
    lo, hi = cell_xrange(G, r)
    b = 2 * r + 2
    qb = 3 ** b
    vals = row_values(G, r, lo, hi, XI)
    row = []
    for x in range(lo, hi + 1):
        y = vals[x]
        black = ETA_DEN * abs(y) < qb
        dep = math.log(qb / (ETA_DEN * abs(y))) if (black and y != 0) else (1e9 if y == 0 else 0.0)
        cells.append((G.m - x, b, black, dep, r, x))
        row.append(1 if black else 0)
    perblock.append((r, b, lo, hi, row))

nb = sum(1 for c in cells if c[2])
print(f"cells touched: {len(cells)}  black: {nb} ({nb/len(cells):.4f})  white: {len(cells)-nb}")
deps = [c[3] for c in cells if c[2]]
print(f"triangle depth over black cells: max {max(deps):.4f}  mean {sum(deps)/len(deps):.4f}  min {min(deps):.4f}")
hist = {}
for d in deps:
    hist[int(d)] = hist.get(int(d), 0) + 1
print("depth histogram (floor):", dict(sorted(hist.items())))

# per-block local weights: total row weight sum_x s^black and number of blacks per block
print("\nper-block: r, level b, x-range, #cells, #black, row weight sum_x s^black(x)")
lines = []
for (r, b, lo, hi, row) in perblock:
    wsum = sum(SV if t else 1.0 for t in row)
    lines.append(f"  r={r:3d} b={b:3d} x=[{lo},{hi}] n={len(row):3d} blk={sum(row):3d} W={wsum:8.2f} row={''.join(str(t) for t in row)}")
print("\n".join(lines[:12]))
print("  ...")
print("\n".join(lines[-4:]))

# M_K / M_2K values at the worst state
V1 = env.MK(r0, K); V2 = env.MK(r0, 2 * K)
print(f"\nM_K({r0},{K})[{S0}] = {V1[S0]:.6e}   M_2K[{S0}] = {V2[S0]:.6e}   CW = log2(ratio)/(2K) = {CWV:.6f}")

json.dump({"J": J, "K": K, "s": SV, "XI": str(XI), "r0": r0, "S0": S0, "CW": CWV,
           "m": G.m, "blocks": blocks,
           "pattern": [[r, b, lo, hi, row] for (r, b, lo, hi, row) in perblock]},
          open("unit.json", "w"))
print("\nwrote unit.json")
