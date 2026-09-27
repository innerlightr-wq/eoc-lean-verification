"""STEPS 4+5 -- true-environment (low-frequency lambda) CW scan, with the triangle-depth
profile of every window recorded, so the depth-conditioned maximum can be read off.

For each (lambda, J, K, anchor r0) we record
   CW(r0)      = max_S log2(M_2K(r0)[S]/M_K(r0)[S]) / (2K)         (floating point)
   depth(r0)   = max over black cells the window can read of ln(3^b/(54|y|))  (exact 3-adic input)
   nblack(r0)  = number of black cells in the window
usage: python3 step45_scan.py J K1,K2,.. stride lam1,lam2,..  > OUT
"""
import json, math, sys
from common import Geom, Env, cell_xrange, row_values, ETA_DEN

J = int(sys.argv[1])
KS = [int(x) for x in sys.argv[2].split(",")]
STR = int(sys.argv[3])
LAMS = [int(x) for x in sys.argv[4].split(",")]
SV = 3.0
G = Geom(J)
rows = []
for LAM in LAMS:
    env = Env(G, LAM, SV)
    # exact per-block depth data (independent of K)
    bdep = []   # max depth of a black cell readable in block r ; and count
    for r in range(G.R):
        lo, hi = cell_xrange(G, r)
        b = 2 * r + 2
        qb = 3 ** b
        md = 0.0
        nb = 0
        for x, y in row_values(G, r, lo, hi, LAM).items():
            ay = abs(y)
            if ETA_DEN * ay < qb:
                nb += 1
                md = max(md, math.log(qb / (ETA_DEN * ay)) if ay else 1e9)
        bdep.append((md, nb))
    for K in KS:
        if 2 * K + 2 >= G.R:
            continue
        best = (-1e9, None)
        for r0 in range(1, G.R - 2 * K, STR):
            v, S, _ = env.cw_at(r0, K)
            w = bdep[r0:r0 + 2 * K]
            dep = max(d for d, _ in w)
            nbl = sum(n for _, n in w)
            rows.append({"lam": LAM, "J": J, "K": K, "r0": r0, "S": S, "cw": v,
                         "depth": dep, "nblack": nbl})
            if v > best[0]:
                best = (v, (r0, S, dep))
        print(f"lam={LAM:5d} J={J} K={K}: max CW = {best[0]:.4f} at (r0,S)={best[1][:2]} "
              f"window max depth {best[1][2]:.2f}", flush=True)
json.dump(rows, open(f"scan_{J}.json", "w"))
print(f"# wrote scan_{J}.json ({len(rows)} windows)")
