"""SPINE TASK 1 (data collection) -- exact additive block weights w_r over many environments.

Reuses the VERIFIED engine scratch/transient_2026-09-16/tcommon.py unchanged.

For every low-frequency environment lambda (odd) at digit-length J:
    a_r = log2 max_S M_{Rend-r}(r)[S],  a_Rend = 0,  Rend = R-1 = J//2 - 1
    w_r = (a_r - a_{r+1})/2      (so sum_{r0<=r<r1} w_r = (a_{r0}-a_{r1})/2 EXACTLY)
plus the exact 3-adic structural statistics of each block:
    nblack[r], pre[r] (leading black run), depth[r] (max triangle depth, float of exact ints)
and the ARGMAX column S of the sweep vector at each block (structural fingerprint of the
extremal state).

usage: python3 s1_scan.py J LAMLO LAMHI SHARD NSHARD TAG
"""
import json, math, os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tcommon import Geom, FastEnv, cell_xrange, row_values, ETA_DEN

J = int(sys.argv[1]); LLO = int(sys.argv[2]); LHI = int(sys.argv[3])
SH = int(sys.argv[4]); NSH = int(sys.argv[5]); TAG = sys.argv[6]
SV = 3.0
DIR = os.path.dirname(os.path.abspath(__file__))

G = Geom(J)
Rend = G.R - 1
lams = [l for l in range(LLO, LHI + 1, 2) if (l // 2) % NSH == SH]
OUT = {"J": J, "R": G.R, "Rend": Rend, "s": SV, "env": {}}
t0 = time.time()
for LAM in lams:
    env = FastEnv(G, LAM, SV)
    V = env.ones(Rend)
    a = [0.0] * (Rend + 1)
    arg = [0] * (Rend + 1)
    for r in range(Rend - 1, -1, -1):
        V = env.apply_T(r, V)
        mx = -1.0; mi = 0
        for i, x in enumerate(V):
            if x > mx:
                mx = x; mi = i
        a[r] = math.log2(mx) if mx > 0 else -1e9
        arg[r] = env.slo[r] + mi
    w = [(a[r] - a[r + 1]) / 2.0 for r in range(Rend)]
    pre, nbl, dep = [], [], []
    for r in range(G.R):
        lo, hi = cell_xrange(G, r)
        b = 2 * r + 2
        qb = 3 ** b
        v = row_values(G, r, lo, hi, LAM)
        k, ok, cnt, md = 0, True, 0, 0.0
        for x in range(lo, hi + 1):
            ay = abs(v[x])
            bl = ETA_DEN * ay < qb
            if bl:
                cnt += 1
                d = math.log(qb / (ETA_DEN * ay)) if ay else 1e9
                if d > md:
                    md = d
            if ok:
                if bl:
                    k += 1
                else:
                    ok = False
        pre.append(k); nbl.append(cnt); dep.append(round(md, 6))
    OUT["env"][str(LAM)] = {"w": [round(x, 12) for x in w], "arg": arg,
                            "pre": pre, "nblack": nbl, "depth": dep,
                            "Lambda_long": a[2] / (2 * (Rend - 2))}
p = os.path.join(DIR, f"s1_w_{J}_{TAG}.json")
json.dump(OUT, open(p, "w"))
print(f"# wrote {p}: {len(lams)} envs in {time.time()-t0:.1f}s", flush=True)
