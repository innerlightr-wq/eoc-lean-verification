"""build and cache the per-block corpus used by tasks 4/5 (and re-used elsewhere).

Per block r of every true environment (lambda, J):
  a_r = log2 max_S M_{Rend-r}(r)[S],  a_Rend = 0,   w_r = (a_r - a_{r+1})/2
  => sum_{r0<=r<r1} w_r = (a_{r0}-a_{r1})/2 EXACTLY, and the mean of w over [r0,Rend)
     is exactly Lambda(r0, Rend-r0), the long-product growth rate (bits per digit-step).
  pre_r, nblack_r, depth_r : exact 3-adic structural statistics of block r
  phase_r = (top[2r+1]-top[2r], top[2r+2]-top[2r+1])  in {1,2}^2  (the geometry phase)

usage: python3 t4_corpus.py
"""
import json, math, os
from tcommon import Geom, FastEnv, cell_xrange, row_values, ETA_DEN

DIR = os.path.dirname(os.path.abspath(__file__))
LAMS = [1, 3, 5, 7, 9, 11, 13, 17, 19, 23, 25, 29, 31, 101, 1025]
JS = [400, 800]
SV = 3.0
CORP = []
for J in JS:
    G = Geom(J)
    Rend = G.R - 1
    for LAM in LAMS:
        env = FastEnv(G, LAM, SV)
        V = env.ones(Rend)
        a = [0.0] * (Rend + 1)
        for r in range(Rend - 1, -1, -1):
            V = env.apply_T(r, V)
            mx = max(V)
            a[r] = math.log2(mx) if mx > 0 else -1e9
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
                    md = max(md, math.log(qb / (ETA_DEN * ay)) if ay else 1e9)
                if ok:
                    if bl:
                        k += 1
                    else:
                        ok = False
            pre.append(k); nbl.append(cnt); dep.append(md)
        phase = [[G.top[2 * r + 1] - G.top[2 * r], G.top[2 * r + 2] - G.top[2 * r + 1]]
                 for r in range(G.R)]
        CORP.append({"J": J, "lam": LAM, "Rend": Rend, "w": w, "pre": pre,
                     "nblack": nbl, "depth": dep, "phase": phase,
                     "Lambda_long": a[2] / (2 * (Rend - 2))})
        print(f"J={J} lam={LAM:5d}: Lambda(2,{Rend-2}) = {a[2]/(2*(Rend-2)):.5f}  "
              f"w in [{min(w):.4f},{max(w):.4f}]", flush=True)
json.dump(CORP, open(os.path.join(DIR, "corpus.json"), "w"))
print(f"wrote corpus.json ({len(CORP)} environments)")
