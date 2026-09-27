"""TASK 1 -- adversarial population.  Full stride-1 pressure series P_j for every
(lambda, J, K), plus the per-block structural statistics needed by tasks 2,3,4,7.

P_j = max_S log2( M_2K(j)[S] / M_K(j)[S] ) / (2K)        (the local CW pressure)
theta_max = 0.137 ;  A_j = 1{P_j > theta_max} ;  a_N = (#A_j)/N.

Per block r we also record (exact 3-adic integer tests):
  pre[r]   = length of the leading all-black prefix of the readable row of block r
  nb[r]    = number of black readable cells in block r
  dep[r]   = max triangle depth ln(3^b/(54|y|)) over readable black cells  (float of exact ints)

usage: python3 t1_scan.py J K1,K2,... lam1,lam2,... TAG  -> press_<J>_<TAG>.json + stdout
"""
import json, math, sys, time
from tcommon import Geom, FastEnv, cell_xrange, row_values, ETA_DEN

THETA_MAX = 0.137
J = int(sys.argv[1])
KS = [int(x) for x in sys.argv[2].split(",")]
LAMS = [int(x) for x in sys.argv[3].split(",")]
TAG = sys.argv[4] if len(sys.argv) > 4 else "a"
SV = 3.0
G = Geom(J)
out = {"J": J, "R": G.R, "s": SV, "theta_max": THETA_MAX, "K": KS, "env": {}}
print(f"J={J} R={G.R} s={SV} theta_max={THETA_MAX}", flush=True)
print(f"{'lam':>6} {'K':>3} {'N':>5} {'A_N':>5} {'a_N':>9} {'maxP':>8} {'meanP':>8} "
      f"{'medP':>8} {'maxrun':>6}", flush=True)
for LAM in LAMS:
    t0 = time.time()
    env = FastEnv(G, LAM, SV)
    pre, nb, dep = [], [], []
    for r in range(G.R):
        lo, hi = cell_xrange(G, r)
        b = 2 * r + 2
        qb = 3 ** b
        v = row_values(G, r, lo, hi, LAM)
        k, run_ok, cnt, md = 0, True, 0, 0.0
        for x in range(lo, hi + 1):
            ay = abs(v[x])
            blk = ETA_DEN * ay < qb
            if blk:
                cnt += 1
                md = max(md, math.log(qb / (ETA_DEN * ay)) if ay else 1e9)
            if run_ok:
                if blk:
                    k += 1
                else:
                    run_ok = False
        pre.append(k)
        nb.append(cnt)
        dep.append(md)
    rec = {"pre": pre, "nblack": nb, "depth": dep, "P": {}}
    for K in KS:
        if 2 * K >= G.R - 1:
            continue
        sw = env.pressure_sweep(K)
        js = sorted(sw)
        Pv = [sw[j][0] for j in js]
        Sv = [sw[j][1] for j in js]
        rec["P"][str(K)] = {"j0": js[0], "P": Pv, "S": Sv}
        N = len(Pv)
        A = sum(1 for p in Pv if p > THETA_MAX)
        mx = max(Pv)
        mean = sum(Pv) / N
        med = sorted(Pv)[N // 2]
        best = cur = 0
        for p in Pv:
            cur = cur + 1 if p > THETA_MAX else 0
            best = max(best, cur)
        print(f"{LAM:>6} {K:>3} {N:>5} {A:>5} {A/N:>9.5f} {mx:>8.4f} {mean:>8.4f} "
              f"{med:>8.4f} {best:>6}", flush=True)
    out["env"][str(LAM)] = rec
    print(f"   # lam={LAM} done in {time.time()-t0:.1f}s", flush=True)
json.dump(out, open(f"press_{J}_{TAG}.json", "w"))
print(f"# wrote press_{J}_{TAG}.json")
