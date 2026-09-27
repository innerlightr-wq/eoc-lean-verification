"""TASK 6 (falsification attempt, sharpest form) -- the unpaid-excess constant C(theta)
over a WIDE lambda range and several J.

For each true low-frequency environment (lambda odd, XI = lambda, geometry J):
   w_r = (a_r - a_{r+1})/2   with a_r = log2 max_S M_{Rend-r}(r)[S],  a_Rend = 0
   C(theta) = max_{r0<r1} sum_{r0<=r<r1} (w_r - theta)      (Kadane, exact max subarray)
   Lam_long = mean of w over [2, Rend-20)
   burst(L) = max over r0 of the L-block mean of w
A LARGE C, or a burst(L) above theta at a large L, would falsify the transience hypothesis.

usage: python3 t6c_Cscan.py J LAM_LO LAM_HI STEP TAG
"""
import json, math, os, sys, time
from tcommon import Geom, FastEnv, cell_xrange, row_values, ETA_DEN

DIR = os.path.dirname(os.path.abspath(__file__))
TH = 0.137
J, LO, HI, STEP, TAG = (int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]),
                        int(sys.argv[4]), sys.argv[5])
SV = 3.0
G = Geom(J)
Rend = G.R - 1
MARGIN = 20
LS = [16, 24, 32, 48, 64, 128]


def kadane(xs):
    best = cur = 0.0
    bi = bj = ci = 0
    for i, x in enumerate(xs):
        if cur + x > x:
            cur += x
        else:
            cur, ci = x, i
        if cur > best:
            best, bi, bj = cur, ci, i + 1
    return best, bi, bj


rows = []
t0 = time.time()
print(f"J={J} R={G.R} lambda {LO}..{HI} step {STEP} (odd only), theta = {TH}", flush=True)
print(f"{'lam':>7} {'Lam_long':>9} {'C(.137)':>9} {'C(.10)':>8} " +
      " ".join(f"b{L:<5}" for L in LS) + f" {'pre6':>5} {'dbr':>4}", flush=True)
for LAM in range(LO, HI + 1, STEP):
    if LAM % 2 == 0:
        continue
    env = FastEnv(G, LAM, SV)
    V = env.ones(Rend)
    a = [0.0] * (Rend + 1)
    for r in range(Rend - 1, -1, -1):
        V = env.apply_T(r, V)
        mx = max(V)
        a[r] = math.log2(mx) if mx > 0 else -1e9
    w = [(a[r] - a[r + 1]) / 2.0 for r in range(Rend)][2:Rend - MARGIN]
    C1, i1, j1 = kadane([x - TH for x in w])
    C2, _, _ = kadane([x - 0.10 for x in w])
    Lam = sum(w) / len(w)
    ps = [0.0]
    for x in w:
        ps.append(ps[-1] + x)
    burst = {}
    for L in LS:
        burst[L] = max(((ps[b + L] - ps[b]) / L for b in range(len(w) - L)), default=-9.0)
    pre = []
    for r in range(G.R):
        lo, hi = cell_xrange(G, r)
        b = 2 * r + 2
        qb = 3 ** b
        v = row_values(G, r, lo, hi, LAM)
        k = 0
        for x in range(lo, hi + 1):
            if ETA_DEN * abs(v[x]) < qb:
                k += 1
            else:
                break
        pre.append(k)
    npre6 = sum(1 for k in pre if k >= 6)
    dbr = cur = 0
    for k in pre:
        cur = cur + 1 if k >= 6 else 0
        dbr = max(dbr, cur)
    rows.append({"lam": LAM, "Lam": Lam, "C137": C1, "C10": C2, "arg": [i1 + 2, j1 + 2],
                 "burst": burst, "pre6": npre6, "dbr": dbr})
    print(f"{LAM:>7} {Lam:>9.5f} {C1:>9.4f} {C2:>8.4f} " +
          " ".join(f"{burst[L]:<6.4f}" for L in LS) + f" {npre6:>5} {dbr:>4}", flush=True)
json.dump(rows, open(os.path.join(DIR, f"cscan_{J}_{TAG}.json"), "w"))
print(f"# {len(rows)} lambda in {time.time()-t0:.0f}s -> cscan_{J}_{TAG}.json")
