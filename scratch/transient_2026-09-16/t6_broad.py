"""TASK 6 -- persistent-adversary search over a wide lambda range (try hard to falsify).

Two statistics per environment, both exact-3-adic-input / float-operator:

 (A) the additive per-block weight  w_r = (a_r - a_{r+1})/2 ,  a_r = log2 max_S M_{Rend-r}(r)[S].
     Its mean over any stretch is EXACTLY the long-product growth rate of that stretch
     (bits per ternary digit-step).  We report
        Lam_long                = mean over blocks [2, Rend-20)
        burst(L) = max_{r0} mean of w over [r0, r0+L)   for L = 8,16,32,64,128
     burst(L) > theta_max for a large L would be a PERSISTENT high-pressure stretch.
 (B) the CW window pressure P_j (K = 16), stride 1: max, count over theta_max, longest run.
     (only in mode "cw", which is ~10x more expensive)

Only lambda ODD and POSITIVE are scanned: lambda and 2*lambda give the same environment
up to a shift of m, and lambda and -lambda give IDENTICAL black patterns (blackness depends
on |y|), so the odd positives are a complete set of orbit representatives.

usage: python3 t6_broad.py MODE J LAM_LO LAM_HI STEP TAG
       MODE in {w, cw}
"""
import json, math, os, sys, time
from tcommon import Geom, FastEnv, cell_xrange, row_values, ETA_DEN

DIR = os.path.dirname(os.path.abspath(__file__))
THETA_MAX = 0.137
MODE = sys.argv[1]
J = int(sys.argv[2])
LO, HI, STEP = int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
TAG = sys.argv[6]
SV = 3.0
G = Geom(J)
Rend = G.R - 1
MARGIN = 20
LS = [8, 16, 32, 64, 128]
rows = []
t0 = time.time()
print(f"MODE={MODE} J={J} R={G.R} lambda = {LO}..{HI} step {STEP} (odd only)", flush=True)
print(f"{'lam':>7} {'Lam_long':>9} " + " ".join(f"b{L:<5}" for L in LS) +
      ("  " + f"{'maxP16':>7} {'n>th':>5} {'run':>4}" if MODE == "cw" else "") +
      f" {'pre6':>5} {'dbr':>4}", flush=True)
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
    w = [(a[r] - a[r + 1]) / 2.0 for r in range(Rend)]
    lo_r, hi_r = 2, Rend - MARGIN
    Lam_long = sum(w[lo_r:hi_r]) / (hi_r - lo_r)
    # prefix sums for sliding means
    ps = [0.0]
    for x in w:
        ps.append(ps[-1] + x)
    burst = {}
    for L in LS:
        best = -9.0
        for r0 in range(lo_r, hi_r - L + 1):
            v = (ps[r0 + L] - ps[r0]) / L
            if v > best:
                best = v
        burst[L] = best
    # structural census
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
    dbr = 0
    cur = 0
    for k in pre:
        cur = cur + 1 if k >= 6 else 0
        dbr = max(dbr, cur)
    rec = {"lam": LAM, "Lam_long": Lam_long, "burst": burst,
           "pre6": npre6, "dbr": dbr, "maxpre": max(pre)}
    extra = ""
    if MODE == "cw":
        sw = env.pressure_sweep(16)
        js = sorted(sw)
        Pv = [sw[j][0] for j in js]
        mx = max(Pv)
        nth = sum(1 for p in Pv if p > THETA_MAX)
        run = best = 0
        for p in Pv:
            run = run + 1 if p > THETA_MAX else 0
            best = max(best, run)
        rec.update({"maxP16": mx, "n_over": nth, "run": best,
                    "argmax": js[Pv.index(mx)]})
        extra = f"  {mx:>7.4f} {nth:>5} {best:>4}"
    rows.append(rec)
    print(f"{LAM:>7} {Lam_long:>9.5f} " + " ".join(f"{burst[L]:<6.4f}" for L in LS) +
          extra + f" {npre6:>5} {dbr:>4}", flush=True)
json.dump(rows, open(os.path.join(DIR, f"broad_{MODE}_{J}_{TAG}.json"), "w"))
print(f"# {len(rows)} lambda in {time.time()-t0:.0f}s -> broad_{MODE}_{J}_{TAG}.json")
