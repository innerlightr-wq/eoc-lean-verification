"""How does the crossover length L*(theta) depend on J?

L*(theta; J) = smallest L such that for EVERY environment in the tested set and EVERY anchor,
the exact L-block mean of w is <= theta.   (w_r = (a_r - a_{r+1})/2, so the L-block mean is
exactly the long-product growth rate of those L blocks, in bits per ternary digit-step.)

Also reports C(theta) = max subarray of (w_r - theta) per (J, lambda).

usage: python3 t3c_Lstar.py J lam1,lam2,... TAG
"""
import json, math, os, sys, time
from tcommon import Geom, FastEnv

DIR = os.path.dirname(os.path.abspath(__file__))
TH = 0.137
J = int(sys.argv[1])
LAMS = [int(x) for x in sys.argv[2].split(",")]
TAG = sys.argv[3]
MARGIN = 20
G = Geom(J)
Rend = G.R - 1
GRID = list(range(4, 129, 2)) + [144, 160, 192, 224, 256, 320, 384]


def kadane(xs):
    best = cur = 0.0
    for x in xs:
        cur = cur + x if cur + x > x else x
        if cur > best:
            best = cur
    return best


agg = {L: (-9.0, None) for L in GRID}
rows = []
print(f"J={J} R={G.R} Rend={Rend}, theta={TH}", flush=True)
print(f"{'lam':>7} {'Lam_long':>9} {'C(.137)':>9} {'L*(.137)':>9} {'L*(.10)':>8} "
      f"{'maxmean@64':>11} {'@128':>8}", flush=True)
for LAM in LAMS:
    t0 = time.time()
    env = FastEnv(G, LAM, 3.0)
    V = env.ones(Rend)
    a = [0.0] * (Rend + 1)
    for r in range(Rend - 1, -1, -1):
        V = env.apply_T(r, V)
        mx = max(V)
        a[r] = math.log2(mx) if mx > 0 else -1e9
    w = [(a[r] - a[r + 1]) / 2.0 for r in range(Rend)][2:Rend - MARGIN]
    ps = [0.0]
    for x in w:
        ps.append(ps[-1] + x)
    C = kadane([x - TH for x in w])
    best = {}
    for L in GRID:
        if L >= len(w):
            continue
        b = max((ps[i + L] - ps[i]) / L for i in range(len(w) - L + 1))
        best[L] = b
        if b > agg[L][0]:
            agg[L] = (b, LAM)
    Ls = next((L for L in GRID if L in best and all(best[M] <= TH for M in GRID
                                                    if M in best and M >= L)), None)
    L10 = next((L for L in GRID if L in best and all(best[M] <= 0.10 for M in GRID
                                                     if M in best and M >= L)), None)
    rows.append({"lam": LAM, "Lam": sum(w) / len(w), "C137": C, "Lstar": Ls,
                 "Lstar10": L10, "best": best})
    print(f"{LAM:>7} {sum(w)/len(w):>9.5f} {C:>9.4f} {str(Ls):>9} {str(L10):>8} "
          f"{best.get(64, float('nan')):>11.5f} {best.get(128, float('nan')):>8.5f}"
          f"   ({time.time()-t0:.0f}s)", flush=True)

print(f"\nENVELOPE over the {len(LAMS)} environments at J={J}:")
print(f"  {'L':>5} {'max mean rate':>14} {'lam':>7} {'>0.137?':>8}")
for L in GRID:
    if agg[L][1] is None:
        continue
    print(f"  {L:>5} {agg[L][0]:>14.5f} {agg[L][1]:>7} "
          f"{'YES' if agg[L][0] > TH else 'no':>8}")
Lstar = next((L for L in GRID if agg[L][1] is not None and
              all(agg[M][0] <= TH for M in GRID if agg[M][1] is not None and M >= L)), None)
print(f"\n  L*(0.137; J={J}) = {Lstar}   "
      f"max C(0.137) = {max(r['C137'] for r in rows):.4f} "
      f"(lam={max(rows, key=lambda r: r['C137'])['lam']})")
json.dump({"J": J, "Lstar": Lstar, "rows": rows,
           "envelope": {str(L): [agg[L][0], agg[L][1]] for L in GRID if agg[L][1] is not None}},
          open(os.path.join(DIR, f"lstar_{J}_{TAG}.json"), "w"))
print(f"wrote lstar_{J}_{TAG}.json")
