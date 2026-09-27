"""Calibration: the CW window pressure P_j against the EXACT growth rate of the same
2K blocks.

  P_j    = max_S log2( M_2K(j)[S] / M_K(j)[S] ) / (2K)          (the CW quantity)
  rate_j = ( a_j - a_{j+2K} ) / (2 * 2K)                        (exact long-product rate
                                                                 of blocks j .. j+2K-1)
Both are "bits per ternary digit-step".  theta_max = 0.137 is the threshold the CW
formulation is compared against, so it matters by how much the CW value over- or
under-states what the operator product actually does.

usage: python3 t2b_cw_vs_rate.py
"""
import json, math, os
from tload import load, series, THETA_MAX

DIR = os.path.dirname(os.path.abspath(__file__))
CORP = {(c["J"], c["lam"]): c for c in json.load(open(os.path.join(DIR, "corpus.json")))}
DATA = {}
for J in (400, 800):
    meta, envs = load(J)
    if envs:
        DATA[J] = envs
OUT = {}
print("=" * 100)
print("CALIBRATION -- CW window pressure P_j vs the exact rate of the same 2K blocks")
print("=" * 100)
print(f"  {'J':>4} {'K':>3} {'N':>5} {'mean P':>8} {'mean rate':>10} {'mean P-rate':>12} "
      f"{'max P':>8} {'rate there':>11} {'max rate':>9} {'#P>th':>6} {'#rate>th':>9}")
for J in sorted(DATA):
    for K in (16, 24, 32):
        Ps, Rs = [], []
        for lam, rec in DATA[J].items():
            s = series(rec, K)
            if s is None:
                continue
            j0, P = s
            c = CORP[(J, lam)]
            w = c["w"]
            ps = [0.0]
            for x in w:
                ps.append(ps[-1] + x)
            for i, p in enumerate(P):
                j = j0 + i
                if j + 2 * K >= len(w):
                    continue
                Ps.append(p)
                Rs.append((ps[j + 2 * K] - ps[j]) / (2 * K))
        n = len(Ps)
        k = max(range(n), key=lambda i: Ps[i])
        print(f"  {J:>4} {K:>3} {n:>5} {sum(Ps)/n:>8.4f} {sum(Rs)/n:>10.4f} "
              f"{sum(Ps[i]-Rs[i] for i in range(n))/n:>12.4f} "
              f"{Ps[k]:>8.4f} {Rs[k]:>11.4f} {max(Rs):>9.4f} "
              f"{sum(1 for p in Ps if p>THETA_MAX):>6} "
              f"{sum(1 for r in Rs if r>THETA_MAX):>9}")
        OUT[f"{J}_{K}"] = {"N": n, "meanP": sum(Ps)/n, "meanRate": sum(Rs)/n,
                           "maxP": Ps[k], "rate_at_maxP": Rs[k], "maxRate": max(Rs),
                           "nP_over": sum(1 for p in Ps if p > THETA_MAX),
                           "nRate_over": sum(1 for r in Rs if r > THETA_MAX)}
print()
print("  P_j is a LOOK-AHEAD RATIO, not the growth rate of the window: it compares the")
print("  2K-block survival vector with the K-block one at the same state.  The table shows")
print("  by how much it overstates the actual 2K-block growth.")
json.dump(OUT, open(os.path.join(DIR, "t2b_cw_vs_rate.json"), "w"), indent=1)
print("\nwrote t2b_cw_vs_rate.json")
