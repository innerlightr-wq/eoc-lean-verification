"""TASK 6 aggregation of the wide C-scans (T6C_<J>_*.txt).

columns: lam  Lam_long  C(.137)  C(.10)  b16 b24 b32 b48 b64 b128  pre6  dbr
"""
import glob, json, os

DIR = os.path.dirname(os.path.abspath(__file__))
TH = 0.137
LS = [16, 24, 32, 48, 64, 128]
OUT = {}
print("=" * 104)
print("TASK 6 -- wide-lambda C-scan: the unpaid-excess constant and sustained bursts")
print("=" * 104)
for J in (400, 800, 1600):
    rows = {}
    for fn in glob.glob(os.path.join(DIR, f"T6C_{J}_*.txt")):
        for line in open(fn):
            t = line.split()
            if len(t) == 12 and t[0].isdigit():
                try:
                    rows[int(t[0])] = [float(x) for x in t[1:10]] + [int(t[10]), int(t[11])]
                except ValueError:
                    pass
    if not rows:
        continue
    lams = sorted(rows)
    n = len(lams)
    Cs = [rows[l][1] for l in lams]
    C10 = [rows[l][2] for l in lams]
    Lam = [rows[l][0] for l in lams]
    aC = max(lams, key=lambda l: rows[l][1])
    aL = max(lams, key=lambda l: rows[l][0])
    print(f"\nJ={J}: {n} true low-frequency environments scanned "
          f"(lambda odd, {min(lams)} <= lambda <= {max(lams)})")
    print(f"  Lambda_long   : median {sorted(Lam)[n//2]:.5f}   MAX {max(Lam):.5f} (lam={aL})"
          f"   -- theta_max/max = {TH/max(Lam):.2f}x margin")
    print(f"  C(0.137)      : median {sorted(Cs)[n//2]:.4f}   MAX {max(Cs):.4f} bits (lam={aC})")
    print(f"  C(0.100)      : median {sorted(C10)[n//2]:.4f}   MAX {max(C10):.4f} bits")
    print(f"  {'L':>5} {'median burst':>13} {'MAX burst':>10} {'argmax':>7} "
          f"{'#lambda > theta_max':>20}")
    bm = {}
    for i, L in enumerate(LS):
        col = [rows[l][3 + i] for l in lams]
        am = max(lams, key=lambda l: rows[l][3 + i])
        nov = sum(1 for v in col if v > TH)
        bm[str(L)] = max(col)
        print(f"  {L:>5} {sorted(col)[n//2]:>13.5f} {max(col):>10.5f} {am:>7} "
              f"{nov:>12}/{n} = {nov/n:.4f}")
    nd = sum(1 for l in lams if rows[l][10] >= 6)
    print(f"  DeepBlackRun(6,6): {nd}/{n} lambda;   max run of blocks with pre>=6 = "
          f"{max(rows[l][10] for l in lams)};   total such blocks = "
          f"{sum(int(rows[l][9]) for l in lams)}")
    top = sorted(lams, key=lambda l: -rows[l][1])[:10]
    print("  top-10 lambda by C(0.137): " +
          ", ".join(f"{l}({rows[l][1]:.3f})" for l in top))
    OUT[str(J)] = {"n": n, "lam_max": max(lams),
                   "maxC137": max(Cs), "argmaxC": aC, "medianC137": sorted(Cs)[n // 2],
                   "maxC10": max(C10),
                   "max_Lambda_long": max(Lam), "argmax_Lambda": aL,
                   "burst_max": bm, "dbr_lambda": nd,
                   "top10_C": [[l, rows[l][1]] for l in top]}
json.dump(OUT, open(os.path.join(DIR, "t6d_aggregate.json"), "w"), indent=1)
print("\nwrote t6d_aggregate.json")
