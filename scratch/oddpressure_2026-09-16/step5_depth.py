"""STEP 5 -- triangle-depth distribution in the true (low-frequency) environments and the
depth-conditioned maximum of the local CW value; plus the structural statistic that actually
separates the adversarial unit from every true-environment unit.

Depth of a black cell = ln(3^b/(54|y|)) (exactly the definition in oddblack_2026-09-16/depth_true.py).
Window depth = max over black cells the window can read.
usage: python3 step5_depth.py
"""
import json, math
from common import Geom, Env, cell_xrange, row_values, ETA_DEN

rows = []
for J in (200, 400, 800):
    rows += json.load(open(f"scan_{J}.json"))
U = json.load(open("unit.json"))

print("window max triangle depth, TRUE low-frequency environments (all J, K, anchors, lambda):")
buckets = {}
for r in rows:
    d = int(r["depth"])
    buckets.setdefault(d, []).append(r)
tot = len(rows)
print(f"{'depth d':>8} {'#windows':>9} {'frac':>8} {'maxCW':>8} {'meanCW':>8}")
for d in sorted(buckets):
    b = buckets[d]
    print(f"{d:>4}-{d+1:<3} {len(b):>9} {len(b)/tot:>8.4f} "
          f"{max(x['cw'] for x in b):>8.4f} {sum(x['cw'] for x in b)/len(b):>8.4f}")
cum = 0
print("\ncumulative P(window depth <= d):")
for d in sorted(buckets):
    cum += len(buckets[d])
    print(f"  d <= {d+1}: {cum/tot:.4f}", end="   ")
print()
le8 = sum(len(b) for d, b in buckets.items() if d < 8)
print(f"\nP(window max depth <= 8) in the true environments = {le8}/{tot} = {le8/tot:.4f}")
sub = [r for r in rows if r["depth"] <= 8.0]
print(f"max CW among true-environment windows of depth <= 8 : {max(x['cw'] for x in sub):.4f}")
print(f"adversarial worst unit: depth {7.9907:.4f}, CW {U['CW']:.4f}  -> factor "
      f"{U['CW']/max(x['cw'] for x in sub):.2f} larger at the SAME depth cap")

# ---- the statistic that separates: contiguous fully-black rows -------------------
print("\nSTRUCTURE: longest run of consecutive blocks whose readable row begins with an")
print("all-black prefix of length >= 6 (the adversarial unit's driver).")
J, SV = 400, 3.0
G = Geom(J)
XA = int(U["XI"])


def runstats(XI):
    pre = []
    for r in range(G.R):
        lo, hi = cell_xrange(G, r)
        b = 2 * r + 2
        qb = 3 ** b
        v = row_values(G, r, lo, hi, XI)
        k = 0
        for x in range(lo, hi + 1):
            if ETA_DEN * abs(v[x]) < qb:
                k += 1
            else:
                break
        pre.append(k)
    best = cur = 0
    for k in pre:
        cur = cur + 1 if k >= 6 else 0
        best = max(best, cur)
    return pre, best


for name, XI in [("adversary depth<=8", XA), ("lam=1", 1), ("lam=5", 5), ("lam=7", 7),
                 ("lam=11", 11), ("lam=101", 101), ("lam=1025", 1025)]:
    pre, best = runstats(XI)
    nb6 = sum(1 for k in pre if k >= 6)
    print(f"  {name:20s} blocks with leading all-black prefix >= 6: {nb6:4d}/{G.R}   "
          f"longest consecutive run of such blocks: {best}   max prefix {max(pre)}")
