"""TASK 3 (exact form) -- the unpaid-excess constant.

The additive per-block weight w_r satisfies  sum_{r0<=r<r1} w_r = (a_{r0}-a_{r1})/2 EXACTLY,
so the question "is every burst paid for by the following quiet stretch, up to O(1)?" is
literally the question whether

        C(theta) := max_{r0 < r1}  sum_{r0<=r<r1} ( w_r - theta )

is a small constant.  If C(theta) < infinity then for EVERY stretch
        sum w_r <= theta*(r1-r0) + C(theta),
i.e. the long-product growth over any block range is theta per step plus a bounded surplus.
C is computed exactly by Kadane's maximum-subarray scan (floats; the w are floats).

Also: the crossover length L*(theta) = the smallest L with
        max_{r0} (1/L) sum_{r0<=r<r0+L} w_r  <=  theta.

usage: python3 t3b_budget.py
"""
import json, math, os

DIR = os.path.dirname(os.path.abspath(__file__))
CORP = json.load(open(os.path.join(DIR, "corpus.json")))
THS = [0.137, 0.10, 0.08, 0.06]
MARGIN = 20
OUT = {}


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


print("=" * 104)
print("TASK 3 (exact) -- unpaid-excess constant C(theta) = max subarray of (w_r - theta)")
print("=" * 104)
print("  C(theta) < inf  <=>  every burst is paid for by the surrounding quiet stretch,")
print("  with a total unpaid surplus of at most C bits (per STEP; a block is 2 steps).\n")
print(f"  {'J':>4} {'lam':>6} " + " ".join(f"C({t}){'':<3}" for t in THS) +
      f"  {'argmax stretch (theta=0.137)':>30}")
mx = {t: (0, None) for t in THS}
for c in CORP:
    w = c["w"][2:c["Rend"] - MARGIN]
    row = []
    arg = None
    for t in THS:
        C, i, j = kadane([x - t for x in w])
        row.append(C)
        if t == 0.137:
            arg = (i + 2, j + 2)
        if C > mx[t][0]:
            mx[t] = (C, (c["J"], c["lam"], i + 2, j + 2))
    OUT[f"{c['J']}_{c['lam']}"] = {"C": dict(zip(map(str, THS), row)), "arg137": arg}
    print(f"  {c['J']:>4} {c['lam']:>6} " + " ".join(f"{v:<9.4f}" for v in row) +
          f"  blocks {arg[0]}..{arg[1]} (len {arg[1]-arg[0]})")
print()
for t in THS:
    C, a = mx[t]
    print(f"  MAX over the 30-environment corpus: C({t}) = {C:.4f} bits  "
          f"(J={a[0]}, lambda={a[1]}, blocks {a[2]}..{a[3]}, length {a[3]-a[2]})")
OUT["max"] = {str(t): [mx[t][0], list(mx[t][1])] for t in THS}

print()
print("=" * 104)
print("CROSSOVER LENGTH  L*(theta) -- max over anchors of the L-block mean rate, all environments")
print("=" * 104)
LS = list(range(4, 65, 2)) + [72, 80, 96, 112, 128, 160]
glob = []
for L in LS:
    best = -9.0
    arg = None
    for c in CORP:
        w = c["w"]
        n = c["Rend"] - MARGIN
        ps = [0.0]
        for x in w:
            ps.append(ps[-1] + x)
        for a in range(2, n - L):
            v = (ps[a + L] - ps[a]) / L
            if v > best:
                best, arg = v, (c["J"], c["lam"], a)
    glob.append((L, best, arg))
print(f"  {'L':>4} {'max mean rate':>14} {'where (J,lam,r0)':>22} {'> 0.137?':>9}")
for (L, b, a) in glob:
    print(f"  {L:>4} {b:>14.5f} {str(a):>22} {'YES' if b > 0.137 else 'no':>9}")
OUT["crossover"] = [[L, b, list(a)] for L, b, a in glob]
first_ok = next((L for L, b, a in glob if b <= 0.137), None)
last_bad = max([L for L, b, a in glob if b > 0.137], default=None)
print(f"\n  L*(0.137) = {first_ok}: for EVERY anchor and EVERY environment in the corpus the")
print(f"  mean rate over {first_ok} or more consecutive blocks is <= 0.137; the last length that")
print(f"  still exceeds it is L = {last_bad}.")
for th in (0.10, 0.08):
    f2 = next((L for L, b, a in glob if b <= th), None)
    print(f"  L*({th}) = {f2}")
    OUT[f"Lstar_{th}"] = f2
OUT["Lstar_0.137"] = first_ok
json.dump(OUT, open(os.path.join(DIR, "t3b_budget.json"), "w"), indent=1)
print("\nwrote t3b_budget.json")
