"""STEP 3 -- can the realizing phase have the arithmetic form xi = lambda * 2^{-m}
with lambda in a low-frequency shell and m the exponent the window geometry dictates?

In cw2env.py's parametrisation the cell value is XI * 2^{-(m-x)} with m = sg+t+1 fixed by J,
so XI *is* lambda, and shifting m by delta is exactly XI -> lambda * 2^{-delta}.
2 is a primitive root mod 3^k for every k, so {lambda*2^{-delta}} runs over ALL units mod 3^q
as delta runs over one period 2*3^{q-1}: existence over unrestricted m is automatic.
The real question is whether it happens for a *small* lambda at a *geometrically reachable* m.

Search strategy (exact): the lowest window level b0 = 12 is a necessary condition and costs only
a discrete log, since 2 generates (Z/3^12)^*.  delta hits the level-b0 survivor set iff
delta = dlog(lambda) - dlog(u) (mod 2*3^11) for some surviving unit u.  Each such delta is then
checked against the remaining 63 levels exactly.

usage: python3 step3_lambda.py [LAMMAX] [DMAX]
"""
import json, sys
from common import Geom, ETA_DEN

LAMMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 500
DMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 2_000_000

U = json.load(open("unit.json"))
J, m, XI = U["J"], U["m"], int(U["XI"])
pat = U["pattern"]
SV = json.load(open("surv.json"))
BF = SV["final_b"]
surv_final = set(int(v) for v in SV["cands"])
units_final = [v for v in surv_final if v % 3 != 0]


def ord2(k):
    qb = 3 ** k
    o = 2 * 3 ** (k - 1)
    for pr in (2, 3):
        while o % pr == 0 and pow(2, o // pr, qb) == 1:
            o //= pr
    return o


print("2 as a primitive root mod 3^k (PROVED MATH; verified here):")
for k in (1, 2, 12, 138):
    print(f"  ord(2 mod 3^{k}) = {ord2(k)} = phi(3^{k}) = {2*3**(k-1)} -> primitive root: "
          f"{ord2(k) == 2*3**(k-1)}")

print(f"\n(a) EXISTENCE over unrestricted m: the orbit {{lam*2^-d : d}} of ANY unit lam is the whole")
print(f"    unit group mod 3^{BF}; the surviving set has {len(units_final)} units, so for EVERY unit lam")
print(f"    (lam = 1 included) there are exactly {len(units_final)} residues d mod 2*3^{BF-1} realizing it.")
print(f"(b) DENSITY over m in one full period = {len(units_final)}/(2*3^{BF-1}) = "
      f"{len(units_final)/(2*3**(BF-1)):.4e}")
print(f"    full period 2*3^{BF-1} has {len(str(2*3**(BF-1)))} decimal digits; geometrically m ~ 1.7516*J.")


def level_ok(b, lo, row, v):
    qb = 3 ** b
    half = qb // 2
    rr = v * pow(2, -(m - lo), qb) % qb
    for t in row:
        y = rr if rr <= half else rr - qb
        if (ETA_DEN * (y if y >= 0 else -y) < qb) != t:
            return False
        rr += rr
        if rr >= qb:
            rr -= qb
    return True


b0 = pat[0][1]
q0 = 3 ** b0
per0 = 2 * 3 ** (b0 - 1)
surv0 = [v for v in range(q0) if level_ok(pat[0][1], pat[0][2], pat[0][4], v)]
surv0_units = [v for v in surv0 if v % 3 != 0]
print(f"\nlevel b={b0}: {len(surv0)} surviving residues mod 3^{b0} ({len(surv0_units)} units), "
      f"density {len(surv0)/q0:.4e}")

# discrete log table mod 3^b0 (2 is a primitive root)
dlog = {}
g = 1
for e in range(per0):
    dlog[g] = e
    g = g * 2 % q0
assert len(dlog) == per0
targ = sorted(dlog[u] for u in surv0_units)

QF = 3 ** BF
invF = pow(2, -1, QF)
ncyc = DMAX // per0 + 1
print(f"\n(c) exhaustive: |lambda| <= {LAMMAX} (3 not | lambda), delta = 0..{DMAX}  (m = {m}+delta,")
print(f"    delta=0 is the m the window dictates; delta<={DMAX} covers every J up to ~{int(DMAX/1.7516):.0e}).")
print(f"    candidate deltas per lambda: {len(targ)} residues x {ncyc} cycles = {len(targ)*ncyc}")

lams = [s * L for L in range(1, LAMMAX + 1) if L % 3 for s in (1, -1)]
hits_full = []
nchk = 0
best_prefix = (0, None)
for L in lams:
    dl = dlog[L % q0]
    for t in targ:
        d0 = (dl - t) % per0
        for c in range(ncyc):
            d = d0 + c * per0
            if d > DMAX:
                break
            nchk += 1
            vF = (L % QF) * pow(invF, d, QF) % QF
            depth = 0
            for (r, b, lo, hi, row) in pat:
                if not level_ok(b, lo, row, vF % (3 ** b)):
                    break
                depth += 1
            if depth > best_prefix[0]:
                best_prefix = (depth, (L, d))
            if depth == len(pat):
                hits_full.append((L, d))

print(f"    (lambda,delta) pairs examined past the level-{b0} test: {nchk}")
print(f"    deepest consecutive-level prefix matched: {best_prefix[0]} of {len(pat)} levels, "
      f"at (lambda,delta) = {best_prefix[1]}")
print(f"    pairs realizing the FULL {len(pat)}-level / {sum(len(p[4]) for p in pat)}-cell pattern: "
      f"{len(hits_full)}  {hits_full[:5]}")

print(f"\n    at the DICTATED m = {m} (delta = 0), levels of the pattern matched by small lambda:")
d0s = []
for L in lams[:60]:
    d = 0
    for (r, b, lo, hi, row) in pat:
        if not level_ok(b, lo, row, L % (3 ** b)):
            break
        d += 1
    d0s.append((L, d))
print("      " + ", ".join(f"{L}:{d}" for L, d in d0s))
allz = all(d == 0 for _, d in d0s)
print(f"      every listed lambda fails at the very first level (b={b0}): {allz}")

# how small must lambda be allowed to get?  smallest |lambda| realizing the pattern at delta=0
smallest = None
for v in sorted(units_final):
    c = min(v, QF - v)
    if smallest is None or c < smallest:
        smallest = c
print(f"\n    smallest |lambda| realizing the pattern at the dictated m (delta=0), i.e. min over the")
print(f"    {len(units_final)} surviving units of min(v, 3^{BF}-v): {smallest}")
print(f"      ({len(str(smallest))} decimal digits; the low-frequency shell is |lambda| <~ 10^3)")

json.dump({"hits_full": hits_full, "nchk": nchk, "best_prefix": [best_prefix[0], best_prefix[1]],
           "surv0": len(surv0), "surv0_units": len(surv0_units),
           "smallest_lambda": str(smallest)}, open("lam.json", "w"))
print("\nwrote lam.json")
