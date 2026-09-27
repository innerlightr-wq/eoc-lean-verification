"""TASK 8 -- exact 3-adic arithmetic around the 16-element exceptional set.

All integer arithmetic is exact.  Inputs are read READ-ONLY from
scratch/oddpressure_2026-09-16/{surv.json,unit.json}.
"""
import json, math

SRC = "/home/elias/GitHub/eoc-lean-verification/scratch/oddpressure_2026-09-16/"
SV = json.load(open(SRC + "surv.json"))
U = json.load(open(SRC + "unit.json"))
BF = SV["final_b"]
QF = 3 ** BF
cands = sorted(int(v) for v in SV["cands"])
XI = int(U["XI"])
m = U["m"]
J = U["J"]
pat = U["pattern"]
ETA_DEN = 54
outj = {}

print("=" * 78)
print("8a. EXACT MULTIPLICATIVE ORDER OF 2 MODULO 3^k    (exact integers)")
print("=" * 78)


def ord_exact(a, k):
    q = 3 ** k
    n = 2 * 3 ** (k - 1)          # phi(3^k)
    o = n
    for p in (2, 3):
        while o % p == 0 and pow(a, o // p, q) == 1:
            o //= p
    assert pow(a, o, q) == 1
    return o


for k in (1, 2, 3, 12, 137, 138):
    o = ord_exact(2, k)
    ph = 2 * 3 ** (k - 1)
    print(f"  ord(2 mod 3^{k:<3}) = {o}")
    if k >= 12:
        print(f"      phi(3^{k}) = {ph}   primitive root: {o == ph}   ({len(str(o))} digits)")
outj["ord2_3_138"] = str(ord_exact(2, 138))
outj["phi_3_138"] = str(2 * 3 ** 137)
print(f"\n  ord(2 mod 3^138) = phi(3^138) = 2*3^137 exactly: "
      f"{ord_exact(2,138) == 2*3**137}")
print("  (LIFTING-THE-EXPONENT / PROVED MATH: 2 is a primitive root mod 3 and mod 9,")
print("   hence mod 3^k for all k>=1; verified exactly here for k = 1,2,3,12,137,138.)")

print()
print("=" * 78)
print("8b. STRUCTURE OF THE 16 EXCEPTIONAL RESIDUES MOD 3^138")
print("=" * 78)


def v3(n):
    if n == 0:
        return 10 ** 9
    c = 0
    while n % 3 == 0:
        n //= 3
        c += 1
    return c


print(f"  |E| = {len(cands)};  units (v3=0): {sum(1 for v in cands if v % 3)}")
print(f"  3-adic valuations v3(x) of the elements:")
vals = {}
for v in cands:
    vals.setdefault(v3(v), []).append(v)
for k in sorted(vals):
    print(f"    v3 = {k}: {len(vals[k])} elements")
outj["valuations"] = {str(k): len(v) for k, v in vals.items()}

print("\n  pairwise differences: multiset of v3(x_i - x_j), i<j  (= shared-prefix length)")
dv = {}
for i in range(len(cands)):
    for j in range(i + 1, len(cands)):
        dv.setdefault(v3(cands[i] - cands[j]), 0)
        dv[v3(cands[i] - cands[j])] += 1
for k in sorted(dv):
    print(f"    v3(diff) = {k:3d}: {dv[k]:4d} pairs "
          f"(i.e. {dv[k]} pairs agree to exactly {k} ternary digits)")
outj["diff_valuations"] = {str(k): v for k, v in dv.items()}
minv = min(dv)
print(f"  => every two exceptional residues already differ at level b = {minv+1};")
print(f"     the whole set lies in {len(set(v % 3**minv for v in cands))} residue class(es) mod 3^{minv}.")

print("\n  additive structure: is E - x0 a subgroup / lattice-like set?")
x0 = cands[0]
D = sorted((v - x0) % QF for v in cands)
Dset = set(D)
closed = sum(1 for a in D for b in D if (a + b) % QF in Dset)
print(f"    x0 = {x0}")
print(f"    |{{a+b mod 3^138 : a,b in E-x0}} n (E-x0)| pairs = {closed} of {len(D)**2}"
      f"   (subgroup would be {len(D)**2})")
print(f"    v3 of the 15 nonzero shifts a = x - x0:")
print("      " + ", ".join(str(v3(a)) for a in D if a))
# try to find generators: the distinct minimal-valuation shifts
gens = sorted(set(v3(a) for a in D if a))
print(f"    distinct shift valuations: {gens}")
# check for a 2^4 coset structure: E = x0 + {sum eps_i g_i}
print("    candidate binary generators (one shift per distinct valuation, smallest):")
G = []
for g in gens:
    cand = [a for a in D if v3(a) == g]
    G.append(min(cand))
    print(f"      v3={g}: {len(cand)} shifts, representative {min(cand)}")
gen4 = G
span = set()
if len(gen4) <= 6:
    import itertools
    for bits in itertools.product([0, 1], repeat=len(gen4)):
        span.add(sum(b * g for b, g in zip(bits, gen4)) % QF)
    print(f"    {{sum eps_i g_i}} has {len(span)} elements; equals E-x0: {span == Dset}")
    outj["binary_span_matches"] = bool(span == Dset)

print("\n  multiplicative symmetries of E (as a subset of Z/3^138):")
for name, f in [("x -> -x", lambda v: (-v) % QF),
                ("x -> 2x", lambda v: 2 * v % QF),
                ("x -> 4x", lambda v: 4 * v % QF),
                ("x -> x^-1 (units)", None)]:
    if f is None:
        us = [v for v in cands if v % 3]
        img = set(pow(v, -1, QF) for v in us)
        print(f"    {name:20s}: image inside E: {len(img & set(cands))}/{len(us)}")
    else:
        img = set(f(v) for v in cands)
        print(f"    {name:20s}: image inside E: {len(img & set(cands))}/{len(cands)}")
# ratio structure of the units
us = sorted(v for v in cands if v % 3)
print(f"\n  ratios u/u0 mod 3^138 for the {len(us)} units (u0 = smallest): their v3(ratio - 1):")
u0 = us[0]
rr = [(pow(u0, -1, QF) * u) % QF for u in us]
print("    " + ", ".join(str(v3(r - 1)) for r in rr))
print("    discrete logs base 2 are not computed (they need ~2*3^137 steps).")

print()
print("=" * 78)
print("8c. SPACING OF THE m WITH lambda*2^{-m} IN THE EXCEPTIONAL SET")
print("=" * 78)
print("  E_b = exceptional set truncated at level b (survivors of the sieve mod 3^b),")
print("  read from the per-level sieve.  For a unit lambda the map m -> lambda*2^{-m} mod 3^b")
print("  is a bijection onto the units of Z/3^b with period ord(2 mod 3^b) = 2*3^{b-1},")
print("  so lambda*2^{-m} in E_b happens exactly |E_b^unit| times per period, for EVERY lambda.")
print()
print(f"  {'b':>4} {'|E_b|':>8} {'|E_b^u|':>8} {'period 2*3^(b-1)':>22} {'mean spacing':>16}")
hist = SV["hist"]
# recompute unit counts per level by re-running the sieve cheaply on the first few levels
from tcommon import Geom


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


b0, lo0, row0 = pat[0][1], pat[0][2], pat[0][4]
E12 = [v for v in range(3 ** b0) if level_ok(b0, lo0, row0, v)]
E12u = [v for v in E12 if v % 3]
levels = [(b0, len(E12), len(E12u))]
cur = E12
prev_b = b0
for (r, b, lo, hi, row) in pat[1:]:
    if b > 20:
        break
    step = b - prev_b
    qp = 3 ** prev_b
    lifted = [v + j * qp for v in cur for j in range(3 ** step)]
    cur = [v for v in lifted if level_ok(b, lo, row, v)]
    levels.append((b, len(cur), sum(1 for v in cur if v % 3)))
    prev_b = b
levels.append((BF, len(cands), sum(1 for v in cands if v % 3)))
for (b, n, nu) in levels:
    per = 2 * 3 ** (b - 1)
    sp = per / nu if nu else float("inf")
    print(f"  {b:>4} {n:>8} {nu:>8} {str(per):>22} {sp:>16.4g}")
outj["levels"] = [[b, n, nu] for b, n, nu in levels]
per138 = 2 * 3 ** 137
nu138 = sum(1 for v in cands if v % 3)
print(f"\n  FULL PATTERN (b = {BF}): mean spacing between successive good m is")
print(f"    2*3^137/{nu138} = {per138//nu138}")
print(f"    ({len(str(per138//nu138))} decimal digits).  COMPUTATIONAL/PROVED: the count per period")
print(f"    is EXACTLY {nu138} for every unit lambda (2 is a primitive root), so the spacing is not")
print(f"    a heuristic -- only its *placement* relative to small m is.")

print("\n  actual m-spacing at the truncated levels, measured for small lambda:")
print(f"  {'lam':>6} {'b':>4} {'#m<=10^6':>10} {'min gap':>9} {'med gap':>9} {'max gap':>9}")
for LAM in (1, 5, 7, 11, 101, 1025):
    for (b, lo, row) in [(b0, lo0, row0), (16, pat[2][2], pat[2][4])]:
        qb = 3 ** b
        Eb = set(v for v in (E12 if b == b0 else []) if True) if b == b0 else None
        if Eb is None:
            # rebuild level-b survivor set by sieving the nested prefix
            cc = E12
            pb = b0
            for (r2, b2, lo2, hi2, row2) in pat[1:]:
                if b2 > b:
                    break
                st = b2 - pb
                qp = 3 ** pb
                cc = [v + j * qp for v in cc for j in range(3 ** st)]
                cc = [v for v in cc if level_ok(b2, lo2, row2, v)]
                pb = b2
            Eb = set(cc)
        hits = []
        v = LAM % qb
        inv2 = pow(2, -1, qb)
        for mm in range(0, 1000001):
            if v in Eb:
                hits.append(mm)
            v = v * inv2 % qb
        gaps = [hits[i + 1] - hits[i] for i in range(len(hits) - 1)]
        if gaps:
            gs = sorted(gaps)
            print(f"  {LAM:>6} {b:>4} {len(hits):>10} {gs[0]:>9} {gs[len(gs)//2]:>9} {gs[-1]:>9}")
        else:
            print(f"  {LAM:>6} {b:>4} {len(hits):>10} {'-':>9} {'-':>9} {'-':>9}")

print()
print("=" * 78)
print("8d. LOWER BOUND ON |lambda| FOR A PHASE IN THE EXCEPTIONAL SET")
print("=" * 78)
print("  The window fixes m = sg + t + 1; the environment is xi = lambda (cw2env parametrisation),")
print("  and moving to a window whose geometry dictates m + delta is xi -> lambda * 2^{-delta}.")
print("  Realizing the 64-level pattern therefore requires")
print(f"       lambda ≡ e * 2^{{delta}}  (mod 3^{BF})   for one of the {len(cands)} e in E.")
print()
mins = []
for delta in range(0, 2001):
    mn = QF
    for e in cands:
        v = e * pow(2, delta, QF) % QF
        mn = min(mn, min(v, QF - v))
    mins.append(mn)
print(f"  min over E of |lambda| at delta = 0 : {mins[0]}  ({len(str(mins[0]))} digits)")
best = min(range(len(mins)), key=lambda i: mins[i])
print(f"  min over 0 <= delta <= 2000        : {mins[best]}  ({len(str(mins[best]))} digits) at delta = {best}")
print(f"  DIGIT FLOOR over that delta range  : {min(len(str(x)) for x in mins)} decimal digits")
outj["min_lambda_delta0"] = str(mins[0])
outj["min_lambda_delta_le_2000"] = str(mins[best])
print()
print("  RIGOROUS (exact-arithmetic) statement, no genericity assumed:")
print(f"    for every delta in [0,2000] and every e in E, min(|e*2^delta|, 3^138-|.|) >= 10^{min(len(str(x)) for x in mins)-1}.")
print("    Hence no |lambda| <= 10^{} realizes the full pattern at any of those 2001 window".format(
    min(len(str(x)) for x in mins) - 1))
print("    geometries.  (This is a finite exact check, not a density argument.)")
print()
print("  COUNTING BOUND (HEURISTIC, stated as such): over delta in [0,D] the set of admissible")
print(f"  lambda mod 3^138 has {len(cands)}*(D+1) elements spread over an interval of length 3^138;")
print("  the expected number with |lambda| <= L is 16*(D+1)*2L/3^138.  For this to reach 1 with")
print("  L = 10^3 one needs D >= 3^138/(32*10^3) - 1 ~ 1.4e+61.")
D_needed = QF // (32 * 1000)
print(f"    exact threshold D = 3^138/(32*1000) = {D_needed}")
print(f"    ({len(str(D_needed))} decimal digits; geometrically m ~ 1.7516*J so J ~ {len(str(D_needed))-1} digits too)")
outj["D_needed_for_L1000"] = str(D_needed)

json.dump(outj, open("t8_adic.json", "w"), indent=1)
print("\nwrote t8_adic.json")
