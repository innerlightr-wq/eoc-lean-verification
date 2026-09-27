"""STEP 2 -- EXACT realizability of the adversarial black pattern by a 3-adic phase.

The pattern of the worst unit imposes, for every touched cell (a,b) = (m-x, 2r+2), the condition
    54*|centered(xi*2^{-(m-x)} mod 3^b)| < 3^b      (black)   /   >= 3^b   (white).
Each condition depends on xi only through xi mod 3^b, and the levels b = 12,14,...,138 are nested,
so we sieve level by level, keeping the EXACT surviving residue set mod 3^b and lifting by 3^2 each
step.  Everything is exact integer arithmetic.

usage: python3 step2_realize.py [CAP]
"""
import json, sys
from common import Geom, ETA_DEN

CAP = int(sys.argv[1]) if len(sys.argv) > 1 else 40_000_000
U = json.load(open("unit.json"))
J, m = U["J"], U["m"]
XI = int(U["XI"])
G = Geom(J)
pat = U["pattern"]           # [r, b, lo, hi, row]
bmin = pat[0][1]

print(f"window: {len(pat)} levels b = {pat[0][1]}..{pat[-1][1]}, "
      f"{sum(len(p[4]) for p in pat)} cell constraints "
      f"({sum(sum(p[4]) for p in pat)} black / {sum(len(p[4])-sum(p[4]) for p in pat)} white)")


def survivors_at(b, cands, lo, row):
    """exact filter of residues mod 3^b against one level's pattern row."""
    qb = 3 ** b
    half = qb // 2
    inv = pow(2, -(m - lo), qb)
    out = []
    n = len(row)
    for v in cands:
        rr = v * inv % qb
        ok = True
        for i in range(n):
            y = rr if rr <= half else rr - qb
            if (ETA_DEN * (y if y >= 0 else -y) < qb) != row[i]:
                ok = False
                break
            rr += rr
            if rr >= qb:
                rr -= qb
        if ok:
            out.append(v)
    return out


# level b = bmin: enumerate all residues mod 3^bmin exactly
r, b, lo, hi, row = pat[0]
print(f"\nlevel b={b}: enumerating all 3^{b} = {3**b} residues ...", flush=True)
cands = survivors_at(b, range(3 ** b), lo, row)
print(f"  survivors {len(cands)}  density {len(cands)/3**b:.6e}   (XI_adv present: {XI % 3**b in set(cands)})")
hist = [(b, len(cands), 3 ** b)]

prev_b = b
for (r, b, lo, hi, row) in pat[1:]:
    step = b - prev_b
    qprev = 3 ** prev_b
    lifted = [v + j * qprev for v in cands for j in range(3 ** step)]
    if len(lifted) > CAP:
        print(f"  !! level {b}: lifted set {len(lifted)} exceeds CAP {CAP}; aborting exact sieve")
        break
    cands = survivors_at(b, lifted, lo, row)
    hist.append((b, len(cands), 3 ** b))
    prev_b = b
    if b % 8 == 2 or len(cands) <= 3:
        print(f"  level b={b:3d}: lifted {len(lifted):9d} -> survivors {len(cands):9d}  "
              f"density {len(cands)/3**b:.4e}", flush=True)
    if not cands:
        print("  *** EMPTY: pattern NOT realizable (should be impossible - XI_adv realizes it)")
        break

print(f"\nFINAL level b={prev_b}: |surviving residues mod 3^{prev_b}| = {len(cands)}")
print(f"  density of the exceptional set = {len(cands)}/3^{prev_b} = {len(cands)/3**prev_b:.6e}")
xa = XI % 3 ** prev_b
print(f"  XI_adv mod 3^{prev_b} in surviving set: {xa in set(cands)}")
units = [v for v in cands if v % 3 != 0]
print(f"  of which 3-adic UNITS (v != 0 mod 3): {len(units)}")
print(f"  explicit realizing residue xi = XI_adv mod 3^{prev_b} =\n    {xa}")
if len(cands) <= 40:
    print("  full surviving set:")
    for v in sorted(cands):
        print(f"    {v}{'   <-- XI_adv' if v == xa else ''}")

print("\nper-level survivor counts (b, count, 3^b):")
for (b, c, q) in hist:
    print(f"  b={b:3d}  count={c:9d}  density={c/q:.4e}")

json.dump({"final_b": prev_b, "cands": [str(v) for v in cands],
           "hist": [[b, c] for (b, c, q) in hist]}, open("surv.json", "w"))
print("\nwrote surv.json")
