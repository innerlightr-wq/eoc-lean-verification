"""Drift-band occupancy of 1-confined prefixes, and the L_1(m)/m ratio frontier (Parts I-III, XI, XXXIV-XXXV,
LVIII-LXII).

For odd m: Syracuse orbit m_j, word d_j = v2(3 m_{j-1} + 1), S_j = sum d, R_j = S_j - j log2 3.
L_1(m) = max N with R_j <= 1 for all j <= N.  On that prefix m_j = m U_j 2^{-R_j} with U_j >= 1, so
R_j <= 1 gives m_j >= m/2, and R_j <= -q gives m_j >= 2^q m.
Reports, for record seeds and for the top-ratio seeds:
  * fraction of times with R_j >= -Q  ("shallow recurrence", Parts XXXI-XXXIX) for Q = 0..8;
  * median / quartiles / max of -R_j;
  * the ratio L_1(m)/m.
usage: python3 bands.py MMAX"""
import math, sys

AL = math.log2(3)
MMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 2000000
NCAP = 400
top = [math.floor(j * AL + 1.0) for j in range(NCAP + 2)]

def prefix(m):
    """returns the list of R_j for j = 1..L_1(m)."""
    x = m; S = 0; Rs = []
    for j in range(1, NCAP + 1):
        v = 3 * x + 1; a = (v & -v).bit_length() - 1
        S += a
        if S > top[j]: break
        Rs.append(S - j * AL); x = v >> a
    return Rs

RECORDS = [27, 703, 35655, 270271, 837799, 1126015, 1859241, 6649279, 10507503]
print("record seeds: drift-band occupancy of the 1-confined prefix")
print("   m           L_1   L_1/m    frac R_j >= -Q for Q = 0,1,2,3,4,6,8      median(-R)  max(-R)")
for m in RECORDS:
    Rs = prefix(m); L = len(Rs)
    if not L: continue
    fr = [sum(1 for r in Rs if r >= -Q) / L for Q in (0, 1, 2, 3, 4, 6, 8)]
    negs = sorted(-r for r in Rs)
    med = negs[L // 2]
    print(f"  {m:10d}  {L:4d}  {L/m:7.4f}   " + " ".join(f"{f:.3f}" for f in fr) +
          f"     {med:7.3f}  {max(negs):7.3f}")

# ratio frontier: top seeds by L_1(m)/m
best = []
m = 3
while m <= MMAX:
    x = m; S = 0; j = 0
    while j < NCAP:
        v = 3 * x + 1; a = (v & -v).bit_length() - 1
        S += a; j += 1
        if S > top[j]: j -= 1; break
        x = v >> a
    best.append((j / m, m, j))
    if len(best) > 20000:
        best.sort(reverse=True); best = best[:20]
    m += 2
best.sort(reverse=True); best = best[:12]
print(f"\ntop seeds by L_1(m)/m over odd 3 <= m <= {MMAX}  (target: < 3 ln 2 = {3*math.log(2):.5f})")
for r, m, L in best:
    print(f"  m = {m:10d}  L_1 = {L:4d}  ratio = {r:.4f}")
print(f"  => sup_{{3 <= m <= {MMAX}}} L_1(m)/m = {best[0][0]:.4f} at m = {best[0][1]}")
