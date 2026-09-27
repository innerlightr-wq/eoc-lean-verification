"""Injective harmonic ceiling, the bootstrap map, and the observable W_N (Parts VI-XIV, XXVI-XXXIV, XLII-XLIII).

Under non-descent (m_j >= m) with distinct orbit values,
   sum_{j<N} 1/m_j <= sum_{r<N} 1/(m+2r) <= (1/2) ln(1+2N/m) + 1/m,
so  R_j <= log2 U_j <= (1/(6 ln 2)) ln(1 + 2j/m) =: B(j)   -- a logarithmic ceiling, versus the old linear
j/(3 m ln 2).  This script measures, for record seeds:
  * L_1 under the barrier R <= 1 (repo convention), under the old linear non-descent ceiling, and under B(j);
  * W_N = sum_{j<N} 2^{R_j} (exact identity: sum 1/m_j = (1/m) sum 2^{R_j}/U_j), and W_N/N, W_N/sqrt(N);
  * quantiles and harmonic mean of m_j/m.
usage: python3 harm.py"""
import math

AL = math.log2(3); LN2 = math.log(2)
NCAP = 600
RECORDS = [27, 703, 2223, 10087, 35655, 270271, 626331, 837799, 1126015, 1859241, 6649279, 10507503, 63728127]

def orbit_prefix(m, ceil_fn):
    """longest prefix with R_j <= ceil_fn(j); returns (L, Rs, vals)."""
    x = m; S = 0; Rs = []; vals = []
    for j in range(1, NCAP + 1):
        v = 3 * x + 1; a = (v & -v).bit_length() - 1
        S += a; x = v >> a
        R = S - j * AL
        if R > ceil_fn(j): return j - 1, Rs, vals
        Rs.append(R); vals.append(x)
    return NCAP, Rs, vals

print("record seeds: confinement length under three ceilings")
print("      m       L_1(R<=1)   L(old linear)  L(harmonic B(j))   B(2m)   old(2m)")
for m in RECORDS:
    L1, _, _ = orbit_prefix(m, lambda j: 1.0)
    Lold, _, _ = orbit_prefix(m, lambda j, m=m: j / (3 * m * LN2))
    Lharm, _, _ = orbit_prefix(m, lambda j, m=m: math.log(1 + 2 * j / m) / (6 * LN2))
    print(f"{m:10d}   {L1:6d}      {Lold:6d}        {Lharm:6d}        "
          f"{math.log(1+4)/(6*LN2):.3f}   {2/(3*LN2):.3f}")

print("\nW_N = sum 2^{R_j} over the 1-confined prefix, and magnitude statistics")
print("      m      N=L_1    W_N     W_N/N   W_N/sqrt(N)   W_N/m    harm.mean(m_j/m)  median(m_j/m)  min")
for m in RECORDS:
    L1, Rs, vals = orbit_prefix(m, lambda j: 1.0)
    if not Rs: continue
    W = sum(2 ** R for R in Rs)
    ratios = sorted(v / m for v in vals)
    hm = len(ratios) / sum(1 / r for r in ratios)
    print(f"{m:10d}  {L1:5d}  {W:8.2f}  {W/L1:7.3f}   {W/math.sqrt(L1):9.3f}  {W/m:9.5f}   "
          f"{hm:12.3f}  {ratios[len(ratios)//2]:12.3f}  {ratios[0]:8.3f}")

print("\nbootstrap map C -> F(C): under non-descent for N = C m the ceiling is B = (1/(6 ln2)) ln(1+2C)")
for C in (0.5, 1.0, 13/9, 2.0, 3.0, 5.0):
    B = math.log(1 + 2 * C) / (6 * LN2)
    Bold = C / (3 * LN2)
    print(f"  C = {C:5.3f}:  harmonic ceiling B = {B:.4f}   (old linear ceiling {Bold:.4f})")
