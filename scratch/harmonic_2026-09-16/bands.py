"""Explicit constants in the band-occupancy theorem, and how loose they are (Parts XXIV-XXXIV).

EOC/HarmonicFloor.band_occupancy: under non-descent with distinct states,
  #{j < N : R_j >= -A} * 2^{-A} <= M * U_N * (2/(M-2) + (1/3) log(1 + 3N/(M-2))).
With N = C*M and the non-descent bound U_N <= (1+1/(3M))^N <= exp(C/3), the occupancy fraction obeys
  #{j < N : R_j >= -A} / N  <=  2^A * exp(C/3) * (1/(3C)) * log(1+3C) + O(1/M).
Print this for the relevant C, and the forced-dip depth A_min(C) = the least A for which the bound is
not yet vacuous (fraction 1).  Then compare with the true occupancy on record seeds.
usage: python3 bands.py"""
import math

AL = math.log2(3)
RECORDS = [27, 703, 2223, 10087, 35655, 270271, 626331, 837799, 1126015, 1859241,
           6649279, 10507503, 63728127]

def frac_bound(C, A):
    return 2 ** A * math.exp(C / 3) * math.log(1 + 3 * C) / (3 * C)

print("provable upper bound on  #{j<N : R_j >= -A}/N  for N = C*M  (M large)")
print("    C      A=0     A=0.5    A=1      A=2      A=3    | forced dip A_min (bound=1)")
for C in (0.5, 1.0, 13 / 9, 2.0, 3.0, 5.0):
    row = f"  {C:5.3f}  "
    for A in (0.0, 0.5, 1.0, 2.0, 3.0):
        row += f"  {frac_bound(C, A):6.3f} "
    # least A with frac_bound >= 1
    f0 = frac_bound(C, 0.0)
    Amin = -math.log2(f0) if f0 < 1 else 0.0
    row += f" |  {Amin:.3f}"
    print(row)

print("\ntrue occupancy on the 1-confined record prefixes (fraction of steps with R_j >= -A):")
print("        m      N    A=0     A=1     A=2     A=3     A=6     min R")
for m in RECORDS:
    x = m; S = 0; Rs = []
    for j in range(1, 400):
        v = 3 * x + 1; a = (v & -v).bit_length() - 1
        S += a; R = S - j * AL
        if R > 1.0: break
        Rs.append(R); x = v >> a
    N = len(Rs)
    row = f"{m:10d} {N:5d}"
    for A in (0.0, 1.0, 2.0, 3.0, 6.0):
        row += f"  {sum(1 for R in Rs if R >= -A)/N:6.3f}"
    print(row + f"  {min(Rs):7.2f}")
