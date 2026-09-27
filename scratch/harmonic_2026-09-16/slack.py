"""Why the barrier height is irrelevant (Parts XIII-XV audit).

For each L_1-record seed, measure the actual peak drift max_{j<=L_1} R_j over its confined prefix, and
compare with the barrier c = 1, with the harmonic ceiling B_m(j) = (1/9) log2(1+3j/(m-2)) proved in
EOC/HarmonicFloor.lean, and with the old linear ceiling j/(3 m ln 2).  If the peak sits far below the
barrier, lowering the barrier cannot move the frontier -- the binding constraint is arithmetic
(realizability), not the drift ceiling.
usage: python3 slack.py"""
import math

AL = math.log2(3); LN2 = math.log(2)
RECORDS = [27, 703, 2223, 10087, 35655, 270271, 626331, 837799, 1126015, 1859241,
           6649279, 10507503, 63728127]

def prefix(m, cap=400):
    x = m; S = 0; Rs = []
    for j in range(1, cap + 1):
        v = 3 * x + 1; a = (v & -v).bit_length() - 1
        S += a; R = S - j * AL
        if R > 1.0: return Rs
        Rs.append(R); x = v >> a
    return Rs

print("        m      L_1   max R_j    argmax   min R_j    B_m(L_1)   old(L_1)   peak/1.0")
for m in RECORDS:
    Rs = prefix(m)
    L = len(Rs); mx = max(Rs); mn = min(Rs); am = Rs.index(mx) + 1
    B = math.log(1 + 3 * L / (m - 2)) / (9 * LN2)
    old = L / (3 * m * LN2)
    print(f"{m:10d}  {L:5d}   {mx:7.4f}   {am:5d}   {mn:8.3f}   {B:8.5f}   {old:8.5f}   {mx:6.3f}")

print("\nhow many of the 1-confined record prefixes would survive a barrier c:")
print("     c      seeds whose whole prefix stays under c (of 13)")
for c in (1.0, 0.5, 0.387, 0.264, 0.167, 0.1, 0.0):
    k = sum(1 for m in RECORDS if max(prefix(m)) <= c)
    print(f"  {c:5.3f}    {k}")
