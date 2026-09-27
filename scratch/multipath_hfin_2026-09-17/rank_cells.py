"""Part XXIII: exact Lebesgue measure of joint black-cell sets on the circle, and 'constraint rank' = -log3(measure).
Black cell (r, z) in phase coordinates T (window of K rows, last row r = K-1):  || 2^z 9^{K-1-r} T || < 1/54.
Measures are computed exactly by sweeping the rational breakpoints (common denominator)."""
from fractions import Fraction as F
from math import log
def measure(cells, K):
    # cells: list of (r, z); N_c = 2^z 9^{K-1-r}
    Ns = [2 ** z * 9 ** (K - 1 - r) for r, z in cells]
    # breakpoints of ||N T|| < 1/54 : T in (m - 1/54)/N, (m + 1/54)/N ; denominators 54 N
    pts = {F(0), F(1)}
    for N in Ns:
        for m in range(0, N + 1):
            for e in (-1, 1):
                x = F(54 * m + e, 54 * N)
                if 0 <= x <= 1: pts.add(x)
    pts = sorted(pts); tot = F(0)
    for a, b in zip(pts, pts[1:]):
        mid = (a + b) / 2
        if all(abs((N * mid) - round(N * mid)) < F(1, 54) for N in Ns): tot += b - a
    return tot
def rk(m): return -log(m, 3) if m > 0 else float('inf')
print("same row, two columns z and z+delta (single-cell rank = 3):")
for d in range(0, 9):
    m = measure([(0, 0), (0, d)], 1); print(f"  delta={d}: measure={float(m):.3e} rank={rk(m):.3f}  (independent would be 6.000; nested 3 + delta*log3 2 = {3 + d*log(2,3):.3f})")
print("consecutive rows r=0,1 with column gap g (path step):")
for g in range(0, 8):
    m = measure([(0, 0), (1, g)], 2); print(f"  g={g}: rank={rk(m):.3f}")
print("two paths, same rows 0,1,2: path A columns (0,3,6), path B shifted by d (black on all 6 cells):")
for d in (0, 1, 2, 3, 5, 8):
    cellsA = [(0, 0), (1, 3), (2, 6)]; cellsB = [(r, z + d) for r, z in cellsA]
    mA = measure(cellsA, 3); mAB = measure(cellsA + cellsB, 3)
    print(f"  d={d}: rank(A)={rk(mA):.3f} rank(A∪B)={rk(mAB):.3f}  added rank={rk(mAB)-rk(mA):.3f}")
