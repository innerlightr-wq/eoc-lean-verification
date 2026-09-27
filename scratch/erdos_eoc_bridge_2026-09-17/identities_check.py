"""Exact checks of the identities used in REPORT.md.
(1) Phase chain: theta_r := frac(2^{x} t_b(xi)), t_b = (xi mod 3^b)/3^b.  With D = (digits b, b+1 of 2^{x} xi) = (2^x xi mod 3^{b+2}) // 3^b:
    frac(2^{x+g} t_{b+2}(xi)) == frac(2^g (theta + D)/9)          (exact rationals)
(2) Reciprocity: A = 3^{-b} mod 2^m, B = 2^{-m} mod 3^b  =>  A/2^m + B/3^b == 1 + 1/(2^m 3^b).
(3) Fixed-target form: for rows b_r = B - 2(K-1-r), frac(2^{e} t_{b_r}(2^{x0} xi)) == frac(2^{e} 9^{K-1-r} T), T = frac(2^{x0} t_B(xi))."""
import random
from fractions import Fraction as F
def fr(x): return x - (x.numerator // x.denominator)
random.seed(1)
for trial in range(2000):
    b = random.randrange(3, 40); x = random.randrange(0, 60); g = random.randrange(1, 20)
    xi = random.randrange(1, 3 ** 50)
    tb = F(xi % 3 ** b, 3 ** b); tb2 = F(xi % 3 ** (b + 2), 3 ** (b + 2))
    theta = fr(2 ** x * tb)
    D = ((2 ** x * xi) % 3 ** (b + 2)) // 3 ** b
    assert fr(2 ** (x + g) * tb2) == fr(2 ** g * (theta + D) / 9)
    assert 0 <= D <= 8
print("(1) phase chain identity: 2000 random exact checks OK")
for trial in range(2000):
    b = random.randrange(1, 40); m = random.randrange(1, 80)
    A = pow(3, -b, 2 ** m); Bv = pow(2, -m, 3 ** b)
    assert F(A, 2 ** m) + F(Bv, 3 ** b) == 1 + F(1, 2 ** m * 3 ** b)
print("(2) reciprocity identity: 2000 random exact checks OK")
for trial in range(500):
    K = random.randrange(1, 8); B = 2 * K + random.randrange(3, 30); x0 = random.randrange(0, 40)
    xi = random.randrange(1, 3 ** 60)
    T = fr(2 ** x0 * F(xi % 3 ** B, 3 ** B))
    for r in range(K):
        br = B - 2 * (K - 1 - r)
        for e in range(0, 12):
            lhs = fr(2 ** e * F((2 ** x0 * xi) % 3 ** br, 3 ** br))
            assert lhs == fr(2 ** e * 9 ** (K - 1 - r) * T)
print("(3) fixed-target identity: 500 random windows exact OK")
