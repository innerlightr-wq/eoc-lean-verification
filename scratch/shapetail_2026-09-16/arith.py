"""The single remaining hypothesis of EOC.ShapeCertificate.shapeTail_of_arith.

    j0 * (3/2)^(j0/2) * 2^sigma  <=  rho1 * 3^T * C(sigma-1, j0-1).

Everything is explicit: no dynamics, no certificate, no operator.  This script checks it exactly
(Python big ints / exact logs) for the Collatz parameters sigma = floor(j0*alpha), T = c*R, and reports
the largest rho1-exponent gamma with rho1 = 2^{-gamma*j0} for which it holds, plus the effect of
replacing C by the entropy lower bound  C(n,k) >= 2^{n H(k/n)}/(n+1)  (the bound a Lean proof would use).
usage: python3 arith.py"""
import math
from math import comb, log2

AL = math.log2(3)

def H(x):
    return -x * log2(x) - (1 - x) * log2(1 - x)

print("   J     sigma    T=0.60R   log2 LHS    log2 C      gamma (exact C)   gamma (entropy bound)")
for J in (200, 300, 400, 600, 800, 1200):
    R = J // 2
    sg = math.floor(J * AL)
    for frac in (0.60,):
        T = int(frac * R)
        lhs = log2(J) + R * log2(1.5) + sg
        n, k = sg - 1, J - 1
        lC = log2(comb(n, k))
        # entropy lower bound C(n,k) >= 2^{n H(k/n)} / (n+1)
        lC_lb = n * H(k / n) - log2(n + 1)
        rhs0 = T * log2(3) + lC
        rhs0_lb = T * log2(3) + lC_lb
        gam = (rhs0 - lhs) / J
        gam_lb = (rhs0_lb - lhs) / J
        print(f"  {J:5d}  {sg:6d}   {T:6d}   {lhs:9.2f}  {lC:9.2f}     {gam:+.5f}"
              f"            {gam_lb:+.5f}")

print("\nsame at T/R = 0.62 (still inside the N0 = 10 budget 0.636 - K/R):")
print("   J     gamma (exact C)   gamma (entropy bound)")
for J in (200, 400, 800, 1200):
    R = J // 2
    sg = math.floor(J * AL)
    T = int(0.62 * R)
    lhs = log2(J) + R * log2(1.5) + sg
    n, k = sg - 1, J - 1
    gam = (T * log2(3) + log2(comb(n, k)) - lhs) / J
    gam_lb = (T * log2(3) + n * H(k / n) - log2(n + 1) - lhs) / J
    print(f"  {J:5d}     {gam:+.5f}            {gam_lb:+.5f}")
