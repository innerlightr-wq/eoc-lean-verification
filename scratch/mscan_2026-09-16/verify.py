"""Exact arithmetic facts used in the report (Parts V, XII, XIV)."""
import math, random
# (1) ord_{3^b}(2) = 2*3^{b-1}: 2 is a primitive root mod 3^b
def order(a, n):
    o = 1; x = a % n
    while x != 1: x = x * a % n; o += 1
    return o
print("ord_{3^b}(2) vs 2*3^{b-1}:", [(b, order(2, 3 ** b) == 2 * 3 ** (b - 1)) for b in range(1, 9)])
# (2) each unit cylinder mod 3^K is hit by exactly one residue class of m mod 2*3^{K-1}
K = 6; q = 3 ** K; P = 2 * 3 ** (K - 1); lam = 5
hit = {}
for m in range(P):
    hit.setdefault(lam * pow(2, -m, q) % q, []).append(m)
units = [u for u in range(q) if u % 3]
print(f"K={K}: #units={len(units)}, #distinct values of lam*2^-m over one period={len(hit)}, "
      f"each hit once: {all(len(v) == 1 for v in hit.values())}")
# (3) Lipschitz dependence of Psi on deep digits: one block changes N_odd by <= 1, so Psi by <= log2(s)/J;
#     digits below depth (1-delta)J affect at most delta*R blocks.
for s in (1.5, 3.0):
    print(f"  s={s}: a change of the last delta*J ternary digits moves Psi by at most "
          f"delta*log2(s)/2 = delta*{math.log2(s) / 2:.3f}")
# (4) cylinder count of a set of measure 2^{-cJ} at depth J
for J, c in ((400, 0.02), (400, 0.05), (1200, 0.02)):
    print(f"  J={J}, measure 2^-{c}J: #cylinders at depth J >= 2^{{{(math.log2(3) - c) * J:.0f}}}, "
          f"m-range needed ~ {J} values")
