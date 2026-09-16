"""Exact check of the hypothesis of EOC.ShapeTailRed.tightTail_of_tilted_choose.

The Lean theorem needs, for some integer tilt u >= 1 and T:
    j0 * Z(u)  <=  rho1 * u^T * C(sigma-1, j0-1),        Z(u) = sum_c (prod_r |B_r|) u^{#tight(c)}
and then gives TightTail(T, rho1) -> ShapeTail -> ... .  Here everything is computed with exact
integers: Z(u) by the block DP, C(sigma-1,j0-1) by Python's comb.

Reported: the cycle-lemma slack C(sigma-1,j0-1)/(j0*Z(1)) (how much the chord-rotation denominator
loses against the true |P_sigma| = Z(1)), and the resulting rho1 = j0*Z(u)/(u^T*C(sigma-1,j0-1)).
usage: python3 exact.py"""
import math
from math import comb

AL = math.log2(3)

def run(J, u, TR):
    R = J // 2
    sg = math.floor(J * AL)
    top = [min(math.floor(i * AL), sg) for i in range(J + 1)]
    # exact integer DP over even prefix sums; weight |B_r| * u^{[|B_r|<=1]}
    f = {0: 1}
    for r in range(R):
        cap = top[2 * r + 1]
        g = {}
        for S, v in f.items():
            for S2 in range(S + 2, top[2 * r + 2] + 1):
                w = min(S2 - 1, cap) - S
                if w >= 1:
                    ww = w * (u if w <= 1 else 1)
                    g[S2] = g.get(S2, 0) + v * ww
        f = g
    Zu = f.get(sg, 0)
    # untilted
    f = {0: 1}
    for r in range(R):
        cap = top[2 * r + 1]
        g = {}
        for S, v in f.items():
            for S2 in range(S + 2, top[2 * r + 2] + 1):
                w = min(S2 - 1, cap) - S
                if w >= 1:
                    g[S2] = g.get(S2, 0) + v * w
        f = g
    Z1 = f.get(sg, 0)
    C = comb(sg - 1, J - 1)
    T = int(TR * R)
    return J, R, sg, Z1, Zu, C, T

print("exact integer check (u = 3, T = 0.55 R)")
print("   J    R    sigma   log2 Z(1)=|P_s|   log2 C(s-1,J-1)   cycle slack log2[C/(J Z1)]"
      "   log2 Z(3)   log2 rho1 = log2[J Z(3)/(3^T C)]   rho1 rate (bits/digit)")
for J in (40, 80, 120, 160, 200):
    J, R, sg, Z1, Zu, C, T = run(J, 3, 0.55)
    if Z1 == 0 or Zu == 0:
        print(f"  {J}: empty"); continue
    lZ1 = math.log2(Z1); lC = math.log2(C); lZu = math.log2(Zu)
    slack = lC - math.log2(J) - lZ1
    lrho = math.log2(J) + lZu - T * math.log2(3) - lC
    print(f"  {J:4d} {R:4d}  {sg:5d}   {lZ1:12.3f}   {lC:14.3f}   {slack:20.3f}"
          f"   {lZu:10.3f}   {lrho:22.3f}   {-lrho/J:10.5f}")

print("\nsame with u = 2 and u = 4 (T = 0.55 R), J = 200:")
for u in (2, 3, 4, 6):
    J, R, sg, Z1, Zu, C, T = run(200, u, 0.55)
    lrho = math.log2(J) + math.log2(Zu) - T * math.log2(u) - math.log2(C)
    print(f"  u = {u}: log2 rho1 = {lrho:.3f}   rate = {-lrho/J:.5f} bits/digit")
