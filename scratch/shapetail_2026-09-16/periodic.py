"""Periodic-barrier relaxation: replace top[i] = floor(i*alpha) by floor(i*p/q) with p/q > alpha.

A convergent p/q > alpha gives a barrier that DOMINATES the true one, so it can only increase the
tilted count Z(u): an upper bound on Z(u) for the relaxed barrier is an upper bound for the true one.
The relaxed operator is periodic with period q (in digits), so a super-eigenvector certificate lives
on a FINITE state space (headroom, phase mod q) -- the form EOC.LocalWindow.ker_le_of_superEigen
consumes.  This script measures how much the relaxation costs.
usage: python3 periodic.py"""
import math

AL = math.log2(3)
U = 3
CONV = [(8, 5), (65, 41), (485, 306)]      # convergents of log2 3 that exceed alpha

def Z(J, topf, u):
    R = J // 2
    sg = math.floor(J * AL)
    top = [min(topf(i), sg) for i in range(J + 1)]
    f = {0: 1}
    for r in range(R):
        cap = top[2 * r + 1]
        g = {}
        for S, v in f.items():
            for S2 in range(S + 2, top[2 * r + 2] + 1):
                w = min(S2 - 1, cap) - S
                if w >= 1:
                    g[S2] = g.get(S2, 0) + v * (w * (u if w <= 1 else 1))
        f = g
    return f.get(sg, 0)

for J in (120, 200):
    zt = Z(J, lambda i: math.floor(i * AL), U)
    z1 = Z(J, lambda i: math.floor(i * AL), 1)
    print(f"\nJ = {J}: true barrier   log2 Z({U}) = {math.log2(zt):.3f}, log2 Z(1) = {math.log2(z1):.3f}")
    for p, q in CONV:
        if p / q <= AL:
            print(f"  p/q = {p}/{q} = {p/q:.7f} is NOT above alpha = {AL:.7f}; skipped"); continue
        zr = Z(J, lambda i, p=p, q=q: (i * p) // q, U)
        zr1 = Z(J, lambda i, p=p, q=q: (i * p) // q, 1)
        if zr == 0: print(f"  p/q = {p}/{q}: empty"); continue
        print(f"  p/q = {p}/{q} = {p/q:.7f} (excess {p/q - AL:.2e}):  log2 Z({U}) = {math.log2(zr):.3f}"
              f"  (+{math.log2(zr)-math.log2(zt):.3f} bits, {(math.log2(zr)-math.log2(zt))/J:.5f}/digit)"
              f"   log2 Z(1) = {math.log2(zr1):.3f} (+{math.log2(zr1)-math.log2(z1):.3f})")

print("\nBudget reminder: at J = 200, T = 0.55R, the Lean hypothesis needs log2 Z(3) <= 374.2,")
print("true value 362.5 -> margin 11.7 bits total (0.117 bits/block, 0.0585 bits/digit).")
