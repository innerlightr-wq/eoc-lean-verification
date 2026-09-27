"""Exact confined-ensemble counts for rational vs true barriers (Parts XX, XXX-XXXII).

Monotonicity (PROVED (MATH), trivial): confinement is S_j <= b(j), so b1 <= b2 pointwise implies
W_{b1} subset W_{b2}.  Hence for a lower convergent beta- < alpha < beta+:
        W_{beta-}  subset  W_alpha  subset  W_{beta+}
and the symmetric differences are exactly differences of counts:
        |W_alpha \\ W_{beta-}| = |W_alpha| - |W_{beta-}|,  |W_{beta+} \\ W_alpha| = |W_{beta+}| - |W_alpha|.

This script computes |W_b(J, sigma)| exactly (big-int DP over prefix sums) for the true barrier
and for each convergent, with sigma = floor(J*alpha) fixed by the TRUE alpha in all cases (the
shell is the object the downstream theorems quantify over).
usage: python3 ensembles.py"""
from decimal import Decimal, getcontext
from fractions import Fraction as F
import math

getcontext().prec = 120
AL = Decimal(3).ln() / Decimal(2).ln()
ALF = F(int(AL * 10**60), 10**60)

def floor_alpha(j):
    return (ALF * j).__floor__()

CONV = [(3, 2), (8, 5), (19, 12), (65, 41), (84, 53), (485, 306), (1054, 665)]

def count_words(J, sg, bar):
    """# positive words d_1..d_J, all prefix sums S_j <= bar(j), total = sg.  Exact big ints."""
    top = [min(bar(j), sg) for j in range(J + 1)]
    if top[J] < sg:
        return 0
    f = {0: 1}
    for j in range(1, J + 1):
        g = {}
        cap = top[j]
        for S, v in f.items():
            for S2 in range(S + 1, cap + 1):
                g[S2] = g.get(S2, 0) + v
        f = g
        if not f:
            return 0
    return f.get(sg, 0)

print("exact confined-word counts |W_b(J, sigma)| with sigma = floor(J*alpha)")
print("(monotone: beta<alpha => W_beta subset W_alpha;  beta>alpha => W_alpha subset W_beta)\n")
for J in (40, 60, 80, 120):
    sg = floor_alpha(J)
    Na = count_words(J, sg, floor_alpha)
    print(f"J = {J}, sigma = {sg}:  log2 |W_alpha| = {math.log2(Na):.4f}")
    print("      p/q      side    log2|W_beta|   |W_beta|/|W_alpha|   symmetric-difference ratio")
    for (p, q) in CONV:
        beta = F(p, q)
        side = "above" if beta > ALF else "below"
        Nb = count_words(J, sg, lambda j, p=p, q=q: (p * j) // q)
        if Nb == 0:
            print(f"  {p:>5}/{q:<5} {side:6s}   (empty)")
            continue
        ratio = Nb / Na
        sym = abs(Nb - Na) / Na
        print(f"  {p:>5}/{q:<5} {side:6s}   {math.log2(Nb):12.4f}   {ratio:16.6f}   {sym:.6f}")
    print()
