"""Seed-size versus confined drift depth, and the tighter non-descent wedge (Parts XI-XXII, XLVIII-LIX).

By the seed-equivalence (prefix locking, part 9) the least realizer of a word equals the least seed whose own
word it is, so every "minimum over words" here is computed by scanning seeds.

For odd m with word d_1.. and S_j, R_j = S_j - j log2 3:
  L_c(m)  = max N with R_j <= c for all j <= N           (c-confined prefix length)
  Q_c(m)  = -min_{j <= L_c(m)} R_j                        (deepest drift reached while c-confined)
Computed:
  (1) excursion frontier r_exc(Q) = min{m : Q_1(m) >= Q}, and log2 r_exc(Q) / Q  (the constant c in the
      target theorem  R_j <= -Q  =>  m >= 2^{cQ}); the all-ones family gives m = 2^r - 1 at Q = 0.585 r,
      i.e. c = 1.71.
  (2) the frontier of Q_1(m)/log2 m  (falsification of "depth is O(log m)").
  (3) the same for the tighter barrier c = 0.5, which is what a minimal counterexample must satisfy for
      j <= m (since its true ceiling is R_j <= j/(3m ln 2) <= 0.481 there).
usage: python3 depth.py MMAX"""
import math, sys

AL = math.log2(3)
MMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 2000000
NCAP = 400

def run(c):
    top = [math.floor(j * AL + c) for j in range(NCAP + 2)]
    rexc = {}            # Q (integer floor) -> least seed reaching depth >= Q
    maxratio = (0.0, 0, 0.0)   # Q/log2 m
    maxL = (0.0, 0, 0)         # L/m
    bestL = 0; firstL = {}
    m = 3
    while m <= MMAX:
        x = m; S = 0; j = 0; minR = 0.0
        while j < NCAP:
            v = 3 * x + 1; a = (v & -v).bit_length() - 1
            if S + a > top[j + 1]: break
            S += a; j += 1; x = v >> a
            R = S - j * AL
            if R < minR: minR = R
        Q = -minR
        qi = int(Q)
        for t in range(qi + 1):
            if t not in rexc: rexc[t] = m
        lg = math.log2(m)
        if Q / lg > maxratio[0]: maxratio = (Q / lg, m, Q)
        if j / m > maxL[0]: maxL = (j / m, m, j)
        if j > bestL:
            for n in range(bestL + 1, j + 1): firstL[n] = m
            bestL = j
        m += 2
    return rexc, maxratio, maxL, bestL, firstL

for c in (1.0, 0.5):
    rexc, maxratio, maxL, bestL, firstL = run(c)
    print(f"=== barrier R_j <= {c} (seeds 3..{MMAX}) ===")
    print(f"  deepest confined prefix L_c = {bestL};  max L_c(m)/m = {maxL[0]:.4f} at m = {maxL[1]} (L = {maxL[2]})")
    print(f"  max Q_c(m)/log2 m = {maxratio[0]:.4f} at m = {maxratio[1]} (Q = {maxratio[2]:.3f})")
    print("   Q   r_exc(Q) = least seed reaching depth Q     log2 r_exc / Q")
    for Q in sorted(rexc):
        if Q >= 2 and (Q <= 8 or Q % 2 == 0):
            r = rexc[Q]
            print(f"  {Q:3d}  {r:12d}    {math.log2(r)/Q:8.3f}")
    print(f"  (all-ones family: m = 2^r - 1 at Q = 0.585 r, i.e. log2 m / Q = 1.710)")
    print()
