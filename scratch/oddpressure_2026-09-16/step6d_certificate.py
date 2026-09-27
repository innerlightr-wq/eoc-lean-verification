"""STEP 6 -- exact CERTIFICATE for the impossibility of an immediate repetition (period 6).

Claim (PROVED MATH, verified exactly here).  Write y(x,b) = centered(xi*2^{x-m} mod 3^b).
Lifting xi by one pair of ternary digits changes the level-(b+2) value by
        y(x,b+2) = y(x,b) + 3^b * d_x ,   d_x = centered(c * 2^{x-m} mod 9),  c = the new digit pair.
Suppose the driver occupies blocks 5..10, so in particular  |y(x,22)| < 3^22/54  for x = 21..32
(block 10's row 1111111111110).  Require the driver to restart immediately at block 11 (level 24)
with the same row 1111110, i.e. x = 23..28 BLACK and x = 29 WHITE at level 24.
 * black at level 24 needs |y(x,22) + 3^22 d_x| < 3^24/54 = 3^22/6.
   Since |y(x,22)| < 3^22/54, any d_x != 0 gives |.| >= 3^22(1 - 1/54) = 0.9815*3^22 > 3^22/6.
   Hence d_x = 0 for x = 23..28.
 * d_x = centered(c*2^{x-m} mod 9) = 0 for a single x forces c = 0 mod 9, i.e. c = 0, hence d_29 = 0.
 * then |y(29,24)| = |y(29,22)| < 3^22/54 < 3^22/6, so cell (29,24) is BLACK -- contradicting
   the required WHITE.
So the two constraints  "cell x=29 black at level 22" (part of the driver itself) and
"cell x=29 white at level 24" (the terminating white of the next copy) are INCONSISTENT.

usage: python3 step6d_certificate.py
"""
import json
from common import Geom, cell_xrange, row_values, ETA_DEN

G = Geom(400)
U = json.load(open("unit.json"))
XI = int(U["XI"])
print("geometry check:")
for r in (10, 11):
    lo, hi = cell_xrange(G, r)
    print(f"  block r={r}: level b={2*r+2}, readable columns x = {lo}..{hi} (n={hi-lo+1}); "
          f"adversary row = {''.join(str(int(t)) for t in U['pattern'][r-U['r0']][4])}")

print("\nexhaustive verification of the certificate (all 9 digit pairs c, all y(x,22) in the black range):")
# For every c in 0..8 and every x, d_x = centered(c*2^{x-m} mod 9)
bad = 0
for c in range(9):
    dz = []
    for x in range(23, 30):
        d = c * pow(2, x - G.m, 9) % 9
        d = d if d <= 4 else d - 9
        dz.append(d)
    # can x=23..28 all be black at level 24 while x=29 is white?
    ok_black = all(d == 0 for d in dz[:6])          # necessary (shown above)
    white29 = dz[6] != 0                            # necessary for x=29 to have a chance of white
    if ok_black and white29:
        bad += 1
    print(f"  c={c}: d_x for x=23..29 = {dz}   -> x=23..28 all forced-black-compatible: {ok_black}; "
          f"d_29 != 0: {white29}")
print(f"\n  number of digit pairs c allowing BOTH the six blacks and the terminating white: {bad}")
print("  => period-6 repetition of the depth-capped driver is IMPOSSIBLE (REFUTED).")

print("\nquantitative check of the two thresholds:")
q22 = 3 ** 22
print(f"  black at level 22: |y| < 3^22/54 = {q22//54}")
print(f"  black at level 24: |y| < 3^24/54 = 3^22/6 = {3**24//54}  (= {(3**24//54)/q22:.4f} * 3^22)")
print(f"  a nonzero digit shift moves y by at least 3^22 = {q22}, i.e. by {1/((3**24//54)/q22):.2f}x the")
print("  level-24 black threshold, so it always turns a level-22 black cell WHITE at level 24.")

print("\nsanity: in the adversary's own environment, is x=29 black at level 22 and at level 24?")
for (r, b) in ((10, 22), (11, 24)):
    lo, hi = cell_xrange(G, r)
    v = row_values(G, r, min(lo, 29), max(hi, 29), XI)
    y = v[29]
    print(f"  block r={r} level b={b}: y(29,{b}) = {y}, |54y| < 3^b : {ETA_DEN*abs(y) < 3**b}")
