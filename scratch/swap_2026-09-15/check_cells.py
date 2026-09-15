"""Exact checks of the swap-angle arithmetic on random cells (big integers).
Cell: pair start i (n = i+2), state S (S <= b(i)), digits d < e (f = e-d), frequency h = 2^a w.
 Delta = h 3^{-n} 2^S (2^e - 2^d) / 2^m mod 1 = (g 3^{-n} mod 2^L)/2^L,  g = w(2^f-1), L = m-a-S-d.
 (1) 3-adic form: Delta = ((-g 2^{-L}) mod 3^n)/3^n + g/(3^n 2^L)  (mod 1)  -- exact identity.
 (2) correction bound g/(3^n 2^L) <= 2^{e+c-sigma-1}/9 when S <= alpha*i + c.
 (3) vertical rigidity: if |x_n| < eta 2^L (bad) then cell (n+1, L) is bad iff 3 | x_n (for eta < 1/4).
 (4) no exact degeneracy: x odd, L >= 1 when a <= t+1."""
import random, math
from fractions import Fraction
random.seed(3); al = math.log2(3)
def cen(x, M):
    x %= M; return x - M if x >= M // 2 else x
bad1 = bad2 = bad3 = bad4 = 0; N = 3000
for _ in range(N):
    c = random.randint(0, 2); J = random.randint(20, 150); t = random.randint(4, 30)
    sig = math.floor(c + J * al); m = sig + t + 1
    i = random.randint(0, J - 2); n = i + 2
    S = random.randint(i, math.floor(c + i * al)); d = random.randint(1, 3); e = d + random.randint(1, 3)
    if S + d + e > sig: continue
    h = random.randint(1, 2 ** t); a = (h & -h).bit_length() - 1; w = h >> a
    g = w * (2 ** (e - d) - 1); L = m - a - S - d
    if L < 1: bad4 += 1; continue
    x = (g * pow(3, -n, 2 ** L)) % 2 ** L
    Delta = Fraction(x, 2 ** L)
    z3 = (-g * pow(2, -L, 3 ** n)) % 3 ** n
    D3 = (Fraction(z3, 3 ** n) + Fraction(g, 3 ** n * 2 ** L)) % 1
    if D3 != Delta: bad1 += 1
    if Fraction(g, 3 ** n * 2 ** L) > Fraction(2 ** (e + c), 9 * 2 ** (sig + 1)): bad2 += 1
    if x % 2 == 0: bad4 += 1
    xc = cen(x, 2 ** L); eta = 0.2
    if abs(xc) < eta * 2 ** L:
        xn = cen((g * pow(3, -(n + 1), 2 ** L)) % 2 ** L, 2 ** L)
        nb = abs(xn) < eta * 2 ** L
        if nb != (xc % 3 == 0): bad3 += 1
print(f"cells tested ~{N}: 3-adic identity failures {bad1}, correction-bound failures {bad2}, vertical-rigidity failures {bad3}, degeneracy/parity failures {bad4}")
