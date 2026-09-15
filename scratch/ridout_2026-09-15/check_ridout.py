"""Exact-arithmetic audit of the Ridout / p-adic Subspace reduction for Tao triangle apexes.

Cell (a,b), b >= 1: y = centered residue of 2^{-a} mod 3^b, X = 2^a y, Y = X - 1 = 3^b z.
Subspace data (n = 2, K = Q, places {inf, 2, 3}, forms inf: X-Y, Y; 2: X, Y; 3: X, Y):
    P = |X-Y| |Y| * |X|_2 |Y|_2 * |X|_3 |Y|_3,   H = max(|X|, |Y|).
Checks (exact, Fractions):
  (1) X - Y = 1, gcd(X, Y) = 1, z = 0 iff a = 0;
  (2) P = y' z' / |X|  (y', z' = {2,3}-free parts of y, z);
  (3) P <= 2|U| with U = y / 3^b   (a >= 1);
  (4) 1 <= H <= 2^a 3^b;
  (5) the reduction:  |U| <= (1/2)(2^a 3^b)^{-delta}  =>  P <= H^{-delta}.
Then reports, over dyadic shells of D = a ln2 + b ln3, the max of s/D where s = ln(eta 3^b/|y|),
and the cells with the largest s/D (a >= 1); and the degenerate column a = 0.
usage: python3 check_ridout.py AMAX BMAX"""
import math, sys
from fractions import Fraction

A, B = int(sys.argv[1]), int(sys.argv[2])
eta = Fraction(1, 54)
LN2, LN3 = math.log(2), math.log(3)


def vp(n, p):
    n = abs(n); k = 0
    while n % p == 0:
        n //= p; k += 1
    return k


def padic(n, p):  # |n|_p as a Fraction
    return Fraction(1, p ** vp(n, p))


def free(n):  # {2,3}-free part of |n|
    n = abs(n)
    while n % 2 == 0: n //= 2
    while n % 3 == 0: n //= 3
    return n


bad = 0; checked = 0; best = []; shell = {}
for b in range(1, B + 1):
    q = 3 ** b; inv2 = (q + 1) // 2; r = 1          # r = 2^{-a} mod q, starting at a = 0
    for a in range(0, A + 1):
        y = r if r <= q // 2 else r - q
        X = (1 << a) * y; Y = X - 1
        assert X - Y == 1 and math.gcd(X, Y) == 1
        if a == 0:
            assert y == 1 and Y == 0                  # degenerate column: z = 0, |U| = 3^{-b}
        else:
            assert Y != 0 and Y % q == 0
            z = Y // q
            P = 1 * abs(Y) * padic(X, 2) * padic(Y, 2) * padic(X, 3) * padic(Y, 3)
            assert P == Fraction(free(y) * free(z), abs(X))                     # (2)
            U = Fraction(abs(y), q)
            assert P <= 2 * U                                                  # (3)
            H = max(abs(X), abs(Y))
            assert 1 <= H <= (1 << a) * q                                      # (4)
            D = a * LN2 + b * LN3
            s = math.log(float(eta * q) / abs(y))
            for delta in (0.05, 0.1, 0.2, 0.3):                                # (5), float margin 1e-9
                if math.log(float(U)) <= math.log(0.5) - delta * D:
                    if not (math.log(float(P)) <= -delta * math.log(H) + 1e-9): bad += 1
            k = int(math.log2(D))
            if s / D > shell.get(k, (-9,))[0]: shell[k] = (s / D, a, b, s)
            best.append((s / D, a, b, s))
            checked += 1
        r = r * inv2 % q

print(f"exact checks passed on {checked} cells (1 <= a <= {A}, 1 <= b <= {B}); reduction failures: {bad}")
print("degenerate column a = 0: y = 1, z = 0, s = ln(eta 3^b) = b ln3 - ln 54  (s/D -> 1): excluded, a >= 1 needed")
print("\nmax s/D over dyadic shells of D = a ln2 + b ln3 (a >= 1):")
for k in sorted(shell):
    v, a, b, s = shell[k]
    print(f"  D in [2^{k:2d}, 2^{k+1:2d}):  max s/D = {v:.4f}  at (a,b) = ({a},{b}), s = {s:.2f}")
best.sort(reverse=True)
print("\ntop cells by s/D (a >= 1):", [(round(v, 3), a, b, round(s, 2)) for v, a, b, s in best[:8]])
big = sorted(best, key=lambda t: -t[3])[:8]
print("top cells by size s:", [(round(s, 2), a, b, round(v, 3)) for v, a, b, s in big])
