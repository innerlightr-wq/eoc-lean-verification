"""Integer membership in Bruun's reducing classes, and the EOC translation at the moment of certification.

For n >= 2: chi(n) = Bruun's certification level (first k Terras steps with 3^s < 2^k; the class of n mod 2^k is
*reducing), sigma(n) = first k with T^k(n) < n.  EOC (accelerated odd map m -> (3m+1)/2^{v2(3m+1)}) quantities at
the certification point: j = odd steps s, S = halvings = k, R = S - j*log2(3) > 0, and the affine correction
log2 U = log2(T^k(n)/n) + R  (exact orbit identity T^k(n) = n * U * 2^{-R}).  Bruun's class criterion P_TV < P_IV
is R > log2 U evaluated at the least class member.
"""
import math

A = math.log2(3)


def cert(n):
    y, s, k = n, 0, 0
    while True:
        if y % 2:
            y = (3 * y + 1) // 2; s += 1
        else:
            y //= 2
        k += 1
        if 3 ** s < 2 ** k:
            return k, s, y


print(f"{'n':>8} {'chi':>4} {'s=j':>4} {'r=S':>4} {'B=2^r-n (Bruun IV-class)':>28} {'T^r(n)':>10} {'R':>9} {'log2 U':>9} {'standard ops s+r':>16}")
for n in (2, 3, 5, 7, 9, 11, 15, 23, 27, 31, 63, 127, 255, 999, 703, 10087, 35655, 626331):
    k, s, y = cert(n)
    R = k - s * A
    logU = math.log2(y / n) + R
    B = (-n) % 2 ** k
    Bs = str(B) if B < 10 ** 12 else f"2^{k}-{n}"
    print(f"{n:8d} {k:4d} {s:4d} {k:4d} {Bs:>28} {y:10d} {R:9.5f} {logU:9.5f} {s + k:16d}")
