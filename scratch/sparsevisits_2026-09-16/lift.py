"""Exponent-lift structure of 2^{-a} mod 3^D (exact integers).
(1) Verify the triangular lift: for 0 <= a < Q_i = 2*3^(i-1) and k in {0,1,2},
    digit_i(2^{-(a + k Q_i)}) = digit_i(2^{-a}) + k * s_i(a)  (mod 3),  s_i(a) in {1,2} depending only on a mod 2,
    and the lower digits are unchanged (balanced ternary digits of the residue mod 3^D).
(2) Transducer memory: write a in mixed radix a = e_0 + sum_{i>=1} k_i Q_i  (e_0 in {0,1}, k_i in {0,1,2}).
    Is digit_i(2^{-a}) determined by (e_0, k_{i-w..i})?  Report the smallest window w that works.
(3) Short-interval occupancy along consecutive exponents at fixed modulus 3^D for the black cylinder
    (three top balanced digits zero) and a one-digit cylinder: M(L)/L versus the Haar densities 1/27, 1/3."""
import sys
from collections import defaultdict

def bal_digits(x, D):
    """balanced ternary digits of the centered residue x mod 3^D, low to high."""
    M = 3 ** D; x %= M
    if x > M // 2: x -= M
    out = []
    for _ in range(D):
        r = x % 3
        if r == 2: r = -1
        out.append(r); x = (x - r) // 3
    return out

D = int(sys.argv[1]) if len(sys.argv) > 1 else 9
M = 3 ** D; Q = 2 * 3 ** (D - 1)
inv2 = pow(2, -1, M)
digs = []; x = 1
for a in range(Q):
    digs.append(bal_digits(x, D)); x = x * inv2 % M
# (1) triangular lift
ok = True
for i in range(1, D):
    Qi = 2 * 3 ** (i - 1)
    s_by_parity = {}
    for a in range(Qi):
        base = digs[a]
        for k in (1, 2):
            other = digs[a + k * Qi]
            if other[:i] != base[:i]: ok = False
            shift = (other[i] - base[i]) % 3
            key = (a % 2, k)
            if s_by_parity.setdefault(key, shift) != shift: ok = False
print(f"D={D}: triangular lift (lower digits fixed, top digit shifted by k*s(a mod 2)): {ok}")
# (2) memory of the offset
def mixed(a):
    e0 = a % 2; rest = a // 2; ks = []
    for i in range(1, D):
        ks.append(rest % 3); rest //= 3
    return e0, ks                     # ks[i-1] = k_i
for i in (3, D - 1):
    for w in range(0, i + 1):
        table = {}; good = True
        for a in range(Q):
            e0, ks = mixed(a)
            key = (e0, tuple(ks[max(0, i - 1 - w):i]))
            v = digs[a][i]
            if table.setdefault(key, v) != v: good = False; break
        if good:
            print(f"  digit {i}: determined by e_0 and the top {w+1} exponent digits k_{i-w}..k_i  (w = {w} of {i})"); break
# (3) short-interval occupancy along consecutive exponents
def occupancy(pred, L):
    s = [1 if pred(d) else 0 for d in digs]
    cur = sum(s[:L]); best = cur
    for a in range(1, Q):
        cur += s[(a + L - 1) % Q] - s[a - 1]; best = max(best, cur)
    return best, sum(s) / Q
for name, pred in (("black (top 3 digits 0)", lambda d: d[D-1] == 0 and d[D-2] == 0 and d[D-3] == 0),
                   ("one top digit 0", lambda d: d[D-1] == 0)):
    for L in (3, 10, 30, 100, 300):
        best, dens = occupancy(pred, L)
        print(f"  {name:24s} L={L:3d}: max occupancy {best:3d} -> M(L)/L = {best/L:.3f}  (full-period density {dens:.4f})")
