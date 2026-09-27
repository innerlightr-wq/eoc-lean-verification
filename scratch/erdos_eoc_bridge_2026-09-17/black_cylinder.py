"""Part VII: exact form of the Tao-black cell at eta = 1/54 (exhaustive check, exact integers).
For x mod 3^b (b >= 3), centered representative y in (-3^b/2, 3^b/2):
  (i)   54|y| < 3^b                                   [Lean: black_fiftyfourth_iff]
  (ii)  balanced ternary digits e_{b-3}, e_{b-2}, e_{b-1} of y are 0
  (iii) ordinary ternary digits b-3, b-2, b-1 of (x + H_b) mod 3^b equal 1, H_b = (3^b-1)/2 = -1/2 mod 3^b
  (iv)  ||x / 3^b|| < 1/54 (distance to nearest integer)
Also: number of residues = 3^{b-3}; minimal decomposition into 3-adic balls (low digits fixed) needs 3^{b-3}
balls of radius 3^{-b} (no two residues share a ball of radius 3^{-(b-1)}); Haar measure exactly 1/27."""
from fractions import Fraction
def balanced(y, b):
    e = []
    for _ in range(b):
        r = y % 3
        if r == 2: r = -1
        e.append(r); y = (y - r) // 3
    assert y == 0
    return e
for b in range(3, 11):
    m = 3 ** b; H = (m - 1) // 2
    S = []
    for x in range(m):
        y = x if x <= m // 2 else x - m
        i = 54 * abs(y) < m
        ii = balanced(y, b)[b - 3:] == [0, 0, 0]
        w = (x + H) % m
        iii = [(w // 3 ** k) % 3 for k in (b - 3, b - 2, b - 1)] == [1, 1, 1]
        fr = Fraction(x, m); iv = min(fr, 1 - fr) < Fraction(1, 54)
        assert i == ii == iii == iv, (b, x)
        if i: S.append(x)
    assert len(S) == 3 ** (b - 3)
    # ball decomposition: residues mod 3^{b-1} of members must be pairwise distinct (else a radius-3^{-(b-1)} ball would be needed wholly inside S)
    sub = {x % 3 ** (b - 1) for x in S}
    full_balls = sum(1 for r in sub if all(((r + k * 3 ** (b - 1)) in set(S)) for k in range(3)))
    print(f"b={b}: |B_b| = {len(S)} = 3^(b-3); Haar measure {Fraction(len(S), m)}; radius-3^-(b-1) balls fully inside: {full_balls}")
print("(i)<=>(ii)<=>(iii)<=>(iv) verified exhaustively for 3 <= b <= 10")
