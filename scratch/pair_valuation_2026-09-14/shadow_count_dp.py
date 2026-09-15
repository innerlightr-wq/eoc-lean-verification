"""Part VIII: counting DP for c-confined prescribed futures that shadow an anchor future.
#{w : |w| = H, w c-confined, w agrees with e* on its first m digits}
  = N(H - m | headroom h)   with   h = c - R_m(e*)   (0 if e*'s first m digits are not c-confined),
where N(n | h) counts words of length n whose drift stays <= h at every step (digits >= 1).
DP state: (t, partial sum S); admissible iff S - t*alpha <= h (decided exactly for rational h)."""
import time
from fractions import Fraction
from math import log2
ALPHA = log2(3)
def v2(n): return (n & -n).bit_length() - 1
def le(S, r, c):  # exact S - r*alpha <= c, c = integer + Fraction offset handled via 2^(q(S)-p) vs 3^(q r)
    c = Fraction(c); p, q = c.numerator, c.denominator; e = q * S - p
    return e < 0 or (1 << e) <= 3 ** (q * r)
def word(m, L):
    out = []
    for _ in range(L):
        x = 3 * m + 1; d = v2(x); out.append(d); m = x >> d
    return out
def count_confined(n, c_minus_R, S_shift, r_shift):
    """words of length n continuing from absolute state (r_shift, S_shift) with R <= c at all steps,
    i.e. S_shift + S' - (r_shift + t) alpha <= c  -- decided exactly with absolute coordinates."""
    c = c_minus_R
    layer = {S_shift: 1}
    states = 1
    for t in range(1, n + 1):
        new = {}
        r = r_shift + t
        for S, w in layer.items():
            d = 1
            while le(S + d, r, c):
                new[S + d] = new.get(S + d, 0) + w
                d += 1
        layer = new
        states += len(layer)
    return sum(layer.values()), states
c = 0
for mu in (27, 703, 10087, 1027431):
    es = word(mu, 400)
    # confinement length of the anchor
    S, L = 0, 0
    while le(S + es[L], L + 1, c):
        S += es[L]; L += 1
    print(f"anchor mu={mu}: L_0 = {L}")
    for H in (50, 100, 200):
        t0 = time.time()
        tot, st = count_confined(H, c, 0, 0)
        row = []
        for m in (0, 5, 10, 20, 40, min(L, H)):
            if m > L or m > H:
                continue
            Sm = sum(es[:m])
            cnt, _ = count_confined(H - m, c, Sm, m)
            row.append(f"m={m}: 2^{log2(cnt)-log2(tot):.1f}" if cnt else f"m={m}: 0")
        print(f"   H={H:3d}: total confined words 2^{log2(tot):.1f}, DP states {st}, "
              f"shadow>=m fraction: {'  '.join(row)}   ({time.time()-t0:.2f}s)")
