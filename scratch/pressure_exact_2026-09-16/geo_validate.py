"""Check the O(sigma) recurrence against the direct definition, and the exact path identity
sum_P 3^N = ker_geo(0->sigma) / (p^j q^(sigma-j))."""
import math
from pexact import Instance, log2ratio
from geo import apply, make_ops, global_geo
def direct(I, r, f, s, p, q):
    top = I.top; cap = top[2*r+1]; H = I.H[r]; lo_n = 2*r+2
    out = []
    for x in range(2*r, top[2*r] + 1):
        acc = 0.0
        for y in range(x + 2, top[2*r+2] + 1):
            v = min(y - 1, cap)
            if v - 1 < x: continue
            W = (v - x) + (s - 1) * (H[v - 1] - H[x])
            acc += p*p*q**(y - x - 2) * W * f[y - lo_n]
        out.append(acc)
    return out
import random
random.seed(1); err = 0.0
for j, t, lam in ((40, 5, 1), (60, 3, 7), (100, 17, 5), (200, 33, 11)):
    I = Instance(j, t, lam=lam, D=6, mode='2adic'); p, q = make_ops(I)
    for r in range(I.R):
        f = [random.random() for _ in range(I.top[2*r+2] - 2*r - 2 + 1)]
        a = apply(I, r, f, 3.0, p, q, 2*r+2); b = direct(I, r, f, 3.0, p, q)
        err = max(err, max(abs(u - v) / max(1e-300, abs(v)) for u, v in zip(a, b) if v > 1e-250) if b else 0)
print("recurrence vs direct: max relative error", err)
for j, t, lam, D in ((100, 17, 1, 108), (200, 33, 5, 54), (400, 66, 1, 108)):
    I = Instance(j, t, lam=lam, D=D, mode='auto'); p, q = make_ops(I)
    Z3 = I.moment(3)
    lhs = math.log2(Z3.numerator if hasattr(Z3,'numerator') else Z3) if Z3 < 2**1000 else Z3.bit_length() + math.log2(Z3 / 2**(Z3.bit_length()) ) if False else None
    lz = log2ratio(Z3, 1)
    rhs = global_geo(I, 3.0, pinned=True) - (j * math.log2(p) + (I.sg - j) * math.log2(q))
    print(f"j={j}: log2 sum 3^N = {lz:.6f}; log2 ker_geo - log2(p^j q^(s-j)) = {rhs:.6f}")
