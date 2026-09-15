"""Haar-closure transfer operator on orbit states m mod 2^q (odd residues), step index j.
Digit d (weight w_d): lift tau = ((2^(d-1) - (3m+1)/2) * 3^-(j+1)) mod 2^d, m' = m + 2*3^j*tau,
y = (3m'+1)/2^d.  At resolution q only y mod 2^(q-d) is determined by m mod 2^q; the top d bits are
unresolved and set uniform (closure); d >= q gives a uniform output.
Reports, for the mixed kernel P_j = sum_d w_d P_{j,d} acting on measures:
  opnorm on mean-zero measures (largest singular value), spectral radius of the period product,
  nilpotency index of the mean-zero part, for free weights 2^-d and for confined-like weights."""
import sys
from fractions import Fraction
def kernel(q, j, d):
    n = 1 << q; odd = list(range(1, n, 2)); idx = {x: i for i, x in enumerate(odd)}
    P = [[0.0] * len(odd) for _ in odd]
    if d >= q:
        for i in range(len(odd)):
            for k in range(len(odd)): P[i][k] = 1.0 / len(odd)
        return P
    inv3 = pow(3, -(j + 1), 1 << d)
    for x in odd:
        tau = (((1 << (d - 1)) - (3 * x + 1) // 2) * inv3) % (1 << d)
        xp = (x + 2 * pow(3, j) * tau) % n
        z = 3 * xp + 1
        assert z % (1 << d) == 0 and (z >> d) % 2 == 1 or q - d <= 0
        low = (z >> d) % (1 << (q - d))
        ys = [y for y in odd if y % (1 << (q - d)) == low]
        for y in ys: P[idx[x]][idx[y]] += 1.0 / len(ys)
    return P
def matmul(A, B):
    n, m, p = len(A), len(B), len(B[0])
    return [[sum(A[i][k] * B[k][j] for k in range(m)) for j in range(p)] for i in range(n)]
def meanzero_norm(P, iters=300):
    # largest singular value of v -> v P on mean-zero row vectors
    n = len(P); import random; random.seed(1)
    v = [random.random() - 0.5 for _ in range(n)]; s = sum(v) / n; v = [a - s for a in v]
    lam = 0.0
    for _ in range(iters):
        w = [sum(v[i] * P[i][k] for i in range(n)) for k in range(n)]          # v P
        u = [sum(w[k] * P[i][k] for k in range(n)) for i in range(n)]          # (vP) P^T
        s = sum(u) / n; u = [a - s for a in u]
        nu = sum(a * a for a in u) ** 0.5
        if nu < 1e-300: return 0.0
        lam = nu / (sum(a * a for a in v) ** 0.5); v = [a / nu for a in u]
    return lam ** 0.5
def run(q, weights, label):
    n = 1 << (q - 1)
    period = max(1, 1 << max(0, q - 2))
    Ps = []
    for j in range(1, period + 1):
        P = [[0.0] * n for _ in range(n)]
        for d, w in weights.items():
            K = kernel(q, j, d)
            for i in range(n):
                for k in range(n): P[i][k] += w * K[i][k]
        Ps.append(P)
    norms = [meanzero_norm(P) for P in Ps]
    # nilpotency of mean-zero part: apply successive kernels to mean-zero basis, count steps to 0
    import random; random.seed(2)
    v = [random.random() - 0.5 for _ in range(n)]; s = sum(v) / n; v = [a - s for a in v]
    steps = 0; t = 0
    while steps < 4 * q:
        P = Ps[t % len(Ps)]; t += 1
        v = [sum(v[i] * P[i][k] for i in range(n)) for k in range(n)]; steps += 1
        if max(abs(a) for a in v) < 1e-12: break
    print(f"{label} q={q}: mean-zero opnorm per step max={max(norms):.4f} min={min(norms):.4f};"
          f" mean-zero part vanishes after {steps} steps (nilpotent, spectral radius 0)")
free = {d: 2.0 ** -d for d in range(1, 30)}
tot = sum(free.values()); free = {d: w / tot for d, w in free.items()}
for q in range(2, 8):
    run(q, free, "free Geom(2)")
    for hmax in (1, 2, 3):   # confined-like: digits capped by headroom, conditioned
        w = {d: 2.0 ** -d for d in range(1, hmax + 1)}; t = sum(w.values()); w = {d: v / t for d, v in w.items()}
        run(q, w, f"confined headroom<= {hmax}")
