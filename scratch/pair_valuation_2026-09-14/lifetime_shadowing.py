"""Part IX check: for beta_j = 1 (least realizer r = chi_j < 2^{S_j}), the paper's perfect-transport
lifetime m*(j) of a realizer n (max m with D_m(n) <= M_j(n)) equals the shadowing length m of r's own
future word (first divergence of the two futures after step j), plus 1 iff n's divergent digit < r's.
M_j(n) = v2(n >> S_j) (collapse identity, verified in transport_collapse_check.py)."""
import random
rng = random.Random(5)
def v2(n): return (n & -n).bit_length() - 1
def step(m):
    x = 3 * m + 1; v = v2(x); return x >> v, v
def word(m, L):
    out = []
    for _ in range(L):
        m, v = step(m); out.append(v)
    return out
tot = bad = beta1 = 0
for _ in range(20000):
    seed = rng.getrandbits(rng.choice([24, 60])) | 1
    j = rng.randint(1, 8)
    w = word(seed, j); S = sum(w)
    r = seed % (1 << (S + 1))
    # least realizer = unique realizer below 2^{S+1}
    if r >= (1 << S):
        continue  # beta_j = 0: M_j = 0 for every realizer (checked separately)
    beta1 += 1
    n = r + (rng.getrandbits(rng.choice([3, 20, 50])) + 1 << (S + 1))
    X = n >> S
    M = v2(X)
    fn, fr = word(n, j + 400)[j:], word(r, j + 400)[j:]
    D, mstar = 0, 0
    while D + fn[mstar] <= M:
        D += fn[mstar]; mstar += 1
    m = 0
    while fn[m] == fr[m]:
        m += 1
    pred = m + (1 if fn[m] < fr[m] else 0)
    tot += 1; bad += mstar != pred
print(f"beta_j=1 cases: {tot}; lifetime == shadowing(+1 if n's divergent digit smaller): {tot-bad}/{tot}")
