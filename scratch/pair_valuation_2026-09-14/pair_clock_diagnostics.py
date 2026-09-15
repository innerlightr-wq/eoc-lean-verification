"""Pair-clock diagnostics (Parts VII-IX). Exact integer dynamics; statistics are COMPUTATIONAL.

Coordinates (diagnostic only, not physical time):
  t_seq = k,  t_arith = S_k,  R_k = S_k - k*log2(3),  tau_split = S_k + min(a, b).

Ensembles:
  U  = uniform odd 2-adic seeds, simulated by random odd 640-bit integers (the first
       ~600 bits of valuation depth are then exactly uniform; all runs stay below S = 250).
  NAT = every odd natural seed below 2^20 (the "natural seed" regime).
"""

import random
from math import log2, sqrt

ALPHA = log2(3)
rng = random.Random(7)


def v2(n):
    n = abs(n)
    return (n & -n).bit_length() - 1


def step(m):
    x = 3 * m + 1
    v = v2(x)
    return x >> v, v


def word(m, n):
    out = []
    for _ in range(n):
        m, v = step(m)
        out.append(v)
    return out, m


def mean_se(xs):
    n = len(xs)
    if n < 2:
        return float("nan"), float("nan"), n
    mu = sum(xs) / n
    var = sum((x - mu) ** 2 for x in xs) / (n - 1)
    return mu, sqrt(var / n), n


def slope(xs, ys):
    n = len(xs)
    mx, my = sum(xs) / n, sum(ys) / n
    sxx = sum((x - mx) ** 2 for x in xs)
    sxy = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    b = sxy / sxx
    res = sum((y - my - b * (x - mx)) ** 2 for x, y in zip(xs, ys)) / (n - 2)
    return b, sqrt(res / sxx)


def rate_table(rows, k, h, label, nbins=5):
    """rows: list of (R_k, dS_h). Quantile bins of R_k, mean dS_h +- SE, and OLS slope."""
    rows = sorted(rows, key=lambda t: t[0])
    n = len(rows)
    print(f"  [{label}] k={k} h={h}  n={n}  (iid Geom(2) prediction: E[dS]={2*h})")
    vals = {}
    for R, y in rows:
        vals.setdefault(round(R, 9), []).append(y)
    keys = sorted(vals)
    bins, cur = [], []
    for key in keys:              # merge whole tie groups until ~n/nbins
        cur.append(key)
        if sum(len(vals[x]) for x in cur) >= n / nbins:
            bins.append(cur); cur = []
    if cur:
        bins.append(cur)
    for bk in bins:
        ys = [y for x in bk for y in vals[x]]
        mu, se, m = mean_se(ys)
        print(f"     R_k in [{bk[0]:+7.2f},{bk[-1]:+7.2f}]  E[dS]={mu:7.3f} +- {se:.3f}  (n={m})")
    b, sb = slope([r[0] for r in rows], [r[1] for r in rows])
    print(f"     OLS slope dE[dS]/dR_k = {b:+.4f} +- {sb:.4f}")


# ------------------------------------------------------------------ Part VII (U)
print("== Part VII: does R_k predict future valuation accumulation? ==")
NU = 60000
KMAX, HMAX = 30, 20
U = []
for _ in range(NU):
    x = rng.getrandbits(640) | 1
    w, _ = word(x, KMAX + HMAX)
    U.append((x, w))
for k in (10, 30):
    for h in (1, 5, 20):
        rows = [(sum(w[:k]) - k * ALPHA, sum(w[k:k + h])) for _, w in U]
        rate_table(rows, k, h, "U, unconditioned")
# past-only confinement vs future-conditioned confinement (k = 10, h = 5)
k, h = 10, 5
past = [(sum(w[:k]) - k * ALPHA, sum(w[k:k + h])) for _, w in U
        if all(sum(w[:j]) <= j * ALPHA for j in range(1, k + 1))]
rate_table(past, k, h, "U, PAST-confined R_j<=0 for j<=k", nbins=3)
fut = [(sum(w[:k]) - k * ALPHA, sum(w[k:k + h])) for _, w in U
       if all(sum(w[:j]) <= j * ALPHA for j in range(1, k + h + 1))]
rate_table(fut, k, h, "U, FUTURE-conditioned R_j<=0 for j<=k+h (selection)", nbins=3)

# ------------------------------------------------------------------ Part VII (NAT)
print("\n== Part VII (natural seeds < 2^20) ==")
NAT = []
for x in range(1, 1 << 20, 2):
    w, _ = word(x, 40)
    NAT.append((x, w))
for k, h in ((5, 5), (10, 5), (20, 5), (20, 20)):
    rows = [(sum(w[:k]) - k * ALPHA, sum(w[k:k + h])) for _, w in NAT]
    rate_table(rows, k, h, "NAT, all")
    # separate the absorbed orbits (value 1 at step k: digits are then 2 forever)
    ms = []
    for x, w in NAT[:: 8]:
        m = x
        for _ in range(k):
            m, _ = step(m)
        ms.append((x, w, m))
    rows = [(sum(w[:k]) - k * ALPHA, sum(w[k:k + h])) for x, w, m in ms if m > 1]
    rate_table(rows, k, h, "NAT, orbit value at step k > 1 (1/8 subsample)")
    rows_m = [(log2(m), sum(w[k:k + h])) for x, w, m in ms if m > 1]
    b, sb = slope([r[0] for r in rows_m], [r[1] for r in rows_m])
    print(f"     control: slope of E[dS] on log2(orbit value at k) = {b:+.4f} +- {sb:.4f}")

# ------------------------------------------------------------------ Part VIII
print("\n== Part VIII: same prefix vs same state ==")
K = 10
cls = {1: [], 2: [], 4: []}
by_S = {}
for x, w in U[:30000]:
    by_S.setdefault(sum(w[:K]), []).append((x, w))
# class 1: exact common prefix of length K, differ at K (same cylinder mod 2^(S_K+1))
tries = 0
while len(cls[1]) < 6000 and tries < 10**5:
    tries += 1
    x, w = U[rng.randrange(30000)]
    SK = sum(w[:K])
    x2 = x + (rng.getrandbits(600) << (SK + 1))
    w2, _ = word(x2, K + 21)
    assert w2[:K] == w[:K]
    if w2[K] != w[K]:
        cls[1].append((x, w, x2, w2))
# class 2: same S_K, different length-K prefix (independent seeds); class 4: |S_K - S'_K| = 1
keys = sorted(by_S)
while len(cls[2]) < 6000 or len(cls[4]) < 6000:
    s = rng.choice(keys)
    A = by_S[s]
    if len(A) >= 2 and len(cls[2]) < 6000:
        (x, w), (x2, w2) = rng.sample(A, 2)
        if w[:K] != w2[:K]:
            cls[2].append((x, w, x2, w2))
    B = by_S.get(s + 1, [])
    if A and B and len(cls[4]) < 6000:
        (x, w), (x2, w2) = rng.choice(A), rng.choice(B)
        cls[4].append((x, w, x2, w2))


def first_diff(w, w2):
    j = 0
    while w[j] == w2[j]:
        j += 1
    return j


for c, name in ((1, "exact common prefix, split at K"), (2, "same S_K, different prefix"),
                (4, "S'_K = S_K + 1 (similar R_K), different prefix")):
    P = cls[c]
    tau = [v2(x2 - x) for x, w, x2, w2 in P]
    SK = [sum(w[:K]) for x, w, x2, w2 in P]
    ok_true = sum(t == sum(w[:first_diff(w, w2)]) + min(w[first_diff(w, w2)], w2[first_diff(w, w2)])
                  for t, (x, w, x2, w2) in zip(tau, P))
    ok_K = sum(t == s + min(w[K], w2[K]) for t, s, (x, w, x2, w2) in zip(tau, SK, P))
    same_cyl = sum(t >= s + 1 for t, s in zip(tau, SK))
    mu, se, n = mean_se([t - s for t, s in zip(tau, SK)])
    # post-split independence: correlation of the two branches' next-10-digit sums
    j0 = [K + 1 for _ in P]  # digits strictly after the state time K
    fa = [sum(w[j:j + 10]) for (x, w, x2, w2), j in zip(P, j0)]
    fb = [sum(w2[j:j + 10]) for (x, w, x2, w2), j in zip(P, j0)]
    ma, mb = sum(fa) / n, sum(fb) / n
    cov = sum((p - ma) * (q - mb) for p, q in zip(fa, fb)) / n
    corr = cov / sqrt(sum((p - ma) ** 2 for p in fa) / n * sum((q - mb) ** 2 for q in fb) / n)
    print(f"  class {c} ({name}): n={n}")
    print(f"     tau = S_j+min(d_j,e_j) at TRUE first difference j: {ok_true}/{n}")
    print(f"     tau = S_K+min(d_K,e_K) (state-at-K formula):       {ok_K}/{n}")
    print(f"     same cylinder mod 2^(S_K+1) (tau >= S_K+1):        {same_cyl}/{n}")
    print(f"     E[tau - S_K] = {mu:+.3f} +- {se:.3f};  post-split branch corr (10 digits) = {corr:+.4f}")

# ------------------------------------------------------------------ Part IX
print("\n== Part IX: pair classes vs future behaviour (class-1 pairs) ==")
P = cls[1]


def fut(w, j, h=10):
    return sum(w[j:j + h])


groups = {}
for x, w, x2, w2 in P:
    k = K
    a, b = w[k], w2[k]
    m = min(a, b)
    tau = sum(w[:k]) + m
    Q = (x2 - x) >> tau if x2 > x else -((x - x2) >> tau)
    keyset = {
        "(a,b) ordered min=1 vs >=2": "min1" if m == 1 else "min>=2",
        "tau - S_K": tau - sum(w[:k]),
        "Q mod 4": Q % 4,
    }
    for name, key in keyset.items():
        groups.setdefault((name, key), []).append((fut(w, k + 1), fut(w2, k + 1),
                                                   w[k + 1], w2[k + 1]))
for (name, key), L in sorted(groups.items(), key=lambda t: (t[0][0], str(t[0][1]))):
    if len(L) < 200:
        continue
    mu, se, n = mean_se([(p + q) / 2 for p, q, _, _ in L])
    p1 = sum((c == 1) for _, _, c, _ in L) / n
    print(f"  {name:28s} = {str(key):6s}  n={n:5d}  E[next-10 dS per branch]={mu:6.3f} +- {se:.3f}"
          f"   P(d_(k+1)=1 in D-branch)={p1:.3f}")

print("\n  Q mod 4 inside the subclass a<b, b-a>=2 (cofactor law predicts Q=1 mod 4 <=> d_(K+1)>=2):")
tab = {}
for x, w, x2, w2 in P:
    a, b = w[K], w2[K]
    if not (a < b and b - a >= 2):
        continue
    tau = sum(w[:K]) + a
    Q = (x2 - x) >> tau if x2 > x else -((x - x2) >> tau)
    tab.setdefault(Q % 4, []).append(w[K + 1])
for key in sorted(tab):
    L = tab[key]
    print(f"     Q mod 4 = {key}: n={len(L)}  P(d_(K+1)=1)={sum(c == 1 for c in L)/len(L):.3f}"
          f"  E[next-10 dS, D-branch]=n/a")

print("\n  NAT two-variable regression dS_h ~ R_k + log2(orbit value at k)  (orbit value > 1):")
for k, h in ((10, 5), (20, 5), (20, 20)):
    X1, X2, Y = [], [], []
    for x, w in NAT[::4]:
        m = x
        for _ in range(k):
            m, _ = step(m)
        if m > 1:
            X1.append(sum(w[:k]) - k * ALPHA); X2.append(log2(m)); Y.append(sum(w[k:k + h]))
    n = len(Y)
    mx1, mx2, my = sum(X1)/n, sum(X2)/n, sum(Y)/n
    a11 = sum((p-mx1)**2 for p in X1); a22 = sum((p-mx2)**2 for p in X2)
    a12 = sum((p-mx1)*(q-mx2) for p, q in zip(X1, X2))
    c1 = sum((p-mx1)*(y-my) for p, y in zip(X1, Y)); c2 = sum((q-mx2)*(y-my) for q, y in zip(X2, Y))
    det = a11*a22 - a12*a12
    b1 = (c1*a22 - c2*a12)/det; b2 = (a11*c2 - a12*c1)/det
    res = sum((y-my-b1*(p-mx1)-b2*(q-mx2))**2 for p, q, y in zip(X1, X2, Y))/(n-3)
    se1 = sqrt(res*a22/det); se2 = sqrt(res*a11/det)
    corr = a12/sqrt(a11*a22)
    print(f"     k={k} h={h} n={n}: coef(R_k)={b1:+.4f}+-{se1:.4f}  coef(log2 m_k)={b2:+.4f}+-{se2:.4f}"
          f"  corr(R_k, log2 m_k)={corr:+.3f}")
