"""Suffix transport + pair/suffix cofactor: finite validation (exact integer arithmetic).

Repository conventions (EOC/ValuationWord.lean, EOC/Realizer.lean): 0-indexed words,
S_t = sum_{i<t} d_i, leastRealizer d N = unique x < 2^(S_N+1) with
3^N x + q_N = 2^S_N (mod 2^(S_N+1)).  sigma^t d := (d_t, d_{t+1}, ...).

Candidates tested:
 (ST)  orbit(r(D), t) = r(sigma^t D)   (mod 2^(S_N - S_t + 1)),   0 <= t <= N
 (PS)  with tau = S_k + min(a,b), m = min(a,b), rho_D = r(sigma^{k+1} D), rho_E likewise,
       r(E) - r(D) = 2^tau Q and
       3^{k+1} Q = 2^{b-m} rho_E - 2^{a-m} rho_D   (mod 2^(min(S_N(D), S_M(E)) - tau + 1))
Also: sharpness of each modulus (+1 must fail somewhere), and prefix-blindness of (PS).
"""

import itertools
import random
from math import log2

ALPHA = log2(3)
rng = random.Random(20260915)


def v2(n):
    n = abs(n)
    return (n & -n).bit_length() - 1


def a_(m):
    return v2(3 * m + 1)


def T(m):
    x = 3 * m + 1
    return x >> v2(x)


def orbit_at(m, n):
    for _ in range(n):
        m = T(m)
    return m


def q_carry(d):
    q, s = 0, 0
    for x in d:
        q = 3 * q + (1 << s)
        s += x
    return q


def r(d):
    S = sum(d)
    mod = 1 << (S + 1)
    x = (((1 << S) - q_carry(d)) * pow(3, -len(d), mod)) % mod
    return x


def geom():
    q = 1
    while rng.random() < 0.5:
        q += 1
    return q


def confined(d):
    s = 0
    for j, x in enumerate(d, 1):
        s += x
        if s > ALPHA * j:
            return False
    return True


# ---------------- (ST) suffix transport ----------------
st = dict(cases=0, fail=0, t0=0, tN=0, tNm1=0, nonleast=0, sharp_fail_plus1=0, confined=0)


def check_st(d, t, x=None):
    N = len(d)
    rD = r(d) if x is None else x
    y = orbit_at(rD, t)
    mod = 1 << (sum(d) - sum(d[:t]) + 1)
    st["cases"] += 1
    if (y - r(d[t:])) % mod:
        st["fail"] += 1
        print("ST COUNTEREXAMPLE", d, t)
    if (y - r(d[t:])) % (mod << 1):
        st["sharp_fail_plus1"] += 1
    st["t0"] += t == 0
    st["tN"] += t == N
    st["tNm1"] += t == N - 1
    st["nonleast"] += x is not None
    st["confined"] += confined(d)


# exhaustive short words, every t in [0, N]
for n in range(1, 7):
    for w in itertools.product(range(1, 5), repeat=n):
        for t in range(0, n + 1):
            check_st(list(w), t)
ex = st["cases"]
# long random words, large digits
for _ in range(20000):
    d = [rng.choice([geom(), geom(), rng.randint(1, 30)]) for _ in range(rng.randint(1, 120))]
    check_st(d, rng.choice([0, len(d), len(d) - 1, rng.randint(0, len(d))]))
# confined words
for _ in range(3000):
    d = []
    for _ in range(rng.randint(1, 80)):
        c = [x for x in (1, 2, 3) if confined(d + [x])]
        if not c:
            break
        d.append(rng.choice(c))
    if d:
        check_st(d, rng.randint(0, len(d)))
# non-least realizers r(D) + 2^(S_N+1) j
for _ in range(5000):
    d = [geom() for _ in range(rng.randint(1, 40))]
    x = r(d) + (1 << (sum(d) + 1)) * rng.randrange(1, 1 << 64)
    check_st(d, rng.randint(0, len(d)), x)
print(f"(ST) {st['cases']} cases ({ex} exhaustive: digits 1..4, N<=6, all t), "
      f"{st['fail']} counterexamples; stats {st}")

# ---------------- (PS) pair/suffix cofactor ----------------
ps = dict(pairs=0, fail=0, sharp_fail_plus1=0, eq_total=0, eq_total_Q_two_cands_ok=0,
          prefix_blind_groups=0, prefix_blind_fail=0)


def pair_data(d, e):
    k = 0
    while d[k] == e[k]:
        k += 1
    A, B = d[k], e[k]
    m = min(A, B)
    tau = sum(d[:k]) + m
    diff = r(e) - r(d)
    assert v2(diff) == tau
    Q = diff >> tau if diff > 0 else -((-diff) >> tau)
    assert Q * (1 << tau) == diff and Q % 2 == 1
    rhoD, rhoE = r(d[k + 1:]), r(e[k + 1:])
    L = min(sum(d), sum(e)) - tau + 1
    pred = (1 << (B - m)) * rhoE - (1 << (A - m)) * rhoD
    return k, A, B, tau, Q, pred, L


def check_ps(d, e):
    k, A, B, tau, Q, pred, L = pair_data(d, e)
    ps["pairs"] += 1
    lhs = pow(3, k + 1) * Q
    if (lhs - pred) % (1 << L):
        ps["fail"] += 1
        print("PS COUNTEREXAMPLE", d, e)
    if (lhs - pred) % (1 << (L + 1)):
        ps["sharp_fail_plus1"] += 1
    if sum(d) == sum(e):
        # Q is then pinned to two candidates by its residue (|Q| < 2^L)
        ps["eq_total"] += 1
        res = (pred * pow(3, -(k + 1), 1 << L)) % (1 << L)
        ps["eq_total_Q_two_cands_ok"] += Q in (res, res - (1 << L))


for n in range(2, 6):
    ws = [list(w) for w in itertools.product(range(1, 4), repeat=n)]
    for d, e in itertools.combinations(ws, 2):
        check_ps(d, e)
ex_ps = ps["pairs"]
for _ in range(20000):
    k = rng.choice([0, 1, 3, 10, 30])
    pre = [geom() for _ in range(k)]
    A, B = rng.sample([1, 2, 3, geom() + 3, rng.randint(1, 20)], 2)
    if A == B:
        continue
    d = pre + [A] + [geom() for _ in range(rng.randint(0, 40))]
    e = pre + [B] + [geom() for _ in range(rng.randint(0, 40))]
    check_ps(d, e)

# prefix-blindness: same (k, a, b, suffixes), different prefix digits -> same Q mod 2^L
for _ in range(3000):
    k = rng.randint(1, 15)
    A, B = rng.sample(range(1, 8), 2)
    sD = [geom() for _ in range(rng.randint(0, 20))]
    sE = [geom() for _ in range(rng.randint(0, 20))]
    residues = set()
    for _ in range(4):
        pre = [geom() for _ in range(k)]
        kk, _, _, tau, Q, pred, L = pair_data(pre + [A] + sD, pre + [B] + sE)
        Lblind = min(A + sum(sD), B + sum(sE)) - min(A, B) + 1  # = L, prefix-free form
        assert Lblind == L
        residues.add(Q % (1 << L))
    ps["prefix_blind_groups"] += 1
    ps["prefix_blind_fail"] += len(residues) != 1
print(f"(PS) {ps['pairs']} pairs ({ex_ps} exhaustive: digits 1..3, length 2..5), "
      f"{ps['fail']} counterexamples; stats {ps}")
