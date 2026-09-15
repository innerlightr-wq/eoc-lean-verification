"""Transport Deficits paper vs. pair-realizer geometry: exact finite checks.

Paper objects are implemented LITERALLY from the paper's definitions (Sections 2-7, App. C):
  C_j = sum_{i<j} 3^{j-1-i} 2^{S_i},  xi_j = -C_j 3^{-j} in Z_2,  chi_j = xi_j mod 2^{S_j},
  beta_j = bit S_j of xi_j,  T_j = (xi_j - chi_j)/2^{S_j},
  A_{j,inf}(n) = sum_{r>=0} 2^{D_r} 3^{-(j+1+r)}  with n's ACTUAL future valuations,
  M_j(n) = v2(T_j - A_{j,inf}(n)).
2-adic quantities are computed modulo 2^P with P chosen so that all truncations are exact.

Claims under test (derived in this round, PROVED (MATH) if the derivation is right):
  (C1) A_{j,inf}(n) = -3^{-j} orbit(n, j)                       [future target = scaled state]
  (C2) T_j = -3^{-j} mu_j,  mu_j := (3^j chi_j + C_j)/2^{S_j}   [past state = scaled anchor state]
  (C3) X_j(n) := T_j - A_{j,inf}(n) = floor(n / 2^{S_j})         [collapse identity]
  (C4) M_j(n) = v2(floor(n / 2^{S_j}))  (infinite iff n < 2^{S_j})
  (C5) least-realizer formula (5): r(D_j) = chi_j + (1 - beta_j) 2^{S_j}  vs repo leastRealizer
  (C6) target-pair valuation: futures agreeing for m digits then a != b give
       v2(A_1 - A_2) = D_m + min(a, b)   (arbitrary AND genuine continuations)
  (C7) N_{D_j}(X, M) = 1 + floor((X - chi_j)/2^{S_j+M})  if beta_j = 1, M >= 1;   0 if beta_j = 0, M >= 1
"""

import random

rng = random.Random(20260916)
P = 48  # 2-adic working precision for T, A comparisons


def v2(n):
    n = abs(n)
    return (n & -n).bit_length() - 1 if n else None  # None = infinite / zero


def a_(m):
    return v2(3 * m + 1)


def T_(m):
    x = 3 * m + 1
    return x >> v2(x)


def word(m, n):
    out = []
    for _ in range(n):
        out.append(a_(m))
        m = T_(m)
    return out


def orbit(m, n):
    for _ in range(n):
        m = T_(m)
    return m


def C_of(d, j):
    C, S = 0, 0
    for i in range(j):
        C = 3 * C + (1 << S)
        S += d[i]
    return C, S


def paper_past(d, j, prec):
    """chi_j, beta_j, T_j mod 2^prec -- literally from xi_j = -C_j 3^{-j}."""
    C, S = C_of(d, j)
    mod = 1 << (S + prec)
    xi = (-C * pow(3, -j, mod)) % mod
    chi = xi % (1 << S)
    beta = (xi >> S) & 1
    T = xi >> S  # (xi - chi)/2^S mod 2^prec
    return chi, beta, T, S, C


def paper_target(fut, j, prec):
    """A_{j,inf} mod 2^prec from a future valuation list long enough that D_L >= prec."""
    mod = 1 << prec
    tot, D = 0, 0
    for r, dr in enumerate(fut):
        if D >= prec:
            return tot
        tot = (tot + pow(2, D, mod) * pow(3, -(j + 1 + r), mod)) % mod
        D += dr
    if D >= prec:
        return tot
    raise ValueError("future too short for requested precision")


def future_of(n, j, prec):
    """n's actual future valuations after j steps, long enough for precision prec."""
    m = orbit(n, j)
    out, D = [], 0
    while D < prec + 2:
        dd = a_(m)
        out.append(dd)
        D += dd
        m = T_(m)
    return out


def least_realizer(d):
    C, S = C_of(d, len(d))
    mod = 1 << (S + 1)
    return (((1 << S) - C) * pow(3, -len(d), mod)) % mod


stat = dict(cases=0, C1=0, C2=0, C3=0, C4=0, C5=0, Minf=0)
seeds = ([rng.randrange(1, 1 << 12) | 1 for _ in range(1500)]
         + [rng.getrandbits(40) | 1 for _ in range(1500)]
         + [rng.getrandbits(200) | 1 for _ in range(1000)])
for n in seeds:
    L = n.bit_length() + 3
    d = word(n, L + 5)
    for j in range(1, L + 1):
        chi, beta, T, S, C = paper_past(d, j, P)
        fut = future_of(n, j, P)
        A = paper_target(fut, j, P)
        mod = 1 << P
        stat["cases"] += 1
        # (C1) A = -3^{-j} orbit(n, j)
        stat["C1"] += (A - (-orbit(n, j) * pow(3, -j, mod))) % mod == 0
        # (C2) T = -3^{-j} mu_j
        mu, rem = divmod(3 ** j * chi + C, 1 << S)
        assert rem == 0
        stat["C2"] += (T - (-mu * pow(3, -j, mod))) % mod == 0
        # (C3) X = floor(n / 2^S) mod 2^P
        X = (T - A) % mod
        stat["C3"] += X == (n >> S) % mod
        # (C4) M via paper vs bit run of n
        Mpaper = v2(X) if X else None  # None: >= P
        Mbits = v2(n >> S) if (n >> S) else None
        stat["C4"] += (Mpaper == Mbits) if (Mbits is not None and Mbits < P) else (Mpaper is None)
        stat["Minf"] += Mbits is None
        # (C5) least realizer formula (5) against the repo's defining congruence
        stat["C5"] += least_realizer(d[:j]) == chi + (1 - beta) * (1 << S)
print("(C1)-(C5) on genuine orbits, every prefix length j = 1..bitlen(n)+3:")
print("   ", stat)

# (C6) target-pair valuation, arbitrary continuations and genuine continuations
def geom():
    q = 1
    while rng.random() < 0.5:
        q += 1
    return q


c6 = dict(arbitrary=0, arb_fail=0, genuine=0, gen_fail=0)
for _ in range(20000):
    j = rng.randint(0, 30)
    m = rng.choice([0, 1, 2, 5, 12])
    common = [geom() for _ in range(m)]
    a, b = rng.sample([1, 2, 3, geom(), rng.randint(1, 15)], 2)
    if a == b:
        continue
    f1 = common + [a] + [geom() for _ in range(80)]
    f2 = common + [b] + [geom() for _ in range(80)]
    need = sum(common) + max(a, b) + 20
    A1, A2 = paper_target(f1, j, need), paper_target(f2, j, need)
    c6["arbitrary"] += 1
    c6["arb_fail"] += v2((A1 - A2) % (1 << need)) != sum(common) + min(a, b)
for _ in range(20000):
    # two genuine realizers of the same prefix: n2 = n1 + 2^{S_j+1} * k
    n1 = rng.getrandbits(rng.choice([20, 60])) | 1
    j = rng.randint(1, 12)
    S = sum(word(n1, j))
    n2 = n1 + (rng.getrandbits(rng.choice([4, 30])) + 1 << (S + 1))
    f1, f2 = future_of(n1, j, 200), future_of(n2, j, 200)
    mm = 0
    while f1[mm] == f2[mm]:
        mm += 1
    need = sum(f1[:mm]) + max(f1[mm], f2[mm]) + 20
    A1, A2 = paper_target(f1, j, need), paper_target(f2, j, need)
    c6["genuine"] += 1
    c6["gen_fail"] += v2((A1 - A2) % (1 << need)) != sum(f1[:mm]) + min(f1[mm], f2[mm])
print("(C6) target-pair valuation v2(A1-A2) = D_m + min(a,b):", c6)

# (C7) exact counting of N_{D_j}(X, M) on fixed prefixes, via the paper's M
print("(C7) N_{D_j}(X,M) on fixed prefixes (paper M computed literally, P =", P, "):")
c7_fail = 0
for trial in range(8):
    seed = rng.getrandbits(30) | 1
    j = rng.randint(3, 6)
    Dj = word(seed, j)
    chi, beta, T, S, C = paper_past(Dj, j, P)
    r = least_realizer(Dj)
    Xmax = 1 << (S + 14)
    Ms = []
    n = r
    while n <= Xmax:
        fut = future_of(n, j, P)
        A = paper_target(fut, j, P)
        X = (T - A) % (1 << P)
        Ms.append(v2(X) if X else P)  # P stands for ">= P" (infinite in fact)
        n += 1 << (S + 1)
    row = []
    for M in range(0, 9):
        emp = sum(x >= M for x in Ms)
        if M == 0:
            pred = len(Ms)
        elif beta == 1:
            pred = 1 + (Xmax - chi) // (1 << (S + M))
        else:
            pred = 0
        c7_fail += emp != pred
        row.append(f"{emp}/{pred}")
    print(f"   D_j={Dj} S_j={S} beta_j={beta} r={r} chi={chi} #realizers<=2^{S+14}={len(Ms)}"
          f"  N(M=0..8) emp/pred: {' '.join(row)}")
print("   C7 mismatches:", c7_fail)
