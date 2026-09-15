"""Finite validation of the first-differing-digit pair valuation theorem.

Candidate (repository 0-indexed conventions, EOC/ValuationWord.lean, EOC/Realizer.lean):
  words d, e agree on indices i < k and differ at index k (a := d k, b := e k, a != b);
  S_k := s d k = sum_{i<k} d i.  Then
      v2(r(E) - r(D)) = S_k + min(a, b)
  for r = leastRealizer, and more generally for ANY two seeds realizing the two words
  through step k+1.

All arithmetic is exact (Python ints). leastRealizer is computed from the repository's
defining congruence (3^N x + q_N = 2^S_N mod 2^(S_N+1), x < 2^(S_N+1)) and then checked
independently against the actual accelerated dynamics a(m) = v2(3m+1).

Run:  python3 verify_pair_valuation.py
"""

import itertools
import random
from math import log2

ALPHA = log2(3)


def v2(n):
    assert n != 0
    n = abs(n)
    return (n & -n).bit_length() - 1


def a(m):
    return v2(3 * m + 1)


def T(m):
    x = 3 * m + 1
    return x >> v2(x)


def orbit_word(m, n):
    out = []
    for _ in range(n):
        out.append(a(m))
        m = T(m)
    return out


def orbit_at(m, n):
    for _ in range(n):
        m = T(m)
    return m


def q_carry(d, n):
    """Repository carry: q_0 = 0, q_{j+1} = 3 q_j + 2^{s_j}."""
    q, s = 0, 0
    for j in range(n):
        q = 3 * q + (1 << s)
        s += d[j]
    return q


def least_realizer(d):
    N, S = len(d), sum(d)
    mod = 1 << (S + 1)
    x = (((1 << S) - q_carry(d, N)) * pow(3, -N, mod)) % mod
    # defining congruence, exactly as in EOC/Realizer.lean
    assert (pow(3, N) * x + q_carry(d, N)) % mod == (1 << S) % mod
    return x


def confined(d, c=0.0):
    s = 0
    for j, dj in enumerate(d, start=1):
        s += dj
        if s - ALPHA * j > c:
            return False
    return True


stats = {"pairs": 0, "fail": 0, "k0": 0, "a_lt_b": 0, "b_lt_a": 0, "min_is_1": 0,
         "min_ge_3": 0, "diff_len": 0, "diff_total": 0, "last_digit_div": 0,
         "both_confined": 0, "old_bound_strict": 0, "quot_fail": 0, "struct_fail": 0}


def check_pair(d, e, realize_check=True):
    """d, e: lists (the finite words).  Returns True if the pair is in scope."""
    k = 0
    while k < min(len(d), len(e)) and d[k] == e[k]:
        k += 1
    if k == min(len(d), len(e)):
        return False  # one word is a prefix of the other: no differing digit
    A, B = d[k], e[k]
    Sk = sum(d[:k])
    rD, rE = least_realizer(d), least_realizer(e)
    if realize_check:
        assert rD % 2 == 1 and orbit_word(rD, len(d)) == d
        assert rE % 2 == 1 and orbit_word(rE, len(e)) == e
    stats["pairs"] += 1
    ok = v2(rE - rD) == Sk + min(A, B)
    if not ok:
        stats["fail"] += 1
        print("COUNTEREXAMPLE", d, e, k, v2(rE - rD), Sk + min(A, B))
    # normalized quotient q = (rE - rD) / 2^(Sk+1)
    diff = rE - rD
    if diff % (1 << (Sk + 1)) != 0 or v2(diff >> (Sk + 1)) != min(A, B) - 1:
        stats["quot_fail"] += 1
    # structural identity 3^{k+1}(x'-x) = 2^{S_k}(2^b m'_{k+1} - 2^a m_{k+1})
    lhs = pow(3, k + 1) * (rE - rD)
    rhs = (1 << Sk) * ((1 << B) * orbit_at(rE, k + 1) - (1 << A) * orbit_at(rD, k + 1))
    if lhs != rhs:
        stats["struct_fail"] += 1
    stats["k0"] += k == 0
    stats["a_lt_b"] += A < B
    stats["b_lt_a"] += B < A
    stats["min_is_1"] += min(A, B) == 1
    stats["min_ge_3"] += min(A, B) >= 3
    stats["diff_len"] += len(d) != len(e)
    stats["diff_total"] += sum(d) != sum(e)
    stats["last_digit_div"] += (k == len(d) - 1 or k == len(e) - 1)
    stats["both_confined"] += confined(d) and confined(e)
    stats["old_bound_strict"] += v2(rE - rD) > Sk + 1
    return True


# ---- Block 1: exhaustive small words (digits 1..4, lengths 1..4) --------------------
words = [list(w) for n in range(1, 5) for w in itertools.product(range(1, 5), repeat=n)]
for d, e in itertools.combinations(words, 2):
    check_pair(d, e)
print(f"block 1 (exhaustive, digits 1..4, lengths 1..4, {len(words)} words): "
      f"{stats['pairs']} pairs, {stats['fail']} counterexamples")

# ---- Block 2: random long words, large first-divergence digits -----------------------
rng = random.Random(20260914)


def geom():
    q = 1
    while rng.random() < 0.5:
        q += 1
    return q


before = stats["pairs"]
while stats["pairs"] - before < 20000:
    k = rng.choice([0, 0, 1, 2, 5, 10, 20, 40, 80])
    prefix = [geom() for _ in range(k)]
    A = rng.choice([1, 1, 2, 3, geom(), rng.randint(1, 25)])
    B = rng.choice([1, 2, 3, geom(), rng.randint(1, 25)])
    if A == B:
        continue
    d = prefix + [A] + [geom() for _ in range(rng.choice([0, 0, 1, 3, 10, 40]))]
    e = prefix + [B] + [geom() for _ in range(rng.choice([0, 1, 2, 7, 30]))]
    check_pair(d, e)
print(f"block 2 (random, k up to 80, digits up to 25, independent suffixes): "
      f"{stats['pairs'] - before} pairs, running total {stats['fail']} counterexamples")

# ---- Block 3: confined words only (c = 0) --------------------------------------------
before = stats["pairs"]
tries = 0
while stats["pairs"] - before < 3000 and tries < 10**6:
    tries += 1
    k = rng.randint(0, 30)
    prefix = []
    for _ in range(k):  # grow a confined prefix
        choices = [x for x in range(1, 4) if confined(prefix + [x])]
        if not choices:
            break
        prefix.append(rng.choice(choices))
    if len(prefix) != k:
        continue
    A, B = rng.sample([1, 2, 3], 2)
    d, e = prefix + [A], prefix + [B]
    for _ in range(rng.randint(0, 15)):
        c = [x for x in range(1, 4) if confined(d + [x])]
        if c:
            d.append(rng.choice(c))
    for _ in range(rng.randint(0, 15)):
        c = [x for x in range(1, 4) if confined(e + [x])]
        if c:
            e.append(rng.choice(c))
    if confined(d) and confined(e):
        check_pair(d, e)
print(f"block 3 (both words 0-confined): {stats['pairs'] - before} pairs, "
      f"running total {stats['fail']} counterexamples")

# ---- Block 4: arbitrary seeds (not least realizers), orbit form ----------------------
gen = {"pairs": 0, "fail": 0, "odd": 0, "even_involved": 0}
for _ in range(40000):
    x = rng.randrange(0, 1 << rng.choice([8, 16, 40, 100]))
    y = rng.randrange(0, 1 << rng.choice([8, 16, 40, 100]))
    if x == y:
        continue
    k, wx = 0, []
    while a(orbit_at(x, k)) == a(orbit_at(y, k)):
        wx.append(a(orbit_at(x, k)))
        k += 1
    A, B = a(orbit_at(x, k)), a(orbit_at(y, k))
    gen["pairs"] += 1
    gen["odd"] += x % 2 == 1 and y % 2 == 1
    gen["even_involved"] += x % 2 == 0 or y % 2 == 0
    if v2(y - x) != sum(wx) + min(A, B):
        gen["fail"] += 1
        print("ORBIT-FORM COUNTEREXAMPLE", x, y)
print(f"block 4 (arbitrary seeds incl. even, orbit form): {gen['pairs']} pairs "
      f"({gen['odd']} odd/odd, {gen['even_involved']} with an even seed), "
      f"{gen['fail']} counterexamples")

# ---- Block 5: control -- same S_k but DIFFERENT prefix --------------------------------
ctrl = {"pairs": 0, "formula_holds": 0, "congruent_mod_2^(Sk+1)": 0}
for n in range(1, 5):
    ws = [list(w) for w in itertools.product(range(1, 5), repeat=n)]
    for p, p2 in itertools.combinations(ws, 2):
        if sum(p) != sum(p2):
            continue
        for A, B in [(1, 2), (2, 1), (1, 3), (3, 2)]:
            d, e = p + [A], p2 + [B]
            diff = least_realizer(e) - least_realizer(d)
            ctrl["pairs"] += 1
            ctrl["formula_holds"] += v2(diff) == sum(p) + min(A, B)
            ctrl["congruent_mod_2^(Sk+1)"] += diff % (1 << (sum(p) + 1)) == 0
print(f"block 5 (control: same S_k, different length-k prefix): {ctrl}")

print()
print("coverage:", stats)
