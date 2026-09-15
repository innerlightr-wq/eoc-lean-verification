"""Log-corridor diagnostics (Part X).  COMPUTATIONAL ONLY: no divergent Collatz orbit is known, so every
family below is a clearly labelled proxy.  Exact integer arithmetic for all wall tests:
    R_n <= U                         <=>  2^(S_n - U) <= 3^n                  (U integer)
    R_n >= -B log2(n+1) - C          <=>  2^(S_n + C) * (n+1)^B >= 3^n        (B, C rational via
                                          Fraction powers on both sides, exact integers)
Corridor: -B log2(n+1) - C <= R_n <= U, checked for n >= 1.

  [A] genuine anchors (odd mu, 3 !| mu, random sizes): first exit L_{B,C,U}(mu), exit wall,
      injectivity of the window, the explicit Lean bound (3 e^{7/9} 2^C mu)^{1/(8/9-B)} for B < 8/9,
      and the exact maximal prescribed matching M^max (optimal divergence at the exit step).
  [B] genuine path-record trajectories: how deep finite orbits dip below log walls
      (B_needed = max_n (-R_n - C)/log2(n+1) before the orbit reaches 1).
  [C] synthetic log-floor-hugging prescribed futures e (B' slope): split depth against genuine
      anchors, checked against the Lean bound  M <= U + L*log2(3).
"""
import random
from fractions import Fraction
from math import log2, exp, floor

rng = random.Random(20260918)
ALPHA = log2(3)
K0 = 3 * exp(7 / 9)


def v2(n):
    return (n & -n).bit_length() - 1


def step(m):
    x = 3 * m + 1
    d = v2(x)
    return x >> d, d


def upper_ok(S, n, U):
    e = S - U
    return e < 0 or (1 << e) <= 3 ** n


def lower_ok(S, n, B, C):
    """exact test S - n*alpha >= -B*log2(n+1) - C, i.e. 2^(S+C) (n+1)^B >= 3^n, B = p/q, C integer."""
    B = Fraction(B)
    p, q = B.numerator, B.denominator
    lhs = (1 << (q * (S + C))) * (n + 1) ** p if S + C >= 0 else None
    if lhs is None:
        # 2^(S+C) < 1: compare 3^{qn} * 2^{-q(S+C)} <= (n+1)^p
        return 3 ** (q * n) * (1 << (-q * (S + C))) <= (n + 1) ** p
    return lhs >= 3 ** (q * n)


def exit_data(mu, B, C, U, cap=5000):
    """first n >= 1 with the anchor outside the corridor; wall; injectivity of the window [0, n)."""
    m, S, seen = mu, 0, {mu}
    inj = True
    digits = []
    for n in range(1, cap + 1):
        m2, d = step(m)
        S += d
        digits.append(d)
        up, lo = upper_ok(S, n, U), lower_ok(S, n, B, C)
        if not (up and lo):
            return n, ("upper" if not up else "lower"), inj, digits, S
        if m2 in seen:
            inj = False
        seen.add(m2)
        m = m2
    return None, None, inj, digits, S


def m_max(digits, S_L, L, B, C, U):
    """max prescribed matching over corridor futures: diverge at index L-1 (0-based) with the best
    admissible digit a != e*_{L-1}; value S_{L-1} + min(a, e*_{L-1})."""
    b = digits[L - 1]
    S_prev = S_L - b
    best = None
    for a in range(1, b + 60):
        if a == b:
            continue
        S = S_prev + a
        if upper_ok(S, L, U) and lower_ok(S, L, B, C):
            val = S_prev + min(a, b)
            best = val if best is None else max(best, val)
    return best


print("[A] genuine anchors: first exit from -B log2(n+1) - C <= R_n <= U")
grid = [(Fraction(0), 2, 2), (Fraction(83, 200), 2, 2), (Fraction(4, 5), 2, 2),
        (Fraction(1), 2, 2), (Fraction(6, 5), 2, 2), (Fraction(4, 5), 6, 1)]
anchors = []
for bits in (10, 20, 40, 80, 160):
    for _ in range(300):
        mu = rng.getrandbits(bits) | 1 | (1 << (bits - 1))
        if mu % 3 == 0:
            mu += 2
        anchors.append(mu)
for B, C, U in grid:
    lower = upper = inj_exits = viol = 0
    Ls, Ms, ratio = [], [], []
    bound_bad = 0
    mbound_bad = 0
    for mu in anchors:
        L, wall, inj, digits, S_L = exit_data(mu, B, C, U)
        if L is None:
            continue
        Ls.append(L)
        lower += wall == "lower"
        upper += wall == "upper"
        mm = m_max(digits, S_L, L, B, C, U)
        if mm is not None:
            Ms.append(mm)
            mbound_bad += mm > U + L * ALPHA + 1e-9
        if B < Fraction(8, 9) and inj:
            inj_exits += 1
            # Lean bound applies to the window [0, L) (anchor inside the corridor for n < L)
            if L - 1 >= 1:
                g = 8 / 9 - float(B)
                log_rhs = log2(K0) + C + log2(mu)          # log2(3 e^{7/9} 2^C mu)
                ratio.append(log2(L - 1) / (log_rhs / g))   # log(window) / log(window bound)
                bound_bad += g * log2(L - 1) > log_rhs
    print(f"   B={float(B):.3f} C={C} U={U}: n={len(Ls)} exits: lower {lower}, upper {upper}; "
          f"mean L {sum(Ls)/len(Ls):.1f}, max L {max(Ls)}; mean M^max {sum(Ms)/len(Ms):.1f}; "
          f"M^max > U+L*alpha: {mbound_bad}", end="")
    if B < Fraction(8, 9):
        print(f"; window bound violated: {bound_bad}/{inj_exits}, "
              f"max log(window)/log(bound) = {max(ratio):.3f}")
    else:
        print("  (B >= 8/9: no unconditional bound; Curry covers B < 1.0359 qualitatively)")

print("\n[B] genuine path-record trajectories: depth of lower excursions relative to log walls")
records = [27, 703, 77671, 1212415, 3873535, 80049391, 1410123943, 1980976057694848447]
for mu in records:
    m, S, n = mu, 0, 0
    worst = None
    Rmin, nmin = 0.0, 0
    while m != 1 and n < 10000:
        m, d = step(m)
        S += d
        n += 1
        R = S - n * ALPHA
        if R < Rmin:
            Rmin, nmin = R, n
        val = (-R - 2) / log2(n + 1)
        if worst is None or val > worst[0]:
            worst = (val, n)
    print(f"   mu={mu}: steps to 1: {n}, min R = {Rmin:.2f} at n={nmin}, "
          f"B needed to contain it (C=2): {worst[0]:.3f} (at n={worst[1]})  "
          f"[vs 8/9 = 0.889, 1/beta* = 1.036]")

print("\n[C] synthetic log-floor-hugging prescribed futures vs genuine anchors")
def hugging_word(Bp, C, U, length):
    """greedy: smallest digit keeping R_n >= -Bp log2(n+1) - C; also R_n <= U."""
    w, S = [], 0
    for n in range(1, length + 1):
        d = 1
        while not lower_ok(S + d, n, Bp, C):
            d += 1
        assert upper_ok(S + d, n, U)
        w.append(d)
        S += d
    return w


for Bp in (Fraction(1, 2), Fraction(4, 5), Fraction(1)):
    e = hugging_word(Bp, 2, 2, 400)
    Svals = []
    bad = 0
    Mvals = []
    for _ in range(3000):
        mu = rng.getrandbits(rng.choice([12, 30, 60])) | 1
        if mu % 3 == 0:
            mu += 2
        # anchor word and split depth against e
        m, S, k = mu, 0, 0
        while True:
            m2, d = step(m)
            if d != e[k]:
                break
            S += d
            k += 1
            m = m2
        M = S + min(d, e[k])
        Mvals.append(M)
        # exit step of the anchor from the corridor with the same parameters (B = Bp)
        L, wall, inj, digits, S_L = exit_data(mu, Bp, 2, 2)
        if L is not None and M > 2 + L * ALPHA + 1e-9:
            bad += 1
    print(f"   B'={float(Bp):.2f}: e digit mean {sum(e)/len(e):.3f} (log-hugging drift), "
          f"split depth vs 3000 anchors: mean {sum(Mvals)/len(Mvals):.2f}, max {max(Mvals)}; "
          f"violations of M <= U + L*alpha: {bad}")
