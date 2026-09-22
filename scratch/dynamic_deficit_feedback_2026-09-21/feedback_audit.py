"""Computational gate for the dynamic-deficit-feedback audit.

Exact integer / Fraction arithmetic only. No floats in any decision.

Purpose (per the audit brief): FALSIFY proposed deterministic lemmas and
calibrate constants. Finite computation cannot establish Type-II behaviour and
is not used for that.

Conventions match EOC/CurryFoundation.lean:
    alpha  = log2 3
    S_N    = sum_{j<N} d_j
    Delta_N = floor(alpha*N) - S_N
    b_{N+1} = floor(alpha*(N+1)) - floor(alpha*N)  in {1,2}
    d_N    = nu_2(3 m_N + 1)
    m_{N+1} = (3 m_N + 1) / 2^{d_N}
    Q_N    = prod_{j<N} (1 + 1/(3 m_j))
"""

from fractions import Fraction
import sys

# alpha = log2 3 as an exact rational lower/upper bracket, refined on demand.
# floor(N*alpha) = floor(N*log2 3) is computed exactly by comparing 3^N with 2^k.


def floor_alpha(n: int) -> int:
    """Exact floor(n * log2 3) via integer comparison 2^k <= 3^n."""
    if n == 0:
        return 0
    k = (3 ** n).bit_length() - 1          # 2^k <= 3^n < 2^(k+1)
    return k


def v2(x: int) -> int:
    return (x & -x).bit_length() - 1


def syracuse_step(m: int):
    t = 3 * m + 1
    d = v2(t)
    return t >> d, d


# ---------------------------------------------------------------- Gate 1
def gate1_identities(m0: int, steps: int) -> bool:
    """Verify, exactly, Delta recursion and the state/deficit formula."""
    m = m0
    S = 0
    Q = Fraction(1)
    ok = True
    for N in range(steps):
        Delta_N = floor_alpha(N) - S
        # state/deficit identity:  m_N = m0 * Q_N * 2^{Delta_N} * 2^{frac(alpha N)}
        # multiply out the fractional part exactly:
        #   m0 * Q_N * 3^N / 2^{S_N} == m_N       (Eliahou-Rozier)
        lhs = Fraction(m0) * Q * Fraction(3 ** N, 2 ** S)
        if lhs != Fraction(m):
            print(f"  IDENTITY FAIL at N={N}: {lhs} != {m}")
            ok = False
        m_next, d = syracuse_step(m)
        b = floor_alpha(N + 1) - floor_alpha(N)
        if b not in (1, 2):
            print(f"  BEATTY GAP FAIL at N={N}: b={b}")
            ok = False
        Delta_next = floor_alpha(N + 1) - (S + d)
        if Delta_next != Delta_N + b - d:
            print(f"  DEFICIT RECURSION FAIL at N={N}")
            ok = False
        Q *= (1 + Fraction(1, 3 * m))
        S += d
        m = m_next
    return ok


# ---------------------------------------------------------------- Gate 2
def gate2_congruences(kmax: int, K: int):
    """nu_2(3m+1) >= k  <=>  m == c_k (mod 2^k); and exact densities."""
    rows = []
    for k in range(1, kmax + 1):
        cls = {m % (2 ** k) for m in range(1, 2 ** (k + 3), 2) if v2(3 * m + 1) >= k}
        inv3 = pow(3, -1, 2 ** k)
        pred = (-inv3) % (2 ** k)
        rows.append((k, sorted(cls), pred, cls == {pred}))
    # densities among odd residues mod 2^K
    odds = [m for m in range(1, 2 ** K, 2)]
    dens = {}
    for m in odds:
        dens[v2(3 * m + 1)] = dens.get(v2(3 * m + 1), 0) + 1
    return rows, {k: Fraction(c, len(odds)) for k, c in sorted(dens.items())}


# ---------------------------------------------------------------- Gate 3
def gate3_ceiling(m0: int, steps: int):
    """Candidate 1: is the state-size ceiling ever tighter than the corridor?"""
    m, S = m0, 0
    tighter = 0
    checked = 0
    for N in range(steps):
        Delta = floor_alpha(N) - S
        b = floor_alpha(N + 1) - floor_alpha(N)
        m_next, d = syracuse_step(m)
        # corridor ceiling (from Delta_{N+1} >= 0):  d <= Delta + b
        corridor = Delta + b
        # state-size ceiling: 2^d | 3m+1  =>  2^d <= 3m+1  =>  d <= log2(3m+1)
        state = (3 * m + 1).bit_length() - 1
        checked += 1
        if state < corridor:
            tighter += 1
        S += d
        m = m_next
    return checked, tighter


def gate3_increments(m0: int, steps: int):
    """Candidate 4 / Gate 2C: classify Delta increments on a real orbit."""
    m, S = m0, 0
    inc = {}
    up_needs = 0
    for N in range(steps):
        b = floor_alpha(N + 1) - floor_alpha(N)
        m_next, d = syracuse_step(m)
        delta_change = b - d
        inc[delta_change] = inc.get(delta_change, 0) + 1
        if delta_change == 1:
            assert b == 2 and d == 1, "increase must be b=2,d=1"
            up_needs += 1
        assert delta_change <= 1, "Delta cannot increase by more than 1"
        S += d
        m = m_next
    return inc, up_needs


def main():
    print("=" * 74)
    print("GATE 1 - exact identities on real orbits")
    print("=" * 74)
    allok = True
    for m0 in (7, 27, 703, 10087):
        ok = gate1_identities(m0, 60)
        allok &= ok
        print(f"  m0={m0:6d}: Eliahou-Rozier state identity, Beatty gap in {{1,2}},")
        print(f"            and Delta_(N+1) = Delta_N + b - d over 60 steps : {'PASS' if ok else 'FAIL'}")
    print(f"\n  all identity checks: {'PASS' if allok else 'FAIL'}")

    print()
    print("=" * 74)
    print("GATE 2A - nu_2(3m+1) >= k is ONE residue class mod 2^k")
    print("=" * 74)
    rows, dens = gate2_congruences(8, 16)
    print(f"  {'k':>3} {'class(es) mod 2^k':>20} {'-3^{-1} mod 2^k':>16} {'single class?':>14}")
    for k, cls, pred, single in rows:
        print(f"  {k:>3} {str(cls):>20} {pred:>16} {str(single):>14}")
    print()
    print("=" * 74)
    print("GATE 2B - exact density of nu_2(3m+1)=k among odd residues mod 2^16")
    print("=" * 74)
    print(f"  {'k':>3} {'density':>12} {'2^-k':>12} {'equal?':>8}")
    for k, f in list(dens.items())[:10]:
        print(f"  {k:>3} {str(f):>12} {str(Fraction(1, 2**k)):>12} {str(f == Fraction(1, 2**k)):>8}")
    print(f"\n  mean of d over this ensemble: {sum(k*f for k,f in dens.items())}")

    print()
    print("=" * 74)
    print("GATE 3 / Candidate 1 - is the state-size ceiling ever tighter")
    print("than the zero-corridor ceiling d <= Delta + b ?")
    print("=" * 74)
    tot = tight = 0
    for m0 in (7, 27, 703, 10087, 106239):
        c, t = gate3_ceiling(m0, 400)
        tot += c
        tight += t
        print(f"  m0={m0:7d}: {t:5d} / {c:5d} steps where state ceiling is tighter")
    print(f"\n  TOTAL: {tight} / {tot}  -> state-size ceiling is {'NEVER' if tight==0 else 'SOMETIMES'} tighter")

    print()
    print("=" * 74)
    print("GATE 2C / Candidate 4 - Delta increment classification")
    print("=" * 74)
    for m0 in (27, 703, 10087):
        inc, ups = gate3_increments(m0, 400)
        pretty = ", ".join(f"{k:+d}:{v}" for k, v in sorted(inc.items(), reverse=True))
        print(f"  m0={m0:6d}  increments {{{pretty}}}")
        print(f"            increases (all with b=2,d=1): {ups}; max increment +1 asserted OK")
    return 0 if allok else 1


if __name__ == "__main__":
    sys.exit(main())
