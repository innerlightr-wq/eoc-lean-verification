#!/usr/bin/env python3
"""
confined_composition_asymptotics.py

Phase I (normalization/asymptotic-scale audit) and Phase III (exact
confined-composition experiments) of the constrained-word theorem audit.

DEFINITIONS (matching the repository's own Lean conventions exactly):
  - A length-N valuation word is a tuple (d_1,...,d_N), d_i >= 1 integers.
  - s_j = d_1+...+d_j (prefix sum); S_N = s_N (total).
  - alpha = log_2(3) (EOC.Confinement.alpha).
  - R_j = s_j - j*alpha (EOC.Confinement.R).
  - Confined(c, d, N): R_j <= c for all 0<=j<=N (EOC.Confinement.Confined).
  - W_c(N, s) := {words of length N, total valuation s, confined through N}.
  - A_N := |W_c(N, s_N)| for a chosen endpoint convention s_N.
  - U_N := C(s_N - 1, N - 1), the UNRESTRICTED shell count (stars and bars).

EXACT BARRIER, reused verbatim from the repository's own established
convention (explorations/hypercuboid_transfer/scripts/round2_verification.py,
`confined_exact`): R_j <= c  <=>  s_j - j*alpha <= c  <=>  s_j - c <= j*alpha
<=> 2^(s_j - c) <= 3^j (since alpha = log_2 3), decided by EXACT integer
comparison -- no floating-point alpha ever enters a confinement decision.

Audit note (Phase 0): explorations/hypercuboid_transfer's own reports
repeatedly cite `EOC.CompositionCounting.valuationShell_card` as an
"already proved" Lean theorem for the unrestricted shell count. THIS FILE
DOES NOT EXIST anywhere in the repository (confirmed by `find` and by
`EOC.lean`'s import list, which has no `CompositionCounting` entry). The
mathematical claim (stars-and-bars) is true and elementary, but it is NOT
currently a Lean theorem in this repository -- this module recomputes it
independently in Python and flags the discrepancy; see
docs/CONSTRAINED_WORD_THEOREM_AUDIT.md.
"""

from __future__ import annotations

import json
import math
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Dict, List, Optional, Tuple

from fractions import Fraction as F

ROOT = Path(__file__).resolve().parent.parent
RESULTS = ROOT / "results" / "constrained_word_asymptotics"

ALPHA = math.log2(3)          # for DISPLAY only -- never used to decide confinement
RHO = 1.0 / ALPHA


# ===========================================================================
# Exact barrier (integral c only; matches the repository's own convention)
# ===========================================================================

def confined_exact(Sj: int, j: int, c: int) -> bool:
    """R_j <= c  <=>  2^(Sj-c) <= 3^j, decided by exact integer comparison.
    Reused verbatim from round2_verification.py's own convention."""
    if Sj <= c:
        return True
    return (2 ** (Sj - c)) <= (3 ** j)


# ===========================================================================
# Phase I: unrestricted shell count and Stirling normalization
# ===========================================================================

def unrestricted_shell(N: int, s: int) -> int:
    """#{(d_1,...,d_N): d_i>=1 integers, sum=s} = C(s-1, N-1). Exact."""
    if s < N:
        return 0
    return math.comb(s - 1, N - 1)


def binary_entropy(p: float) -> float:
    if p <= 0.0 or p >= 1.0:
        return 0.0
    return -p * math.log2(p) - (1 - p) * math.log2(1 - p)


def log2_choose_exact(n: int, k: int) -> float:
    """log2(C(n,k)) computed exactly then converted -- exact for the integer,
    float only in the final log conversion (display precision only, never
    used to decide anything combinatorial)."""
    if k < 0 or k > n:
        return float("-inf")
    val = math.comb(n, k)
    return math.log2(val)


@dataclass
class ShellAsymptoticRow:
    N: int
    s_N: int
    convention: str
    log2_U_N_exact: float
    predicted_extensive_alphaNH2: float
    predicted_full_T2: float
    residual_after_extensive: float
    residual_after_T2_minus_half_logN: float


def stirling_prediction(N: int, s_N: int) -> Tuple[float, float]:
    """Returns (alpha*N*H2(rho) term evaluated at the ACTUAL s_N/N ratio,
    full T2 prediction alpha*N*H2(rho) - 0.5*log2(N) + C(convention)).
    Uses the ACTUAL ratio p = N/s_N (not the limiting rho) for the leading
    term, since that is what is actually being compared against log2(U_N)."""
    p = N / s_N
    leading = s_N * binary_entropy(p) / 1.0  # s*H2(N/s), in bits (log2 H2)
    # Endpoint-convention constant, derived by hand (Phase I):
    # log2 C(s-1,N-1) = (s-1)*H2((N-1)/(s-1)) - 0.5*log2(2*pi*(N-1)*(s-N)/(s-1)) + o(1)
    # We evaluate the correction term explicitly rather than assuming it.
    n_eff, k_eff = s_N - 1, N - 1
    if k_eff <= 0 or n_eff <= k_eff:
        return leading, leading
    p_eff = k_eff / n_eff
    leading_eff = n_eff * binary_entropy(p_eff)
    correction = -0.5 * math.log2(2 * math.pi * n_eff * p_eff * (1 - p_eff))
    return leading, leading_eff + correction


def shell_normalization_audit(Ns: List[int], convention: str) -> List[ShellAsymptoticRow]:
    rows = []
    for N in Ns:
        if convention == "floor":
            s_N = math.floor(ALPHA * N)
        elif convention == "ceil":
            s_N = math.ceil(ALPHA * N)
        else:
            raise ValueError(convention)
        if s_N < N:
            s_N = N
        log2U = log2_choose_exact(s_N - 1, N - 1)
        extensive_only, full_T2 = stirling_prediction(N, s_N)
        rows.append(ShellAsymptoticRow(
            N=N, s_N=s_N, convention=convention,
            log2_U_N_exact=log2U,
            predicted_extensive_alphaNH2=extensive_only,
            predicted_full_T2=full_T2,
            residual_after_extensive=log2U - extensive_only,
            residual_after_T2_minus_half_logN=log2U - full_T2,
        ))
    return rows


# ===========================================================================
# Phase III: exact confined-word counts via forward DP
# ===========================================================================

def confined_count_forward_dp(N: int, s_target: int, c: int, d_max: Optional[int] = None) -> int:
    """Forward DP: exact count of length-N positive-integer words with total
    s_target, confined (R_j<=c for all j<=N).

    KEY PERFORMANCE FACTS (both proved, not just assumed):
    (1) for FIXED j and c, confined_exact(S,j,c) is monotonically
        non-increasing in S once S>c (2^(S-c) is strictly increasing in S,
        so once it exceeds the fixed bound 3^j it stays exceeded for every
        larger S). The inner loop over digit d therefore BREAKS as soon as
        confinement first fails, rather than testing every larger d.
    (2) 3^j depends only on j, not on the state or digit -- it is computed
        ONCE per outer iteration and reused, rather than recomputed inside
        `confined_exact` on every single (state, digit) trial. Without both
        fixes this DP is intractable past a few hundred N (recomputing a
        ~j*log10(3)-digit power for every rejected digit dominates runtime).
    """
    dp: Dict[int, int] = {0: 1}
    for j in range(1, N + 1):
        ndp: Dict[int, int] = {}
        cap = d_max if d_max is not None else (s_target + 1)
        pow3j = 3 ** j
        for Sj_prev, cnt in dp.items():
            d = 1
            while Sj_prev + d <= s_target and d <= cap:
                Sj = Sj_prev + d
                ok = Sj <= c or (2 ** (Sj - c)) <= pow3j
                if ok:
                    ndp[Sj] = ndp.get(Sj, 0) + cnt
                    d += 1
                else:
                    break  # monotonicity: no larger d at this (j,c) can be confined either
        dp = ndp
        if not dp:
            break
    return dp.get(s_target, 0)


def brute_force_count(N: int, s_target: int, c: int) -> int:
    """Ground truth via explicit recursive enumeration -- ONLY for small
    (N, s_target); used exclusively by the test suite for cross-validation."""
    count = 0

    def rec(j, Sj):
        nonlocal count
        if j == N:
            if Sj == s_target:
                count += 1
            return
        d = 1
        while Sj + d <= s_target:
            Snext = Sj + d
            if confined_exact(Snext, j + 1, c):
                rec(j + 1, Snext)
            d += 1

    rec(0, 0)
    return count


def default_s_N(N: int, convention: str = "floor") -> int:
    if convention == "floor":
        return max(N, math.floor(ALPHA * N))
    if convention == "ceil":
        return max(N, math.ceil(ALPHA * N))
    raise ValueError(convention)


@dataclass
class CountAsymptoticRow:
    N: int
    s_N: int
    c: int
    convention: str
    A_N: int
    U_N: int
    log2_A_N: float
    log2_U_N: float
    D_N: float               # log2(U_N) - log2(A_N)
    q_N: float                # A_N / U_N (as float, DISPLAY only)
    q_N_exact_str: str        # exact fraction, as a string, for the record


def compute_count_asymptotics(Ns: List[int], c: int, convention: str = "floor") -> List[CountAsymptoticRow]:
    rows = []
    for N in Ns:
        s_N = default_s_N(N, convention)
        A_N = confined_count_forward_dp(N, s_N, c)
        U_N = unrestricted_shell(N, s_N)
        if A_N == 0:
            continue
        log2A = math.log2(A_N)
        log2U = math.log2(U_N)
        qfrac = F(A_N, U_N)
        rows.append(CountAsymptoticRow(
            N=N, s_N=s_N, c=c, convention=convention, A_N=A_N, U_N=U_N,
            log2_A_N=log2A, log2_U_N=log2U, D_N=log2U - log2A,
            q_N=float(qfrac), q_N_exact_str=f"{qfrac.numerator}/{qfrac.denominator}",
        ))
    return rows


def effective_exponent_sequence(rows: List[CountAsymptoticRow]) -> List[Tuple[int, int, float]]:
    """Successive-size effective exponent: gamma_eff between consecutive N's,
    from q_N ~ N^{-gamma} => gamma_eff = -(log q_{N2}-log q_{N1})/(log N2-log N1)."""
    out = []
    for i in range(len(rows) - 1):
        r1, r2 = rows[i], rows[i + 1]
        if r1.q_N <= 0 or r2.q_N <= 0:
            continue
        gamma_eff = -(math.log(r2.q_N) - math.log(r1.q_N)) / (math.log(r2.N) - math.log(r1.N))
        out.append((r1.N, r2.N, gamma_eff))
    return out


def dense_sweep_regression(N_lo: int, N_hi: int, c: int, convention: str = "floor") -> Dict:
    """A dense (step=1) sweep of q_N over [N_lo,N_hi], with an ordinary
    least-squares fit of log(q_N) vs log(N) over the WHOLE range (not just
    two endpoints), plus fits over the first and second HALF separately
    (interval bounds / held-out-range check: if the two half-range slopes
    disagree substantially, a single stable exponent is not supported)."""
    rows = compute_count_asymptotics(list(range(N_lo, N_hi + 1)), c, convention)
    xs = [math.log(r.N) for r in rows]
    ys = [math.log(r.q_N) for r in rows]

    def ols_slope(xs, ys):
        n = len(xs)
        mx, my = sum(xs) / n, sum(ys) / n
        num = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
        den = sum((x - mx) ** 2 for x in xs)
        slope = num / den
        intercept = my - slope * mx
        # residual standard error of the slope (classical OLS formula)
        resid = [y - (slope * x + intercept) for x, y in zip(xs, ys)]
        s2 = sum(r ** 2 for r in resid) / max(1, n - 2)
        se_slope = math.sqrt(s2 / den) if den > 0 else float("nan")
        return slope, se_slope

    full_slope, full_se = ols_slope(xs, ys)
    mid = len(xs) // 2
    first_slope, first_se = ols_slope(xs[:mid], ys[:mid])
    second_slope, second_se = ols_slope(xs[mid:], ys[mid:])

    return {
        "N_range": [N_lo, N_hi], "c": c, "n_points": len(rows),
        "full_range_slope_negGamma": full_slope, "full_range_se": full_se,
        "first_half_slope_negGamma": first_slope, "first_half_se": first_se,
        "second_half_slope_negGamma": second_slope, "second_half_se": second_se,
        "gamma_full": -full_slope, "gamma_first_half": -first_slope, "gamma_second_half": -second_slope,
    }


def main():
    RESULTS.mkdir(parents=True, exist_ok=True)
    manifest: Dict = {}

    print("=" * 78)
    print("PHASE I: Stirling normalization audit (floor vs ceil endpoint)")
    print("=" * 78)
    Ns_shell = [50, 100, 200, 400, 800, 1600, 3200]
    for convention in ("floor", "ceil"):
        print(f"\n--- convention: s_N = {convention}(alpha*N) ---")
        rows = shell_normalization_audit(Ns_shell, convention)
        for r in rows:
            print(f"  N={r.N:5d} s_N={r.s_N:5d}  log2(U_N)={r.log2_U_N_exact:12.4f}  "
                  f"extensive-only resid={r.residual_after_extensive:+8.4f}  "
                  f"full-T2 resid={r.residual_after_T2_minus_half_logN:+8.4f}")
        manifest[f"shell_audit_{convention}"] = [asdict(r) for r in rows]
    print("""
  READING: 'extensive-only resid' should GROW like -0.5*log2(N) (i.e. drift
  down without bound) if the entropy coefficient alone (alpha*N*H2(rho)) is
  used without the Stirling correction -- confirming the coefficient is
  right but incomplete. 'full-T2 resid' (extensive term + derived -1/2 log
  correction + derived endpoint constant) should stay BOUNDED (O(1)) as N
  grows, confirming the full T2 asymptotic form. Floor vs ceil differ only
  in a bounded (Sturmian) shift of the O(1) constant, not in the -1/2
  exponent or the leading coefficient.
""")

    print("=" * 78)
    print("PHASE III: exact confined-word count asymptotics A_N, U_N, q_N")
    print("=" * 78)
    Ns_count = [10, 20, 40, 80, 160, 320, 640, 800]
    for c in (0, 1, 3):
        print(f"\n--- c = {c}, convention = floor ---")
        rows = compute_count_asymptotics(Ns_count, c, "floor")
        for r in rows:
            print(f"  N={r.N:5d} s_N={r.s_N:5d}  A_N bits={r.log2_A_N:10.3f}  "
                  f"U_N bits={r.log2_U_N:10.3f}  D_N={r.D_N:8.4f}  q_N={r.q_N:.6e}")
        exps = effective_exponent_sequence(rows)
        print("  effective exponents (q_N ~ N^-gamma) between successive N:")
        for n1, n2, g in exps:
            print(f"    N:{n1:5d}->{n2:5d}  gamma_eff = {g:+.4f}")
        manifest[f"count_asymptotics_c{c}"] = {
            "rows": [asdict(r) for r in rows],
            "effective_exponents": exps,
        }

    print("\n--- even/odd N subsequence stratification, c=0 ---")
    rows_all = compute_count_asymptotics(list(range(10, 201, 2)), 0, "floor")
    rows_even = [r for r in rows_all if r.N % 4 == 0]
    rows_odd = [r for r in rows_all if r.N % 4 == 2]
    exp_even = effective_exponent_sequence(rows_even)
    exp_odd = effective_exponent_sequence(rows_odd)
    print(f"  N%4==0 effective exponents (last 3): {exp_even[-3:]}")
    print(f"  N%4==2 effective exponents (last 3): {exp_odd[-3:]}")
    manifest["subsequence_stratification"] = {
        "mod4_0_exponents": exp_even, "mod4_2_exponents": exp_odd,
    }

    print("=" * 78)
    print("DENSE SWEEP + OLS REGRESSION (proper exponent estimate, not adjacent-point ratios)")
    print("=" * 78)
    for c, hi in ((0, 400), (1, 400), (3, 200)):
        res = dense_sweep_regression(20, hi, c, "floor")
        print(f"  c={c}: n_points={res['n_points']}  "
              f"gamma_full={res['gamma_full']:+.4f} (se={res['full_range_se']:.4f})  "
              f"gamma_1st_half={res['gamma_first_half']:+.4f}  gamma_2nd_half={res['gamma_second_half']:+.4f}")
        manifest[f"dense_regression_c{c}"] = res
    print("""
  READING: if gamma_1st_half and gamma_2nd_half disagree by much more than
  a few standard errors, a SINGLE stable power-law exponent over this range
  is NOT supported by the data as tested -- this must be reported as an
  honest negative/uncertain finding, not smoothed into a single headline
  gamma. Compare directly against T2's rigorously-confirmed exponent 1/2:
  q_N = A_N/U_N is NOT the same normalization as U_N itself, so there is no
  a priori reason gamma should equal 1/2 -- any match or mismatch is a
  finding to report, not to assume.
""")

    (RESULTS / "confined_composition_asymptotics.json").write_text(json.dumps(manifest, indent=2, default=str))
    print(f"\nWrote {RESULTS/'confined_composition_asymptotics.json'}")


if __name__ == "__main__":
    main()
