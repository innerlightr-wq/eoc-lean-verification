#!/usr/bin/env python3
"""
catalan_barrier_control.py

Phase II: Catalan/Dyck theory as a control experiment.

Dyck paths of semilength n: increments +1/-1, 2n steps, endpoint 0, every
prefix partial sum >= 0. Exact survivor count C_n = C(2n,n)/(n+1).

This is a DIFFERENT combinatorial object from the confined valuation-word
problem (bounded +-1 increments and a FIXED zero barrier/endpoint, vs.
unbounded positive increments and an IRRATIONAL-slope drifting barrier), but
it shares the general shape "count positive-integer-type paths conditioned
to stay below/above a barrier and hit a fixed endpoint," which is exactly
what Phase II asks to be tested as a control: which observed phenomena are
generic consequences of prefix conditioning, and which are specific to the
valuation-word problem's own arithmetic.
"""

from __future__ import annotations

import json
import math
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Dict, List, Tuple

from fractions import Fraction as F

ROOT = Path(__file__).resolve().parent.parent
RESULTS = ROOT / "results" / "constrained_word_asymptotics"


# ===========================================================================
# Exact Catalan numbers, and the same forward/backward DP architecture
# ===========================================================================

def catalan_exact(n: int) -> int:
    """C_n = C(2n,n)/(n+1), exact integer arithmetic."""
    return math.comb(2 * n, n) // (n + 1)


def dyck_forward_dp(n: int) -> int:
    """Forward DP over the SAME architecture as confined_count_forward_dp:
    state = partial sum after j steps, step in {+1,-1}, confined to >=0
    throughout, endpoint = 0 at step 2n. Must equal catalan_exact(n)
    exactly for every n -- this IS the Catalan specialization of the
    generic DP (Phase VII, T1)."""
    dp: Dict[int, int] = {0: 1}
    for j in range(1, 2 * n + 1):
        ndp: Dict[int, int] = {}
        for h_prev, cnt in dp.items():
            for step in (1, -1):
                h = h_prev + step
                if h >= 0:
                    ndp[h] = ndp.get(h, 0) + cnt
        dp = ndp
    return dp.get(0, 0)


def dyck_backward_completion_counts(n: int) -> Dict[Tuple[int, int], int]:
    """B[(j,h)] = number of confined completions from (j,h) to (2n,0).
    Exact backward DP, used for the collision-probability computation."""
    memo: Dict[Tuple[int, int], int] = {}

    def rec(j: int, h: int) -> int:
        if h < 0:
            return 0
        if j == 2 * n:
            return 1 if h == 0 else 0
        if (j, h) in memo:
            return memo[(j, h)]
        val = rec(j + 1, h + 1) + (rec(j + 1, h - 1) if h - 1 >= 0 else 0)
        memo[(j, h)] = val
        return val

    out = {}
    for j in range(2 * n + 1):
        for h in range(0, 2 * n - j + 1):
            out[(j, h)] = rec(j, h)
    return out


# ===========================================================================
# Phase II items 1-8
# ===========================================================================

def unrestricted_shell_dyck(n: int) -> int:
    """Unrestricted analogue: all +-1 sequences of length 2n (no positivity
    constraint), which return to 0 -- i.e. exactly n up-steps, n down-steps,
    unordered: C(2n,n). This is the DIRECT Dyck analogue of the valuation
    problem's unrestricted shell count U_N (stars-and-bars)."""
    return math.comb(2 * n, n)


def survival_fraction(n: int) -> float:
    return catalan_exact(n) / unrestricted_shell_dyck(n)


def one_position_marginal(n: int, j: int) -> Dict[int, F]:
    """Exact marginal law of the height at step j, under the UNIFORM measure
    on Dyck paths of semilength n (i.e. each of the C_n paths equally
    likely). Computed via forward-count-times-backward-count / C_n."""
    dp: Dict[int, int] = {0: 1}
    for jj in range(1, j + 1):
        ndp: Dict[int, int] = {}
        for h_prev, cnt in dp.items():
            for step in (1, -1):
                h = h_prev + step
                if h >= 0:
                    ndp[h] = ndp.get(h, 0) + cnt
        dp = ndp
    back = dyck_backward_completion_counts(n)
    Cn = catalan_exact(n)
    marg = {}
    for h, fwd_cnt in dp.items():
        b = back.get((j, h), 0)
        if fwd_cnt * b > 0:
            marg[h] = F(fwd_cnt * b, Cn)
    return marg


def prefix_cylinder_mass(n: int, prefix: Tuple[int, ...]) -> F:
    """Exact probability (under uniform measure on the C_n Dyck paths) that
    a uniformly random Dyck path begins with the given sign prefix."""
    j = len(prefix)
    h = sum(prefix)
    partial = [0]
    for s in prefix:
        partial.append(partial[-1] + s)
    if any(p < 0 for p in partial) or h < 0:
        return F(0)
    back = dyck_backward_completion_counts(n)
    Cn = catalan_exact(n)
    return F(back.get((j, h), 0), Cn)


def dyck_forward_confined_counts(k: int) -> Dict[int, int]:
    """#{length-k +-1 sequences with EVERY prefix >=0} reaching height h,
    for each reachable h -- i.e. the forward-DP count of CONFINED-SO-FAR
    prefixes (a ballot-type count, generally SMALLER than the unrestricted
    binomial C(k,(k+h)/2), since it also requires nonnegativity throughout
    the prefix, not just at the end)."""
    dp: Dict[int, int] = {0: 1}
    for _ in range(k):
        ndp: Dict[int, int] = {}
        for h_prev, cnt in dp.items():
            for step in (1, -1):
                h = h_prev + step
                if h >= 0:
                    ndp[h] = ndp.get(h, 0) + cnt
        dp = ndp
    return dp


def collision_probability_exact(n: int, k: int) -> F:
    """P_{n,k}: two independent uniform Dyck paths of semilength n agree on
    their first k steps.

    CORRECTED formulation (an earlier version of this function incorrectly
    used the UNRESTRICTED binomial C(k,(k+h)/2) as the number of length-k
    prefixes reaching height h; this is wrong because a Dyck-path prefix
    must ALSO stay nonnegative at every intermediate step, not just at
    depth k -- caught by test_collision_probability_hand_example_n1, which
    returned an impossible probability > 1 under the old formula). The
    correct forward count is `dyck_forward_confined_counts(k)`, a genuine
    ballot-type count (via reflection, C(k,ups) - C(k,ups+1)), computed
    here by direct DP rather than assumed.

    P_{n,k} = sum_h [confined_forward_count(h)] * [B(k,h)/C_n]^2, since
    every one of those `confined_forward_count(h)` DISTINCT length-k
    prefixes reaching height h shares the identical continuation
    probability B(k,h)/C_n (completion count depends only on the state
    (k,h), not on which specific prefix reached it).
    """
    back = dyck_backward_completion_counts(n)
    Cn = catalan_exact(n)
    fwd = dyck_forward_confined_counts(min(k, 2 * n))
    total = F(0)
    for h, n_prefixes in fwd.items():
        Bkh = back.get((k, h), 0)
        if Bkh == 0:
            continue
        p_prefix = F(Bkh, Cn)
        total += n_prefixes * p_prefix * p_prefix
    return total


def logarithmic_correction(n: int) -> float:
    """log2(C_n) - [2n - 0.5*log2(n)] -- should approach a constant
    (log2(1/sqrt(pi)) ~ -0.9), the classical Catalan asymptotic
    C_n ~ 4^n / (n^1.5 * sqrt(pi))."""
    log2Cn = math.log2(catalan_exact(n))
    predicted = 2 * n - 1.5 * math.log2(n) if n > 0 else 0
    return log2Cn - predicted


def decomposition_costs(n: int) -> Dict[str, float]:
    """The three-way decomposition requested by Phase II:
    log2(U_n) [unrestricted, = 2n bits exactly for the naive +-1 count]
    vs bridge cost (endpoint=0 constraint alone, ~ -0.5log2(n))
    vs positivity/confinement cost (~ -log2(n), i.e. an ADDITIONAL n^-1
    factor on top of the bridge cost) vs total Catalan correction (~ -1.5
    log2(n))."""
    log2_unrestricted_all_walks = 2 * n  # 2^{2n} total +-1 walks
    log2_bridge_only = 2 * n - 0.5 * math.log2(n) - 0.5 * math.log2(math.pi / 2) if n > 0 else 0.0
    # bridge-only: C(2n,n) via central-binomial asymptotic 4^n/sqrt(pi n)
    log2_C2n_n = math.log2(math.comb(2 * n, n))
    log2_Cn = math.log2(catalan_exact(n))
    return {
        "log2_all_walks_2^2n": log2_unrestricted_all_walks,
        "log2_bridge_C(2n,n)_exact": log2_C2n_n,
        "bridge_correction_vs_2n": log2_C2n_n - log2_unrestricted_all_walks,
        "log2_Catalan_C_n_exact": log2_Cn,
        "total_correction_vs_2n": log2_Cn - log2_unrestricted_all_walks,
        "positivity_extra_correction_vs_bridge": log2_Cn - log2_C2n_n,
    }


@dataclass
class CatalanRow:
    n: int
    C_n: int
    U_n: int
    survival_fraction: float
    log2_correction: float


def main():
    RESULTS.mkdir(parents=True, exist_ok=True)
    manifest: Dict = {}

    print("=" * 78)
    print("PHASE II.0: generic DP exactly reproduces Catalan numbers")
    print("=" * 78)
    all_match = True
    for n in list(range(0, 21)) + [30, 50, 75, 100]:
        exact = catalan_exact(n)
        dp = dyck_forward_dp(n)
        match = (exact == dp)
        all_match = all_match and match
        if n <= 20 or n in (30, 50, 75, 100):
            print(f"  n={n:4d}: C_n(exact)={exact:>25d}  DP={dp:>25d}  match={match}")
    print(f"\n  ALL {len(list(range(0,21)))+4} tested n values match exactly: {all_match}")
    manifest["catalan_dp_match_all"] = all_match

    print("\n" + "=" * 78)
    print("PHASE II.1-3: unrestricted shell, constrained count, survival fraction")
    print("=" * 78)
    rows = []
    for n in [5, 10, 20, 40, 80, 160, 320]:
        Cn = catalan_exact(n)
        Un = unrestricted_shell_dyck(n)
        sf = Cn / Un
        lc = logarithmic_correction(n)
        rows.append(CatalanRow(n=n, C_n=Cn, U_n=Un, survival_fraction=sf, log2_correction=lc))
        print(f"  n={n:4d}  C_n bits={math.log2(Cn):10.3f}  U_n bits={math.log2(Un):10.3f}  "
              f"survival={sf:.6e}  n*survival={n*sf:.4f}  log2_corr(->const)={lc:+.4f}")
    manifest["catalan_survival_rows"] = [asdict(r) for r in rows]
    print("""
  READING: survival_fraction * n should approach a CONSTANT (confirming the
  classical survival cost ~ n^-1, i.e. C_n/C(2n,n) ~ const/n exactly --
  standard fact, re-derived/verified here), and log2_correction should
  approach log2(1/sqrt(pi)) = -0.9624... exactly.
""")

    print("=" * 78)
    print("PHASE II.4: one-position marginals (interior)")
    print("=" * 78)
    n_test = 40
    for j in [10, 20, 30]:
        marg = one_position_marginal(n_test, j)
        total = sum(marg.values())
        print(f"  n={n_test}, j={j}: support size={len(marg)}, total mass={float(total):.6f} (should be 1)")
        # report a few heights near the "typical" scaled height (arcsine-ish for bridges, but
        # for a Dyck path at INTERIOR j, the typical height scale is O(sqrt(j)) -- report the mode
        mode_h = max(marg, key=lambda h: marg[h])
        print(f"    mode height = {mode_h}, P(mode) = {float(marg[mode_h]):.6f}")
    manifest["marginal_totals_checked"] = True

    print("\n" + "=" * 78)
    print("PHASE II.5: prefix-cylinder masses")
    print("=" * 78)
    for prefix in [(1,) * 5, (1, -1) * 5, (1, 1, -1, 1, -1)]:
        mass = prefix_cylinder_mass(60, prefix)
        print(f"  n=60, prefix={prefix}: P = {mass} = {float(mass):.6e}")

    print("\n" + "=" * 78)
    print("PHASE II.6: collision probability of two independent uniform Dyck paths")
    print("=" * 78)
    n_coll = 30
    for k in [1, 2, 5, 10, 20, 30, 40, 55, 59, 60]:
        p = collision_probability_exact(n_coll, k)
        negl2p = -math.log2(float(p)) if p > 0 else float("inf")
        print(f"  n={n_coll}, k={k:3d} (theta={k/(2*n_coll):.3f}): "
              f"P_coll = {float(p):.8e}   -log2(P)/k = {negl2p/k if k>0 else 0:.4f}")
    manifest["collision_n30_computed"] = True

    print("\n" + "=" * 78)
    print("PHASE II.7-8: logarithmic correction behavior, k regimes summary")
    print("=" * 78)
    for n in [10, 20, 40, 80]:
        dc = decomposition_costs(n)
        print(f"  n={n}: {dc}")
    print("""
  DECOMPOSITION READING: 'bridge_correction_vs_2n' should approach
  -0.5*log2(n) - 0.5*log2(pi/2) (endpoint-only cost, the ordinary bridge
  local-limit cost ~ n^-1/2); 'positivity_extra_correction_vs_bridge'
  should approach an ADDITIONAL -log2(n) + const (the extra n^-1 cost of
  the reflection/positivity constraint on TOP of the bridge cost); their
  sum, 'total_correction_vs_2n', is the full Catalan n^-3/2 correction.
  This is the exact n^{-1/2} (bridge) times n^{-1} (positivity) = n^{-3/2}
  (total) decomposition Phase II asks to identify.
""")

    (RESULTS / "catalan_barrier_control.json").write_text(json.dumps(manifest, indent=2, default=str))
    print(f"Wrote {RESULTS/'catalan_barrier_control.json'}")


if __name__ == "__main__":
    main()
