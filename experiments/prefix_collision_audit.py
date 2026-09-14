#!/usr/bin/env python3
"""
prefix_collision_audit.py

Phase V: collision probability and Renyi structure, for the CONFINED
VALUATION-WORD problem under the UNIFORM measure on W_c(N, s_N) (NOT the
geometric cylinder measure already studied in
explorations/hypercuboid_transfer/scripts/round2_verification.py -- that
work computed cylinder-MASS collision/survival quantities under the
geometric Geom(2) product measure; this module computes the DIFFERENT
object explicitly requested by this audit: collision probability of two
words drawn UNIFORMLY from the finite set W_c(N,s_N)).

DEFINITION (as specified): choose two words independently and uniformly
from W_c(N, s_N). P_{N,k} := probability their first k digits agree.
Using EXACT prefix counts C_N(prefix) (unweighted cardinalities: the number
of full-length confined words with total s_N that extend a given length-k
prefix),

    P_{N,k} = sum_{admissible length-k prefixes} [C_N(prefix)/A_N]^2.

Since C_N(prefix) depends only on the prefix's OWN (j=k, S=partial sum)
state (all admissible completions from a given (k,S) count the same,
regardless of which specific digits produced S), this reduces to

    P_{N,k} = sum_S [ (#prefixes of length k reaching state (k,S)) *
                        B(k,S)^2 ] / A_N^2

where B(k,S) is the EXACT (unweighted) forward-DP-style backward
completion count from (k,S) to (N, s_N). This is the raw combinatorial
analogue of round2_verification.py's Doob h-transform section, but with
counts instead of geometric masses.
"""

from __future__ import annotations

import json
import math
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Dict, List, Optional, Tuple

from fractions import Fraction as F

import sys
sys.path.insert(0, str(Path(__file__).resolve().parent))
from confined_composition_asymptotics import confined_exact, unrestricted_shell, default_s_N


# ===========================================================================
# Exact forward-count and backward-completion-count tables
# ===========================================================================

def forward_counts_table(N: int, c: int, s_max: int) -> List[Dict[int, int]]:
    """forward[j] = {S: #length-j confined prefixes with partial sum S}."""
    forward = [{0: 1}]
    for j in range(1, N + 1):
        prev = forward[-1]
        cur: Dict[int, int] = {}
        pow3j = 3 ** j
        for Sprev, cnt in prev.items():
            d = 1
            while Sprev + d <= s_max:
                S = Sprev + d
                ok = S <= c or (2 ** (S - c)) <= pow3j
                if ok:
                    cur[S] = cur.get(S, 0) + cnt
                    d += 1
                else:
                    break
        forward.append(cur)
    return forward


def backward_counts_table(N: int, c: int, s_target: int, s_max: int) -> List[Dict[int, int]]:
    """backward[j] = {S: #confined completions from state (j,S) to (N,s_target)}.
    Computed by a SEPARATE backward recursion (genuinely different
    implementation direction from the forward table, used as a cross-check)."""
    backward: List[Dict[int, int]] = [dict() for _ in range(N + 1)]
    backward[N] = {s_target: 1}
    for j in range(N - 1, -1, -1):
        cur: Dict[int, int] = {}
        nxt = backward[j + 1]
        pow3jp1 = 3 ** (j + 1)
        # candidate S values at depth j: any S with 0<=S<=s_target
        # (we only need S values that are reachable, but for a clean backward
        # pass we scan all S in [0, s_target] and check confinement/next-step validity)
        for S in range(0, s_target + 1):
            total = 0
            d = 1
            while S + d <= s_target:
                Snext = S + d
                ok = Snext <= c or (2 ** (Snext - c)) <= pow3jp1
                if not ok:
                    break
                total += nxt.get(Snext, 0)
                d += 1
            if total > 0:
                cur[S] = total
        backward[j] = cur
    return backward


def collision_probability_exact(N: int, s_target: int, c: int, k: int) -> Tuple[F, int, int]:
    """Returns (P_{N,k}, A_N, number of admissible length-k prefix states)."""
    s_max = s_target
    forward = forward_counts_table(k, c, s_max)
    backward = backward_counts_table(N, c, s_target, s_max)
    A_N = backward[0].get(0, 0)
    if A_N == 0:
        return F(0), 0, 0
    fwd_k = forward[k]
    total = 0
    n_states = 0
    for S, fcnt in fwd_k.items():
        b = backward[k].get(S, 0)
        if b > 0:
            total += fcnt * b * b
            n_states += 1
    return F(total, A_N * A_N), A_N, n_states


def brute_force_collision(N: int, s_target: int, c: int, k: int) -> F:
    """Ground truth via full enumeration of W_c(N,s_target) -- SMALL N only."""
    words = []

    def rec(j, S, word):
        if j == N:
            if S == s_target:
                words.append(tuple(word))
            return
        d = 1
        while S + d <= s_target:
            Snext = S + d
            if confined_exact(Snext, j + 1, c):
                word.append(d)
                rec(j + 1, Snext, word)
                word.pop()
            d += 1

    rec(0, 0, [])
    A = len(words)
    if A == 0:
        return F(0)
    from collections import Counter
    prefix_counts = Counter(w[:k] for w in words)
    total = sum(cnt * cnt for cnt in prefix_counts.values())
    return F(total, A * A)


# ===========================================================================
# Geometric/iid comparison, derived from first principles
# ===========================================================================

def one_digit_candidate_distribution(N: int, c: int, s_target: int, j: int) -> Dict[int, F]:
    """The EXACT one-digit law at depth j (from state S=s_j(word) averaged
    over the uniform measure on W_c(N,s_target)) -- i.e. the marginal
    distribution of the (j+1)-th digit under uniform sampling of a full word.
    This is the object whose Renyi-2 entropy is the natural 'R_2' candidate,
    computed EXACTLY, not assumed to be Geom(2)."""
    s_max = s_target
    forward = forward_counts_table(j, c, s_max)
    backward = backward_counts_table(N, c, s_target, s_max)
    A_N = backward[0].get(0, 0)
    digit_mass: Dict[int, int] = {}
    for S, fcnt in forward[j].items():
        d = 1
        while S + d <= s_target:
            Snext = S + d
            if confined_exact(Snext, j + 1, c):
                b = backward[j + 1].get(Snext, 0)
                digit_mass[d] = digit_mass.get(d, 0) + fcnt * b
                d += 1
            else:
                break
    total = sum(digit_mass.values())
    if total == 0:
        return {}
    return {d: F(m, total) for d, m in digit_mass.items()}


def renyi2_entropy_bits(dist: Dict[int, F]) -> float:
    collision = sum((p) ** 2 for p in dist.values())
    if collision == 0:
        return float("inf")
    return -math.log2(float(collision))


def main():
    RESULTS = Path(__file__).resolve().parent.parent / "results" / "constrained_word_asymptotics"
    RESULTS.mkdir(parents=True, exist_ok=True)
    manifest: Dict = {}

    print("=" * 78)
    print("Phase V: exact prefix collision probability P_{N,k}, uniform measure")
    print("=" * 78)

    N, c = 40, 0
    s_N = default_s_N(N, "floor")
    print(f"\nSetup: N={N}, s_N={s_N}, c={c}")
    A_N_check = backward_counts_table(N, c, s_N, s_N)[0].get(0, 0)
    print(f"A_N = {A_N_check}")

    print("\n--- P_{N,0}=1 and P_{N,N}=1/A_N sanity checks ---")
    p0, _, _ = collision_probability_exact(N, s_N, c, 0)
    pN, _, _ = collision_probability_exact(N, s_N, c, N)
    print(f"  P_{{N,0}} = {p0}  (must be 1): {p0 == 1}")
    print(f"  P_{{N,N}} = {pN}  vs 1/A_N = {F(1, A_N_check)}: match={pN == F(1, A_N_check)}")

    print("\n--- monotonicity 0<=P_{N,k+1}<=P_{N,k}<=1, and k regimes ---")
    ks = list(range(0, N + 1, 2)) + [N]
    ks = sorted(set(ks))
    rows = []
    prev_p = None
    monotone_ok = True
    for k in ks:
        p, A_N_k, n_states = collision_probability_exact(N, s_N, c, k)
        pf = float(p)
        neglog2 = -math.log2(pf) if pf > 0 else float("inf")
        theta = k / N
        if prev_p is not None and pf > float(prev_p) + 1e-15:
            monotone_ok = False
        prev_p = p
        rows.append({"k": k, "theta": theta, "P": pf, "neglog2P": neglog2,
                     "neglog2P_over_k": neglog2 / k if k > 0 else 0.0, "n_states": n_states})
        print(f"  k={k:3d} theta={theta:.3f}  P_coll={pf:.6e}  -log2(P)={neglog2:8.3f}  "
              f"-log2(P)/k={neglog2/k if k>0 else 0:.4f}")
    print(f"\n  Monotonicity P_{{N,k+1}} <= P_{{N,k}} holds throughout: {monotone_ok}")
    manifest["monotonicity_ok"] = monotone_ok
    manifest["collision_rows_N40_c0"] = rows

    print("\n--- one-digit candidate distribution vs Geom(2) at several depths ---")
    for j in [0, 5, 15, 25, 35]:
        dist = one_digit_candidate_distribution(N, c, s_N, j)
        r2 = renyi2_entropy_bits(dist)
        geom2_r2 = math.log2(3)  # exact: Renyi-2 of Geom(2) is log2(3) = alpha (see round2_verification.py Part G)
        print(f"  depth j={j:3d}: support={sorted(dist.keys())[:8]}{'...' if len(dist)>8 else ''}  "
              f"P(d=1)={float(dist.get(1,0)):.4f}  Renyi2={r2:.4f} bits  "
              f"(unconditioned Geom(2) Renyi2 = alpha = {geom2_r2:.4f})")
        manifest[f"digit_dist_j{j}"] = {str(k): float(v) for k, v in dist.items()}

    print("""
  READING: this is the EXACT one-digit marginal under UNIFORM sampling from
  W_c(N,s_N) -- a genuinely different object from round2_verification.py's
  geometric-cylinder-measure Doob h-transform (Part C there). If this
  distribution's Renyi-2 entropy tracks alpha=log2(3) closely at interior
  depths but departs near the boundary (j near 0 or near N), that supports
  classifying the -log2(P)/k asymptote as close to the base-digit Renyi-2
  rate away from endpoint effects, with endpoint-driven deviation -- NOT
  proof of a stationary rate, since finite-N/finite-k effects are exactly
  what is being measured here.
""")

    print("=" * 78)
    print("k-regime comparison across N (does -log2(P)/k stabilize as N grows?)")
    print("=" * 78)
    for N2 in [20, 30, 40, 50]:
        s_N2 = default_s_N(N2, "floor")
        for theta in (0.25, 0.5, 0.75):
            k = max(1, round(theta * N2))
            p, _, _ = collision_probability_exact(N2, s_N2, c, k)
            pf = float(p)
            rate = -math.log2(pf) / k if pf > 0 else float("inf")
            print(f"  N={N2:3d} k={k:3d} theta={theta}: -log2(P)/k = {rate:.4f}")

    (RESULTS / "prefix_collision_audit.json").write_text(json.dumps(manifest, indent=2, default=str))
    print(f"\nWrote {RESULTS/'prefix_collision_audit.json'}")


if __name__ == "__main__":
    main()
