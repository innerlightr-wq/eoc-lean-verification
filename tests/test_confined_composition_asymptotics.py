"""Tests for experiments/confined_composition_asymptotics.py."""

import math
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "experiments"))

from confined_composition_asymptotics import (  # noqa: E402
    confined_exact, unrestricted_shell, confined_count_forward_dp,
    brute_force_count, default_s_N, binary_entropy,
)


def test_unrestricted_shell_matches_stars_and_bars_hand_example():
    # #{(d1,d2,d3): d_i>=1, sum=5} = C(4,2) = 6: (1,1,3),(1,3,1),(3,1,1),
    # (1,2,2),(2,1,2),(2,2,1) -- hand-enumerable.
    assert unrestricted_shell(3, 5) == 6
    assert unrestricted_shell(1, 1) == 1
    assert unrestricted_shell(2, 2) == 1  # only (1,1)
    assert unrestricted_shell(2, 1) == 0  # impossible: need sum>=N


def test_confined_exact_matches_direct_inequality_small_cases():
    # R_j = S_j - j*alpha <= c  <=>  S_j - c <= j*log2(3) <=> 2^(S_j-c)<=3^j
    for Sj, j, c in [(1, 1, 0), (2, 1, 0), (3, 1, 0), (2, 1, 1), (5, 2, 0)]:
        exact = confined_exact(Sj, j, c)
        direct = (Sj - c) <= j * math.log2(3)
        assert exact == direct, (Sj, j, c)


def test_dp_matches_brute_force_small_N_s_c():
    for N in range(1, 6):
        for s in range(N, N + 8):
            for c in (0, 1, 2):
                dp_val = confined_count_forward_dp(N, s, c)
                bf_val = brute_force_count(N, s, c)
                assert dp_val == bf_val, (N, s, c, dp_val, bf_val)


def test_dp_zero_when_s_less_than_N():
    assert confined_count_forward_dp(5, 3, 0) == 0


def test_dp_never_exceeds_unrestricted_shell():
    for N in range(1, 8):
        for s in range(N, N + 10):
            for c in (0, 1, 3):
                A = confined_count_forward_dp(N, s, c)
                U = unrestricted_shell(N, s)
                assert A <= U


def test_default_s_N_floor_and_ceil_conventions():
    alpha = math.log2(3)
    for N in [10, 100, 1000]:
        s_floor = default_s_N(N, "floor")
        s_ceil = default_s_N(N, "ceil")
        assert s_floor <= math.floor(alpha * N) + 1  # +1 guard for N>alpha*N edge case
        assert s_ceil >= math.ceil(alpha * N)
        assert s_ceil - s_floor in (0, 1)


def test_binary_entropy_hand_values():
    assert abs(binary_entropy(0.5) - 1.0) < 1e-12
    assert binary_entropy(0.0) == 0.0
    assert binary_entropy(1.0) == 0.0
    # H2(1/alpha) should be a specific known value used throughout this audit
    rho = 1 / math.log2(3)
    h = binary_entropy(rho)
    assert 0.9 < h < 1.0  # sanity bound: rho~0.63, H2 near its max but not exactly 1


def test_confinement_monotone_in_c():
    """Increasing c can only WEAKEN the barrier -- A_N(c) must be
    non-decreasing in c for fixed (N,s)."""
    N, s = 6, 12
    prev = 0
    for c in range(0, 5):
        val = confined_count_forward_dp(N, s, c)
        assert val >= prev
        prev = val


def test_reproducibility_deterministic():
    """Running the DP twice gives identical results (no hidden randomness)."""
    for N, s, c in [(20, 32, 0), (30, 48, 1)]:
        a1 = confined_count_forward_dp(N, s, c)
        a2 = confined_count_forward_dp(N, s, c)
        assert a1 == a2


def test_no_floating_point_alpha_in_confinement_decision():
    """Structural check: confined_exact's source contains no comparison
    against a floating-point alpha value -- it must decide via the exact
    integer inequality 2^(S-c) <= 3^j only."""
    import inspect
    src = inspect.getsource(confined_exact)
    assert "log2" not in src and "math.log" not in src and "ALPHA" not in src
    assert "2 ** (Sj - c)" in src or "2**(Sj-c)" in src.replace(" ", "")
