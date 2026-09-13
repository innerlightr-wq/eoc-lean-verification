"""Tests for experiments/catalan_barrier_control.py."""

import math
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "experiments"))

from catalan_barrier_control import (  # noqa: E402
    catalan_exact, dyck_forward_dp, dyck_backward_completion_counts,
    unrestricted_shell_dyck, one_position_marginal, prefix_cylinder_mass,
    collision_probability_exact,
)

KNOWN_CATALAN = [1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796]


def test_catalan_exact_matches_known_sequence():
    for n, c in enumerate(KNOWN_CATALAN):
        assert catalan_exact(n) == c


def test_dp_matches_catalan_exact_up_to_100():
    for n in list(range(0, 21)) + [30, 50, 75, 100]:
        assert dyck_forward_dp(n) == catalan_exact(n)


def test_unrestricted_shell_dyck_is_central_binomial():
    for n in range(0, 10):
        assert unrestricted_shell_dyck(n) == math.comb(2 * n, n)


def test_survival_fraction_exact_identity():
    """C_n / C(2n,n) = 1/(n+1) EXACTLY (not merely asymptotically)."""
    for n in range(1, 20):
        Cn = catalan_exact(n)
        Un = unrestricted_shell_dyck(n)
        from fractions import Fraction
        assert Fraction(Cn, Un) == Fraction(1, n + 1)


def test_backward_completion_counts_match_forward_at_origin():
    n = 8
    back = dyck_backward_completion_counts(n)
    assert back[(0, 0)] == catalan_exact(n)


def test_one_position_marginal_normalizes_to_one():
    n = 15
    for j in [0, 3, 7, 15]:
        marg = one_position_marginal(n, j)
        from fractions import Fraction
        total = sum(marg.values(), Fraction(0))
        assert total == 1


def test_marginal_at_j0_is_deterministic_height_zero():
    marg = one_position_marginal(10, 0)
    assert list(marg.keys()) == [0]


def test_prefix_cylinder_mass_zero_for_infeasible_prefix():
    # A prefix that goes negative is infeasible.
    mass = prefix_cylinder_mass(10, (-1, -1))
    assert mass == 0


def test_prefix_cylinder_mass_one_for_empty_prefix():
    mass = prefix_cylinder_mass(10, ())
    assert mass == 1


def test_collision_probability_hand_example_n1():
    """n=1: only one Dyck path (1,-1) exists (C_1=1), so collision
    probability is 1 at every k."""
    for k in [0, 1, 2]:
        p = collision_probability_exact(1, k)
        assert p == 1


def test_collision_probability_monotone_in_k():
    n = 10
    prev = None
    for k in range(0, 2 * n + 1):
        p = collision_probability_exact(n, k)
        if prev is not None:
            assert p <= prev
        prev = p


def test_collision_probability_at_k_equals_2n_is_one_over_Cn():
    n = 8
    p = collision_probability_exact(n, 2 * n)
    from fractions import Fraction
    assert p == Fraction(1, catalan_exact(n))


def test_reproducibility_of_dyck_dp():
    assert dyck_forward_dp(25) == dyck_forward_dp(25) == catalan_exact(25)
