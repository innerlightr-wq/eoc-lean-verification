"""Tests for experiments/prefix_collision_audit.py."""

import sys
from pathlib import Path
from fractions import Fraction as F
from collections import Counter

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "experiments"))

from prefix_collision_audit import (  # noqa: E402
    collision_probability_exact, brute_force_collision, forward_counts_table,
    backward_counts_table,
)
from confined_composition_asymptotics import confined_exact, confined_count_forward_dp  # noqa: E402


def _brute_words(N, s, c):
    words = []

    def rec(j, S, word):
        if j == N:
            if S == s:
                words.append(tuple(word))
            return
        d = 1
        while S + d <= s:
            Snext = S + d
            if confined_exact(Snext, j + 1, c):
                word.append(d)
                rec(j + 1, Snext, word)
                word.pop()
            d += 1

    rec(0, 0, [])
    return words


def test_collision_probability_matches_brute_force_pair_enumeration():
    """Exact P_{N,k} must match brute-force enumeration of ALL pairs of
    words in W_c(N,s) for small (N,s,c)."""
    for (N, s, c) in [(4, 6, 0), (6, 9, 0), (4, 7, 1)]:
        words = _brute_words(N, s, c)
        A = len(words)
        assert A > 0
        for k in range(0, N + 1):
            p_exact, A_check, _ = collision_probability_exact(N, s, c, k)
            assert A_check == A
            p_bf = brute_force_collision(N, s, c, k)
            assert p_exact == p_bf, (N, s, c, k, p_exact, p_bf)


def test_P_N_0_is_one():
    # (N,s,c) verified nonempty (A_N>0) via confined_count_forward_dp first.
    for (N, s, c) in [(6, 9, 0), (8, 12, 1)]:
        p, _, _ = collision_probability_exact(N, s, c, 0)
        assert p == 1


def test_P_N_N_equals_one_over_A_N():
    for (N, s, c) in [(6, 9, 0), (8, 12, 1)]:
        p, A, _ = collision_probability_exact(N, s, c, N)
        assert A > 0
        assert p == F(1, A)


def test_monotonicity_in_k():
    N, s, c = 12, 20, 0
    prev = None
    for k in range(0, N + 1):
        p, _, _ = collision_probability_exact(N, s, c, k)
        if prev is not None:
            assert p <= prev
        prev = p


def test_forward_and_backward_tables_agree_on_A_N():
    """Cross-check: forward count at depth N (with S=s fixed) must equal
    backward count at depth 0 (both compute A_N, via genuinely different
    recursions -- forward accumulation vs backward completion)."""
    N, s, c = 10, 16, 0
    forward = forward_counts_table(N, c, s)
    A_forward = forward[N].get(s, 0)
    backward = backward_counts_table(N, c, s, s)
    A_backward = backward[0].get(0, 0)
    assert A_forward == A_backward == confined_count_forward_dp(N, s, c)


def test_no_negative_or_over_one_probabilities():
    N, s, c = 15, 24, 0
    for k in range(0, N + 1):
        p, _, _ = collision_probability_exact(N, s, c, k)
        assert 0 <= p <= 1


def test_exact_barrier_decision_near_close_comparison():
    """A hand-picked near-tie: does 2^(S-c) <= 3^j resolve correctly right
    at a boundary where S-c and j*log2(3) are numerically very close?
    j=8: 3^8=6561; 2^12=4096<=6561 (True), 2^13=8192>6561 (False) --
    confirms the exact integer comparison resolves a case where
    floor(8*log2(3))=12 exactly (8*log2(3)=12.679...)."""
    assert confined_exact(12, 8, 0) is True
    assert confined_exact(13, 8, 0) is False


def test_reproducibility():
    N, s, c, k = 20, 32, 0, 10
    p1, _, _ = collision_probability_exact(N, s, c, k)
    p2, _, _ = collision_probability_exact(N, s, c, k)
    assert p1 == p2
