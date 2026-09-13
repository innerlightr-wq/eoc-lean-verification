"""Tests for experiments/cyclic_rotation_audit.py."""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "experiments"))

from cyclic_rotation_audit import (  # noqa: E402
    all_positive_compositions, rotations, is_confined, is_primitive,
    max_partial_sum_multiplicity, cycle_lemma_classical_check, confined_exact,
)


def test_all_positive_compositions_hand_count():
    comps = list(all_positive_compositions(3, 5))
    assert len(comps) == 6  # C(4,2)=6
    assert all(len(c) == 3 and sum(c) == 5 and all(d >= 1 for d in c) for c in comps)
    assert set(comps) == {(1, 1, 3), (1, 3, 1), (3, 1, 1), (1, 2, 2), (2, 1, 2), (2, 2, 1)}


def test_rotations_hand_example():
    word = (1, 2, 3)
    rots = rotations(word)
    assert rots == [(1, 2, 3), (2, 3, 1), (3, 1, 2)]


def test_rotations_orbit_size_for_periodic_word():
    """A periodic word like (2,2,2,2) has only 1 DISTINCT rotation, even
    though it has 4 rotation POSITIONS -- this must not be silently
    conflated (no double-counting of imprimitive rotations)."""
    word = (2, 2, 2, 2)
    rots = rotations(word)
    assert len(rots) == 4          # 4 positions
    assert len(set(rots)) == 1     # but only 1 distinct rotation
    assert not is_primitive(word)


def test_is_primitive_hand_examples():
    assert is_primitive((1, 2, 3))
    assert not is_primitive((2, 2))
    assert not is_primitive((1, 2, 1, 2))
    assert is_primitive((1, 2, 1, 3))


def test_is_confined_matches_direct_check():
    word = (1, 1, 1)
    # partial sums 1,2,3; confined_exact at c=0: j=1,S=1: 2^1<=3^1 True;
    # j=2,S=2: 2^2=4<=9 True; j=3,S=3: 2^3=8<=27 True.
    assert is_confined(word, 0)
    word2 = (5, 1, 1)
    # j=1,S=5,c=0: 2^5=32 <= 3^1=3? False -> not confined
    assert not is_confined(word2, 0)


def test_unique_argmax_for_all_small_words():
    """Irrationality guarantee: R_j must have a UNIQUE maximizer for every
    tested word (this is a PROVED fact, checked exhaustively here)."""
    for N in range(1, 6):
        for s in range(N, N + 5):
            for word in all_positive_compositions(N, s):
                Rmax, mult, argmax = max_partial_sum_multiplicity(word)
                assert mult == 1


def test_classical_cycle_lemma_hand_example():
    """Classical cycle lemma, a_i<=1: sequence (1,1,-1) has k=1, and exactly
    1 rotation should have all partial sums positive."""
    a = (1, 1, -1)
    k, count = cycle_lemma_classical_check(a)
    assert k == 1
    assert count == 1


def test_classical_cycle_lemma_larger_hand_example():
    """(1,-1,1,1,-1): k=1. Check by hand which rotations work."""
    a = (1, -1, 1, 1, -1)
    k, count = cycle_lemma_classical_check(a)
    assert k == 1
    assert count == 1  # cycle lemma guarantees exactly k=1


def test_naive_cycle_lemma_analogue_fails_minimal_counterexample():
    """The EXPLICIT minimal counterexample found by the audit: (N,s,c) =
    (3,5,1) has words with DIFFERING numbers of confined rotations --
    killing the hypothesis that n_confined_rotations depends only on
    (N,s,c)."""
    words_with_counts = []
    for word in all_positive_compositions(3, 5):
        n_conf = sum(1 for w in rotations(word) if is_confined(w, 1))
        words_with_counts.append((word, n_conf))
    counts = {c for _, c in words_with_counts}
    assert len(counts) > 1, "expected the (N,s,c)=(3,5,1) group to exhibit varying rotation counts"


def test_start_after_max_construction_counterexample():
    """Explicit hand-verified counterexample: word (1,3,1), c=0. The unique
    argmax of R_j is at j=2 (verified below); rotating to start there gives
    (1,1,3), which must NOT be confined (kills the naive cycle-lemma-style
    'start right after the max' construction for unbounded digits)."""
    word = (1, 3, 1)
    c = 0
    Rmax, mult, argmax = max_partial_sum_multiplicity(word)
    assert mult == 1
    start = argmax % len(word)
    rotated = word[start:] + word[:start]
    assert rotated == (1, 1, 3)
    assert not is_confined(rotated, c)
    # and the ORIGINAL word must itself be a valid confined-eligible word for this test to be meaningful
    # (at least check it's a legitimate composition; confinement of the original is not required by the claim)
    assert sum(word) == 5 and len(word) == 3


def test_reproducibility_of_rotation_audit():
    word = (1, 2, 3, 1)
    r1 = rotations(word)
    r2 = rotations(word)
    assert r1 == r2
