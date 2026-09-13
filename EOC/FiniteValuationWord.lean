import EOC.Confinement
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace EOC

open Finset

/-!
# Finite valuation words

The canonical representation is `Fin N → ℕ`.  Its length is intrinsic, so fixed-length
cardinality statements do not carry a separate length proof.  Cyclic rotation is implemented
later by transporting `List.rotate` across `List.ofFn`; that confines the dependent-length
bookkeeping to the rotation API while retaining the cardinality advantages of finite functions.
-/

/-- A finite valuation word of length `N`. -/
abbrev FiniteValuationWord (N : ℕ) := Fin N → ℕ

namespace FiniteValuationWord

/-- Every digit of a finite valuation word is positive. -/
def Positive (w : FiniteValuationWord N) : Prop := ∀ i, 1 ≤ w i

/-- Extend a finite word to an infinite valuation word.  The value beyond the finite word is
irrelevant to all prefix statements below; choosing `1` preserves positivity. -/
def toInfinite (w : FiniteValuationWord N) : ℕ → ℕ :=
  fun i ↦ if h : i < N then w ⟨i, h⟩ else 1

@[simp] theorem toInfinite_apply_of_lt (w : FiniteValuationWord N) {i : ℕ} (hi : i < N) :
    w.toInfinite i = w ⟨i, hi⟩ := by
  simp [toInfinite, hi]

@[simp] theorem toInfinite_apply_of_le (w : FiniteValuationWord N) {i : ℕ} (hi : N ≤ i) :
    w.toInfinite i = 1 := by
  simp [toInfinite, Nat.not_lt.mpr hi]

/-- The paper's prefix sum `S_j`, for a finite word. -/
def prefixSum (w : FiniteValuationWord N) (j : ℕ) : ℕ :=
  ((List.ofFn w).take j).sum

/-- The total sum `S_N` of a finite word of length `N`. -/
def total (w : FiniteValuationWord N) : ℕ := w.prefixSum N

theorem prefixSum_eq_s (w : FiniteValuationWord N) {j : ℕ} (hj : j ≤ N) :
    w.prefixSum j = s w.toInfinite j := by
  induction j with
  | zero => simp [prefixSum, s]
  | succ j ih =>
      have hjN : j < N := by omega
      rw [s_succ, ← ih (by omega)]
      rw [prefixSum, List.sum_take_succ _ _ (by simpa using hjN)]
      simp [prefixSum, toInfinite, hjN]

theorem total_eq_sum_univ (w : FiniteValuationWord N) :
    w.total = ∑ i, w i := by
  rw [total, prefixSum, List.take_of_length_le (by simp), List.sum_ofFn]

/-- Positivity of the finite word is exactly positivity of its infinite extension on `[0,N)`. -/
theorem positive_iff_toInfinite (w : FiniteValuationWord N) :
    w.Positive ↔ ∀ i < N, 1 ≤ w.toInfinite i := by
  constructor
  · intro hw i hi
    rw [toInfinite_apply_of_lt w hi]
    exact hw ⟨i, hi⟩
  · intro hw i
    simpa using hw i i.isLt

end FiniteValuationWord

/-- A positive finite valuation word of length `N`. -/
abbrev PositiveValuationWord (N : ℕ) :=
  {w : FiniteValuationWord N // w.Positive}

/-- Paper-faithful finite confinement: only the indices `1 ≤ j ≤ N` are constrained. -/
def PaperConfined (a c : ℝ) (w : FiniteValuationWord N) : Prop :=
  ∀ j, 1 ≤ j → j ≤ N → (w.prefixSum j : ℝ) - (j : ℝ) * a ≤ c

/-- For `c ≥ 0`, paper-faithful confinement at the Collatz slope is equivalent to the
repository's existing `EOC.Confined`.  The sign condition is exactly what supplies its extra
`j = 0` endpoint. -/
theorem paperConfined_alpha_iff_confined {c : ℝ} (hc : 0 ≤ c)
    (w : FiniteValuationWord N) :
    PaperConfined alpha c w ↔ Confined c w.toInfinite N := by
  constructor
  · intro hw j hjN
    by_cases hj0 : j = 0
    · subst j
      simpa [R] using hc
    · simpa [PaperConfined, R, w.prefixSum_eq_s hjN] using
        hw j (Nat.one_le_iff_ne_zero.mpr hj0) hjN
  · intro hw j hj1 hjN
    simpa [R, w.prefixSum_eq_s hjN] using hw j hjN

end EOC
