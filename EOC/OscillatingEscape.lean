import EOC.SeparatedReturns
import EOC.BoundedDrift

/-!
# The oscillating word has no positive realizer — closing a restricted observation

`docs/SEPARATED_RETURNS_CORRECTION_AUDIT.md` left one item open. The oscillating word `oscD c`
(digit `2` inside the corridor, digit `1` outside) was used there to refute a uniform bound on the
number of corridor episodes, and the report recorded a *disjunction*: either the least prefix
realizers of `oscD c` are unbounded, or some positive integer realizes the entire infinite word and
hence never reaches `1`.

**That disjunction is unnecessary.** The repository already contains the theorem that settles it:
`EOC.leastRealizer_unbounded_of_two_sided_drift` (`EOC/BoundedDrift.lean`) needs only a fixed
two-sided drift window and **no periodicity hypothesis**. The oscillating word has such a window,
by construction. This file supplies the two walls in exact integer form, the missing
integer-to-real bridge for the upper wall, and the conclusion.

**This is a restricted observation, not progress on excluding divergence.** The theorem applies
precisely because `oscD c` has drift bounded *below* by a constant. A divergent orbit's word has
`R_n → −∞` (Curry ⟹ bounded carry ⟹ linear negative drift), so it has **no** lower wall and this
machinery says nothing whatever about it. See `docs/DIVERGENCE_EXCLUSION_SURVEY.md` §5.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace OscillatingEscape

open SeparatedReturns

/-! ## 1. The two walls, in exact integer form -/

/-- `s` and the oscillating word's own running sum agree. -/
theorem s_oscD (c n : ℕ) : s (oscD c) n = oscS c n := S_oscD c n

/-- **Upper wall.** `2^{S_n} ≤ 2^{c+1}·3^n`, i.e. `R_n ≤ c + 1`.

Immediate from the invariant `3·2^{S_n} ≤ 4·(2^c·3^n)` of `SeparatedReturns.osc_invariant`:
`3X ≤ 4Y ≤ 6Y` gives `X ≤ 2Y`. -/
theorem oscS_upper (c n : ℕ) : 2 ^ oscS c n ≤ 2 ^ (c + 1) * 3 ^ n := by
  have hinv := osc_invariant c n
  have hpow : (2 : ℕ) ^ (c + 1) * 3 ^ n = 2 * (2 ^ c * 3 ^ n) := by rw [pow_succ]; ring
  rw [hpow]
  omega

/-- **Lower wall.** `3^n ≤ 2·2^{S_n}`, i.e. `R_n ≥ −1`.

Induction. Inside the corridor the digit is `2`, so `2^S` quadruples while `3^n` only triples;
outside the corridor the word is *above* `2^c·3^n ≥ 3^n` to begin with, and the digit-`1` step
doubles, which still clears `3^{n+1}`. -/
theorem oscS_lower (c n : ℕ) : 3 ^ n ≤ 2 * 2 ^ oscS c n := by
  induction n with
  | zero => simp [oscS]
  | succ n ih =>
      have h2c : (1 : ℕ) ≤ 2 ^ c := Nat.one_le_two_pow
      have h3 : (3 : ℕ) ^ (n + 1) = 3 * 3 ^ n := by rw [pow_succ]; ring
      by_cases h : InC c n
      · have hA : 2 ^ oscS c (n + 1) = 4 * 2 ^ oscS c n := by
          rw [oscS_succ, oscD_eq_two h, pow_add]; ring
        omega
      · have hA : 2 ^ oscS c (n + 1) = 2 * 2 ^ oscS c n := by
          rw [oscS_succ, oscD_eq_one h, pow_add]; ring
        have hout : 2 ^ c * 3 ^ n < 2 ^ oscS c n := by
          have : ¬ (2 ^ oscS c n ≤ 2 ^ c * 3 ^ n) := h
          omega
        have h3n : (3 : ℕ) ^ n ≤ 2 ^ c * 3 ^ n :=
          Nat.le_mul_of_pos_left _ (by positivity)
        omega

/-! ## 2. The missing integer-to-real bridge

`BoundedDrift.three_pow_le_of_drift` converts a real *lower* drift bound into integer form. The
*upper* wall needs the opposite conversion, which the repository did not have. -/

/-- **From an integer upper bound on `2^{S_N}` to a real upper bound on the drift.**
If `2^{S_N} ≤ 2^K·3^N` then `R_N ≤ K`. -/
theorem R_le_of_pow_le (d : ℕ → ℕ) (K N : ℕ) (h : 2 ^ s d N ≤ 2 ^ K * 3 ^ N) :
    R d N ≤ (K : ℝ) := by
  have hcast : ((2 : ℝ) ^ s d N) ≤ (2 : ℝ) ^ K * (3 : ℝ) ^ N := by exact_mod_cast h
  have hpos : (0 : ℝ) < (2 : ℝ) ^ s d N := by positivity
  have hlog := Real.logb_le_logb_of_le (b := 2) (by norm_num) hpos hcast
  rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow, Real.logb_pow,
      Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at hlog
  unfold R alpha
  linarith

/-! ## 3. The conclusion -/

/-- **The oscillating word has unbounded least prefix realizers.**

Applying `leastRealizer_unbounded_of_int_drift` with upper wall `c+1` and lower wall `G = 1`. No
periodicity, injectivity, or Curry input is used. -/
theorem osc_leastRealizer_unbounded (c : ℕ) :
    ∀ M, ∃ N, M < leastRealizer (oscD c) N := by
  refine leastRealizer_unbounded_of_int_drift ((c : ℝ) + 1) 1 (oscD c)
    (fun i => oscD_pos c i) (fun N => ?_) (fun j => ?_)
  · have h := R_le_of_pow_le (oscD c) (c + 1) N (by rw [s_oscD]; exact oscS_upper c N)
    push_cast at h
    linarith
  · rw [s_oscD, pow_one]
    exact oscS_lower c j

/-- **Hence no positive integer realizes the entire oscillating word**, via the ZCRE equivalence.

This settles the disjunction recorded in `docs/SEPARATED_RETURNS_CORRECTION_AUDIT.md`: the first
alternative holds, unconditionally, and the second (a positive orbit never reaching `1`) is not
needed and is not asserted. -/
theorem osc_no_positive_realizer (c : ℕ) :
    ¬ ∃ m0, Odd m0 ∧ ∀ i, a (orbit m0 i) = oscD c i := by
  intro hreal
  obtain ⟨M, hM⟩ :=
    (ZCRERealizerGrowth.boundedPrefixRealizers_iff_positiveRealizer (oscD c)
      (fun i => oscD_pos c i)).mpr hreal
  obtain ⟨N, hN⟩ := osc_leastRealizer_unbounded c M
  exact absurd (hM N) (by omega)

end OscillatingEscape
end EOC
