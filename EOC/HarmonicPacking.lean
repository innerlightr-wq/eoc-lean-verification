import EOC.FinitePrefixPacking
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Harmonic packing of coprime-to-`6` orbit states and the `8/9` logarithmic-floor exclusion

This file formalizes the elementary fixed-modulus harmonic-packing argument appearing in §4.1 of
the EOC manuscript (Lemma 4.3 *carry budget*, Lemma 4.4 *carry demand*, Theorem 4.5
*logarithmic-floor exclusion for every `B < 8/9`*).

Ingredients, by provenance:

* **Classical / modular.** Every post-initial accelerated state is odd and not divisible by `3`
  (`three_not_dvd_orbit_succ`, `orbit_succ_coprime_six`, already in `EOC.FinitePrefixPacking`);
  the harmonic bound `∑_{i<n} 1/(i+1) ≤ 1 + log n`, proved here by telescoping the elementary
  inequality `1 - x⁻¹ ≤ log x` (`sum_range_inv_succ_le_one_add_log`); `log x ≤ x - 1`.
* **Eliahou–Rozier product identity.** The exponentiated identity
  `m_k * 2^(R_k) = m_0 * ∏_{i<k} (1 + 1/(3 m_i))` is derived here (`orbit_mul_two_rpow_R`) from the
  exact natural-number identity `BoundedDriftCore.orbit_product_identity` already in the repository.
* **The manuscript's mod-`3` packing refinement.** Distinct states coprime to `6` are packed
  against the progressions `6j+1, 6j+5`, whose harmonic density is `1/3` rather than the `1/2` of
  all odd integers (`sum_inv_orbit_le`). This turns the carry-budget exponent into `1/9`
  (`carryE_le`), and the exponent comparison `1 - B > 1/9 ↔ B < 8/9` gives Theorem 4.5
  (`injective_orbit_not_eventually_log_floor`).

Every analytic statement is first proved as an explicit finite inequality with explicit
constants; no asymptotic notation is used as a hypothesis.

Scope. Stronger divergence-side results from the literature exist; they are intentionally not
used or formalized here. Neither the stronger threshold of the manuscript's §4.2 nor any claim
that `8/9` is the limit of this fixed-modulus method is formalized in this file.
-/

namespace EOC
namespace HarmonicPacking

open Finset

/-! ## 1. A rearrangement bound for antitone functions on finite sets of naturals -/

/-- For an antitone `f`, the sum of `f` over any finite set `T` of naturals is at most the sum of
`f` over the initial segment `{0, …, |T| - 1}` of the same cardinality. -/
theorem sum_le_sum_range_card_of_antitone (f : ℕ → ℝ) (hf : Antitone f) (T : Finset ℕ) :
    ∑ x ∈ T, f x ≤ ∑ j ∈ range T.card, f j := by
  induction T using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have ha : a ∉ s := fun has => lt_irrefl a (hlt a has)
    -- all elements of `s` lie below `a`, so `|s| ≤ a`
    have hcard : s.card ≤ a := by
      have hsub : s ⊆ range a := fun x hx => mem_range.mpr (hlt x hx)
      simpa using card_le_card hsub
    rw [sum_insert ha, card_insert_of_notMem ha, sum_range_succ, add_comm]
    exact add_le_add ih (hf hcard)

/-! ## 2. The harmonic sum of the progression `3j + 1` has leading coefficient `1/3` -/

theorem inv_three_mul_add_one_antitone :
    Antitone (fun j : ℕ => (1 : ℝ) / (3 * (j : ℝ) + 1)) := by
  intro i j hij
  have hi : (0 : ℝ) < 3 * (i : ℝ) + 1 := by positivity
  apply one_div_le_one_div_of_le hi
  have : (i : ℝ) ≤ j := by exact_mod_cast hij
  linarith

/-- **Harmonic bound.** `∑_{i<n} 1/(i+1) ≤ 1 + log n` for every `n` (the classical bound
`H_n ≤ 1 + log n`). Integral-free: telescope `1/(j+2) ≤ log (j+2) - log (j+1)`, which is
`1 - x⁻¹ ≤ log x` at `x = (j+2)/(j+1)`. -/
theorem sum_range_inv_succ_le_one_add_log (n : ℕ) :
    ∑ i ∈ range n, ((i : ℝ) + 1)⁻¹ ≤ 1 + Real.log n := by
  rcases n with _ | n
  · simp
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hn2 : (0 : ℝ) < (n : ℝ) + 1 + 1 := by positivity
    -- `1/(n+2) ≤ log (n+2) - log (n+1)`
    have hstep : ((n : ℝ) + 1 + 1)⁻¹ ≤ Real.log ((n : ℝ) + 1 + 1) - Real.log ((n : ℝ) + 1) := by
      have h := Real.one_sub_inv_le_log_of_pos (div_pos hn2 hn1)
      rw [Real.log_div hn2.ne' hn1.ne', inv_div] at h
      have hid : 1 - ((n : ℝ) + 1) / ((n : ℝ) + 1 + 1) = ((n : ℝ) + 1 + 1)⁻¹ := by
        field_simp
        ring
      linarith
    push_cast at ih ⊢
    linarith

/-- **Explicit finite harmonic bound.** `∑_{j<n} 1/(3j+1) ≤ 4/3 + (1/3) log n` for every `n`.
The leading coefficient `1/3` is exact: for `j ≥ 1`, `1/(3j+1) ≤ (1/3)(1/j)`, and
`∑_{i<n} 1/(i+1) ≤ 1 + log n` (`sum_range_inv_succ_le_one_add_log`). -/
theorem sum_range_inv_three_mul_add_one_le (n : ℕ) :
    ∑ j ∈ range n, (1 : ℝ) / (3 * (j : ℝ) + 1) ≤ 4 / 3 + (1 / 3) * Real.log n := by
  rcases n with _ | n
  · norm_num
  -- split off the `j = 0` term
  rw [sum_range_succ']
  have hterm : ∀ j ∈ range n, (1 : ℝ) / (3 * ((j + 1 : ℕ) : ℝ) + 1)
      ≤ (1 / 3) * ((j : ℝ) + 1)⁻¹ := by
    intro j _
    push_cast
    have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    rw [show (1 : ℝ) / 3 * ((j : ℝ) + 1)⁻¹ = 1 / (3 * ((j : ℝ) + 1)) by field_simp]
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have hsum : ∑ j ∈ range n, (1 : ℝ) / (3 * ((j + 1 : ℕ) : ℝ) + 1)
      ≤ (1 / 3) * ∑ j ∈ range n, ((j : ℝ) + 1)⁻¹ := by
    rw [mul_sum]
    exact sum_le_sum hterm
  have hH := sum_range_inv_succ_le_one_add_log n
  have hlog : Real.log (n : ℝ) ≤ Real.log ((n + 1 : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · exact Real.log_le_log (by exact_mod_cast hn) (by push_cast; linarith)
  simp only [Nat.cast_zero, mul_zero, zero_add, ne_eq, one_ne_zero, not_false_eq_true,
    div_self]
  linarith

/-! ## 3. Distinct-state harmonic packing over the integers coprime to `6` -/

/-- A value `x` that is odd and not divisible by `3` satisfies `3 (rank x - 1) + 1 ≤ x`, where
`rank = coprimeSixRank` enumerates `1, 5, 7, 11, 13, …` as `1, 2, 3, 4, 5, …`. -/
theorem three_mul_rank_pred_add_one_le {x : ℕ} (hodd : Odd x) (hthree : ¬ 3 ∣ x) :
    3 * (coprimeSixRank x - 1) + 1 ≤ x := by
  have h1 := coprimeSixRank_pos x
  have h2 := three_mul_coprimeSixRank_le_add_two hodd hthree
  omega

/-- **Harmonic packing (finite form).** If `m 0, …, m (n-1)` are pairwise distinct, odd and not
divisible by `3`, then `∑_{k<n} 1/m_k ≤ ∑_{j<n} 1/(3j+1)`: the extremal configuration is the
initial segment `1, 5, 7, 11, …` of the integers coprime to `6`, whose `j`-th element is at least
`3j + 1`. -/
theorem sum_inv_le_sum_inv_three_mul_add_one (m : ℕ → ℕ) (n : ℕ)
    (hinj : ∀ i < n, ∀ j < n, m i = m j → i = j)
    (hodd : ∀ i < n, Odd (m i)) (hthree : ∀ i < n, ¬ 3 ∣ m i) :
    ∑ k ∈ range n, (1 : ℝ) / (m k : ℝ) ≤ ∑ j ∈ range n, (1 : ℝ) / (3 * (j : ℝ) + 1) := by
  set f : ℕ → ℝ := fun j => (1 : ℝ) / (3 * (j : ℝ) + 1) with hf
  set r : ℕ → ℕ := fun k => coprimeSixRank (m k) - 1 with hr
  have hrinj : Set.InjOn r (range n : Set ℕ) := by
    intro i hi j hj hij
    have hi' : i < n := mem_range.mp hi
    have hj' : j < n := mem_range.mp hj
    have hpi := coprimeSixRank_pos (m i)
    have hpj := coprimeSixRank_pos (m j)
    have hrank : coprimeSixRank (m i) = coprimeSixRank (m j) := by
      simp only [hr] at hij
      omega
    exact hinj i hi' j hj'
      (coprimeSixRank_injective_on (hodd i hi') (hthree i hi') (hodd j hj') (hthree j hj') hrank)
  -- termwise: `1/m_k ≤ f (r k)`
  have hterm : ∀ k ∈ range n, (1 : ℝ) / (m k : ℝ) ≤ f (r k) := by
    intro k hk
    have hk' : k < n := mem_range.mp hk
    have hle := three_mul_rank_pred_add_one_le (hodd k hk') (hthree k hk')
    have hle' : 3 * ((r k : ℕ) : ℝ) + 1 ≤ (m k : ℝ) := by exact_mod_cast hle
    exact one_div_le_one_div_of_le (by positivity) hle'
  calc ∑ k ∈ range n, (1 : ℝ) / (m k : ℝ)
      ≤ ∑ k ∈ range n, f (r k) := sum_le_sum hterm
    _ = ∑ x ∈ (range n).image r, f x := (sum_image hrinj).symm
    _ ≤ ∑ j ∈ range ((range n).image r).card, f j :=
        sum_le_sum_range_card_of_antitone f inv_three_mul_add_one_antitone _
    _ = ∑ j ∈ range n, f j := by rw [card_image_of_injOn hrinj, card_range]

/-- **Coprime-six harmonic packing along an accelerated orbit.** If the first `N` states of the
odd orbit of `M` are pairwise distinct, then `∑_{k<N} 1/m_k ≤ 7/3 + (1/3) log N`.

The initial state contributes at most `1`; the post-initial states are distinct integers coprime
to `6` and are packed by `sum_inv_le_sum_inv_three_mul_add_one`. -/
theorem sum_inv_orbit_le (M N : ℕ) (hM : Odd M)
    (hinj : ∀ i < N, ∀ j < N, orbit M i = orbit M j → i = j) :
    ∑ k ∈ range N, (1 : ℝ) / (orbit M k : ℝ) ≤ 7 / 3 + (1 / 3) * Real.log N := by
  rcases N with _ | n
  · norm_num
  rw [sum_range_succ']
  have h0 : (1 : ℝ) / (orbit M 0 : ℝ) ≤ 1 := by
    have : (1 : ℝ) ≤ (orbit M 0 : ℝ) := by exact_mod_cast (odd_orbit hM 0).pos
    rw [div_le_one (by linarith)]
    exact this
  have hpack := sum_inv_le_sum_inv_three_mul_add_one (fun k => orbit M (k + 1)) n
    (fun i hi j hj heq => by
      have := hinj (i + 1) (by omega) (j + 1) (by omega) heq
      omega)
    (fun i _ => odd_orbit hM (i + 1))
    (fun i _ => three_not_dvd_orbit_succ M i)
  have hharm := sum_range_inv_three_mul_add_one_le n
  have hlog : Real.log (n : ℝ) ≤ Real.log ((n + 1 : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · exact Real.log_le_log (by exact_mod_cast hn) (by push_cast; linarith)
  linarith

/-! ## 4. Carry quantities and the Eliahou–Rozier identity -/

open PeriodicCore BoundedDriftCore

/-- The valuation word of the accelerated orbit of `M`. -/
noncomputable abbrev orbWord (M : ℕ) : ℕ → ℕ := fun n => a (orbit M n)

/-- The manuscript's carry product `U_N = ∏_{k<N} (1 + 1/(3 m_k))`. -/
noncomputable def carryU (M N : ℕ) : ℝ := ∏ k ∈ range N, (1 + 1 / (3 * (orbit M k : ℝ)))

/-- The manuscript's carry sum `E_N = ∑_{k<N} log₂ (1 + 1/(3 m_k))`. -/
noncomputable def carryE (M N : ℕ) : ℝ :=
  ∑ k ∈ range N, Real.logb 2 (1 + 1 / (3 * (orbit M k : ℝ)))

theorem carry_factor_pos (x : ℕ) : 0 < 1 + 1 / (3 * (x : ℝ)) := by
  have : 0 ≤ 1 / (3 * (x : ℝ)) := by positivity
  linarith

theorem carryU_pos (M N : ℕ) : 0 < carryU M N :=
  prod_pos fun k _ => carry_factor_pos (orbit M k)

theorem carryU_succ (M k : ℕ) :
    carryU M (k + 1) = carryU M k * (1 + 1 / (3 * (orbit M k : ℝ))) := by
  unfold carryU
  rw [prod_range_succ]

theorem carryE_eq_logb_carryU (M N : ℕ) : carryE M N = Real.logb 2 (carryU M N) := by
  induction N with
  | zero => simp [carryE, carryU]
  | succ N ih =>
    rw [carryU_succ, Real.logb_mul (carryU_pos M N).ne' (carry_factor_pos _).ne', ← ih]
    unfold carryE
    rw [sum_range_succ]

/-- `U_N = 2^{E_N}` (the manuscript's definition of `U`). -/
theorem carryU_eq_two_rpow_carryE (M N : ℕ) : carryU M N = (2 : ℝ) ^ carryE M N := by
  rw [carryE_eq_logb_carryU, Real.rpow_logb (by norm_num) (by norm_num) (carryU_pos M N)]

/-- Cast of the core range product. -/
theorem cast_pr (f : ℕ → ℕ) (n : ℕ) : ((pr f n : ℕ) : ℝ) = ∏ i ∈ range n, (f i : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pr_succ, Nat.cast_mul, ih, prod_range_succ]

/-- `2^{R_k} = 2^{s_k} / 3^k`, with `R_k = s_k - k log₂ 3` the repository's real drift. -/
theorem two_rpow_R (d : ℕ → ℕ) (k : ℕ) :
    (2 : ℝ) ^ (R d k) = (2 : ℝ) ^ (s d k) / (3 : ℝ) ^ k := by
  have h3 : (3 : ℝ) ^ k = (2 : ℝ) ^ ((k : ℝ) * alpha) := by
    unfold alpha
    rw [mul_comm, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_logb (by norm_num) (by norm_num) (by norm_num), Real.rpow_natCast]
  unfold R
  rw [Real.rpow_sub (by norm_num), Real.rpow_natCast, h3]

/-- **Eliahou–Rozier identity (exponentiated form, manuscript Lemma 2.2).** For odd `M`,
`m_k · 2^{R_k} = m_0 · U_k`. Derived from the exact natural-number identity
`BoundedDriftCore.orbit_product_identity`. -/
theorem orbit_mul_two_rpow_R (M k : ℕ) (hM : Odd M) :
    (orbit M k : ℝ) * (2 : ℝ) ^ (R (orbWord M) k) = (M : ℝ) * carryU M k := by
  have hid := orbit_product_identity (orbit M) (orbWord M) (orbit_step M) k
  rw [← s_eq_sr] at hid
  have hid' : (2 : ℝ) ^ (s (orbWord M) k) * (orbit M k : ℝ) * ∏ i ∈ range k, (3 * (orbit M i : ℝ))
      = (3 : ℝ) ^ k * (M : ℝ) * ∏ i ∈ range k, (3 * (orbit M i : ℝ) + 1) := by
    have := congrArg (fun n : ℕ => (n : ℝ)) hid
    simp only [Nat.cast_mul, Nat.cast_pow, cast_pr, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one,
      orbit_zero] at this
    exact this
  have hpos : ∀ i ∈ range k, (0 : ℝ) < 3 * (orbit M i : ℝ) := fun i _ => by
    have : (0 : ℝ) < (orbit M i : ℝ) := by exact_mod_cast (odd_orbit hM i).pos
    positivity
  have hP : (0 : ℝ) < ∏ i ∈ range k, (3 * (orbit M i : ℝ)) := prod_pos hpos
  have hU : carryU M k
      = (∏ i ∈ range k, (3 * (orbit M i : ℝ) + 1)) / ∏ i ∈ range k, (3 * (orbit M i : ℝ)) := by
    unfold carryU
    rw [← prod_div_distrib]
    refine prod_congr rfl fun i _ => ?_
    have : (orbit M i : ℝ) ≠ 0 := by exact_mod_cast (odd_orbit hM i).pos.ne'
    field_simp
  rw [two_rpow_R, hU]
  have h3k : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  field_simp
  linear_combination hid'

/-- **Carry demand (manuscript Lemma 4.4).** `U_{k+1} - U_k = 2^{R_k} / (3 m_0)` exactly. -/
theorem carryU_succ_sub (M k : ℕ) (hM : Odd M) :
    carryU M (k + 1) - carryU M k = (2 : ℝ) ^ (R (orbWord M) k) / (3 * (M : ℝ)) := by
  have hmk : (0 : ℝ) < (orbit M k : ℝ) := by exact_mod_cast (odd_orbit hM k).pos
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM.pos
  have hid := orbit_mul_two_rpow_R M k hM
  -- solve the Eliahou–Rozier identity for `U_k`
  have hU : carryU M k = (orbit M k : ℝ) * (2 : ℝ) ^ (R (orbWord M) k) / (M : ℝ) := by
    rw [eq_div_iff hM0.ne']
    linarith
  -- `U_{k+1} - U_k = U_k / (3 m_k)`, then substitute
  rw [carryU_succ, hU]
  field_simp
  ring

/-! ## 5. Carry budget: the `1/9` exponent (manuscript Lemma 4.3) -/

/-- `log₂ (1 + x) ≤ x / ln 2` for `x ≥ 0`. -/
theorem logb_two_one_add_le (x : ℝ) (hx : 0 ≤ x) : Real.logb 2 (1 + x) ≤ x / Real.log 2 := by
  unfold Real.logb
  apply div_le_div_of_nonneg_right _ (Real.log_pos one_lt_two).le
  have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + x)
  linarith

/-- **Carry budget, explicit finite form (manuscript Lemma 4.3).** If the first `N` states of the
odd orbit of `M` are pairwise distinct, then
`E_N ≤ (1/9) log₂ N + 7 / (9 ln 2)`.

The coefficient `1/9 = (1/3) · (1/3)`: one factor `1/3` is the `1/(3 m_k)` inside the carry
factor, the other is the harmonic density of the integers coprime to `6` (`sum_inv_orbit_le`). -/
theorem carryE_le (M N : ℕ) (hM : Odd M)
    (hinj : ∀ i < N, ∀ j < N, orbit M i = orbit M j → i = j) :
    carryE M N ≤ (1 / 9) * Real.logb 2 N + 7 / (9 * Real.log 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hterm : ∀ k ∈ range N, Real.logb 2 (1 + 1 / (3 * (orbit M k : ℝ)))
      ≤ (1 / (3 * Real.log 2)) * (1 / (orbit M k : ℝ)) := by
    intro k _
    calc Real.logb 2 (1 + 1 / (3 * (orbit M k : ℝ)))
        ≤ 1 / (3 * (orbit M k : ℝ)) / Real.log 2 := logb_two_one_add_le _ (by positivity)
      _ = (1 / (3 * Real.log 2)) * (1 / (orbit M k : ℝ)) := by ring
  have hpack := sum_inv_orbit_le M N hM hinj
  calc carryE M N
      ≤ ∑ k ∈ range N, (1 / (3 * Real.log 2)) * (1 / (orbit M k : ℝ)) := sum_le_sum hterm
    _ = (1 / (3 * Real.log 2)) * ∑ k ∈ range N, (1 / (orbit M k : ℝ)) := by rw [mul_sum]
    _ ≤ (1 / (3 * Real.log 2)) * (7 / 3 + (1 / 3) * Real.log N) :=
        mul_le_mul_of_nonneg_left hpack (by positivity)
    _ = (1 / 9) * Real.logb 2 N + 7 / (9 * Real.log 2) := by
        unfold Real.logb
        field_simp
        ring

/-- **Carry budget, product form.** Under the same hypotheses and `N ≥ 1`,
`U_N = 2^{E_N} ≤ e^{7/9} · N^{1/9}`. -/
theorem carryU_le (M N : ℕ) (hM : Odd M) (hN : 1 ≤ N)
    (hinj : ∀ i < N, ∀ j < N, orbit M i = orbit M j → i = j) :
    carryU M N ≤ Real.exp (7 / 9) * (N : ℝ) ^ ((1 : ℝ) / 9) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  rw [carryU_eq_two_rpow_carryE]
  calc (2 : ℝ) ^ carryE M N
      ≤ (2 : ℝ) ^ ((1 / 9) * Real.logb 2 N + 7 / (9 * Real.log 2)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (carryE_le M N hM hinj)
    _ = Real.exp (7 / 9) * (N : ℝ) ^ ((1 : ℝ) / 9) := by
        rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos hNpos, ← Real.exp_add]
        congr 1
        unfold Real.logb
        field_simp
        ring

/-- Asymptotic packaging of the carry budget: for an injective orbit, `2^{E_N} = O(N^{1/9})`.
This is a corollary of the explicit bound `carryU_le`; no asymptotic statement is assumed. -/
theorem carryU_isBigO (M : ℕ) (hM : Odd M) (hinj : ∀ i j, orbit M i = orbit M j → i = j) :
    (fun N : ℕ => carryU M N) =O[Filter.atTop] (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 9)) := by
  refine Asymptotics.IsBigO.of_bound (Real.exp (7 / 9)) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  rw [Real.norm_of_nonneg (carryU_pos M N).le,
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)]
  exact carryU_le M N hM hN (fun i _ j _ h => hinj i j h)

/-! ## 6. The `8/9` logarithmic-floor exclusion (manuscript Theorem 4.5) -/

/-- Telescoped carry demand: `U_{N₁+t} = U_{N₁} + ∑_{i<t} 2^{R_{N₁+i}} / (3 m_0)`. -/
theorem carryU_telescope (M N₁ : ℕ) (hM : Odd M) (t : ℕ) :
    carryU M (N₁ + t)
      = carryU M N₁ + ∑ i ∈ range t, (2 : ℝ) ^ (R (orbWord M) (N₁ + i)) / (3 * (M : ℝ)) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h := carryU_succ_sub M (N₁ + t) hM
    rw [← add_assoc, sum_range_succ, ← add_assoc, ← ih]
    linarith

/-- **Demand side.** An eventual floor `R_k ≥ -B log₂ k` (`k ≥ N₁ ≥ 1`, `B ≥ 0`) forces
`t · (N₁+t)^{-B} ≤ 3 m_0 · U_{N₁+t}`: the carry product grows at least like `N^{1-B}`. -/
theorem floor_lower_accumulation (M : ℕ) (hM : Odd M) (B : ℝ) (hB0 : 0 ≤ B) (N₁ : ℕ)
    (hN₁ : 1 ≤ N₁) (hfloor : ∀ k ≥ N₁, -B * Real.logb 2 k ≤ R (orbWord M) k) (t : ℕ) :
    (t : ℝ) * ((N₁ + t : ℕ) : ℝ) ^ (-B) ≤ 3 * (M : ℝ) * carryU M (N₁ + t) := by
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM.pos
  set N : ℕ := N₁ + t with hNdef
  -- each summand is at least `N^{-B} / (3 m_0)`
  have hterm : ∀ i ∈ range t, ((N : ℕ) : ℝ) ^ (-B) / (3 * (M : ℝ))
      ≤ (2 : ℝ) ^ (R (orbWord M) (N₁ + i)) / (3 * (M : ℝ)) := by
    intro i hi
    have hit : i < t := mem_range.mp hi
    set k : ℕ := N₁ + i with hk
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
    have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
    have hkN : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show k ≤ N by omega)
    -- `k^{-B} = 2^{-B log₂ k} ≤ 2^{R_k}`
    have hpow : (k : ℝ) ^ (-B) ≤ (2 : ℝ) ^ (R (orbWord M) k) := by
      have heq : (k : ℝ) ^ (-B) = (2 : ℝ) ^ (-B * Real.logb 2 k) := by
        rw [mul_comm, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
          Real.rpow_logb (by norm_num) (by norm_num) hkpos]
      rw [heq]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (hfloor k (by omega))
    -- `N^{-B} ≤ k^{-B}` since `k ≤ N` and `-B ≤ 0`
    have hNk : (N : ℝ) ^ (-B) ≤ (k : ℝ) ^ (-B) :=
      Real.rpow_le_rpow_of_nonpos hkpos hkN (by linarith)
    exact div_le_div_of_nonneg_right (le_trans hNk hpow) (by positivity)
  have hsum : (t : ℝ) * ((N : ℕ) : ℝ) ^ (-B) / (3 * (M : ℝ))
      ≤ ∑ i ∈ range t, (2 : ℝ) ^ (R (orbWord M) (N₁ + i)) / (3 * (M : ℝ)) := by
    calc (t : ℝ) * ((N : ℕ) : ℝ) ^ (-B) / (3 * (M : ℝ))
        = ∑ _i ∈ range t, ((N : ℕ) : ℝ) ^ (-B) / (3 * (M : ℝ)) := by
          rw [sum_const, card_range, nsmul_eq_mul, mul_div_assoc]
      _ ≤ _ := sum_le_sum hterm
  have htel := carryU_telescope M N₁ hM t
  have hU₁ := carryU_pos M N₁
  rw [div_le_iff₀ (by positivity)] at hsum
  have : ∑ i ∈ range t, (2 : ℝ) ^ (R (orbWord M) (N₁ + i)) / (3 * (M : ℝ))
      ≤ carryU M N := by rw [hNdef, htel]; linarith
  nlinarith

/-- The exponent comparison behind Theorem 4.5: the demand exponent `1 - B` exceeds the budget
exponent `1/9` exactly when `B < 8/9`. -/
theorem exponent_gap_iff (B : ℝ) : (1 : ℝ) / 9 < 1 - B ↔ B < 8 / 9 := by
  constructor <;> intro h <;> linarith

/-- **Logarithmic-floor exclusion, `8/9` (manuscript Theorem 4.5).** Let `M` be odd with an
injective accelerated orbit (manuscript Definition 4.1). For every real `B < 8/9`, the floor
`R_k ≥ -B log₂ k` does not hold for all sufficiently large `k`.

Proof outline: an eventual floor forces `(N/2) · N^{-B} ≤ 3 m_0 U_N` (`floor_lower_accumulation`),
while the carry budget gives `U_N ≤ e^{7/9} N^{1/9}` (`carryU_le`). Hence `N^{(1-B) - 1/9}` stays
bounded, which is impossible because `(1 - B) - 1/9 > 0` (`exponent_gap_iff`). -/
theorem injective_orbit_not_eventually_log_floor (M : ℕ) (hM : Odd M)
    (hinj : ∀ i j, orbit M i = orbit M j → i = j) (B : ℝ) (hB : B < 8 / 9) :
    ¬ ∃ N₀ : ℕ, ∀ k ≥ N₀, -B * Real.logb 2 k ≤ R (orbWord M) k := by
  rintro ⟨N₀, hfloor⟩
  -- WLOG `B ≥ 0`: a floor at `B` implies the floor at `max B 0`, since `log₂ k ≥ 0` for `k ≥ 1`.
  set B' : ℝ := max B 0 with hB'def
  have hB'0 : 0 ≤ B' := le_max_right _ _
  have hB'lt : B' < 8 / 9 := max_lt hB (by norm_num)
  set N₁ : ℕ := max N₀ 1 with hN₁def
  have hN₁ : 1 ≤ N₁ := le_max_right _ _
  have hfloor' : ∀ k ≥ N₁, -B' * Real.logb 2 k ≤ R (orbWord M) k := by
    intro k hk
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast le_trans hN₁ hk
    have hlog : 0 ≤ Real.logb 2 k := Real.logb_nonneg (by norm_num) hk1
    have hBB' : B ≤ B' := le_max_left _ _
    have : -B' * Real.logb 2 k ≤ -B * Real.logb 2 k := by nlinarith
    exact le_trans this (hfloor k (le_trans (le_max_left _ _) hk))
  -- the exponent gap `ε = (1 - B') - 1/9 > 0`
  have hgap : (1 : ℝ) / 9 < 1 - B' := (exponent_gap_iff B').mpr hB'lt
  set ε : ℝ := (1 - B') - 1 / 9 with hεdef
  have hε : 0 < ε := by linarith
  set K : ℝ := 6 * (M : ℝ) * Real.exp (7 / 9) with hKdef
  -- `x^ε → ∞`, so pick a horizon where `N^ε > K`
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp ((tendsto_rpow_atTop hε).eventually_gt_atTop K)
  set t : ℕ := max N₁ ⌈X⌉₊ with htdef
  set N : ℕ := N₁ + t with hNdef
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hNX : X ≤ (N : ℝ) := by
    have h1 : X ≤ (⌈X⌉₊ : ℝ) := Nat.le_ceil X
    have h2 : (⌈X⌉₊ : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show ⌈X⌉₊ ≤ N by omega)
    linarith
  have hbig : K < (N : ℝ) ^ ε := hX N hNX
  -- demand: `t N^{-B'} ≤ 3 m_0 U_N`, with `N ≤ 2t`
  have hlow := floor_lower_accumulation M hM B' hB'0 N₁ hN₁ hfloor' t
  have ht2 : (N : ℝ) ≤ 2 * (t : ℝ) := by exact_mod_cast (show N ≤ 2 * t by omega)
  -- budget: `U_N ≤ e^{7/9} N^{1/9}`
  have hup := carryU_le M N hM hN1 (fun i _ j _ h => hinj i j h)
  have hnegB : (0 : ℝ) ≤ (N : ℝ) ^ (-B') := Real.rpow_nonneg hNpos.le _
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  -- `N^{ε} · N^{1/9} = N · N^{-B'}`
  have hsplit : (N : ℝ) ^ ε * (N : ℝ) ^ ((1 : ℝ) / 9) = (N : ℝ) * (N : ℝ) ^ (-B') := by
    rw [← Real.rpow_add hNpos, show ε + 1 / 9 = 1 + (-B') by rw [hεdef]; ring,
      Real.rpow_add hNpos, Real.rpow_one]
  have hchain : (N : ℝ) ^ ε * (N : ℝ) ^ ((1 : ℝ) / 9) ≤ K * (N : ℝ) ^ ((1 : ℝ) / 9) := by
    rw [hsplit]
    calc (N : ℝ) * (N : ℝ) ^ (-B')
        ≤ 2 * (t : ℝ) * (N : ℝ) ^ (-B') := mul_le_mul_of_nonneg_right ht2 hnegB
      _ = 2 * ((t : ℝ) * (N : ℝ) ^ (-B')) := by ring
      _ ≤ 2 * (3 * (M : ℝ) * carryU M N) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          simpa [hNdef] using hlow
      _ = 6 * (M : ℝ) * carryU M N := by ring
      _ ≤ 6 * (M : ℝ) * (Real.exp (7 / 9) * (N : ℝ) ^ ((1 : ℝ) / 9)) :=
          mul_le_mul_of_nonneg_left hup (by positivity)
      _ = K * (N : ℝ) ^ ((1 : ℝ) / 9) := by rw [hKdef]; ring
  have hN9 : (0 : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 9) := Real.rpow_pos_of_pos hNpos _
  have : (N : ℝ) ^ ε ≤ K := le_of_mul_le_mul_right hchain hN9
  linarith

/-- **Theorem 4.5, "infinitely often" form.** Equivalent restatement of
`injective_orbit_not_eventually_log_floor`: for every `B < 8/9` and every threshold `N₀` there is
`k ≥ N₀` with `R_k < -B log₂ k`, i.e. the floor fails for infinitely many `k`. -/
theorem injective_orbit_log_floor_fails_infinitely_often (M : ℕ) (hM : Odd M)
    (hinj : ∀ i j, orbit M i = orbit M j → i = j) (B : ℝ) (hB : B < 8 / 9) :
    ∀ N₀ : ℕ, ∃ k ≥ N₀, R (orbWord M) k < -B * Real.logb 2 k := by
  have h := injective_orbit_not_eventually_log_floor M hM hinj B hB
  push Not at h
  exact h

end HarmonicPacking
end EOC
