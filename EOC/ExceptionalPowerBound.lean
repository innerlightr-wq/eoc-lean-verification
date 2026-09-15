import EOC.EntropyBounds
import EOC.SurvivorDensity

/-!
# The baseline power bound `C_U · X^{H₂(1/α)}` for confined seeds

Combines `SurvivorDensity.survivor_count_le` (union bound over confined words + iid Chernoff) with
the elementary binomial entropy bound of `EntropyBounds`, at the fresh-bit depth
`N_X = ⌊log₂ X / α⌋`.

* `f_le_tangent` — for `x > 1`, `y ≥ 1`: `f y ≤ f x + (y − x)·log (x/(x−1)) + (y − x)²/x`, where
  `f t = t log t − (t−1) log (t−1)` (so `log C(s,N) ≤ N·f(s/N)`).
* `log_choose_barrier_le` — `log C(s_N, N) ≤ N·f(α) + c·log(α/(α−1)) + (c+1)²`.
* `f_alpha_div_log_two` — `f(α)/log 2 = α − I₀` (bits), hence `f(α)/(α log 2) = 1 − I₀/α`.
* `survivor_count_le_rpow` — for `X ≥ 4`, the odd seeds `μ < X` that are `c`-confined for
  `N_X = ⌊log₂ X / α⌋₊` steps number at most `Cc · X^{1 − I₀/α}`, with the explicit constant
  `Cc = e^{λ* c}·2^{I₀}/2 + e^{(c+1)² + c·log(α/(α−1))}`.
* `exceptional_count_le_rpow` — the same bound for the exceptional class
  `E_U = {μ odd : μ stays U-confined forever}` below `X`.
* `one_sub_I0_div_alpha_eq` — the exponent is `1 − I₀/α = H₂(1/α)` (binary entropy in bits).
* `exceptional_count_le_of_firstMoment` — conditional: a first-moment bound `S_X(N) ≤ C·M_X(N)`
  at depth `N ≥ A log₂ X` gives `#(E_U ∩ [0,X)) ≤ (C e^{λ* U}/2)·X^{1 − I₀ A}`.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace ExceptionalPowerBound

open Real Finset CapacityBounds EntropyBounds SurvivorDensity TaoExternal

/-- Tangent-line bound for the concave function `f`. -/
theorem f_le_tangent {x y : ℝ} (hx : 1 < x) (hy : 1 ≤ y) :
    f y ≤ f x + (y - x) * (log x - log (x - 1)) + (y - x) ^ 2 / x := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  have hy0 : 0 < y := by linarith
  have key : f y - f x - (y - x) * (log x - log (x - 1)) =
      y * (log y - log x) - (y - 1) * (log (y - 1) - log (x - 1)) := by
    unfold f
    ring
  have h1 : y * (log y - log x) ≤ y * (y / x - 1) := by
    have h := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
    rw [Real.log_div hy0.ne' hx0.ne'] at h
    exact mul_le_mul_of_nonneg_left h hy0.le
  have h2 : -((y - 1) * (log (y - 1) - log (x - 1))) ≤ x - y := by
    rcases eq_or_lt_of_le hy with h | h
    · rw [← h]
      simp only [sub_self, zero_mul, neg_zero]
      linarith
    · have hy1 : 0 < y - 1 := by linarith
      have hl := Real.log_le_sub_one_of_pos (div_pos hx1 hy1)
      rw [Real.log_div hx1.ne' hy1.ne'] at hl
      have hm := mul_le_mul_of_nonneg_left hl hy1.le
      have e : (y - 1) * ((x - 1) / (y - 1) - 1) = x - y := by
        field_simp
        ring
      nlinarith
  have h3 : y * (y / x - 1) + (x - y) = (y - x) ^ 2 / x := by
    field_simp
    ring
  linarith

theorem log_alpha_ratio_pos : 0 < log alpha - log (alpha - 1) := by
  have hα := one_lt_alpha
  have := Real.log_lt_log (by linarith : (0 : ℝ) < alpha - 1) (by linarith : alpha - 1 < alpha)
  linarith

/-- `log C(s_N, N) ≤ N f(α) + c log(α/(α−1)) + (c+1)²`. -/
theorem log_choose_barrier_le (c : ℕ) {N : ℕ} (hN : 1 ≤ N) :
    log (Nat.choose (collatzBarrier c N) N) ≤
      N * f alpha + c * (log alpha - log (alpha - 1)) + ((c : ℝ) + 1) ^ 2 := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hα := one_lt_alpha
  have hL := log_alpha_ratio_pos
  have h1 := log_choose_le_ent (collatzBarrier c N) N (le_collatzBarrier c N)
  rw [ent_eq_mul_f hN (le_collatzBarrier c N)] at h1
  set s : ℝ := (collatzBarrier c N : ℝ) with hs
  have hs_hi : s ≤ N * alpha + c := Nat.floor_le (barrier_arg_nonneg c N)
  have hs_lo : (N : ℝ) * alpha + c - 1 < s := Nat.sub_one_lt_floor _
  have hsN : (N : ℝ) ≤ s := by rw [hs]; exact_mod_cast le_collatzBarrier c N
  have hy1 : 1 ≤ s / N := by rw [le_div_iff₀ hN0]; linarith
  have ht := f_le_tangent hα hy1
  set e : ℝ := s - N * alpha with he
  have hyα : s / N - alpha = e / N := by rw [he]; field_simp
  rw [hyα] at ht
  have hmul : (N : ℝ) * f (s / N) ≤
      N * f alpha + e * (log alpha - log (alpha - 1)) + e ^ 2 / (N * alpha) := by
    have := mul_le_mul_of_nonneg_left ht hN0.le
    have eq1 : (N : ℝ) * (f alpha + e / N * (log alpha - log (alpha - 1)) + (e / N) ^ 2 / alpha) =
        N * f alpha + e * (log alpha - log (alpha - 1)) + e ^ 2 / (N * alpha) := by
      field_simp
    linarith
  have he_hi : e ≤ c := by rw [he]; linarith
  have he_lo : -1 < e := by rw [he]; have := (Nat.cast_nonneg c : (0 : ℝ) ≤ c); linarith
  have hesq : e ^ 2 ≤ ((c : ℝ) + 1) ^ 2 := by
    have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
    nlinarith
  have hNα : (1 : ℝ) ≤ N * alpha := by nlinarith
  have hterm2 : e ^ 2 / (N * alpha) ≤ ((c : ℝ) + 1) ^ 2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [sq_nonneg e]
  have hterm1 : e * (log alpha - log (alpha - 1)) ≤ c * (log alpha - log (alpha - 1)) :=
    mul_le_mul_of_nonneg_right he_hi hL.le
  linarith

theorem f_alpha_div_log_two : f alpha / log 2 = alpha - I0 := by
  have hl2 : log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  unfold f I0 collatzAlpha Real.logb
  field_simp
  ring

theorem f_alpha_pos : 0 < f alpha := by
  have hα := one_lt_alpha
  rw [alpha_entropy_eq]
  exact mul_pos (by linarith) (Real.binEntropy_pos (by positivity) (inv_lt_one_of_one_lt₀ hα))

theorem I0_pos' : 0 < I0 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith [rateNats_pos, rateNats_eq_I0_mul_log_two, hlog2]

/-- The exponent `1 − I₀/α` is the binary entropy `H₂(1/α)` in bits. -/
theorem one_sub_I0_div_alpha_eq : 1 - I0 / alpha = Real.binEntropy alpha⁻¹ / log 2 := by
  have hα : alpha ≠ 0 := by linarith [one_lt_alpha]
  have hl2 : log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have h1 := f_alpha_div_log_two
  rw [alpha_entropy_eq] at h1
  field_simp at h1 ⊢
  linarith

/-- The fresh-bit depth `N_X = ⌊log₂ X / α⌋₊`. -/
noncomputable def Nstar (X : ℕ) : ℕ := ⌊Real.logb 2 X / alpha⌋₊

/-- The explicit constant. -/
noncomputable def Cconst (c : ℕ) : ℝ :=
  Real.exp (lambdaStar * c) * (2 : ℝ) ^ I0 / 2 +
    Real.exp (((c : ℝ) + 1) ^ 2 + c * (log alpha - log (alpha - 1)))

theorem one_le_Nstar {X : ℕ} (hX : 4 ≤ X) : 1 ≤ Nstar X := by
  unfold Nstar
  have hα := one_lt_alpha
  have hα2 : alpha < 2 := collatzAlpha_lt_two
  have hlog : (2 : ℝ) ≤ Real.logb 2 X := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast (by omega : 0 < X))]
    norm_num
    exact_mod_cast hX
  have : (1 : ℝ) ≤ Real.logb 2 X / alpha := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  exact Nat.one_le_floor_iff _ |>.mpr this

open Classical in
/-- **Baseline power bound.** For `X ≥ 4`, the odd seeds below `X` that stay `c`-confined for
`N_X = ⌊log₂ X / α⌋₊` steps number at most `Cconst c · X^{1 − I₀/α}`. -/
theorem survivor_count_le_rpow (c : ℕ) {X : ℕ} (hX : 4 ≤ X) :
    (((range X).filter fun μ =>
        Odd μ ∧ Confined (c : ℝ) (fun i => a (orbit μ i)) (Nstar X)).card : ℝ) ≤
      Cconst c * (X : ℝ) ^ (1 - I0 / alpha) := by
  have hN := one_le_Nstar hX
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hα := one_lt_alpha
  have hαpos : 0 < alpha := by linarith
  have hI0 := I0_pos'
  have hbase := survivor_count_le c hN X
  set N := Nstar X with hNdef
  set t : ℝ := Real.logb 2 X / alpha with ht
  have ht0 : 0 ≤ t := by
    rw [ht]
    exact div_nonneg (Real.logb_nonneg (by norm_num) (by exact_mod_cast (by omega : 1 ≤ X)))
      hαpos.le
  have hN_le : (N : ℝ) ≤ t := Nat.floor_le ht0
  have hN_ge : t - 1 < N := Nat.sub_one_lt_floor t
  -- rpow facts
  have hX_t : (2 : ℝ) ^ (Real.logb 2 X) = X := Real.rpow_logb (by norm_num) (by norm_num) hXpos
  have hpow1 : (2 : ℝ) ^ (-(I0 * (N : ℝ))) ≤ (2 : ℝ) ^ I0 * (X : ℝ) ^ (-(I0 / alpha)) := by
    have hle : -(I0 * (N : ℝ)) ≤ I0 + Real.logb 2 X * (-(I0 / alpha)) := by
      have : Real.logb 2 X * (-(I0 / alpha)) = -(I0 * t) := by rw [ht]; ring
      rw [this]
      nlinarith
    calc (2 : ℝ) ^ (-(I0 * (N : ℝ))) ≤ (2 : ℝ) ^ (I0 + Real.logb 2 X * (-(I0 / alpha))) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hle
      _ = (2 : ℝ) ^ I0 * (X : ℝ) ^ (-(I0 / alpha)) := by
          rw [Real.rpow_add (by norm_num), Real.rpow_mul (by norm_num), hX_t]
  have hterm1 : (X : ℝ) / 2 * (Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (N : ℝ)))) ≤
      Real.exp (lambdaStar * c) * (2 : ℝ) ^ I0 / 2 * (X : ℝ) ^ (1 - I0 / alpha) := by
    have hXr : (X : ℝ) ^ (1 - I0 / alpha) = X * (X : ℝ) ^ (-(I0 / alpha)) := by
      rw [sub_eq_add_neg, Real.rpow_add hXpos, Real.rpow_one]
    rw [hXr]
    have he : 0 ≤ Real.exp (lambdaStar * c) := (Real.exp_pos _).le
    calc (X : ℝ) / 2 * (Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (N : ℝ))))
        ≤ (X : ℝ) / 2 *
            (Real.exp (lambdaStar * c) * ((2 : ℝ) ^ I0 * (X : ℝ) ^ (-(I0 / alpha)))) := by
          gcongr
      _ = Real.exp (lambdaStar * c) * (2 : ℝ) ^ I0 / 2 * (X * (X : ℝ) ^ (-(I0 / alpha))) := by
          ring
  -- binomial term
  have hC : (Nat.choose (collatzBarrier c N) N : ℝ) ≤
      Real.exp (((c : ℝ) + 1) ^ 2 + c * (log alpha - log (alpha - 1))) *
        (X : ℝ) ^ (1 - I0 / alpha) := by
    have hCpos : (0 : ℝ) < Nat.choose (collatzBarrier c N) N := by
      exact_mod_cast Nat.choose_pos (le_collatzBarrier c N)
    have hlog := log_choose_barrier_le c hN
    have hNf : (N : ℝ) * f alpha ≤ t * f alpha :=
      mul_le_mul_of_nonneg_right hN_le f_alpha_pos.le
    have hexp : t * f alpha = Real.log X * (1 - I0 / alpha) := by
      have hl2 : log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
      have hfa : f alpha = log 2 * (alpha - I0) := by
        have h := f_alpha_div_log_two
        rw [div_eq_iff hl2] at h
        linarith
      rw [ht, Real.logb, hfa]
      field_simp
    calc (Nat.choose (collatzBarrier c N) N : ℝ)
        = Real.exp (log (Nat.choose (collatzBarrier c N) N)) := (Real.exp_log hCpos).symm
      _ ≤ Real.exp (((c : ℝ) + 1) ^ 2 + c * (log alpha - log (alpha - 1)) +
            Real.log X * (1 - I0 / alpha)) := by
          apply Real.exp_le_exp.mpr
          linarith
      _ = Real.exp (((c : ℝ) + 1) ^ 2 + c * (log alpha - log (alpha - 1))) *
            (X : ℝ) ^ (1 - I0 / alpha) := by
          rw [Real.exp_add, Real.rpow_def_of_pos hXpos]
  calc _ ≤ (X : ℝ) / 2 * (Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (N : ℝ)))) +
        (Nat.choose (collatzBarrier c N) N : ℝ) := hbase
    _ ≤ Cconst c * (X : ℝ) ^ (1 - I0 / alpha) := by
        unfold Cconst
        rw [add_mul]
        exact add_le_add hterm1 hC

open Classical in
/-- **Exceptional class, baseline power bound.** The odd seeds below `X` that stay `U`-confined
forever number at most `Cconst U · X^{1 − I₀/α}`, `1 − I₀/α = H₂(1/α) ≈ 0.949956`. -/
theorem exceptional_count_le_rpow (U : ℕ) {X : ℕ} (hX : 4 ≤ X) :
    (((range X).filter fun μ =>
        Odd μ ∧ ∀ N, Confined (U : ℝ) (fun i => a (orbit μ i)) N).card : ℝ) ≤
      Cconst U * (X : ℝ) ^ (1 - I0 / alpha) := by
  refine le_trans ?_ (survivor_count_le_rpow U hX)
  exact_mod_cast card_le_card fun μ hμ => by
    rw [mem_filter] at hμ ⊢
    exact ⟨hμ.1, hμ.2.1, hμ.2.2 _⟩

open Classical in
/-- **Conditional power bound (first-moment equidistribution ⇒ exponent `1 − I₀A`).** If at some
depth `N ≥ A·log₂ X` the confined seeds below `X` satisfy the first-moment bound
`S_X(N) ≤ C·(X/2)·p_N(U)` (`p_N(U)` = the iid `Geom(2)` persistence probability), then the
exceptional class below `X` has at most `(C e^{λ* U}/2)·X^{1 − I₀ A}` elements. For `A = 1/α` this
is the unconditional baseline; any `A > 1/α` would improve the exponent. -/
theorem exceptional_count_le_of_firstMoment (U : ℕ) {X N : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X)
    (A C : ℝ) (hC : 0 ≤ C) (hNA : A * Real.logb 2 X ≤ N)
    (hyp : (((range X).filter fun μ =>
        Odd μ ∧ Confined (U : ℝ) (fun i => a (orbit μ i)) N).card : ℝ) ≤
      C * ((X : ℝ) / 2 * iidGeom2VectorProb N (geomPersistenceEvent collatzAlpha U N))) :
    (((range X).filter fun μ =>
        Odd μ ∧ ∀ M, Confined (U : ℝ) (fun i => a (orbit μ i)) M).card : ℝ) ≤
      C * Real.exp (lambdaStar * U) / 2 * (X : ℝ) ^ (1 - I0 * A) := by
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hI0 := I0_pos'
  have hsub : (((range X).filter fun μ =>
        Odd μ ∧ ∀ M, Confined (U : ℝ) (fun i => a (orbit μ i)) M).card : ℝ) ≤
      (((range X).filter fun μ =>
        Odd μ ∧ Confined (U : ℝ) (fun i => a (orbit μ i)) N).card : ℝ) := by
    exact_mod_cast card_le_card fun μ hμ => by
      rw [mem_filter] at hμ ⊢
      exact ⟨hμ.1, hμ.2.1, hμ.2.2 _⟩
  have hP := geometric_persistence_upper_bound_bits (U : ℝ) N hN
  have hpow : (2 : ℝ) ^ (-(I0 * (N : ℝ))) ≤ (X : ℝ) ^ (-(I0 * A)) := by
    have hX_t : (2 : ℝ) ^ (Real.logb 2 X) = X := Real.rpow_logb (by norm_num) (by norm_num) hXpos
    calc (2 : ℝ) ^ (-(I0 * (N : ℝ))) ≤ (2 : ℝ) ^ (Real.logb 2 X * (-(I0 * A))) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          nlinarith
      _ = (X : ℝ) ^ (-(I0 * A)) := by rw [Real.rpow_mul (by norm_num), hX_t]
  have hXr : (X : ℝ) ^ (1 - I0 * A) = X * (X : ℝ) ^ (-(I0 * A)) := by
    rw [sub_eq_add_neg, Real.rpow_add hXpos, Real.rpow_one]
  have he : 0 ≤ Real.exp (lambdaStar * U) := (Real.exp_pos _).le
  calc _ ≤ C * ((X : ℝ) / 2 * iidGeom2VectorProb N (geomPersistenceEvent collatzAlpha U N)) :=
        hsub.trans hyp
    _ ≤ C * ((X : ℝ) / 2 * (Real.exp (lambdaStar * U) * (X : ℝ) ^ (-(I0 * A)))) := by
        gcongr
        exact hP.trans (mul_le_mul_of_nonneg_left hpow he)
    _ = C * Real.exp (lambdaStar * U) / 2 * (X : ℝ) ^ (1 - I0 * A) := by
        rw [hXr]
        ring

end ExceptionalPowerBound
end EOC
