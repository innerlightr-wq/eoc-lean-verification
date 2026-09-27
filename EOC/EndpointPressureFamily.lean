import EOC.EndpointPressure
import EOC.FrontierFamilyMulti

set_option maxHeartbeats 800000

/-!
# The explicit family from frequency-summed pressure

This file reuses every numerical constant of `FrontierFamilyMulti`, but replaces the legacy
dangerous-window hypothesis by the strictly weaker frequency-summed odd-dark pressure hypothesis.
-/

namespace EOC
namespace EndpointPressureFamily

open Finset CapacityBounds FiniteValuationWord PrefixCollision
open Classical
open FrontierFamilyMulti

private theorem shell_le_two_mul {j σ : ℕ} (hj : 2 ≤ j)
    (h63 : 63 * σ + 37 ≤ 100 * j) : σ + 2 ≤ 2 * j := by
  omega

theorem pairData_fam (hm : 1000 ≤ m) {s σ : ℕ}
    (hσK : σ < collatzBarrier 0 (P * m) + 1)
    (hx : collatzBarrier 0 (P * m) ≤ σ + 4 * m)
    (hLt : P * m + m - P * m ≤ s - σ)
    (ht : s - σ ≤ collatzBarrier 0 (P * m + m) - σ)
    (hpress : EndpointPressure.PowerOfTwoSummedPressureAt
      0 (P * m) σ (s - σ) (σ + (s - σ)) (1 / 108) (1 / 6) (93 / 10)) :
    EndpointPressure.ExplicitPairDataSummed 0 (P * m + m) (P * m) s σ 1 := by
  have hm100 : 100 ≤ m := by omega
  have hσb : σ ≤ collatzBarrier 0 (P * m) := by omega
  have hLm : P * m + m - P * m = m := by omega
  have h63 := h63_fam hm100
  refine ⟨4 * m, 1079998, 205198 * m, 1 / 108, 1 / 6, 93 / 10,
    1 / 6 + 1 / 1000, 1 / 60000,
    ?_, ?_, ?_, ?_, hσb, ?_, ?_, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_,
    by omega, by omega, by rw [hLm] at hLt ⊢; exact hLt, ht, by omega,
    hnum_fam hm100 hσb hx (by omega) ht, hpress⟩
  · unfold P; omega
  · exact ⟨540000 * m, by unfold P; ring⟩
  · simpa using hx
  · unfold P; omega
  · have : 63 * σ ≤ 63 * collatzBarrier 0 (P * m) := Nat.mul_le_mul_left _ hσb
    have hs63 : 63 * σ + 37 ≤ 100 * (P * m) := by omega
    have hj2 : 2 ≤ P * m := by unfold P; omega
    exact shell_le_two_mul hj2 hs63
  · have hσ2 : σ ≤ 2 * (P * m) := hσb.trans (b_le_two_j m)
    unfold P at hσ2 ⊢
    omega
  · have hj : (1080000000 : ℝ) ≤ ((P * m : ℕ) : ℝ) := by
      have : 1080000000 ≤ P * m := by unfold P; omega
      exact_mod_cast this
    push_cast at hj
    norm_num
    linarith
  · have e : ((P * m / 300 - 4 * m : ℕ) : ℝ) = 3596 * m := by
      have : P * m / 300 - 4 * m = 3596 * m := by unfold P; omega
      rw [this]
      push_cast
      ring
    rw [e]
    push_cast
    unfold P
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  · have hl2 := Real.log_two_lt_d9
    have hc := one_sub_cos_ge
    push_cast
    unfold P
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hcpos : (0 : ℝ) ≤ 1 - Real.cos (Real.pi * (1 / 108)) := by linarith
    nlinarith

/-- Exceptional-set bound for the explicit family from frequency-summed pressure alone. -/
theorem exceptional_bound_family_of_summedPressure (m : ℕ) (hm : 1000 ≤ m)
    (hpressure : ∀ σ t,
      collatzBarrier 0 (P * m) ≤ σ + 4 * m →
      σ ≤ collatzBarrier 0 (P * m) → m ≤ t →
      t ≤ collatzBarrier 0 (P * m + m) - σ →
      EndpointPressure.PowerOfTwoSummedPressureAt
        0 (P * m) σ t (σ + t) (1 / 108) (1 / 6) (93 / 10)) :
    (((range (2 ^ (collatzBarrier 0 (P * m) + 1))).filter fun μ =>
        Odd μ ∧ ∀ M, Confined ((0 : ℕ) : ℝ) (fun i => a (orbit μ i)) M).card : ℝ) ≤
      3 / 2 * ((2 ^ (collatzBarrier 0 (P * m) + 1) : ℕ) : ℝ) ^
        (Real.binEntropy alpha⁻¹ / Real.log 2 - TaoExternal.I0 / 2000000) := by
  have hm100 : 100 ≤ m := by omega
  have hLm : P * m + m - P * m = m := by omega
  have hgap := gap_ge (m := m) (by omega)
  have hKpos : (0 : ℝ) < ((collatzBarrier 0 (P * m) + 1 : ℕ) : ℝ) := by positivity
  have hbase := EndpointPressure.exceptional_bound_of_summedPressure_and_scalar
    0 (collatzBarrier 0 (P * m) + 1) (P * m) (4 * m)
    (((P * m + m : ℕ) : ℝ) / ((collatzBarrier 0 (P * m) + 1 : ℕ) : ℝ)) 1 1
    (N := P * m + m) (by norm_num) (by norm_num) (by unfold P; omega) (by omega)
    (Nat.lt_succ_self _) (by omega) (by rw [div_mul_cancel₀ _ hKpos.ne'])
    (by rw [hLm]; omega) (lt_of_le_of_lt (scalar_rho hm100) (by norm_num))
    (scalar_main hm100) (by
      intro s σ hKs hσK hx hLt ht
      have hLt' : m ≤ s - σ := by rw [hLm] at hLt; exact hLt
      exact pairData_fam hm hσK hx hLt ht
        (hpressure σ (s - σ) hx (by omega) hLt' ht))
  have hI0 := ExceptionalPowerBound.I0_pos'
  have hent := ExceptionalPowerBound.one_sub_I0_div_alpha_eq
  have hA := A_ge (m := m) hm100
  have hexp : 1 - TaoExternal.I0 *
      (((P * m + m : ℕ) : ℝ) / ((collatzBarrier 0 (P * m) + 1 : ℕ) : ℝ)) ≤
      Real.binEntropy alpha⁻¹ / Real.log 2 - TaoExternal.I0 / 2000000 := by
    rw [← hent]
    have := mul_le_mul_of_nonneg_left hA hI0.le
    have e : TaoExternal.I0 * (alpha⁻¹ + 1 / 2000000) =
        TaoExternal.I0 / alpha + TaoExternal.I0 / 2000000 := by
      rw [div_eq_mul_inv]
      ring
    linarith
  have hx1 : (1 : ℝ) ≤ ((2 ^ (collatzBarrier 0 (P * m) + 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_two_pow
  rw [show TaoExternal.lambdaStar * ((0 : ℕ) : ℝ) = 0 by simp, Real.exp_zero] at hbase
  calc
    _ ≤ _ := hbase
    _ = 3 / 2 * ((2 ^ (collatzBarrier 0 (P * m) + 1) : ℕ) : ℝ) ^
        (1 - TaoExternal.I0 *
          (((P * m + m : ℕ) : ℝ) / ((collatzBarrier 0 (P * m) + 1 : ℕ) : ℝ))) := by
          norm_num
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1 hexp) (by norm_num)

/-- Backward compatibility: the legacy dangerous-window hypotheses imply the new family theorem. -/
theorem exceptional_bound_family_of_dangerousWindowSparsity (m : ℕ) (hm : 1000 ≤ m)
    (hfr : ∀ σ t, collatzBarrier 0 (P * m) ≤ σ + 4 * m →
      σ ≤ collatzBarrier 0 (P * m) → m ≤ t →
      t ≤ collatzBarrier 0 (P * m + m) - σ →
      FrontierRegion.PowerOfTwoDangerousWindowSparsityAt
        0 (P * m) σ t (σ + t) (Kwin m) (1 / 108) 2 2) :
    (((range (2 ^ (collatzBarrier 0 (P * m) + 1))).filter fun μ =>
        Odd μ ∧ ∀ M, Confined ((0 : ℕ) : ℝ) (fun i => a (orbit μ i)) M).card : ℝ) ≤
      3 / 2 * ((2 ^ (collatzBarrier 0 (P * m) + 1) : ℕ) : ℝ) ^
        (Real.binEntropy alpha⁻¹ / Real.log 2 - TaoExternal.I0 / 2000000) := by
  apply exceptional_bound_family_of_summedPressure m hm
  intro σ t hx hσ hm_t ht
  have hm100 : 100 ≤ m := by omega
  have hjσ : P * m < σ := by
    have hlow := ShapeRegion.lower_barrier (P * m) (by unfold P; omega)
    unfold P at hlow hx ⊢
    omega
  have h2 : σ + 1 ≤ 2 * (P * m) := by
    have h63 := h63_fam hm100
    have := Nat.mul_le_mul_left 63 hσ
    omega
  convert EndpointPressure.summedPressure_of_dangerousWindowSparsity (A := 7)
    (by unfold P; omega) (by exact ⟨540000 * m, by unfold P; ring⟩) hjσ hσ
    (by
      have := Nat.mul_le_mul_left 63 hσ
      have h63 := h63_fam hm100
      omega)
    h2 (Nat.floor_pos.mpr (by
      have hj := j_ge hm100
      have hlog : (1 : ℝ) ≤ Real.logb 2 ((P * m : ℕ) : ℝ) := by
        rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]
        have : (2 : ℝ) ≤ ((P * m : ℕ) : ℝ) := by linarith
        simpa using this
      linarith))
    (by
      have h0 : (0 : ℝ) ≤ 7 * Real.logb 2 ((P * m : ℕ) : ℝ) := by
        have hj := j_ge hm100
        have hlog : (1 : ℝ) ≤ Real.logb 2 ((P * m : ℕ) : ℝ) := by
          rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]
          have : (2 : ℝ) ≤ ((P * m : ℕ) : ℝ) := by linarith
          simpa using this
        linarith
      have hf := Nat.floor_le h0
      change ((FrontierFamilyMulti.Kwin m : ℕ) : ℝ) ≤
        7 * Real.logb 2 ((P * m : ℕ) : ℝ) + 1
      rw [FrontierFamilyMulti.Kwin]
      exact hf.trans (by linarith))
    (by norm_num) (hfr σ t hx hσ hm_t ht) using 1 <;> norm_num

end EndpointPressureFamily
end EOC
