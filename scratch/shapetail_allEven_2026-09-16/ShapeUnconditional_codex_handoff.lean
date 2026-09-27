import EOC.ShapeCertificate
import EOC.BinomialEntropy
import EOC.CapacityBounds
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Choose.Sum

/-!
# An explicit unconditional ShapeTail scale family

This file instantiates the exact ShapeTail certificate on the cofinal family
`j₀ = 300(q+1)` for the actual zero-offset Collatz barrier.  All numerical
comparisons are integer comparisons.
-/

namespace EOC
namespace ShapeUnconditional

set_option maxHeartbeats 300000

open Finset CapacityBounds OddBlack ShapeCertificate

theorem alpha_block_lower : (475 : ℝ) < 300 * alpha := by
  have hp : (2 : ℕ) ^ 475 < 3 ^ 300 := by native_decide
  have hp' : (2 : ℝ) ^ 475 < 3 ^ 300 := by exact_mod_cast hp
  have h := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) (by positivity) hp'
  rw [Real.logb_pow, Real.logb_pow] at h
  norm_num at h ⊢
  simpa [alpha, mul_comm] using h

theorem alpha_block_upper : 300 * alpha < (476 : ℝ) := by
  have hp : (3 : ℕ) ^ 300 < 2 ^ 476 := by native_decide
  have h := alpha_mul_lt_of_pow_lt 300 476 hp
  simpa [mul_comm] using h

theorem barrier_add_lower (n : ℕ) :
    collatzBarrier 0 n + 475 ≤ collatzBarrier 0 (n + 300) := by
  unfold collatzBarrier
  rw [Nat.le_floor_iff (barrier_arg_nonneg 0 (n + 300))]
  have hfl := Nat.floor_le (barrier_arg_nonneg 0 n)
  push_cast at hfl ⊢
  norm_num at hfl ⊢
  nlinarith [alpha_block_lower]

theorem barrier_add_upper (n : ℕ) :
    collatzBarrier 0 (n + 300) ≤ collatzBarrier 0 n + 476 := by
  unfold collatzBarrier
  have hlo := Nat.sub_one_lt_floor ((n : ℝ) * alpha)
  have hhi := Nat.floor_le (barrier_arg_nonneg 0 (n + 300))
  push_cast at hlo hhi
  norm_num at hlo hhi
  have hr : (⌊((n + 300 : ℕ) : ℝ) * alpha + (0 : ℕ)⌋₊ : ℝ)
      < (⌊(n : ℝ) * alpha + (0 : ℕ)⌋₊ : ℝ) + 477 := by
    norm_num
    nlinarith [alpha_block_upper]
  have hn : ⌊((n + 300 : ℕ) : ℝ) * alpha + (0 : ℕ)⌋₊
      < ⌊(n : ℝ) * alpha + (0 : ℕ)⌋₊ + 477 := by exact_mod_cast hr
  omega

theorem choose_mul_le_choose_add (n m k l : ℕ) :
    n.choose k * m.choose l ≤ (n + m).choose (k + l) := by
  rw [Nat.add_choose_eq]
  have hm : (k, l) ∈ antidiagonal (k + l) := by simp
  exact Finset.single_le_sum
    (fun (ij : ℕ × ℕ) (_ : ij ∈ antidiagonal (k + l)) =>
      Nat.zero_le (n.choose ij.1 * m.choose ij.2)) hm

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem choose_block_growth (q : ℕ) :
    (collatzBarrier 0 (300 * (q + 1)) - 1).choose (300 * (q + 1) - 1) *
        ((475).choose 300)
      ≤ (collatzBarrier 0 (300 * (q + 2)) - 1).choose (300 * (q + 2) - 1) := by
  let n := collatzBarrier 0 (300 * (q + 1)) - 1
  let k := 300 * (q + 1) - 1
  have hj : 1 ≤ 300 * (q + 1) := by omega
  have hs : 1 ≤ collatzBarrier 0 (300 * (q + 1)) :=
    le_trans hj (le_collatzBarrier 0 _)
  have hn : n + 475 ≤ collatzBarrier 0 (300 * (q + 2)) - 1 := by
    dsimp [n]
    have h := barrier_add_lower (300 * (q + 1))
    have heq : 300 * (q + 2) = 300 * (q + 1) + 300 := by ring
    rw [heq]
    omega
  have hk : k + 300 = 300 * (q + 2) - 1 := by
    dsimp [k]
    omega
  calc
    n.choose k * (475).choose 300 ≤ (n + 475).choose (k + 300) :=
      choose_mul_le_choose_add n 475 k 300
    _ ≤ (collatzBarrier 0 (300 * (q + 2)) - 1).choose (k + 300) :=
      Nat.choose_le_choose _ hn
    _ = _ := by rw [hk]

def J (q : ℕ) : ℕ := 300 * (q + 1)
noncomputable def Sigma (q : ℕ) : ℕ := collatzBarrier 0 (J q)
def T (q : ℕ) : ℕ := 93 * (q + 1)
def K (q : ℕ) : ℕ := 12 * (q + 1)

theorem J_succ (q : ℕ) : J (q + 1) = J q + 300 := by simp [J]; ring
theorem T_succ (q : ℕ) : T (q + 1) = T q + 93 := by simp [T]; ring
theorem J_half_succ (q : ℕ) : J (q + 1) / 2 = J q / 2 + 150 := by simp [J]; omega

theorem sigma_zero : Sigma 0 = 475 := by
  dsimp [Sigma, J, collatzBarrier]
  change ⌊(300 : ℝ) * alpha⌋₊ = 475
  have hlo := alpha_block_lower
  have hhi := alpha_block_upper
  have hl : 475 ≤ ⌊(300 : ℝ) * alpha⌋₊ := by
    apply (Nat.le_floor_iff (by positivity)).mpr
    exact alpha_block_lower.le
  have hu : ⌊(300 : ℝ) * alpha⌋₊ < 476 := by
    by_contra h
    push Not at h
    have hc : (476 : ℝ) ≤ (⌊(300 : ℝ) * alpha⌋₊ : ℝ) := by exact_mod_cast h
    have hf := Nat.floor_le (by positivity : (0 : ℝ) ≤ 300 * alpha)
    linarith
  omega

theorem sigma_succ_lower (q : ℕ) : Sigma q + 475 ≤ Sigma (q + 1) := by
  rw [Sigma, Sigma, J_succ]
  exact barrier_add_lower (J q)

theorem sigma_succ_upper (q : ℕ) : Sigma (q + 1) ≤ Sigma q + 476 := by
  rw [Sigma, Sigma, J_succ]
  exact barrier_add_upper (J q)

theorem choose_block_growth' (q : ℕ) :
    (Sigma q - 1).choose (J q - 1) * (475).choose 300 ≤
      (Sigma (q + 1) - 1).choose (J (q + 1) - 1) := by
  rw [Sigma, Sigma]
  have hq : J q = 300 * (q + 1) := rfl
  have hs : J (q + 1) = 300 * (q + 2) := by simp [J]; ring
  rw [hq, hs]
  exact choose_block_growth q

theorem choose95_lower : 2 ^ 86 ≤ (95).choose 60 := by native_decide
theorem choose94_lower : 2 ^ 85 ≤ (94).choose 59 := by native_decide

theorem choose475_lower : 2 ^ 430 ≤ (475).choose 300 := by
  native_decide

theorem block_constant :
    2 * 3 ^ 150 * 2 ^ 477 ≤ 2 ^ 150 * 3 ^ 93 * (475).choose 300 := by
  have hn : 2 * 3 ^ 150 * 2 ^ 477 ≤ (2 ^ 150 * 3 ^ 93) * 2 ^ 430 := by
    native_decide
  have hc : (2 ^ 150 * 3 ^ 93) * 2 ^ 430
      ≤ (2 ^ 150 * 3 ^ 93) * (475).choose 300 :=
    Nat.mul_le_mul_left _ choose475_lower
  exact hn.trans hc

theorem choose474_lower : 2 ^ 429 ≤ (474).choose 299 := by
  native_decide

theorem arith_nat_zero :
    300 * 3 ^ 150 * 2 ^ 476 ≤ 2 ^ 150 * 3 ^ 93 * (474).choose 299 := by
  have hn : 300 * 3 ^ 150 * 2 ^ 476 ≤ (2 ^ 150 * 3 ^ 93) * 2 ^ 429 := by
    native_decide
  have hc : (2 ^ 150 * 3 ^ 93) * 2 ^ 429
      ≤ (2 ^ 150 * 3 ^ 93) * (474).choose 299 :=
    Nat.mul_le_mul_left _ choose474_lower
  exact hn.trans hc

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem arith_nat (q : ℕ) :
    J q * 3 ^ (J q / 2) * 2 ^ (Sigma q + (q + 1))
      ≤ 2 ^ (J q / 2) * 3 ^ T q * (Sigma q - 1).choose (J q - 1) := by
  induction q with
  | zero =>
      rw [sigma_zero]
      convert arith_nat_zero using 1 <;> norm_num [J, T]
  | succ q ih =>
      have hJ : J (q + 1) ≤ 2 * J q := by simp [J]; omega
      have hsig : Sigma (q + 1) + (q + 2) ≤ Sigma q + (q + 1) + 477 := by
        have := sigma_succ_upper q
        omega
      have hchoose := choose_block_growth' q
      have hL :
          J (q + 1) * 3 ^ (J (q + 1) / 2) * 2 ^ (Sigma (q + 1) + (q + 2))
            ≤ (J q * 3 ^ (J q / 2) * 2 ^ (Sigma q + (q + 1))) *
                (2 * 3 ^ 150 * 2 ^ 477) := by
        rw [J_half_succ, pow_add]
        calc
          J (q + 1) * (3 ^ (J q / 2) * 3 ^ 150) *
                2 ^ (Sigma (q + 1) + (q + 2))
              ≤ (2 * J q) * (3 ^ (J q / 2) * 3 ^ 150) *
                2 ^ (Sigma q + (q + 1) + 477) := by gcongr <;> norm_num
          _ = _ := by rw [pow_add]; ring
      have hR :
          (2 ^ (J q / 2) * 3 ^ T q * (Sigma q - 1).choose (J q - 1)) *
                (2 ^ 150 * 3 ^ 93 * (475).choose 300)
            ≤ 2 ^ (J (q + 1) / 2) * 3 ^ T (q + 1) *
                (Sigma (q + 1) - 1).choose (J (q + 1) - 1) := by
        rw [J_half_succ, T_succ, pow_add, pow_add]
        simpa [mul_assoc, mul_left_comm, mul_comm] using Nat.mul_le_mul_left
          (2 ^ (J q / 2) * 3 ^ T q) hchoose
      calc
        J (q + 1) * 3 ^ (J (q + 1) / 2) * 2 ^ (Sigma (q + 1) + (q + 2))
            ≤ (J q * 3 ^ (J q / 2) * 2 ^ (Sigma q + (q + 1))) *
                (2 * 3 ^ 150 * 2 ^ 477) := hL
        _ ≤ (2 ^ (J q / 2) * 3 ^ T q * (Sigma q - 1).choose (J q - 1)) *
                (2 * 3 ^ 150 * 2 ^ 477) := Nat.mul_le_mul_right _ ih
        _ ≤ (2 ^ (J q / 2) * 3 ^ T q * (Sigma q - 1).choose (J q - 1)) *
                (2 ^ 150 * 3 ^ 93 * (475).choose 300) :=
              Nat.mul_le_mul_left _ block_constant
        _ ≤ _ := hR

end ShapeUnconditional
end EOC
