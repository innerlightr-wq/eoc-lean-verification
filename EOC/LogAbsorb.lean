import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Absorbing a logarithmic surplus into the exponential rate

The averaged-pressure hypothesis that the EOC programme is heading towards has the shape

  `∑_{r<n} w_r ≤ θ n + C log₂ n`

(the `O(log n)` term is forced: it is the Karlin–Altschul/Cramér maximal-segment behaviour of a
negative-drift sum, measured in `scratch/transient_2026-09-16`).  Downstream the quantity that
matters is `2^{∑ w}`, so the surplus contributes a *polynomial* factor `n^C`.  This file records the
elementary bookkeeping that absorbs it into a slightly larger exponential rate, with an explicit
finite threshold:

  **`log_absorb`** : for `0 ≤ C`, `θ < θ'` and `n ≥ (3C/(θ'-θ))²`,
  `C · log₂ n + θ · n ≤ θ' · n`.

The threshold comes from `log x ≤ 2√x` (i.e. `Real.log_le_sub_one_of_pos` applied to `√x`) and
`2/log 2 ≤ 3`.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace LogAbsorb

open Real

/-- `log x ≤ 2 √x` for `x > 0`. -/
theorem log_le_two_mul_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h := Real.log_le_sub_one_of_pos hs
  have hlog : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx.le
  rw [hlog] at h
  linarith

/-- `logb 2 x ≤ 3 √x` for `x > 0`: from `log x ≤ 2√x` and `2 / log 2 ≤ 3`. -/
theorem logb_le_three_mul_sqrt {x : ℝ} (hx : 0 < x) : Real.logb 2 x ≤ 3 * Real.sqrt x := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hl2 : (0.6931471803 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hs : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have h := log_le_two_mul_sqrt hx
  rw [Real.logb, div_le_iff₀ hlog2]
  nlinarith

/-- **Log absorption with an explicit threshold.**  If `0 ≤ C`, `θ < θ'` and
`n ≥ (3C/(θ'-θ))²`, then `C · log₂ n + θ · n ≤ θ' · n`. -/
theorem log_absorb {C θ θ' : ℝ} (hC : 0 ≤ C) (hθ : θ < θ') {n : ℝ} (hn0 : 0 < n)
    (hn : (3 * C / (θ' - θ)) ^ 2 ≤ n) :
    C * Real.logb 2 n + θ * n ≤ θ' * n := by
  have hd : 0 < θ' - θ := by linarith
  have hs : 0 ≤ Real.sqrt n := Real.sqrt_nonneg n
  have hsq : Real.sqrt ((3 * C / (θ' - θ)) ^ 2) ≤ Real.sqrt n := Real.sqrt_le_sqrt hn
  have hle : 3 * C / (θ' - θ) ≤ Real.sqrt n := by
    have hnn : 0 ≤ 3 * C / (θ' - θ) := by positivity
    rwa [Real.sqrt_sq hnn] at hsq
  -- hence `3 C ≤ (θ' - θ) √n`, and `C logb 2 n ≤ 3 C √n ≤ (θ'-θ) n`
  have h3C : 3 * C ≤ (θ' - θ) * Real.sqrt n := by
    rw [div_le_iff₀ hd] at hle
    linarith
  have hlogb := logb_le_three_mul_sqrt hn0
  have hstep : C * Real.logb 2 n ≤ C * (3 * Real.sqrt n) :=
    mul_le_mul_of_nonneg_left hlogb hC
  have hsn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
  nlinarith [hstep, h3C, hs, hsn]

/-- **Exponential form.**  Under the same hypotheses, `2^(C log₂ n + θ n) ≤ 2^(θ' n)`; i.e. the
polynomial factor `n^C` produced by a logarithmic surplus is absorbed by any strictly larger
exponential rate beyond the explicit threshold. -/
theorem rpow_log_absorb {C θ θ' : ℝ} (hC : 0 ≤ C) (hθ : θ < θ') {n : ℝ} (hn0 : 0 < n)
    (hn : (3 * C / (θ' - θ)) ^ 2 ≤ n) :
    (2 : ℝ) ^ (C * Real.logb 2 n + θ * n) ≤ (2 : ℝ) ^ (θ' * n) :=
  Real.rpow_le_rpow_of_exponent_le one_le_two (log_absorb hC hθ hn0 hn)

end LogAbsorb
end EOC
