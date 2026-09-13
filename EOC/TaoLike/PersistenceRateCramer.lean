import EOC.TaoLike.PersistenceModel
import Mathlib.Analysis.MeanInequalities

/-!
# The persistence rate `I0` is the Geom(2) Cramér rate

**Consolidation theorem (Round 3 of the hypercuboid-transfer exploration).**

`EOC.TaoExternal.I0` was originally derived as an ad hoc Chernoff-bound optimum
(`geometric_persistence_upper_bound_bits`). This file proves that `I0`, and more generally its
defining closed form at *any* level `a` in the relevant range, is exactly the base-`2`
Cramér/large-deviation rate function of the `Geom(2)` law:

  `I(a) := sup_{t ∈ (0,2)} [(a - 1) * logb 2 t + logb 2 (2 - t)]`

(the base-`2` Legendre transform of the `Geom(2)` log-moment-generating function, evaluated at
level `a`), i.e. `I(a) = a - a * logb 2 a + (a - 1) * logb 2 (a - 1)` for every `a ∈ (1, 2)`, not
merely at `a = collatzAlpha`.

This is a **reframing/consolidation result**: it does not strengthen any existing Chernoff bound,
and it does not touch the cylinder-restart or realizer machinery at all. It shows that an already-
proved numerical constant is the standard textbook object, unifying two previously separate-
looking derivations. See `explorations/hypercuboid_transfer/ROUND2_REPORT.md` Part XIII for the
by-hand derivation this file formalizes, and `ROUND3_FORMALIZATION_REPORT.md` for its status.

No claim in this file is about any real Collatz orbit, any fixed seed, or `CriticalCrossing`; it
is a fact about the abstract `Geom(2)` probability law only (matching `PersistenceModel.lean`'s
own explicit scope discipline).
-/

namespace EOC
namespace TaoExternal

open Real

/-- **General-level closed form**, matching `I0`'s defining expression but at an arbitrary level
`a` rather than only at `collatzAlpha`. This is the same formula, generalized; `I0` itself is the
special case `a = collatzAlpha` (see `I0_eq_geom2CramerRate_collatzAlpha` below). -/
noncomputable def geom2CramerRate (a : ℝ) : ℝ :=
  a - a * Real.logb 2 a + (a - 1) * Real.logb 2 (a - 1)

/-- `I0` is literally the `a = collatzAlpha` instance of `geom2CramerRate` — the two formulas
are definitionally the same expression. -/
theorem I0_eq_geom2CramerRate_collatzAlpha : I0 = geom2CramerRate collatzAlpha := rfl

/-- The Legendre-transform integrand, in base-`2` log units: `(a-1) logb2 t + logb2 (2-t)`. This
is `logb 2` of the tilted-weight ratio at parameter `t = 2 * exp(lam)` (`lam` the exponential
tilt), i.e. the quantity being optimized over `t` in the Cramér/Legendre-transform picture. -/
noncomputable def geom2LegendreIntegrand (a t : ℝ) : ℝ :=
  (a - 1) * Real.logb 2 t + Real.logb 2 (2 - t)

/-- The critical point `t* = 2(a-1)/a` (matching `2 * Real.exp lambdaStar` at `a = collatzAlpha`,
up to the change of variables `t = 2 e^{lam}`). -/
noncomputable def tStar (a : ℝ) : ℝ := 2 * (a - 1) / a

theorem tStar_pos {a : ℝ} (ha : 1 < a) : 0 < tStar a := by
  unfold tStar
  have ha0 : 0 < a := by linarith
  positivity

theorem tStar_lt_two {a : ℝ} (ha1 : 1 < a) (ha2 : a < 2) : tStar a < 2 := by
  have ha0 : 0 < a := by linarith
  have hsub : (2:ℝ) - tStar a = 2 / a := by unfold tStar; field_simp [ha0.ne'] <;> ring
  have hpos : (0:ℝ) < 2 / a := by positivity
  linarith

/-- **Upper bound half of the Legendre transform**: the integrand is bounded above by
`geom2CramerRate a` at *every* `t ∈ (0,2)`, for every level `a ∈ (1,2)`. Proved via the two-point
weighted AM-GM inequality (`Real.geom_mean_le_arith_mean2_weighted`), with weights
`w₁ = (a-1)/a`, `w₂ = 1/a` and points `p₁ = t/w₁`, `p₂ = (2-t)/w₂`. -/
theorem geom2LegendreIntegrand_le (a t : ℝ) (ha1 : 1 < a) (ha2 : a < 2)
    (ht0 : 0 < t) (ht2 : t < 2) :
    geom2LegendreIntegrand a t ≤ geom2CramerRate a := by
  have ha0 : 0 < a := by linarith
  have ham1 : 0 < a - 1 := by linarith
  have h2t : 0 < 2 - t := by linarith
  have hw1 : (0:ℝ) ≤ (a - 1) / a := by positivity
  have hw2 : (0:ℝ) ≤ 1 / a := by positivity
  have hwsum : (a - 1) / a + 1 / a = 1 := by
    field_simp [ha0.ne'] <;> ring
  have hp1 : (0:ℝ) ≤ t / ((a - 1) / a) := by positivity
  have hp2 : (0:ℝ) ≤ (2 - t) / (1 / a) := by positivity
  have hamgm := Real.geom_mean_le_arith_mean2_weighted hw1 hw2 hp1 hp2 hwsum
  have hsum_eq : (a - 1) / a * (t / ((a - 1) / a)) + 1 / a * ((2 - t) / (1 / a)) = 2 := by
    field_simp [ha0.ne', ham1.ne'] <;> ring
  rw [hsum_eq] at hamgm
  -- hamgm : (t / ((a-1)/a)) ^ ((a-1)/a) * ((2-t) / (1/a)) ^ (1/a) ≤ 2
  have hp1pos : 0 < t / ((a - 1) / a) := by positivity
  have hp2pos : 0 < (2 - t) / (1 / a) := by positivity
  have hprodpos : 0 < (t / ((a - 1) / a)) ^ ((a - 1) / a) * ((2 - t) / (1 / a)) ^ (1 / a) := by
    positivity
  have hlogb_mono :
      Real.logb 2 ((t / ((a - 1) / a)) ^ ((a - 1) / a) * ((2 - t) / (1 / a)) ^ (1 / a))
        ≤ Real.logb 2 2 :=
    Real.logb_le_logb_of_le (by norm_num) hprodpos hamgm
  rw [Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2)] at hlogb_mono
  rw [Real.logb_mul (by positivity) (by positivity),
      Real.logb_rpow_eq_mul_logb_of_pos hp1pos,
      Real.logb_rpow_eq_mul_logb_of_pos hp2pos] at hlogb_mono
  -- hlogb_mono :
  --   (a-1)/a * logb 2 (t / ((a-1)/a)) + 1/a * logb 2 ((2-t) / (1/a)) ≤ 1
  rw [Real.logb_div ht0.ne' (by positivity), Real.logb_div h2t.ne' (by positivity)] at hlogb_mono
  have hw1log : Real.logb 2 ((a - 1) / a) = Real.logb 2 (a - 1) - Real.logb 2 a := by
    rw [Real.logb_div ham1.ne' ha0.ne']
  have hw2log : Real.logb 2 (1 / a) = - Real.logb 2 a := by
    rw [one_div, Real.logb_inv]
  rw [hw1log, hw2log] at hlogb_mono
  -- hlogb_mono :
  --   (a-1)/a * (logb2 t - (logb2(a-1) - logb2 a)) + 1/a * (logb2(2-t) - (-logb2 a)) ≤ 1
  have hmul : a * ((a - 1) / a * (Real.logb 2 t - (Real.logb 2 (a - 1) - Real.logb 2 a))
      + 1 / a * (Real.logb 2 (2 - t) - (-Real.logb 2 a))) ≤ a * 1 :=
    mul_le_mul_of_nonneg_left hlogb_mono ha0.le
  have hexpand : a * ((a - 1) / a * (Real.logb 2 t - (Real.logb 2 (a - 1) - Real.logb 2 a))
      + 1 / a * (Real.logb 2 (2 - t) - (-Real.logb 2 a)))
      = (a - 1) * Real.logb 2 t - (a - 1) * (Real.logb 2 (a - 1) - Real.logb 2 a)
        + (Real.logb 2 (2 - t) + Real.logb 2 a) := by
    field_simp [ha0.ne'] <;> ring
  rw [hexpand] at hmul
  unfold geom2LegendreIntegrand geom2CramerRate
  nlinarith [hmul]

/-- **The bound is attained exactly at `t = tStar a`.** Together with the previous theorem this
shows `geom2CramerRate a` is exactly the maximum (hence supremum) of the Legendre-transform
integrand over `t ∈ (0,2)`. -/
theorem geom2LegendreIntegrand_tStar_eq (a : ℝ) (ha1 : 1 < a) (ha2 : a < 2) :
    geom2LegendreIntegrand a (tStar a) = geom2CramerRate a := by
  have ha0 : 0 < a := by linarith
  have ham1 : (0:ℝ) < a - 1 := by linarith
  have h2sub : (2:ℝ) - tStar a = 2 / a := by
    unfold tStar; field_simp [ha0.ne'] <;> ring
  have hlog_tstar : Real.logb 2 (tStar a) = 1 + Real.logb 2 (a - 1) - Real.logb 2 a := by
    unfold tStar
    rw [show (2:ℝ) * (a - 1) / a = 2 * ((a - 1) / a) by ring,
        Real.logb_mul (by norm_num) (by positivity),
        Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2),
        Real.logb_div ham1.ne' ha0.ne']
    ring
  have hlog_2sub : Real.logb 2 (2 - tStar a) = 1 - Real.logb 2 a := by
    rw [h2sub, Real.logb_div (by norm_num) ha0.ne',
        Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2)]
  unfold geom2LegendreIntegrand geom2CramerRate
  rw [hlog_tstar, hlog_2sub]
  ring

/-- **`geom2CramerRate a` is the exact supremum** of the Legendre-transform integrand over
`t ∈ (0,2)`, for every level `a ∈ (1,2)`: it is an upper bound (previous theorem) that is also
attained (this theorem), hence `IsGreatest`. -/
theorem geom2CramerRate_isGreatest (a : ℝ) (ha1 : 1 < a) (ha2 : a < 2) :
    IsGreatest {v : ℝ | ∃ t ∈ Set.Ioo (0:ℝ) 2, v = geom2LegendreIntegrand a t}
      (geom2CramerRate a) := by
  constructor
  · exact ⟨tStar a, ⟨tStar_pos ha1, tStar_lt_two ha1 ha2⟩,
      (geom2LegendreIntegrand_tStar_eq a ha1 ha2).symm⟩
  · rintro v ⟨t, ⟨ht0, ht2⟩, rfl⟩
    exact geom2LegendreIntegrand_le a t ha1 ha2 ht0 ht2

/-- **Headline identity**: `geom2CramerRate a` equals the supremum (`sSup`) of the Legendre-
transform integrand over `t ∈ (0,2)`, i.e. it *is* the Geom(2) Cramér/large-deviation rate at
level `a`, for every `a ∈ (1,2)`. -/
theorem geom2CramerRate_eq_sSup (a : ℝ) (ha1 : 1 < a) (ha2 : a < 2) :
    geom2CramerRate a
      = sSup {v : ℝ | ∃ t ∈ Set.Ioo (0:ℝ) 2, v = geom2LegendreIntegrand a t} :=
  (geom2CramerRate_isGreatest a ha1 ha2).csSup_eq.symm

/-- **Specialization to `α = log₂3`**: the repository's own persistence rate `I0` is exactly the
Geom(2) Cramér rate at the Collatz level `α`. -/
theorem I0_eq_geom2_cramer_rate :
    I0 = sSup {v : ℝ | ∃ t ∈ Set.Ioo (0:ℝ) 2, v = geom2LegendreIntegrand collatzAlpha t} := by
  rw [I0_eq_geom2CramerRate_collatzAlpha]
  exact geom2CramerRate_eq_sSup collatzAlpha one_lt_collatzAlpha collatzAlpha_lt_two

end TaoExternal
end EOC
