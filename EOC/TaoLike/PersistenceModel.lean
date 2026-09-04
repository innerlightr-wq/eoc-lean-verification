import EOC.TaoLike.TaoInterface
import EOC.Confinement
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Geometric persistence upper bound (Milestone 6)

**EXPONENTIAL-RATE UPPER BOUND.** A Chernoff/exponential-Markov bound for the "persistence"
event — the centered partial sums of an iid `Geom(2)^n` vector staying below a threshold `c`
at every prefix — under the concrete `iidGeom2VectorProb n` law from Milestone 4B.

This is a statement about the abstract iid `Geom(2)^n` probability model only. It is **not**
a theorem about real Collatz trajectories; that transfer is reserved for a later milestone
(`shifted_persistence_transfer`). It proves only an exponential-rate upper bound: the sharp
`n^(-3/2)` polynomial ballot-theorem prefactor is **not** claimed.
-/

namespace EOC
namespace TaoExternal

/-! ## Part 4: `geomPersistenceEvent` and the endpoint-event reduction -/

/-- The partial digit sum `Σ_{i<j} a_i`, real-valued. -/
noncomputable def digitSum (n : ℕ) (a : Fin n → ℕ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < j), (a i : ℝ)

/-- The centered partial sum `Σ_{i<j} (a_i - α)` at prefix length `j`. -/
noncomputable def centeredSum (α : ℝ) (n : ℕ) (a : Fin n → ℕ) (j : ℕ) : ℝ :=
  digitSum n a j - (j : ℝ) * α

/-- The **persistence event**: the centered partial sum stays `≤ c` at every prefix
`1 ≤ j ≤ n`. -/
def geomPersistenceEvent (α c : ℝ) (n : ℕ) : Set (Fin n → ℕ) :=
  {a | ∀ j, 1 ≤ j → j ≤ n → centeredSum α n a j ≤ c}

/-- The endpoint total sum `Σ_i a_i` (all of `Fin n`). -/
noncomputable def totalSum (n : ℕ) (a : Fin n → ℕ) : ℝ := ∑ i : Fin n, (a i : ℝ)

/-- The endpoint centered sum `Σ_i a_i - n·α`. -/
noncomputable def totalCenteredSum (α : ℝ) (n : ℕ) (a : Fin n → ℕ) : ℝ :=
  totalSum n a - (n : ℝ) * α

theorem digitSum_eq_totalSum (n : ℕ) (a : Fin n → ℕ) : digitSum n a n = totalSum n a := by
  unfold digitSum totalSum
  congr 1
  exact Finset.filter_true_of_mem (fun i _ => i.isLt)

theorem centeredSum_eq_totalCenteredSum (α : ℝ) (n : ℕ) (a : Fin n → ℕ) :
    centeredSum α n a n = totalCenteredSum α n a := by
  unfold centeredSum totalCenteredSum
  rw [digitSum_eq_totalSum]

/-- **Endpoint-event reduction.** The persistence event is contained in the (weaker) endpoint
event `{a | totalCenteredSum α n a ≤ c}` — it suffices to Chernoff-bound the latter. -/
theorem geomPersistenceEvent_subset_endpoint (α c : ℝ) (n : ℕ) (hn : 1 ≤ n) (a : Fin n → ℕ)
    (ha : a ∈ geomPersistenceEvent α c n) : totalCenteredSum α n a ≤ c := by
  have h := ha n hn (le_refl n)
  rwa [centeredSum_eq_totalCenteredSum] at h

/-! ## Part 5: generic product-tsum-equals-power lemma

Generalizes `atomWeight_tsum_eq_one`'s induction pattern to an arbitrary nonnegative summable
single-digit weight `w`, rather than rebuilding independence machinery from scratch. -/

theorem genProdWeight_cons {w : ℕ → ℝ} (n k : ℕ) (a : Fin n → ℕ) :
    (∏ i, w ((Fin.cons k a : Fin (n + 1) → ℕ) i)) = w k * ∏ i, w (a i) := by
  rw [Fin.prod_univ_succ]
  simp

set_option maxHeartbeats 1000000 in
-- w is an abstract (uninterpreted) weight function, so unification here is
-- much slower than for the concrete geom2/atomWeight case it generalizes.
theorem genProdWeight_summable {w : ℕ → ℝ} (hw_nonneg : ∀ k, 0 ≤ w k) (hw_summable : Summable w)
    (n : ℕ) : Summable (fun a : Fin n → ℕ => ∏ i, w (a i)) := by
  induction n with
  | zero => exact Summable.of_finite
  | succ n ih =>
      have hmul : Summable (fun p : ℕ × (Fin n → ℕ) => w p.1 * ∏ i, w (p.2 i)) :=
        Summable.mul_of_nonneg hw_summable ih
          hw_nonneg (fun a => Finset.prod_nonneg (fun i _ => hw_nonneg _))
      have heq : (fun p : ℕ × (Fin n → ℕ) => w p.1 * ∏ i, w (p.2 i))
          = (fun a : Fin (n + 1) → ℕ => ∏ i, w (a i))
            ∘ (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)) := by
        funext p
        simp only [Function.comp_apply]
        rw [← genProdWeight_cons n p.1 p.2]
        congr 1
      rw [heq] at hmul
      exact (Equiv.summable_iff (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ))).mp hmul

set_option maxHeartbeats 1000000 in
-- same reason as genProdWeight_summable above: w is abstract.
theorem genProdWeight_tsum_succ {w : ℕ → ℝ} (hw_nonneg : ∀ k, 0 ≤ w k) (hw_summable : Summable w)
    (n : ℕ) :
    ∑' a : Fin (n + 1) → ℕ, ∏ i, w (a i)
      = (∑' k, w k) * ∑' a : Fin n → ℕ, ∏ i, w (a i) := by
  rw [← Equiv.tsum_eq (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ))]
  have heq : ∀ p : ℕ × (Fin n → ℕ),
      ∏ i, w ((Fin.consEquiv (fun _ : Fin (n + 1) => ℕ) p) i) = w p.1 * ∏ i, w (p.2 i) := by
    intro p
    rw [← genProdWeight_cons n p.1 p.2]
    congr 1
  simp_rw [heq]
  exact (Summable.tsum_mul_tsum hw_summable (genProdWeight_summable hw_nonneg hw_summable n)
    (Summable.mul_of_nonneg hw_summable (genProdWeight_summable hw_nonneg hw_summable n) hw_nonneg
      (fun a => Finset.prod_nonneg (fun i _ => hw_nonneg _)))).symm

/-- **Generic product-tsum-equals-power** (generalizing `atomWeight_tsum_eq_one`): for any
nonnegative summable single-digit weight `w`, the length-`n` iid product law normalizes to
`(Σ' w)^n`. -/
theorem genProdWeight_tsum_eq_pow {w : ℕ → ℝ} (hw_nonneg : ∀ k, 0 ≤ w k)
    (hw_summable : Summable w) (n : ℕ) :
    ∑' a : Fin n → ℕ, ∏ i, w (a i) = (∑' k, w k) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [genProdWeight_tsum_succ hw_nonneg hw_summable, ih, pow_succ']

/-! ## Part 6: the tilted digit weight and its moment generating function `Mfun` -/

/-- The exponentially-tilted single-digit weight `geom2(k) · exp(-lam(k-α))`. -/
noncomputable def tiltedDigitWeight (α lam : ℝ) (k : ℕ) : ℝ :=
  geom2 k * Real.exp (-lam * ((k : ℝ) - α))

/-- The moment generating function value `M(lam) = exp(lamα) / (2·exp(lam) - 1)`. -/
noncomputable def Mfun (α lam : ℝ) : ℝ := Real.exp (lam * α) / (2 * Real.exp lam - 1)

theorem tiltedDigitWeight_nonneg (α lam : ℝ) (k : ℕ) : 0 ≤ tiltedDigitWeight α lam k :=
  mul_nonneg (geom2_nonneg k) (Real.exp_pos _).le

theorem tiltedDigitWeight_le_geom2_mul_const (α lam : ℝ) (hlam : 0 ≤ lam) (k : ℕ) :
    tiltedDigitWeight α lam k ≤ Real.exp (lam * α) * geom2 k := by
  unfold tiltedDigitWeight
  have hexp_le : Real.exp (-lam * ((k : ℝ) - α)) ≤ Real.exp (lam * α) * Real.exp (-lam * k) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  calc geom2 k * Real.exp (-lam * ((k : ℝ) - α))
      ≤ geom2 k * (Real.exp (lam * α) * Real.exp (-lam * k)) :=
        mul_le_mul_of_nonneg_left hexp_le (geom2_nonneg k)
    _ ≤ geom2 k * (Real.exp (lam * α) * 1) := by
        apply mul_le_mul_of_nonneg_left _ (geom2_nonneg k)
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        rw [Real.exp_le_one_iff]
        nlinarith [Nat.cast_nonneg (α := ℝ) k]
    _ = Real.exp (lam * α) * geom2 k := by ring

theorem tiltedDigitWeight_summable (α lam : ℝ) (hlam : 0 ≤ lam) :
    Summable (tiltedDigitWeight α lam) := by
  apply Summable.of_nonneg_of_le (tiltedDigitWeight_nonneg α lam)
    (tiltedDigitWeight_le_geom2_mul_const α lam hlam)
  exact geom2_summable.mul_left _

theorem tiltedDigitWeight_tsum (α lam : ℝ) (hlam : 0 < lam) :
    ∑' k, tiltedDigitWeight α lam k = Mfun α lam := by
  unfold Mfun
  have hstep : ∀ k : ℕ, tiltedDigitWeight α lam k
      = Real.exp (lam * α) * (geom2 k * Real.exp (-lam * (k : ℝ))) := by
    intro k
    unfold tiltedDigitWeight
    rw [show (-lam * ((k : ℝ) - α)) = lam * α + (-lam * (k : ℝ)) by ring, Real.exp_add]
    ring
  rw [tsum_congr hstep, tsum_mul_left]
  have hr_lt : Real.exp (-lam) / 2 < 1 := by
    have : Real.exp (-lam) < 1 := by
      rw [Real.exp_lt_one_iff]; linarith
    linarith
  have hr_nonneg : (0:ℝ) ≤ Real.exp (-lam) / 2 := by positivity
  have hsum0 : Summable (fun n : ℕ => (Real.exp (-lam) / 2 : ℝ) ^ n) :=
    summable_geometric_of_lt_one hr_nonneg hr_lt
  have hgsummable : Summable geom2 := geom2_summable
  have hterm0 : geom2 0 * Real.exp (-lam * ((0:ℕ) : ℝ)) = 0 := by
    rw [geom2_eq_zero]; ring
  have hsplit : Summable (fun k : ℕ => geom2 k * Real.exp (-lam * (k : ℝ))) := by
    apply Summable.of_nonneg_of_le
      (fun k => mul_nonneg (geom2_nonneg k) (Real.exp_pos _).le)
      (fun k => ?_) hgsummable
    calc geom2 k * Real.exp (-lam * (k : ℝ)) ≤ geom2 k * 1 := by
          apply mul_le_mul_of_nonneg_left _ (geom2_nonneg k)
          rw [Real.exp_le_one_iff]
          nlinarith [Nat.cast_nonneg (α := ℝ) k]
      _ = geom2 k := by ring
  rw [hsplit.tsum_eq_zero_add, hterm0, zero_add]
  have hterm1 : ∀ n : ℕ,
      geom2 (n + 1) * Real.exp (-lam * (((n : ℕ) + 1 : ℕ) : ℝ))
        = (Real.exp (-lam) / 2) * (Real.exp (-lam) / 2) ^ n := by
    intro n
    rw [geom2_eq_of_pos (by omega : 1 ≤ n + 1),
      mul_comm (-lam) (((n : ℕ) + 1 : ℕ) : ℝ), Real.exp_nat_mul, ← mul_pow,
      show (1 / 2 : ℝ) * Real.exp (-lam) = Real.exp (-lam) / 2 by ring, pow_succ]
    ring
  rw [tsum_congr hterm1, tsum_mul_left, tsum_geometric_of_lt_one hr_nonneg hr_lt]
  have hexp_pos : (0:ℝ) < Real.exp lam := Real.exp_pos lam
  have hden_pos : (0:ℝ) < 2 * Real.exp lam - 1 := by
    have h1 : (1:ℝ) < Real.exp lam := by
      rw [show (1:ℝ) = Real.exp 0 by simp]
      exact Real.exp_lt_exp.mpr hlam
    linarith
  rw [Real.exp_neg]
  field_simp

/-! ## Part 7: the pointwise Chernoff inequality and the generic Chernoff bound -/

theorem tiltedAtomWeight_eq (α lam : ℝ) (n : ℕ) (a : Fin n → ℕ) :
    (∏ i, tiltedDigitWeight α lam (a i))
      = atomWeight n a * Real.exp (-lam * totalCenteredSum α n a) := by
  unfold tiltedDigitWeight atomWeight totalCenteredSum totalSum
  rw [Finset.prod_mul_distrib, ← Real.exp_sum]
  congr 2
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  ring

theorem geom_persistence_pointwise_chernoff (α c lam : ℝ) (hlam : 0 < lam) (n : ℕ) (hn : 1 ≤ n)
    (a : Fin n → ℕ) :
    Set.indicator (geomPersistenceEvent α c n) (atomWeight n) a
      ≤ Real.exp (lam * c) * ∏ i, tiltedDigitWeight α lam (a i) := by
  rw [tiltedAtomWeight_eq]
  by_cases ha : a ∈ geomPersistenceEvent α c n
  · have hend : totalCenteredSum α n a ≤ c := geomPersistenceEvent_subset_endpoint α c n hn a ha
    have hexp_ge : (1:ℝ) ≤ Real.exp (lam * c) * Real.exp (-lam * totalCenteredSum α n a) := by
      rw [← Real.exp_add]
      have h0le : (0:ℝ) ≤ lam * c + -lam * totalCenteredSum α n a := by nlinarith
      calc (1:ℝ) = Real.exp 0 := Real.exp_zero.symm
        _ ≤ Real.exp (lam * c + -lam * totalCenteredSum α n a) := Real.exp_le_exp.mpr h0le
    simp only [Set.indicator, ha, ite_true]
    nlinarith [atomWeight_nonneg n a, hexp_ge]
  · simp only [Set.indicator, ha, ite_false]
    exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (atomWeight_nonneg n a) (Real.exp_pos _).le)

/-- **Concrete specialized helper** (fixes `w := tiltedDigitWeight α lam` once, rather than
letting `iid_geom_chernoff_bound` repeatedly instantiate the fully generic
`genProdWeight_summable` machinery inline — this is what keeps that theorem's elaboration
cost practical). -/
theorem tiltedVectorWeight_summable (α lam : ℝ) (hlam : 0 ≤ lam) (n : ℕ) :
    Summable (fun a : Fin n → ℕ => ∏ i, tiltedDigitWeight α lam (a i)) :=
  genProdWeight_summable (tiltedDigitWeight_nonneg α lam) (tiltedDigitWeight_summable α lam hlam) n

/-- **Concrete specialized helper**, companion to `tiltedVectorWeight_summable`. -/
theorem tiltedVectorWeight_tsum (α lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    ∑' a : Fin n → ℕ, ∏ i, tiltedDigitWeight α lam (a i) = (Mfun α lam) ^ n := by
  rw [genProdWeight_tsum_eq_pow (tiltedDigitWeight_nonneg α lam)
      (tiltedDigitWeight_summable α lam hlam.le) n, tiltedDigitWeight_tsum α lam hlam]

/-- **Generic-λ Chernoff bound.** The persistence event's probability under `iidGeom2VectorProb`
is bounded by `exp(λc)·M(λ)^n` for every `λ > 0`.

Proved via `tsum_nonneg`/`Summable.tsum_sub` rather than `Summable.tsum_mono` inside a `calc`:
the latter (which mixes a `≤`-step through a generic `Summable.tsum_mono` invocation with
subsequent `=`-steps under `Trans` resolution) was measured to blow up elaboration time on
this abstract `Fin n → ℕ`-indexed goal — plausibly the `SummationFilter`/`[L.NeBot]` instance
search this Mathlib's generalized `Summable.tsum_mono` carries, compounded across the several
pending metavariables from neighboring `have`s. The `tsum_nonneg`/`Summable.tsum_sub`/`linarith`
route proves the identical inequality without ever invoking that lemma. -/
theorem iid_geom_chernoff_bound (α c lam : ℝ) (hlam : 0 < lam) (n : ℕ) (hn : 1 ≤ n) :
    iidGeom2VectorProb n (geomPersistenceEvent α c n) ≤ Real.exp (lam * c) * (Mfun α lam) ^ n := by
  unfold iidGeom2VectorProb genEventProb
  have hsummable_rhs : Summable (fun a : Fin n → ℕ =>
      Real.exp (lam * c) * ∏ i, tiltedDigitWeight α lam (a i)) :=
    (tiltedVectorWeight_summable α lam hlam.le n).mul_left _
  have hbound : ∀ a : Fin n → ℕ, Set.indicator (geomPersistenceEvent α c n) (atomWeight n) a
      ≤ Real.exp (lam * c) * ∏ i, tiltedDigitWeight α lam (a i) :=
    fun a => geom_persistence_pointwise_chernoff α c lam hlam n hn a
  have hsummable_lhs : Summable (fun a : Fin n → ℕ =>
      Set.indicator (geomPersistenceEvent α c n) (atomWeight n) a) :=
    Summable.of_nonneg_of_le (fun a => Set.indicator_nonneg (fun x _ => atomWeight_nonneg n x) a)
      hbound hsummable_rhs
  have hle : ∑' a : Fin n → ℕ, Set.indicator (geomPersistenceEvent α c n) (atomWeight n) a
      ≤ ∑' a : Fin n → ℕ, Real.exp (lam * c) * ∏ i, tiltedDigitWeight α lam (a i) := by
    have hsub_nonneg : ∀ a : Fin n → ℕ, 0 ≤
        Real.exp (lam * c) * (∏ i, tiltedDigitWeight α lam (a i))
          - Set.indicator (geomPersistenceEvent α c n) (atomWeight n) a := fun a => by
      linarith [hbound a]
    have hsub_summable : Summable (fun a : Fin n → ℕ =>
        Real.exp (lam * c) * (∏ i, tiltedDigitWeight α lam (a i))
          - Set.indicator (geomPersistenceEvent α c n) (atomWeight n) a) :=
      hsummable_rhs.sub hsummable_lhs
    have h0le : (0:ℝ) ≤ ∑' a : Fin n → ℕ,
        (Real.exp (lam * c) * (∏ i, tiltedDigitWeight α lam (a i))
          - Set.indicator (geomPersistenceEvent α c n) (atomWeight n) a) := tsum_nonneg hsub_nonneg
    rwa [Summable.tsum_sub hsummable_rhs hsummable_lhs, sub_nonneg] at h0le
  have heq : ∑' a : Fin n → ℕ, Real.exp (lam * c) * ∏ i, tiltedDigitWeight α lam (a i)
      = Real.exp (lam * c) * (Mfun α lam) ^ n := by
    rw [tsum_mul_left, tiltedVectorWeight_tsum α lam hlam n]
  linarith [hle, heq]

/-! ## Part 8: `collatzAlpha` and its order facts

`EOC.Confinement` already defines `alpha := Real.logb 2 3` with `one_lt_alpha : 1 < alpha`
(used throughout the repo's drift/confinement arguments, e.g. `EOC.BoundedDrift`,
`EOC.Periodic`). No `alpha < 2` or `4/3 < alpha` fact exists anywhere in the repo (checked via
grep). `collatzAlpha` below is a **thin alias for that existing constant** — not a competing
definition — so this milestone's Layer B statements can use the name the brief specifies. -/

noncomputable def collatzAlpha : ℝ := alpha

theorem collatzAlpha_eq_log_div_log : collatzAlpha = Real.log 3 / Real.log 2 := by
  rfl

theorem one_lt_collatzAlpha : 1 < collatzAlpha := one_lt_alpha

/-- `3 < 4 = 2^2` gives `log 3 < 2 log 2`, i.e. `collatzAlpha < 2`. -/
theorem collatzAlpha_lt_two : collatzAlpha < 2 := by
  rw [collatzAlpha_eq_log_div_log, div_lt_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))]
  have h4 : Real.log (4:ℝ) = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 ^ (2:ℕ) by norm_num, Real.log_pow]; push_cast; ring
  calc Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
    _ = 2 * Real.log 2 := h4

/-- `2^4 = 16 < 27 = 3^3` gives `4 log 2 < 3 log 3`, i.e. `4/3 < collatzAlpha`. Used to prove
`rateNats > 0` via the factorization `-3(α-2)²(α-4/3) ≤ 0`. -/
theorem four_thirds_lt_collatzAlpha : (4:ℝ) / 3 < collatzAlpha := by
  rw [collatzAlpha_eq_log_div_log, lt_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))]
  have h27 : Real.log (27:ℝ) = 3 * Real.log 3 := by
    rw [show (27:ℝ) = 3 ^ (3:ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have h16 : Real.log (16:ℝ) = 4 * Real.log 2 := by
    rw [show (16:ℝ) = 2 ^ (4:ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have hlt : Real.log (16:ℝ) < Real.log (27:ℝ) := Real.log_lt_log (by norm_num) (by norm_num)
  nlinarith [hlt, h27, h16]

theorem collatzAlpha_sub_one_pos : 0 < collatzAlpha - 1 := by linarith [one_lt_collatzAlpha]

/-! ## Part 9: the optimal tilt `lambdaStar` -/

theorem collatzAlpha_div_pos : 0 < collatzAlpha / (2 * (collatzAlpha - 1)) :=
  div_pos (by linarith [one_lt_collatzAlpha]) (by linarith [collatzAlpha_sub_one_pos])

/-- `α / (2(α-1)) > 1 ⟺ α > 2(α-1) ⟺ 2 > α`, i.e. this is exactly `collatzAlpha_lt_two`. -/
theorem collatzAlpha_div_gt_one : 1 < collatzAlpha / (2 * (collatzAlpha - 1)) := by
  rw [lt_div_iff₀ (by linarith [collatzAlpha_sub_one_pos] : (0:ℝ) < 2 * (collatzAlpha - 1))]
  nlinarith [collatzAlpha_lt_two]

noncomputable def lambdaStar : ℝ := Real.log (collatzAlpha / (2 * (collatzAlpha - 1)))

theorem lambdaStar_pos : 0 < lambdaStar :=
  Real.log_pos collatzAlpha_div_gt_one

theorem exp_lambdaStar : Real.exp lambdaStar = collatzAlpha / (2 * (collatzAlpha - 1)) :=
  Real.exp_log collatzAlpha_div_pos

/-! ## Part 10: `rateNats` and its positivity -/

theorem two_exp_lambdaStar_sub_one_pos : 0 < 2 * Real.exp lambdaStar - 1 := by
  have h1 : (1:ℝ) < Real.exp lambdaStar := by
    rw [show (1:ℝ) = Real.exp 0 by simp]
    exact Real.exp_lt_exp.mpr lambdaStar_pos
  linarith

theorem Mfun_collatzAlpha_lambdaStar_pos : 0 < Mfun collatzAlpha lambdaStar := by
  unfold Mfun
  exact div_pos (Real.exp_pos _) two_exp_lambdaStar_sub_one_pos

/-- **Key positivity step.** At the optimal tilt, `M(λ*) < 1`. Proved via strict convexity of
`exp` (the exponent `collatzAlpha * lambdaStar` is the convex combination
`(collatzAlpha/2) • (2·lambdaStar) + (1 - collatzAlpha/2) • 0`, since `0 < collatzAlpha < 2`),
which reduces the claim to the purely algebraic fact `3(α-2)²(α-4/3) ≥ 0` — true since
`α > 4/3` (`four_thirds_lt_collatzAlpha`). -/
theorem Mfun_collatzAlpha_lambdaStar_lt_one : Mfun collatzAlpha lambdaStar < 1 := by
  unfold Mfun
  rw [div_lt_one two_exp_lambdaStar_sub_one_pos]
  have hexp2 : Real.exp (2 * lambdaStar) = (collatzAlpha / (2 * (collatzAlpha - 1))) ^ 2 := by
    rw [two_mul, Real.exp_add, exp_lambdaStar]; ring
  have hconv := strictConvexOn_exp.2 (Set.mem_univ (2 * lambdaStar)) (Set.mem_univ (0:ℝ))
      (ne_of_gt (by linarith [lambdaStar_pos] : (0:ℝ) < 2 * lambdaStar))
      (show (0:ℝ) < collatzAlpha / 2 by linarith [one_lt_collatzAlpha])
      (show (0:ℝ) < 1 - collatzAlpha / 2 by linarith [collatzAlpha_lt_two])
      (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at hconv
  rw [show collatzAlpha / 2 * (2 * lambdaStar) = lambdaStar * collatzAlpha by ring, hexp2] at hconv
  have halg : collatzAlpha / 2 * (collatzAlpha / (2 * (collatzAlpha - 1))) ^ 2
        + (1 - collatzAlpha / 2)
      ≤ 2 * Real.exp lambdaStar - 1 := by
    rw [exp_lambdaStar, ← sub_nonneg]
    have hd0 : (collatzAlpha - 1) ≠ 0 := ne_of_gt collatzAlpha_sub_one_pos
    have expand : 2 * (collatzAlpha / (2 * (collatzAlpha - 1))) - 1
          - (collatzAlpha / 2 * (collatzAlpha / (2 * (collatzAlpha - 1))) ^ 2
             + (1 - collatzAlpha / 2))
        = 3 * (collatzAlpha - 2) ^ 2 * (collatzAlpha - 4 / 3)
            / (2 * (2 * (collatzAlpha - 1)) ^ 2) := by
      field_simp
      ring
    rw [expand]
    apply div_nonneg _ (by positivity)
    apply mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    linarith [four_thirds_lt_collatzAlpha]
  linarith [hconv, halg]

noncomputable def rateNats : ℝ := -Real.log (Mfun collatzAlpha lambdaStar)

theorem rateNats_pos : 0 < rateNats := by
  unfold rateNats
  have := Real.log_neg Mfun_collatzAlpha_lambdaStar_pos Mfun_collatzAlpha_lambdaStar_lt_one
  linarith

theorem Mfun_collatzAlpha_lambdaStar_eq_exp_neg_rateNats :
    Mfun collatzAlpha lambdaStar = Real.exp (-rateNats) := by
  unfold rateNats
  rw [neg_neg, Real.exp_log Mfun_collatzAlpha_lambdaStar_pos]

/-! ## Part 11: the specialized exponential-rate persistence upper bound

**EXPONENTIAL-RATE UPPER BOUND** — not the sharp `n^(-3/2)` ballot-theorem prefactor, no
lower bound, no matching asymptotics. This is a statement about the abstract iid `Geom(2)^n`
law only, not (yet) about real Collatz trajectories. -/

/-- Specializes `iid_geom_chernoff_bound` at the optimal tilt `lambdaStar`, exposing the exact
positive natural-log rate `rateNats`. -/
theorem geometric_persistence_upper_bound (c : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    iidGeom2VectorProb n (geomPersistenceEvent collatzAlpha c n)
      ≤ Real.exp (lambdaStar * c) * Real.exp (-(rateNats * (n : ℝ))) := by
  have hbound := iid_geom_chernoff_bound collatzAlpha c lambdaStar lambdaStar_pos n hn
  have hpow : (Mfun collatzAlpha lambdaStar) ^ n = Real.exp (-(rateNats * (n : ℝ))) := by
    rw [Mfun_collatzAlpha_lambdaStar_eq_exp_neg_rateNats, ← Real.exp_nat_mul]
    congr 1
    ring
  rwa [hpow] at hbound

/-! ## Part 12: the bit-rate `I0` and `rateNats = I0 * ln 2`

Uses Mathlib's existing `Real.logb 2` as the binary log — no new `log2` helper is introduced. -/

noncomputable def I0 : ℝ :=
  collatzAlpha - collatzAlpha * Real.logb 2 collatzAlpha
    + (collatzAlpha - 1) * Real.logb 2 (collatzAlpha - 1)

theorem two_exp_lambdaStar_sub_one_eq_inv : 2 * Real.exp lambdaStar - 1 = (collatzAlpha - 1)⁻¹ := by
  have hd0 : (collatzAlpha - 1) ≠ 0 := ne_of_gt collatzAlpha_sub_one_pos
  rw [exp_lambdaStar]
  field_simp
  ring

theorem rateNats_eq_I0_mul_log_two : rateNats = I0 * Real.log 2 := by
  have hd0 : (collatzAlpha - 1) ≠ 0 := ne_of_gt collatzAlpha_sub_one_pos
  have ha0 : collatzAlpha ≠ 0 := ne_of_gt (by linarith [one_lt_collatzAlpha])
  have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  unfold rateNats Mfun
  rw [two_exp_lambdaStar_sub_one_eq_inv,
    Real.log_div (Real.exp_pos _).ne' (inv_ne_zero hd0), Real.log_exp, Real.log_inv]
  unfold lambdaStar
  rw [Real.log_div ha0 (by positivity : (2 * (collatzAlpha - 1)) ≠ 0),
    Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hd0]
  unfold I0
  rw [Real.logb, Real.logb]
  field_simp
  ring

/-! ## Part 13 (optional): bit-rate corollary -/

/-- Same bound as `geometric_persistence_upper_bound`, expressed in bits via `(2:ℝ)^(-I0·n)`
(`Real.rpow`, forced by the real-valued exponent `-(I0 * (n:ℝ))`). -/
theorem geometric_persistence_upper_bound_bits (c : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    iidGeom2VectorProb n (geomPersistenceEvent collatzAlpha c n)
      ≤ Real.exp (lambdaStar * c) * (2:ℝ) ^ (-(I0 * (n : ℝ))) := by
  have hbase := geometric_persistence_upper_bound c n hn
  have heq : Real.exp (-(rateNats * (n : ℝ))) = (2:ℝ) ^ (-(I0 * (n : ℝ))) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2), rateNats_eq_I0_mul_log_two]
    congr 1
    ring
  rwa [heq] at hbase

end TaoExternal
end EOC
