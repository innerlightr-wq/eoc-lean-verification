import EOC.TaoLike.ConditionalMixing
import EOC.TaoLike.PersistenceModel

/-!
# Early/late shift split (Milestone 8)

Repairs the Round 4E/4F gap: transferring a real Collatz prefix law to iid via
`TaoMixingHypothesis` at rate `K.A · 2^(-K.c1·t)` is only useful once `t` is large enough that
this error is polynomially small in the ambient scale `Y`. For small `t` it is not. The
structural repair:

* **EARLY** (`t` small): transfer the *entire* length-`(t+n)` joint valuation vector directly
  via `TaoMixingHypothesis`, no restart needed — `early_shift_persistence_upper_bound`.
* **LATE** (`t` large enough that the prefix Tao error is already useful): split by the
  realized prefix's partial sum into GOOD (small, → Milestone 7 restart transfer) and BAD
  (large, → iid Chernoff tail + prefix Tao transfer) — building blocks only in this file (see
  the epistemic status note at the end for exactly what is and is not established).

**EPISTEMIC STATUS.** Every theorem here that uses Tao's interface takes
`(tao : TaoMixingHypothesis)` as an explicit hypothesis — CONDITIONAL, not a formalization of
Tao's Proposition 1.9 itself. This file does NOT prove the union-over-shifts theorem, does NOT
implement `ε log Y` bookkeeping, Borel–Cantelli, or logarithmic density. It is NOT a pointwise
claim about individual Collatz orbits, and NOT EOC or the Collatz conjecture.
-/

namespace EOC
namespace TaoExternal

open Finset

/-! ## Part 1: the joint shifted persistence event and its iid suffix marginalization -/

/-- The length-`n` suffix (coordinates `t, …, t+n-1`) of a length-`(t+n)` vector. -/
noncomputable def suffixVector (t n : ℕ) (a : Fin (t + n) → ℕ) : Fin n → ℕ :=
  fun i => a (Fin.natAdd t i)

/-- The length-`t` prefix (coordinates `0, …, t-1`) of a length-`(t+n)` vector. -/
noncomputable def prefixVector (t n : ℕ) (a : Fin (t + n) → ℕ) : Fin t → ℕ :=
  fun i => a (Fin.castAdd n i)

/-- The **joint shifted persistence event**: a length-`(t+n)` vector whose suffix (coordinates
`t, …, t+n-1`) satisfies `geomPersistenceEvent collatzAlpha c n`. The prefix coordinates are
unconstrained. -/
def jointShiftedPersistenceEvent (t n : ℕ) (c : ℝ) : Set (Fin (t + n) → ℕ) :=
  suffixVector t n ⁻¹' geomPersistenceEvent collatzAlpha c n

theorem atomWeight_eq_prefix_mul_suffix (t n : ℕ) (a : Fin (t + n) → ℕ) :
    atomWeight (t + n) a = atomWeight t (prefixVector t n a) * atomWeight n (suffixVector t n a) := by
  unfold atomWeight prefixVector suffixVector
  exact Fin.prod_univ_add (fun i => geom2 (a i))

/-- **IID suffix marginalization.** The prefix coordinates, being unconstrained, marginalize
out (their total iid mass is `1`, `atomWeight_tsum_eq_one`), leaving exactly the length-`n`
suffix law. -/
theorem iidGeom2VectorProb_joint_eq (t n : ℕ) (c : ℝ) :
    iidGeom2VectorProb (t + n) (jointShiftedPersistenceEvent t n c)
      = iidGeom2VectorProb n (geomPersistenceEvent collatzAlpha c n) := by
  unfold iidGeom2VectorProb genEventProb jointShiftedPersistenceEvent
  rw [← Equiv.tsum_eq (Fin.appendEquiv t n)]
  have hg_nonneg : ∀ q : Fin n → ℕ,
      0 ≤ Set.indicator (geomPersistenceEvent collatzAlpha c n) (atomWeight n) q :=
    fun q => Set.indicator_nonneg (fun x _ => atomWeight_nonneg n x) q
  have hg_le : ∀ q : Fin n → ℕ,
      Set.indicator (geomPersistenceEvent collatzAlpha c n) (atomWeight n) q ≤ atomWeight n q :=
    fun q => Set.indicator_le_self' (fun x _ => atomWeight_nonneg n x) q
  have hg_summable :
      Summable (Set.indicator (geomPersistenceEvent collatzAlpha c n) (atomWeight n)) :=
    Summable.of_nonneg_of_le hg_nonneg hg_le (atomWeight_summable n)
  have hpt : ∀ pq : (Fin t → ℕ) × (Fin n → ℕ),
      Set.indicator (suffixVector t n ⁻¹' geomPersistenceEvent collatzAlpha c n)
          (atomWeight (t + n)) (Fin.appendEquiv t n pq)
        = atomWeight t pq.1
          * Set.indicator (geomPersistenceEvent collatzAlpha c n) (atomWeight n) pq.2 := by
    intro pq
    have hsuf : suffixVector t n (Fin.appendEquiv t n pq) = pq.2 := by
      funext i
      simp [suffixVector, Fin.appendEquiv]
    have hpre : prefixVector t n (Fin.appendEquiv t n pq) = pq.1 := by
      funext i
      simp [prefixVector, Fin.appendEquiv]
    have hw := atomWeight_eq_prefix_mul_suffix t n (Fin.appendEquiv t n pq)
    rw [hpre, hsuf] at hw
    by_cases hmem : pq.2 ∈ geomPersistenceEvent collatzAlpha c n
    · have hmem' : Fin.appendEquiv t n pq
          ∈ suffixVector t n ⁻¹' geomPersistenceEvent collatzAlpha c n := by
        rw [Set.mem_preimage, hsuf]; exact hmem
      simp only [Set.indicator, hmem, hmem', ite_true]
      rw [hw]
    · have hmem' : Fin.appendEquiv t n pq
          ∉ suffixVector t n ⁻¹' geomPersistenceEvent collatzAlpha c n := by
        rw [Set.mem_preimage, hsuf]; exact hmem
      simp only [Set.indicator, hmem, hmem', ite_false, mul_zero]
  rw [tsum_congr hpt, ← Summable.tsum_mul_tsum (atomWeight_summable t) hg_summable
        (Summable.mul_of_nonneg (atomWeight_summable t) hg_summable (atomWeight_nonneg t)
          hg_nonneg),
    atomWeight_tsum_eq_one t, one_mul]

/-! ## Part 2: the EARLY-shift direct joint-vector transfer

`TaoMixingHypothesis.finite_valuation_mixing` is fully generic over the starting law — it does
NOT require a realized prefix or a restart; it applies to any finite-support
`genEventProb`-shaped law directly. This is exactly what makes the EARLY case free of the
restart machinery: apply it once, at length `t+n`, no Milestone 7 restart theorem invoked. -/

/-- **Fixed-witness EARLY-shift direct transfer.** Same as `early_shift_persistence_upper_bound`,
but `K` (with its defining `TaoMixingProperty hK`) is supplied by the caller instead of derived
internally from `tao` — so a single `Kearly` can be chosen once and reused uniformly across
every shift `t` in a finite early range (Milestone 12), instead of each call to
`tao.finite_valuation_mixing c0 hc0` producing a separately-opaque existential witness. -/
theorem early_shift_persistence_upper_bound_of_constants
    (c0 : ℝ) (K : TaoMixingConstants c0) (hK : TaoMixingProperty c0 K)
    (w : ℕ → ℝ) (hw_nonneg : ∀ m, 0 ≤ w m) (Nwin : ℕ)
    (hw_supp : Function.support w ⊆ ↑(range Nwin))
    (hw_odd : genEventProb w {m : ℕ | ¬ Odd m} = 0)
    (t n : ℕ) (hn : 1 ≤ n) (c : ℝ)
    (Qres : ℕ) (hQrel : (Qres : ℝ) ≥ (2 + c0) * ((t + n : ℕ) : ℝ)) :
    taoL1TV (pushforward (genEventProb w) (fun m => (m : ZMod (2 ^ Qres)))) (unifOddResidues Qres)
        ≤ K.Cres * (2 : ℝ) ^ (-(Qres : ℝ)) →
      pushforward (genEventProb w) (fun m => valuationVector m (t + n))
          (jointShiftedPersistenceEvent t n c)
        ≤ Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n : ℝ)))
          + K.A * (2 : ℝ) ^ (-(K.c1 * ((t + n : ℕ) : ℝ))) := by
  intro hres
  have htv := hK (t + n) Qres (genEventProb w) (by omega) hQrel hw_odd hres
  set F : ℕ → (Fin (t + n) → ℕ) := fun m => valuationVector m (t + n) with hF_def
  have hw'_nonneg : ∀ v : Fin (t + n) → ℕ, 0 ≤ ∑ j ∈ range Nwin, if F j = v then w j else 0 := by
    intro v
    apply Finset.sum_nonneg
    intro j _
    split_ifs
    · exact hw_nonneg j
    · exact le_refl 0
  have hw'_summable : Summable (fun v : Fin (t + n) → ℕ =>
      ∑ j ∈ range Nwin, if F j = v then w j else 0) := by
    apply summable_of_hasFiniteSupport
    apply Set.Finite.subset (Finset.finite_toSet ((range Nwin).image F))
    intro v hv
    by_contra hvni
    apply hv
    apply Finset.sum_eq_zero
    intro j hj
    rw [if_neg]
    intro hveq
    apply hvni
    exact Finset.mem_image.mpr ⟨j, hj, hveq⟩
  have hbridge := event_discrepancy_le_taoL1TV hw'_nonneg (atomWeight_nonneg (t + n))
    hw'_summable (atomWeight_summable (t + n))
  have hle := event_prob_le_of_discrepancy hbridge (jointShiftedPersistenceEvent t n c)
  have hiid := geometric_persistence_upper_bound_bits c n hn
  calc pushforward (genEventProb w) F (jointShiftedPersistenceEvent t n c)
      = genEventProb (fun v : Fin (t + n) → ℕ => ∑ j ∈ range Nwin, if F j = v then w j else 0)
          (jointShiftedPersistenceEvent t n c) := by
        rw [genEventProb_pushforward_fiber_general Nwin w hw_supp F]
    _ ≤ iidGeom2VectorProb (t + n) (jointShiftedPersistenceEvent t n c)
          + K.A * (2 : ℝ) ^ (-(K.c1 * ((t + n : ℕ) : ℝ))) := by
        unfold iidGeom2VectorProb
        unfold iidGeom2VectorProb at htv
        rw [genEventProb_pushforward_fiber_general Nwin w hw_supp F] at htv
        linarith [hle, htv]
    _ = iidGeom2VectorProb n (geomPersistenceEvent collatzAlpha c n)
          + K.A * (2 : ℝ) ^ (-(K.c1 * ((t + n : ℕ) : ℝ))) := by
        rw [iidGeom2VectorProb_joint_eq]
    _ ≤ Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n : ℝ)))
          + K.A * (2 : ℝ) ^ (-(K.c1 * ((t + n : ℕ) : ℝ))) := by
        linarith [hiid]

/-- **EARLY-shift direct transfer.** For any finite-support (`Function.support w ⊆ range Nwin`),
nonnegative, odd-supported starting weight `w`, transferring the *entire* length-`(t+n)`
joint valuation vector directly bounds the shifted persistence probability by the iid rate
plus a single Tao mixing error at length `t+n` — no restart, no prefix/GOOD-BAD split. -/
theorem early_shift_persistence_upper_bound
    (tao : TaoMixingHypothesis)
    (w : ℕ → ℝ) (hw_nonneg : ∀ m, 0 ≤ w m) (Nwin : ℕ)
    (hw_supp : Function.support w ⊆ ↑(range Nwin))
    (hw_odd : genEventProb w {m : ℕ | ¬ Odd m} = 0)
    (t n : ℕ) (hn : 1 ≤ n) (c : ℝ)
    (c0 : ℝ) (hc0 : 0 < c0) (Qres : ℕ) (hQrel : (Qres : ℝ) ≥ (2 + c0) * ((t + n : ℕ) : ℝ)) :
    ∃ K : TaoMixingConstants c0,
      taoL1TV (pushforward (genEventProb w) (fun m => (m : ZMod (2 ^ Qres)))) (unifOddResidues Qres)
          ≤ K.Cres * (2 : ℝ) ^ (-(Qres : ℝ)) →
        pushforward (genEventProb w) (fun m => valuationVector m (t + n))
            (jointShiftedPersistenceEvent t n c)
          ≤ Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n : ℝ)))
            + K.A * (2 : ℝ) ^ (-(K.c1 * ((t + n : ℕ) : ℝ))) := by
  obtain ⟨K, hK⟩ := tao.finite_valuation_mixing c0 hc0
  exact ⟨K, early_shift_persistence_upper_bound_of_constants c0 K hK w hw_nonneg Nwin hw_supp
    hw_odd t n hn c Qres hQrel⟩

/-! ## Part 3: the iid Geom(2) sum upper-tail Chernoff bound (BAD-prefix ingredient)

Not the persistence theorem — a separate, simpler tail bound for `S_t = Σ_{i<t} a_i` under
`iidGeom2VectorProb t`. Only exponential decay in `t` is needed here, not a sharp rate. -/

/-- The real-valued sum of a length-`t` vector. -/
noncomputable def vecRealSum (t : ℕ) (a : Fin t → ℕ) : ℝ := ∑ i : Fin t, (a i : ℝ)

/-- The upper-tail event `{S_t ≥ s}`. -/
def sumAtLeastEvent (t : ℕ) (s : ℝ) : Set (Fin t → ℕ) := {a | s ≤ vecRealSum t a}

/-- The upper-tail moment generating function `E[e^(θG)] = e^θ/(2-e^θ)` for `G ~ Geom(2)`,
valid for `0 < θ < log 2`. -/
noncomputable def geomUpperMgf (theta : ℝ) : ℝ := Real.exp theta / (2 - Real.exp theta)

/-- The exponentially-tilted single-digit weight for the upper tail: `geom2(k)·exp(θk)`. -/
noncomputable def tiltedUpperWeight (theta : ℝ) (k : ℕ) : ℝ := geom2 k * Real.exp (theta * (k : ℝ))

theorem tiltedUpperWeight_nonneg (theta : ℝ) (k : ℕ) : 0 ≤ tiltedUpperWeight theta k :=
  mul_nonneg (geom2_nonneg k) (Real.exp_pos _).le

theorem tiltedUpperWeight_le (theta : ℝ) (k : ℕ) :
    tiltedUpperWeight theta k ≤ (Real.exp theta / 2) ^ k := by
  unfold tiltedUpperWeight
  have h1 : geom2 k * 2 ^ k ≤ 1 := by
    have h1' := geom2_le_half_pow k
    rw [show (1 / 2 : ℝ) ^ k = 1 / 2 ^ k by rw [div_pow, one_pow]] at h1'
    rwa [le_div_iff₀ (by positivity : (0:ℝ) < 2 ^ k)] at h1'
  have h2 : Real.exp (theta * (k : ℝ)) = Real.exp theta ^ k := by
    rw [mul_comm, Real.exp_nat_mul]
  rw [h2, div_pow, le_div_iff₀ (by positivity : (0:ℝ) < 2 ^ k)]
  nlinarith [mul_le_mul_of_nonneg_right h1 (pow_pos (Real.exp_pos theta) k).le]

theorem tiltedUpperWeight_summable (theta : ℝ) (hθ1 : theta < Real.log 2) :
    Summable (tiltedUpperWeight theta) := by
  have hr_lt : Real.exp theta / 2 < 1 := by
    have h1 : Real.exp theta < 2 := by
      calc Real.exp theta < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr hθ1
        _ = 2 := Real.exp_log (by norm_num)
    linarith
  have hr_nonneg : (0:ℝ) ≤ Real.exp theta / 2 := by positivity
  have hsum0 : Summable (fun k : ℕ => (Real.exp theta / 2 : ℝ) ^ k) :=
    summable_geometric_of_lt_one hr_nonneg hr_lt
  exact Summable.of_nonneg_of_le (tiltedUpperWeight_nonneg theta) (tiltedUpperWeight_le theta) hsum0

theorem tiltedUpperWeight_tsum (theta : ℝ) (_hθ0 : 0 < theta) (hθ1 : theta < Real.log 2) :
    ∑' k, tiltedUpperWeight theta k = geomUpperMgf theta := by
  unfold geomUpperMgf
  have hr_lt : Real.exp theta / 2 < 1 := by
    have h1 : Real.exp theta < 2 := by
      calc Real.exp theta < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr hθ1
        _ = 2 := Real.exp_log (by norm_num)
    linarith
  have hr_nonneg : (0:ℝ) ≤ Real.exp theta / 2 := by positivity
  have hsplit : Summable (tiltedUpperWeight theta) := tiltedUpperWeight_summable theta hθ1
  have hterm0 : tiltedUpperWeight theta 0 = 0 := by
    unfold tiltedUpperWeight; rw [geom2_eq_zero]; ring
  rw [hsplit.tsum_eq_zero_add, hterm0, zero_add]
  have hterm1 : ∀ n : ℕ, tiltedUpperWeight theta (n + 1)
      = (Real.exp theta / 2) * (Real.exp theta / 2) ^ n := by
    intro n
    unfold tiltedUpperWeight
    rw [geom2_eq_of_pos (by omega : 1 ≤ n + 1),
      mul_comm theta (((n : ℕ) + 1 : ℕ) : ℝ), Real.exp_nat_mul, ← mul_pow, pow_succ]
    ring
  rw [tsum_congr hterm1, tsum_mul_left, tsum_geometric_of_lt_one hr_nonneg hr_lt]
  have hexp_pos : (0:ℝ) < Real.exp theta := Real.exp_pos theta
  have h2mexp_pos : (0:ℝ) < 2 - Real.exp theta := by linarith
  field_simp

/-- **IID BAD-prefix Chernoff tail.** For `0 < θ < log 2`, `P_iid(S_t ≥ s) ≤ e^(-θs)·M_up(θ)^t`.
Priority: exact positive exponential decay in `t`, not the sharp large-deviation rate. -/
theorem iid_geom_sum_upper_tail (theta : ℝ) (hθ0 : 0 < theta) (hθ1 : theta < Real.log 2)
    (t : ℕ) (s : ℝ) :
    iidGeom2VectorProb t (sumAtLeastEvent t s)
      ≤ Real.exp (-(theta * s)) * (geomUpperMgf theta) ^ t := by
  unfold iidGeom2VectorProb genEventProb
  have htw_nonneg := tiltedUpperWeight_nonneg theta
  have htw_summable := tiltedUpperWeight_summable theta hθ1
  have hbound : ∀ a : Fin t → ℕ,
      Set.indicator (sumAtLeastEvent t s) (atomWeight t) a
        ≤ Real.exp (-(theta * s)) * ∏ i, tiltedUpperWeight theta (a i) := by
    intro a
    have hprod_eq : (∏ i, tiltedUpperWeight theta (a i))
        = atomWeight t a * Real.exp (theta * vecRealSum t a) := by
      unfold tiltedUpperWeight atomWeight vecRealSum
      rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.mul_sum]
    rw [hprod_eq]
    by_cases ha : a ∈ sumAtLeastEvent t s
    · have hend : s ≤ vecRealSum t a := ha
      have hexp_ge : (1:ℝ) ≤ Real.exp (-(theta * s)) * Real.exp (theta * vecRealSum t a) := by
        rw [← Real.exp_add]
        have h0le : (0:ℝ) ≤ -(theta * s) + theta * vecRealSum t a := by nlinarith
        calc (1:ℝ) = Real.exp 0 := Real.exp_zero.symm
          _ ≤ Real.exp (-(theta * s) + theta * vecRealSum t a) := Real.exp_le_exp.mpr h0le
      simp only [Set.indicator, ha, ite_true]
      nlinarith [atomWeight_nonneg t a, hexp_ge]
    · simp only [Set.indicator, ha, ite_false]
      exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (atomWeight_nonneg t a) (Real.exp_pos _).le)
  have hsummable_rhs : Summable (fun a : Fin t → ℕ =>
      Real.exp (-(theta * s)) * ∏ i, tiltedUpperWeight theta (a i)) :=
    (genProdWeight_summable htw_nonneg htw_summable t).mul_left _
  have hsummable_lhs : Summable (fun a : Fin t → ℕ =>
      Set.indicator (sumAtLeastEvent t s) (atomWeight t) a) :=
    Summable.of_nonneg_of_le (fun a => Set.indicator_nonneg (fun x _ => atomWeight_nonneg t x) a)
      hbound hsummable_rhs
  have hle : ∑' a : Fin t → ℕ, Set.indicator (sumAtLeastEvent t s) (atomWeight t) a
      ≤ ∑' a : Fin t → ℕ, Real.exp (-(theta * s)) * ∏ i, tiltedUpperWeight theta (a i) := by
    have hsub_nonneg : ∀ a : Fin t → ℕ, 0 ≤
        Real.exp (-(theta * s)) * (∏ i, tiltedUpperWeight theta (a i))
          - Set.indicator (sumAtLeastEvent t s) (atomWeight t) a := fun a => by
      linarith [hbound a]
    have hsub_summable : Summable (fun a : Fin t → ℕ =>
        Real.exp (-(theta * s)) * (∏ i, tiltedUpperWeight theta (a i))
          - Set.indicator (sumAtLeastEvent t s) (atomWeight t) a) :=
      hsummable_rhs.sub hsummable_lhs
    have h0le : (0:ℝ) ≤ ∑' a : Fin t → ℕ,
        (Real.exp (-(theta * s)) * (∏ i, tiltedUpperWeight theta (a i))
          - Set.indicator (sumAtLeastEvent t s) (atomWeight t) a) := tsum_nonneg hsub_nonneg
    rwa [Summable.tsum_sub hsummable_rhs hsummable_lhs, sub_nonneg] at h0le
  have heq : ∑' a : Fin t → ℕ, Real.exp (-(theta * s)) * ∏ i, tiltedUpperWeight theta (a i)
      = Real.exp (-(theta * s)) * (geomUpperMgf theta) ^ t := by
    rw [tsum_mul_left, genProdWeight_tsum_eq_pow htw_nonneg htw_summable t,
      tiltedUpperWeight_tsum theta hθ0 hθ1]
  linarith [hle, heq]

/-! ## Part 4: GOOD/BAD prefix events and the information-budget bridge -/

/-- **GOOD prefix**: the length-`t` prefix's digit sum stays below the threshold `sMax`. -/
noncomputable def goodPrefixEvent (t : ℕ) (sMax : ℝ) : Set (Fin t → ℕ) := (sumAtLeastEvent t sMax)ᶜ

/-- **BAD prefix**: the complement — the prefix sum reaches or exceeds `sMax`. Defined directly
as `sumAtLeastEvent`, so `iid_geom_sum_upper_tail` applies to it with no further translation. -/
noncomputable def badPrefixEvent (t : ℕ) (sMax : ℝ) : Set (Fin t → ℕ) := sumAtLeastEvent t sMax

/-- **Option B (info-budget bridge).** A finite threshold `sMaxNat` on `S d t` — chosen so that
the exponential info-budget inequality already holds at `sMaxNat` — implies it for every
`S d t ≤ sMaxNat`, via monotonicity of `2^x`. This is exactly Milestone 7's
`conditional_shifted_persistence_upper_bound`/`_bits` admissibility hypothesis
`2·(1+1/η)·2^(S d t+2Q) ≤ K.Cres·Y`, isolated so the (later) GOOD-prefix argument can invoke
Milestone 7 without re-deriving this inequality. -/
theorem good_prefix_implies_info_budget
    (sMaxNat : ℕ) (d : ℕ → ℕ) (t : ℕ) (hS_le : S d t ≤ sMaxNat)
    (η : ℝ) (hη : 0 < η) (Y : ℕ) (K_Cres : ℝ) (Q : ℕ)
    (hparam : 2 * (1 + 1 / η) * (2 : ℝ) ^ (sMaxNat + 2 * Q) ≤ K_Cres * (Y : ℝ)) :
    2 * (1 + 1 / η) * (2 : ℝ) ^ (S d t + 2 * Q) ≤ K_Cres * (Y : ℝ) := by
  calc 2 * (1 + 1 / η) * (2 : ℝ) ^ (S d t + 2 * Q)
      ≤ 2 * (1 + 1 / η) * (2 : ℝ) ^ (sMaxNat + 2 * Q) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply pow_le_pow_right₀ (by norm_num) (by omega)
    _ ≤ K_Cres * (Y : ℝ) := hparam

/-! ## Part 5: the prefix Tao transfer (BAD-prefix ingredient)

Structurally identical to `early_shift_persistence_upper_bound` — the *same* generic
`TaoMixingHypothesis.finite_valuation_mixing` interface, applied at length `t` (the prefix)
instead of `t+n` (the joint block). No restart is needed here either: this is a direct
transfer of the real prefix law to iid, composed with `iid_geom_sum_upper_tail` to bound the
resulting iid BAD-prefix probability. -/

/-- **Fixed-witness BAD-prefix Tao transfer.** Same as `prefix_bad_tao_transfer`, but `K` (with
its defining `TaoMixingProperty hK`) is supplied by the caller instead of derived internally
from `tao` — so a single `K` can be chosen once (e.g. via `tao.finite_valuation_mixing cPrefix
hcPrefix`) and its residue-closeness hypothesis stated as an explicit top-level hypothesis
(needed for Milestone 11's BAD-prefix bound, since `K` is not otherwise available before the
proof begins). -/
theorem prefix_bad_tao_transfer_of_constants
    (c0 : ℝ) (K : TaoMixingConstants c0) (hK : TaoMixingProperty c0 K)
    (w : ℕ → ℝ) (hw_nonneg : ∀ m, 0 ≤ w m) (Nwin : ℕ)
    (hw_supp : Function.support w ⊆ ↑(range Nwin))
    (hw_odd : genEventProb w {m : ℕ | ¬ Odd m} = 0)
    (t : ℕ) (ht : 1 ≤ t) (sMax : ℝ) (theta : ℝ) (hθ0 : 0 < theta) (hθ1 : theta < Real.log 2)
    (Qres : ℕ) (hQrel : (Qres : ℝ) ≥ (2 + c0) * (t : ℝ)) :
    taoL1TV (pushforward (genEventProb w) (fun m => (m : ZMod (2 ^ Qres)))) (unifOddResidues Qres)
        ≤ K.Cres * (2 : ℝ) ^ (-(Qres : ℝ)) →
      pushforward (genEventProb w) (fun m => valuationVector m t) (badPrefixEvent t sMax)
        ≤ Real.exp (-(theta * sMax)) * (geomUpperMgf theta) ^ t
          + K.A * (2 : ℝ) ^ (-(K.c1 * (t : ℝ))) := by
  intro hres
  have htv := hK t Qres (genEventProb w) ht hQrel hw_odd hres
  set F : ℕ → (Fin t → ℕ) := fun m => valuationVector m t with hF_def
  have hw'_nonneg : ∀ v : Fin t → ℕ, 0 ≤ ∑ j ∈ range Nwin, if F j = v then w j else 0 := by
    intro v
    apply Finset.sum_nonneg
    intro j _
    split_ifs
    · exact hw_nonneg j
    · exact le_refl 0
  have hw'_summable : Summable (fun v : Fin t → ℕ =>
      ∑ j ∈ range Nwin, if F j = v then w j else 0) := by
    apply summable_of_hasFiniteSupport
    apply Set.Finite.subset (Finset.finite_toSet ((range Nwin).image F))
    intro v hv
    by_contra hvni
    apply hv
    apply Finset.sum_eq_zero
    intro j hj
    rw [if_neg]
    intro hveq
    apply hvni
    exact Finset.mem_image.mpr ⟨j, hj, hveq⟩
  have hbridge := event_discrepancy_le_taoL1TV hw'_nonneg (atomWeight_nonneg t)
    hw'_summable (atomWeight_summable t)
  have hle := event_prob_le_of_discrepancy hbridge (badPrefixEvent t sMax)
  have htail := iid_geom_sum_upper_tail theta hθ0 hθ1 t sMax
  calc pushforward (genEventProb w) F (badPrefixEvent t sMax)
      = genEventProb (fun v : Fin t → ℕ => ∑ j ∈ range Nwin, if F j = v then w j else 0)
          (badPrefixEvent t sMax) := by
        rw [genEventProb_pushforward_fiber_general Nwin w hw_supp F]
    _ ≤ iidGeom2VectorProb t (badPrefixEvent t sMax) + K.A * (2 : ℝ) ^ (-(K.c1 * (t : ℝ))) := by
        unfold iidGeom2VectorProb
        unfold iidGeom2VectorProb at htv
        rw [genEventProb_pushforward_fiber_general Nwin w hw_supp F] at htv
        linarith [hle, htv]
    _ ≤ Real.exp (-(theta * sMax)) * (geomUpperMgf theta) ^ t
          + K.A * (2 : ℝ) ^ (-(K.c1 * (t : ℝ))) := by
        unfold badPrefixEvent
        linarith [htail]

/-- **BAD-prefix Tao transfer.** `P_real(BAD_t) ≤ P_iid(BAD_t) + K.A·2^(-K.c1·t)`, then bounded
further by the iid Chernoff tail: `P_real(BAD_t) ≤ e^(-θ·sMax)·M_up(θ)^t + K.A·2^(-K.c1·t)`. -/
theorem prefix_bad_tao_transfer
    (tao : TaoMixingHypothesis)
    (w : ℕ → ℝ) (hw_nonneg : ∀ m, 0 ≤ w m) (Nwin : ℕ)
    (hw_supp : Function.support w ⊆ ↑(range Nwin))
    (hw_odd : genEventProb w {m : ℕ | ¬ Odd m} = 0)
    (t : ℕ) (ht : 1 ≤ t) (sMax : ℝ) (theta : ℝ) (hθ0 : 0 < theta) (hθ1 : theta < Real.log 2)
    (c0 : ℝ) (hc0 : 0 < c0) (Qres : ℕ) (hQrel : (Qres : ℝ) ≥ (2 + c0) * (t : ℝ)) :
    ∃ K : TaoMixingConstants c0,
      taoL1TV (pushforward (genEventProb w) (fun m => (m : ZMod (2 ^ Qres)))) (unifOddResidues Qres)
          ≤ K.Cres * (2 : ℝ) ^ (-(Qres : ℝ)) →
        pushforward (genEventProb w) (fun m => valuationVector m t) (badPrefixEvent t sMax)
          ≤ Real.exp (-(theta * sMax)) * (geomUpperMgf theta) ^ t
            + K.A * (2 : ℝ) ^ (-(K.c1 * (t : ℝ))) := by
  obtain ⟨K, hK⟩ := tao.finite_valuation_mixing c0 hc0
  exact ⟨K, prefix_bad_tao_transfer_of_constants c0 K hK w hw_nonneg Nwin hw_supp hw_odd t ht sMax
    theta hθ0 hθ1 Qres hQrel⟩

/-! ## Part 6: scope note — the LATE union theorem is NOT proved here

Parts 4–5 give the individual LATE-shift ingredients: `goodPrefixEvent`/`badPrefixEvent`,
`good_prefix_implies_info_budget` (GOOD ⟹ Milestone 7's admissibility hypothesis), and
`prefix_bad_tao_transfer` (the real BAD-prefix probability ≤ iid Chernoff tail + Tao error).
Combining them with Milestone 7's `conditional_shifted_persistence_upper_bound_bits` into a
single closed-form

    P_real(persistence at fixed t) ≤ exp(λ*c)·2^(-I0·n) + futureMixingError(n)
      + iidBadTail(t) + prefixMixingError(t)

is **NOT proved in this file** — it is blocked by a genuine architectural gap, not a Lean
difficulty. The obstruction:

Milestone 7's `conditional_shifted_persistence_upper_bound_bits` is a statement about ONE
FIXED admissible triple `(d, t, r)` with `Realizes d t r` — `conditionalRestartLaw` is a
deterministic Milestones-1–3 cylinder-counting construction, built entirely independently of
any probability law over starting seeds. GOOD/BAD, by contrast, are only meaningful as *events
under a law* `N` (or `genEventProb w`) over starting seeds — `goodPrefixEvent`/`badPrefixEvent`
above are subsets of `Fin t → ℕ`, and `prefix_bad_tao_transfer` bounds `pushforward w (...)
badPrefixEvent`, a genuine probability. To combine the two branches one needs a statement of
the shape

    P_real(persistence_t ∩ GOOD_t) ≤ (sup over admissible realized r ∈ GOOD_t of
      "the conditional future law of the true seed given its realized prefix r")·(M7 bound)

i.e. a theorem asserting that *the true conditional future law of the global random seed,
given its realized length-`t` prefix equals `r`, is (well-approximated by)
`conditionalRestartLaw r ...`* — a disintegration / finite law-of-total-probability statement
over prefix cylinders. No such theorem exists anywhere in this repository (checked: no
disintegration, total-probability, or prefix-partition lemma in `EOC/TaoLike/*.lean` or the
Milestones 1–4 files). Per the Milestone 8 brief, this finding is itself the correct Milestone
8 outcome for the LATE case: the missing lemma should be named `prefix_partition` and attempted
as its own future milestone, not forced through with an unjustified aggregation step here. -/

end TaoExternal
end EOC
