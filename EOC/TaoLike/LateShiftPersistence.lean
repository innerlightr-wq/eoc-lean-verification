import EOC.TaoLike.ShiftedPersistence
import EOC.TaoLike.EarlyLate
import EOC.TaoLike.PrefixPartition
import EOC.TaoLike.RestartLawAlignment

/-!
# Fixed late-shift persistence (Milestone 11)

Combines Milestone 7 (`conditional_shifted_persistence_upper_bound_bits_at_window_of_constants`),
the uniform Tao witness refactor, Milestone 8's BAD-prefix machinery
(`prefix_bad_tao_transfer_of_constants`, `iid_geom_sum_upper_tail`,
`good_prefix_implies_info_budget`), Milestone 9's finite prefix partition
(`good_prefix_event_bound_of_conditional_bound`), and Milestone 10's exact restart-law
alignment (`harmonic_prefixMass_eq_W_with_bound`,
`prefix_conditional_future_eq_restart_future_at_window`) into ONE theorem about the TRUE
harmonic seed law on a fixed window `[Y, Y+H)`: a GOOD/BAD split of the realized length-`t`
prefix bounds the probability that the *restarted* future length-`n` valuation block persists
below a drift ceiling `c`.

**EPISTEMIC STATUS.** FORMALLY VERIFIED *conditional on* the external `TaoMixingHypothesis`
witnesses `Kfuture`/`Kprefix` (with their defining `TaoMixingProperty`) and TWO explicit
residue-closeness hypotheses (`hbudget_param`, `hresidue_prefix`) that play exactly the role
Tao's own hypothesis's antecedent plays elsewhere in this development — genuinely external
assumptions about the harmonic seed law's residue distribution, not derived here. This is ONE
FIXED shift `t` and ONE FIXED future length `n`: there is NO union over `t`, no
`τ log Y`/`δ log Y` substitution, no Borel–Cantelli step, no logarithmic-density conclusion. It
is NOT a pointwise claim about individual Collatz orbits, NOT a formalization of Tao's
Proposition 1.9, NOT EOC, and NOT the Collatz conjecture.

## Why this file also extends `RestartLawAlignment.lean` and `EarlyLate.lean`

Two genuine interface gaps, identified in the earlier (now-superseded) investigation recorded
in this file's history, are closed as prerequisites, both additive-only (no existing theorem's
statement is changed):

* `RestartLawAlignment.lean` gained `_at_window` variants of
  `genEventProb_prefixConditional_eq_reindexed`, `prefixConditional_restart_eq_
  conditionalRestartLaw`, and `prefix_conditional_future_eq_restart_future`, each taking
  `kmin, N, hmem, hiff` as EXPLICIT parameters. This lets Milestone 11 obtain `kmin, N, hmem,
  hNlb` exactly ONCE per realized prefix (from `harmonic_prefixMass_eq_W_with_bound`) and reuse
  the *same* local constants both in the M7 `_at_window` chain and in the future-law identity —
  avoiding the "existential re-selection" problem (two separate calls to a theorem returning
  `∃ kmin N, ...` give syntactically distinct witnesses, even when mathematically forced equal).
* `EarlyLate.lean` gained `prefix_bad_tao_transfer_of_constants`, a fixed-witness version of
  `prefix_bad_tao_transfer` taking `K, hK` explicitly, so `Kprefix`'s residue-closeness
  hypothesis can be stated as an explicit top-level hypothesis of the principal theorem below
  (impossible with the original `tao`-only signature, since `K` there is only available *inside*
  the proof).
-/

namespace EOC
namespace TaoExternal

open Finset

/-! ## Part 1: arithmetic glue between `S d t` and `vecRealSum` -/

/-- The word `S`-sum and the `Fin`-indexed real vector sum agree, for the word built from a
seed's own actual orbit valuations. -/
theorem S_eq_vecRealSum (m t : ℕ) :
    ((S (fun i => a (orbit m i)) t : ℕ) : ℝ) = vecRealSum t (valuationVector m t) := by
  unfold S s vecRealSum valuationVector
  rw [Nat.cast_sum]
  exact Finset.sum_range (fun i => (a (orbit m i) : ℝ))

/-! ## Part 2: recovering a representative seed from a positive-mass prefix -/

/-- **Representative extraction.** Any realized prefix `v` with positive prefix mass under the
harmonic window weight is witnessed by some concrete odd seed `r0 ∈ [Y, Nwin)` realizing it. -/
theorem exists_realizer_of_prefixMass_pos (Y Nwin t : ℕ) (v : Fin t → ℕ)
    (hpos : 0 < prefixMass (harmonicWindowWeight Y Nwin) Nwin t v) :
    ∃ r0 : ℕ, r0 < Nwin ∧ Y ≤ r0 ∧ Odd r0 ∧ valuationVector r0 t = v := by
  classical
  by_contra hcon
  push_neg at hcon
  have hz : prefixMass (harmonicWindowWeight Y Nwin) Nwin t v = 0 := by
    unfold prefixMass
    apply Finset.sum_eq_zero
    intro j hj
    by_cases hveq : valuationVector j t = v
    · rw [if_pos hveq]
      unfold harmonicWindowWeight
      by_cases hcondj : Y ≤ j ∧ j < Nwin ∧ Odd j
      · exact absurd hveq (hcon j (Finset.mem_range.mp hj) hcondj.1 hcondj.2.2)
      · exact if_neg hcondj
    · exact if_neg hveq
  linarith [hpos, hz]

/-! ## Part 3: finite-support monotonicity and subadditivity of `genEventProb` -/

/-- A `genEventProb`-shaped event probability, for a finitely-supported weight, equals a finite
`Finset.sum` over its support window — the bookkeeping fact underlying monotonicity and
subadditivity below. -/
theorem genEventProb_eq_finsum_of_supp (w : ℕ → ℝ) (Nwin : ℕ)
    (hw_supp : Function.support w ⊆ ↑(range Nwin)) (S : Set ℕ) :
    genEventProb w S = ∑ m ∈ range Nwin, Set.indicator S w m := by
  unfold genEventProb
  have hind_supp : Function.support (Set.indicator S w) ⊆ ↑(range Nwin) := by
    intro m hm
    apply hw_supp
    intro hwm0
    exact hm (by simp [Set.indicator, hwm0])
  exact tsum_eq_sum' hind_supp

/-- **Monotonicity.** For a finitely-supported nonnegative weight, `genEventProb` is monotone
under set inclusion. -/
theorem genEventProb_mono_of_supp (w : ℕ → ℝ) (hw_nonneg : ∀ m, 0 ≤ w m) (Nwin : ℕ)
    (hw_supp : Function.support w ⊆ ↑(range Nwin)) (A B : Set ℕ) (hAB : A ⊆ B) :
    genEventProb w A ≤ genEventProb w B := by
  rw [genEventProb_eq_finsum_of_supp w Nwin hw_supp A, genEventProb_eq_finsum_of_supp w Nwin hw_supp B]
  apply Finset.sum_le_sum
  intro m _
  by_cases hmA : m ∈ A
  · have hmB : m ∈ B := hAB hmA
    simp [Set.indicator, hmA, hmB]
  · by_cases hmB : m ∈ B
    · simp only [Set.indicator, hmA, hmB, if_false, if_true]
      exact hw_nonneg m
    · simp [Set.indicator, hmA, hmB]

/-- **Subadditivity.** For a finitely-supported nonnegative weight, `genEventProb` of a union is
at most the sum of the individual event probabilities. -/
theorem genEventProb_union_le_of_supp (w : ℕ → ℝ) (hw_nonneg : ∀ m, 0 ≤ w m) (Nwin : ℕ)
    (hw_supp : Function.support w ⊆ ↑(range Nwin)) (A B : Set ℕ) :
    genEventProb w (A ∪ B) ≤ genEventProb w A + genEventProb w B := by
  rw [genEventProb_eq_finsum_of_supp w Nwin hw_supp (A ∪ B),
    genEventProb_eq_finsum_of_supp w Nwin hw_supp A,
    genEventProb_eq_finsum_of_supp w Nwin hw_supp B, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro m _
  by_cases hmA : m ∈ A <;> by_cases hmB : m ∈ B <;>
    simp only [Set.indicator, Set.mem_union, hmA, hmB, if_true, if_false, or_true, true_or,
      or_false, false_or] <;>
    linarith [hw_nonneg m]

/-! ## Part 4: the GOOD-prefix true fiber bound -/

/-- **GOOD-prefix true fiber bound.** For a realized length-`t` prefix `v` with positive
harmonic prefix mass, the joint probability, under the TRUE harmonic seed law on `[Y, Y+H)`, of
persistence of the restarted future block together with realizing `v`, is at most `Bgood` times
the prefix mass — with `Bgood` depending on neither `v` nor any representative seed, `kmin`,
`N`, or `W`. Consumes `harmonic_prefixMass_eq_W_with_bound` (Milestone 10) to obtain ONE window
witness `kmin, N, hmem, hNlb`, threaded verbatim into BOTH
`conditional_shifted_persistence_upper_bound_bits_at_window_of_constants` (Milestone 7) and
`prefix_conditional_future_eq_restart_future_at_window` (Milestone 10) — no second,
independently-derived window witness is introduced. -/
theorem good_prefix_true_fiber_bound
    (Y H : ℕ) (hYpos : 0 < Y)
    (t : ℕ) (ht : 1 ≤ t) (n : ℕ) (hn : 1 ≤ n) (c : ℝ)
    (sMaxNat : ℕ) (hsmall : 2 ^ (sMaxNat + 1) ≤ Y)
    (η : ℝ) (hη : 0 < η) (hHη : η * (Y : ℝ) ≤ (H : ℝ))
    (hthick : 4 * (2 : ℝ) ^ (sMaxNat + 1) ≤ η * (Y : ℝ))
    (c0 : ℝ) (Q : ℕ) (hQ1 : 1 ≤ Q) (hQrel : (Q : ℝ) ≥ (2 + c0) * (n : ℝ))
    (Kfuture : TaoMixingConstants c0) (hKfuture : TaoMixingProperty c0 Kfuture)
    (hbudget_param : 2 * (1 + 1 / η) * (2 : ℝ) ^ (sMaxNat + 2 * Q) ≤ Kfuture.Cres * (Y : ℝ))
    (v : Fin t → ℕ) (hgood : v ∈ goodPrefixEvent t (sMaxNat : ℝ))
    (hpos : 0 < prefixMass (harmonicWindowWeight Y (Y + H)) (Y + H) t v) :
    genEventProb (harmonicWindowWeight Y (Y + H))
        (((fun m => valuationVector (orbit m t) n) ⁻¹' geomPersistenceEvent collatzAlpha c n)
          ∩ {m | valuationVector m t = v})
      ≤ (Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n : ℝ)))
          + Kfuture.A * (2 : ℝ) ^ (-(Kfuture.c1 * (n : ℝ))))
        * prefixMass (harmonicWindowWeight Y (Y + H)) (Y + H) t v := by
  classical
  obtain ⟨r0, hr0lt, hr0Y, hr0odd, hveq0⟩ := exists_realizer_of_prefixMass_pos Y (Y + H) t v hpos
  have hd_pos : ∀ i < t, 1 ≤ a (orbit r0 i) := fun i _ => hd_pos_of_orbit hr0odd i
  have hr0 : Realizes (fun i => a (orbit r0 i)) t r0 := ⟨hr0odd, fun j _ => rfl⟩
  set d : ℕ → ℕ := fun i => a (orbit r0 i) with hd_def
  set r : ℕ := leastRealizer d t with hr_def
  have hr : Realizes d t r := leastRealizer_realizes d t ht hd_pos
  have hvreq : valuationVector r t = v := by
    have h1 := (realizes_iff_valuationVector_eq d t r).mp hr
    have h2 := (realizes_iff_valuationVector_eq d t r0).mp hr0
    rw [h1.2, ← h2.2, hveq0]
  rw [← hvreq] at hpos ⊢
  have hlt : vecRealSum t v < (sMaxNat : ℝ) := by
    have hbad : v ∉ sumAtLeastEvent t (sMaxNat : ℝ) := hgood
    unfold sumAtLeastEvent at hbad
    simpa using hbad
  have hSR : (S d t : ℝ) < (sMaxNat : ℝ) := by
    have hSeq := S_eq_vecRealSum r0 t
    rw [← hd_def, hveq0] at hSeq
    linarith [hSeq, hlt]
  have hSgood : S d t ≤ sMaxNat := by exact_mod_cast hSR.le
  have hrlt : r < 2 ^ (S d t + 1) := leastRealizer_lt d t
  have hpow_le : (2 : ℕ) ^ (S d t + 1) ≤ 2 ^ (sMaxNat + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hYr : r ≤ Y := by omega
  obtain ⟨kmin, N, hmem, hiff, hNlb0, hWeq⟩ :=
    harmonic_prefixMass_eq_W_with_bound d t r Y (Y + H) hd_pos hr hYr (Nat.le_add_right Y H)
  have hNlb : ((Y : ℝ) + (H : ℝ)) - (Y : ℝ) ≤ ((N : ℝ) + 2) * (2 ^ (S d t + 1) : ℝ) := by
    push_cast at hNlb0
    linarith [hNlb0]
  have hthick_local : 4 * (2 : ℝ) ^ (S d t + 1) ≤ η * (Y : ℝ) := by
    have hpowR : (2 : ℝ) ^ (S d t + 1) ≤ (2 : ℝ) ^ (sMaxNat + 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    linarith [hthick, hpowR]
  have hbudget : 2 * (1 + 1 / η) * (2 : ℝ) ^ (S d t + 2 * Q) ≤ Kfuture.Cres * (Y : ℝ) :=
    good_prefix_implies_info_budget sMaxNat d t hSgood η hη Y Kfuture.Cres Q hbudget_param
  obtain ⟨W, hWpos, hWdef, hbound⟩ :=
    conditional_shifted_persistence_upper_bound_bits_at_window_of_constants c0 Kfuture hKfuture d t
      r hr ht c n hn Y H hYr hYpos η hη hHη Q hQrel hQ1 hthick_local kmin N hmem hNlb
  have hWeqW : prefixMass (harmonicWindowWeight Y (Y + H)) (Y + H) t (valuationVector r t) = W :=
    hWeq.trans hWdef.symm
  have hbound' := hbound hbudget
  have hrestart :=
    prefix_conditional_future_eq_restart_future_at_window d t r Y (Y + H) n hr kmin N hmem hiff
      (geomPersistenceEvent collatzAlpha c n)
  have hjoint : genEventProb (harmonicWindowWeight Y (Y + H))
      (((fun m => valuationVector (orbit m t) n) ⁻¹' geomPersistenceEvent collatzAlpha c n)
        ∩ {m | valuationVector m t = valuationVector r t})
      = genEventProb (prefixConditionalWeight (harmonicWindowWeight Y (Y + H)) (Y + H) t
            (valuationVector r t))
          ((fun m => valuationVector (orbit m t) n) ⁻¹' geomPersistenceEvent collatzAlpha c n)
        * prefixMass (harmonicWindowWeight Y (Y + H)) (Y + H) t (valuationVector r t) := by
    rw [genEventProb_prefixConditionalWeight_eq, div_mul_cancel₀]
    exact ne_of_gt hpos
  have hEexp : genEventProb (prefixConditionalWeight (harmonicWindowWeight Y (Y + H)) (Y + H) t
        (valuationVector r t))
      ((fun m => valuationVector (orbit m t) n) ⁻¹' geomPersistenceEvent collatzAlpha c n)
      = pushforward (pushforward (genEventProb (prefixConditionalWeight
          (harmonicWindowWeight Y (Y + H)) (Y + H) t (valuationVector r t)))
          (fun m => orbit m t)) (fun x => valuationVector x n)
          (geomPersistenceEvent collatzAlpha c n) := by
    unfold pushforward
    rfl
  rw [hjoint, hEexp, hrestart, hWeqW]
  exact mul_le_mul_of_nonneg_right hbound' hWpos.le

/-! ## Part 5: the BAD-prefix true bound -/

/-- **BAD-prefix true bound.** Under the TRUE harmonic seed law on `[Y, Y+H)`, the probability
that the realized length-`t` prefix is BAD (`S d t ≥ sMaxNat`) is bounded by the iid Chernoff
tail plus a Tao mixing error at length `t`, directly via `prefix_bad_tao_transfer_of_constants`
(Milestone 8) — no new mixing argument, no reproving of `iid_geom_sum_upper_tail`. -/
theorem bad_prefix_true_bound
    (Y H t : ℕ) (ht : 1 ≤ t) (sMaxNat : ℕ)
    (hnorm : genEventProb (harmonicWindowWeight Y (Y + H)) Set.univ = 1)
    (theta : ℝ) (hθ0 : 0 < theta) (hθ1 : theta < Real.log 2)
    (cPrefix : ℝ) (Qpre : ℕ) (hQpre1 : 1 ≤ Qpre) (hQprerel : (Qpre : ℝ) ≥ (2 + cPrefix) * (t : ℝ))
    (Kprefix : TaoMixingConstants cPrefix) (hKprefix : TaoMixingProperty cPrefix Kprefix)
    (hresidue_prefix : taoL1TV
        (pushforward (genEventProb (harmonicWindowWeight Y (Y + H)))
          (fun m => (m : ZMod (2 ^ Qpre))))
        (unifOddResidues Qpre)
      ≤ Kprefix.Cres * (2 : ℝ) ^ (-(Qpre : ℝ))) :
    genEventProb (harmonicWindowWeight Y (Y + H))
        {m | valuationVector m t ∈ badPrefixEvent t (sMaxNat : ℝ)}
      ≤ Real.exp (-(theta * (sMaxNat : ℝ))) * (geomUpperMgf theta) ^ t
        + Kprefix.A * (2 : ℝ) ^ (-(Kprefix.c1 * (t : ℝ))) := by
  have hw_nonneg := harmonicWindowWeight_nonneg Y (Y + H)
  have hw_supp := harmonicWindowWeight_supp Y (Y + H)
  have hw_odd : genEventProb (harmonicWindowWeight Y (Y + H)) {m : ℕ | ¬ Odd m} = 0 := by
    unfold genEventProb
    have hzero : ∀ m, Set.indicator {m : ℕ | ¬ Odd m} (harmonicWindowWeight Y (Y + H)) m = 0 := by
      intro m
      by_cases hm : ¬ Odd m
      · rw [Set.indicator_of_mem hm]
        unfold harmonicWindowWeight
        rw [if_neg]
        rintro ⟨_, _, hodd⟩
        exact hm hodd
      · rw [Set.indicator_of_notMem hm]
    rw [tsum_congr hzero, tsum_zero]
  have hw_sum : ∑' m, harmonicWindowWeight Y (Y + H) m = 1 := by
    simpa [genEventProb] using hnorm
  have htransfer := prefix_bad_tao_transfer_of_constants cPrefix Kprefix hKprefix
    (harmonicWindowWeight Y (Y + H)) hw_nonneg (Y + H) hw_supp hw_sum hw_odd t ht
    (sMaxNat : ℝ) theta hθ0 hθ1 Qpre hQprerel hresidue_prefix
  have hpf : pushforward (genEventProb (harmonicWindowWeight Y (Y + H)))
      (fun m => valuationVector m t) (badPrefixEvent t (sMaxNat : ℝ))
      = genEventProb (harmonicWindowWeight Y (Y + H))
          {m | valuationVector m t ∈ badPrefixEvent t (sMaxNat : ℝ)} := by
    unfold pushforward
    rfl
  rw [hpf] at htransfer
  exact htransfer

/-! ## Part 6: the fixed late-shift persistence theorem -/

/-- **Fixed late-shift persistence.** ONE FIXED shift `t`, ONE FIXED future block length `n`,
under the TRUE harmonic seed law on `[Y, Y+H)`: the probability that the future valuation
block after `t` accelerated Collatz steps satisfies `geomPersistenceEvent collatzAlpha c n` is
bounded by the GOOD contribution (iid persistence Chernoff rate plus a future Tao mixing
error, Milestones 6/7) plus the BAD contribution (iid Chernoff tail plus a prefix Tao mixing
error, Milestone 8). `Kfuture` is chosen ONCE, outside the GOOD-prefix aggregation, and reused
unchanged for every realized GOOD prefix (via `good_prefix_true_fiber_bound`); `Kprefix` is an
independently-chosen witness for the (possibly different) prefix-level parameter `cPrefix`. -/
theorem fixed_late_shift_persistence_upper_bound
    (Y H : ℕ) (hYpos : 0 < Y)
    (t : ℕ) (ht : 1 ≤ t) (n : ℕ) (hn : 1 ≤ n) (c : ℝ)
    (sMaxNat : ℕ) (hsmall : 2 ^ (sMaxNat + 1) ≤ Y)
    (η : ℝ) (hη : 0 < η) (hHη : η * (Y : ℝ) ≤ (H : ℝ))
    (hthick : 4 * (2 : ℝ) ^ (sMaxNat + 1) ≤ η * (Y : ℝ))
    (hnorm : genEventProb (harmonicWindowWeight Y (Y + H)) Set.univ = 1)
    (c0 : ℝ) (Q : ℕ) (hQ1 : 1 ≤ Q) (hQrel : (Q : ℝ) ≥ (2 + c0) * (n : ℝ))
    (Kfuture : TaoMixingConstants c0) (hKfuture : TaoMixingProperty c0 Kfuture)
    (hbudget_param : 2 * (1 + 1 / η) * (2 : ℝ) ^ (sMaxNat + 2 * Q) ≤ Kfuture.Cres * (Y : ℝ))
    (theta : ℝ) (hθ0 : 0 < theta) (hθ1 : theta < Real.log 2)
    (cPrefix : ℝ) (Qpre : ℕ) (hQpre1 : 1 ≤ Qpre) (hQprerel : (Qpre : ℝ) ≥ (2 + cPrefix) * (t : ℝ))
    (Kprefix : TaoMixingConstants cPrefix) (hKprefix : TaoMixingProperty cPrefix Kprefix)
    (hresidue_prefix : taoL1TV
        (pushforward (genEventProb (harmonicWindowWeight Y (Y + H)))
          (fun m => (m : ZMod (2 ^ Qpre))))
        (unifOddResidues Qpre)
      ≤ Kprefix.Cres * (2 : ℝ) ^ (-(Qpre : ℝ))) :
    genEventProb (harmonicWindowWeight Y (Y + H))
        ((fun m => valuationVector (orbit m t) n) ⁻¹' geomPersistenceEvent collatzAlpha c n)
      ≤ (Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n : ℝ)))
          + Kfuture.A * (2 : ℝ) ^ (-(Kfuture.c1 * (n : ℝ))))
        + (Real.exp (-(theta * (sMaxNat : ℝ))) * (geomUpperMgf theta) ^ t
          + Kprefix.A * (2 : ℝ) ^ (-(Kprefix.c1 * (t : ℝ)))) := by
  classical
  have hw_nonneg : ∀ m, 0 ≤ harmonicWindowWeight Y (Y + H) m :=
    harmonicWindowWeight_nonneg Y (Y + H)
  have hw_supp : Function.support (harmonicWindowWeight Y (Y + H)) ⊆ ↑(range (Y + H)) :=
    harmonicWindowWeight_supp Y (Y + H)
  have hBgood_nonneg : 0 ≤ Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n : ℝ)))
      + Kfuture.A * (2 : ℝ) ^ (-(Kfuture.c1 * (n : ℝ))) := by
    have h1 : 0 ≤ Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n : ℝ))) := by positivity
    have h2 : 0 ≤ Kfuture.A * (2 : ℝ) ^ (-(Kfuture.c1 * (n : ℝ))) :=
      mul_nonneg Kfuture.hA.le (by positivity)
    linarith
  -- GOOD aggregation (Milestone 9).
  have hGOODagg := good_prefix_event_bound_of_conditional_bound (harmonicWindowWeight Y (Y + H))
    (Y + H) t hw_supp hw_nonneg (fun v => v ∈ goodPrefixEvent t (sMaxNat : ℝ))
    ((fun m => valuationVector (orbit m t) n) ⁻¹' geomPersistenceEvent collatzAlpha c n)
    (Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n : ℝ)))
      + Kfuture.A * (2 : ℝ) ^ (-(Kfuture.c1 * (n : ℝ))))
    hBgood_nonneg
    (fun v hgood hpos => good_prefix_true_fiber_bound Y H hYpos t ht n hn c sMaxNat hsmall η hη
      hHη hthick c0 Q hQ1 hQrel Kfuture hKfuture hbudget_param v hgood hpos)
  rw [prefixMass_tsum_eq_one (Y + H) t (harmonicWindowWeight Y (Y + H)) hw_supp hnorm,
    mul_one] at hGOODagg
  -- BAD bound (Milestone 8).
  have hBADbound := bad_prefix_true_bound Y H t ht sMaxNat hnorm theta hθ0 hθ1 cPrefix Qpre
    hQpre1 hQprerel Kprefix hKprefix hresidue_prefix
  -- Combine via subadditivity over `E ⊆ (E ∩ GOOD_seed) ∪ BAD_seed`.
  have hsubset :
      ((fun m => valuationVector (orbit m t) n) ⁻¹' geomPersistenceEvent collatzAlpha c n)
        ⊆ (((fun m => valuationVector (orbit m t) n) ⁻¹' geomPersistenceEvent collatzAlpha c n)
            ∩ {m | valuationVector m t ∈ goodPrefixEvent t (sMaxNat : ℝ)})
          ∪ {m | valuationVector m t ∈ badPrefixEvent t (sMaxNat : ℝ)} := by
    intro m hmE
    by_cases hgb : valuationVector m t ∈ goodPrefixEvent t (sMaxNat : ℝ)
    · exact Or.inl ⟨hmE, hgb⟩
    · apply Or.inr
      have hgb' : valuationVector m t ∈ sumAtLeastEvent t (sMaxNat : ℝ) := by
        unfold goodPrefixEvent at hgb
        rw [Set.mem_compl_iff, not_not] at hgb
        exact hgb
      exact hgb'
  have hmono := genEventProb_mono_of_supp (harmonicWindowWeight Y (Y + H)) hw_nonneg (Y + H) hw_supp
    ((fun m => valuationVector (orbit m t) n) ⁻¹' geomPersistenceEvent collatzAlpha c n)
    ((((fun m => valuationVector (orbit m t) n) ⁻¹' geomPersistenceEvent collatzAlpha c n)
        ∩ {m | valuationVector m t ∈ goodPrefixEvent t (sMaxNat : ℝ)})
      ∪ {m | valuationVector m t ∈ badPrefixEvent t (sMaxNat : ℝ)}) hsubset
  have hsubadd := genEventProb_union_le_of_supp (harmonicWindowWeight Y (Y + H)) hw_nonneg (Y + H)
    hw_supp
    (((fun m => valuationVector (orbit m t) n) ⁻¹' geomPersistenceEvent collatzAlpha c n)
      ∩ {m | valuationVector m t ∈ goodPrefixEvent t (sMaxNat : ℝ)})
    {m | valuationVector m t ∈ badPrefixEvent t (sMaxNat : ℝ)}
  linarith [hmono, hsubadd, hGOODagg, hBADbound]

end TaoExternal
end EOC
