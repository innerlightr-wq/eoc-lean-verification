import EOC.TaoLike.AllShiftsAveragedPersistence

/-!
# Normalization closure: the actual harmonic probability law

**AUDIT FINDING (confirms the task brief).** `harmonicWindowWeight Y Z` is the RAW harmonic
weight `1/m` on odd `m ∈ [Y,Z)`, zero elsewhere. Its total mass
`Σ_{Y≤m<Z, odd m} 1/m` is generally **not** `1` — Milestones 11–12
(`fixed_late_shift_persistence_upper_bound`, `all_shifts_averaged_persistence_finite`) assumed
this as an explicit hypothesis `hnorm`, which is honest as an assumption but is **not**
automatically true of the raw harmonic window and must not be treated as such.

This file closes that gap: it defines the actual total mass `harmonicWindowMass`, the actual
normalized probability weight `normalizedHarmonicWindowWeight`, proves the normalization is
genuine (not assumed), and transfers Milestones 11–12 to the normalized law — reusing the
existing GOOD/BAD machinery rather than re-deriving it. `harmonicWindowWeight` itself is left
completely unchanged; nothing here silently reinterprets it.

**EPISTEMIC STATUS.** Everything in this file is unconditional deterministic real-analysis
(finite sums, positivity, division identities) EXCEPT the normalized siblings of M11/M12, which
inherit exactly the same external Tao-mixing/residue-closeness hypotheses as their raw-weight
counterparts (now stated for the normalized weight, which is the mathematically correct object
for a residue-closeness-to-uniform hypothesis to be about in the first place). No asymptotics,
no logarithmic scaling, no summability, no density-zero conclusions are proved here.
-/

namespace EOC
namespace TaoExternal

open Finset

/-! ## Part 1: the total harmonic window mass -/

/-- **The total harmonic window mass.** `genEventProb (harmonicWindowWeight Y Z) Set.univ` —
the actual (generally not `1`) total harmonic weight of the odd naturals in `[Y,Z)`. -/
noncomputable def harmonicWindowMass (Y Z : ℕ) : ℝ :=
  genEventProb (harmonicWindowWeight Y Z) Set.univ

/-- **Exact finite-sum identity** for the harmonic window mass, in the exact endpoint
convention (`Y ≤ m`, `m < Z` from `range Z`, `Odd m`) already used by `harmonicWindowWeight`. -/
theorem harmonicWindowMass_eq_sum (Y Z : ℕ) :
    harmonicWindowMass Y Z = ∑ m ∈ range Z, if Y ≤ m ∧ Odd m then (1 : ℝ) / (m : ℝ) else 0 := by
  unfold harmonicWindowMass
  rw [genEventProb_eq_finsum_of_supp (harmonicWindowWeight Y Z) Z (harmonicWindowWeight_supp Y Z)
    Set.univ]
  apply Finset.sum_congr rfl
  intro m hm
  have hmZ : m < Z := Finset.mem_range.mp hm
  rw [Set.indicator_of_mem (Set.mem_univ m)]
  unfold harmonicWindowWeight
  by_cases h : Y ≤ m ∧ Odd m
  · rw [if_pos ⟨h.1, hmZ, h.2⟩, if_pos h]
  · rw [if_neg (fun hcond : Y ≤ m ∧ m < Z ∧ Odd m => h ⟨hcond.1, hcond.2.2⟩), if_neg h]

/-! ## Part 2: positivity -/

/-- **Positivity from a witness.** If some odd `m ∈ [Y,Z)` exists, the harmonic window mass is
positive. Not claimed for empty windows. -/
theorem harmonicWindowMass_pos_of_mem (Y Z m : ℕ) (hYm : Y ≤ m) (hmZ : m < Z) (hodd : Odd m) :
    0 < harmonicWindowMass Y Z := by
  have hwm : harmonicWindowWeight Y Z m = 1 / (m : ℝ) := by
    unfold harmonicWindowWeight
    rw [if_pos ⟨hYm, hmZ, hodd⟩]
  have hmposR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hodd.pos
  have hle : genEventProb (harmonicWindowWeight Y Z) {m} ≤ harmonicWindowMass Y Z :=
    genEventProb_mono_of_supp (harmonicWindowWeight Y Z) (harmonicWindowWeight_nonneg Y Z) Z
      (harmonicWindowWeight_supp Y Z) {m} Set.univ (Set.subset_univ _)
  rw [genEventProb_singleton, hwm] at hle
  have : (0 : ℝ) < 1 / (m : ℝ) := div_pos one_pos hmposR
  linarith

/-- **Practical positivity for `[Y, Y+H)`.** If `Y` itself is odd and positive, or more
generally some odd witness exists in `[Y,Y+H)`, the window has positive mass. Since `Y` odd
already provides such a witness (`m := Y`), this is the direct corollary used downstream. -/
theorem harmonicWindowMass_pos_of_odd_left (Y H : ℕ) (hYodd : Odd Y) (hHpos : 0 < H) :
    0 < harmonicWindowMass Y (Y + H) :=
  harmonicWindowMass_pos_of_mem Y (Y + H) Y (le_refl Y) (by omega) hYodd

/-! ## Part 3: the normalized harmonic window weight -/

/-- **The normalized harmonic window weight.** The actual harmonic probability law on
`[Y,Z)` — `harmonicWindowWeight` rescaled by its own total mass. Lean's total real division
means this is defined even when `harmonicWindowMass Y Z = 0` (it is then identically `0`), but
every normalization/scaling theorem below states positivity of the mass explicitly rather than
relying on this convention. -/
noncomputable def normalizedHarmonicWindowWeight (Y Z : ℕ) (m : ℕ) : ℝ :=
  harmonicWindowWeight Y Z m / harmonicWindowMass Y Z

theorem normalizedHarmonicWindowWeight_nonneg (Y Z : ℕ) (m : ℕ) :
    0 ≤ normalizedHarmonicWindowWeight Y Z m :=
  div_nonneg (harmonicWindowWeight_nonneg Y Z m) (by
    unfold harmonicWindowMass
    unfold genEventProb
    apply tsum_nonneg
    intro x
    exact Set.indicator_nonneg (fun y _ => harmonicWindowWeight_nonneg Y Z y) x)

theorem normalizedHarmonicWindowWeight_supp (Y Z : ℕ) :
    Function.support (normalizedHarmonicWindowWeight Y Z) ⊆ ↑(range Z) := by
  intro m hm
  by_contra hmni
  apply hm
  unfold normalizedHarmonicWindowWeight
  have hw0 : harmonicWindowWeight Y Z m = 0 := by
    by_contra h0
    exact hmni (harmonicWindowWeight_supp Y Z h0)
  rw [hw0, zero_div]

/-! ## Part 4: event-probability scaling identity -/

/-- **Event-probability scaling identity.** The normalized law's probability of any event `E`
is exactly the raw harmonic weight's `E`-mass divided by the total mass — the bridge from the
raw harmonic sums used throughout Milestones 1–12 to an actual probability law. Holds for
every event, with no positivity hypothesis needed (both sides are consistently `0` under Lean's
total division convention when the mass is `0`). -/
theorem genEventProb_normalizedHarmonicWindowWeight_eq (Y Z : ℕ) (E : Set ℕ) :
    genEventProb (normalizedHarmonicWindowWeight Y Z) E
      = genEventProb (harmonicWindowWeight Y Z) E / harmonicWindowMass Y Z := by
  unfold genEventProb normalizedHarmonicWindowWeight
  have hpt : ∀ m, Set.indicator E
      (fun m => harmonicWindowWeight Y Z m / harmonicWindowMass Y Z) m
      = Set.indicator E (harmonicWindowWeight Y Z) m / harmonicWindowMass Y Z := by
    intro m
    by_cases hmE : m ∈ E
    · simp [Set.indicator, hmE]
    · simp [Set.indicator, hmE]
  simp_rw [hpt, div_eq_mul_inv]
  rw [tsum_mul_right]

/-- **Converse scaling identity.** Recovers the raw harmonic event mass from the normalized
probability, valid whenever the total mass is positive (needed since `M * (x/M) = x` requires
`M ≠ 0`). -/
theorem genEventProb_harmonicWindowWeight_eq_mass_mul (Y Z : ℕ) (hpos : 0 < harmonicWindowMass Y Z)
    (E : Set ℕ) :
    genEventProb (harmonicWindowWeight Y Z) E
      = harmonicWindowMass Y Z * genEventProb (normalizedHarmonicWindowWeight Y Z) E := by
  rw [genEventProb_normalizedHarmonicWindowWeight_eq, mul_div_cancel₀]
  exact ne_of_gt hpos

/-- **The normalization theorem, proved (not assumed).** Whenever the total harmonic mass is
positive, the normalized weight genuinely is a probability law: its total mass is exactly `1`.
This is the theorem that closes the semantic gap Milestones 11–12 left as the explicit
hypothesis `hnorm`. -/
theorem genEventProb_normalizedHarmonicWindowWeight_univ (Y Z : ℕ)
    (hpos : 0 < harmonicWindowMass Y Z) :
    genEventProb (normalizedHarmonicWindowWeight Y Z) Set.univ = 1 := by
  rw [genEventProb_normalizedHarmonicWindowWeight_eq]
  unfold harmonicWindowMass
  exact div_self (ne_of_gt hpos)

/-! ## Part 5: prefix-mass and prefix-conditional-weight scaling invariance -/

/-- **Prefix-mass scaling.** The normalized weight's prefix mass is the raw prefix mass divided
by the total mass — an immediate consequence of `Finset.sum_div`. -/
theorem prefixMass_normalizedHarmonicWindowWeight_eq (Y Z t : ℕ) (v : Fin t → ℕ) :
    prefixMass (normalizedHarmonicWindowWeight Y Z) Z t v
      = prefixMass (harmonicWindowWeight Y Z) Z t v / harmonicWindowMass Y Z := by
  unfold prefixMass normalizedHarmonicWindowWeight
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs
  · rfl
  · simp

/-- **Prefix-conditional-weight scaling invariance.** Conditioning on a positive-mass prefix
cancels the global normalization constant exactly: the normalized weight's prefix-conditional
law coincides with the raw weight's, on the nose. This is what lets Milestone 10's exact
restart-law alignment (built entirely against `harmonicWindowWeight`) remain reusable without
modification for the normalized law. -/
theorem prefixConditionalWeight_normalizedHarmonicWindowWeight_eq (Y Z t : ℕ) (v : Fin t → ℕ)
    (hpos : 0 < harmonicWindowMass Y Z) :
    prefixConditionalWeight (normalizedHarmonicWindowWeight Y Z) Z t v
      = prefixConditionalWeight (harmonicWindowWeight Y Z) Z t v := by
  have hM : harmonicWindowMass Y Z ≠ 0 := ne_of_gt hpos
  funext m
  unfold prefixConditionalWeight
  rw [prefixMass_normalizedHarmonicWindowWeight_eq]
  unfold normalizedHarmonicWindowWeight
  set a : ℝ := if valuationVector m t = v then harmonicWindowWeight Y Z m else 0 with ha_def
  set b : ℝ := prefixMass (harmonicWindowWeight Y Z) Z t v with hb_def
  have hite : (if valuationVector m t = v then harmonicWindowWeight Y Z m / harmonicWindowMass Y Z
        else 0) = a / harmonicWindowMass Y Z := by
    rw [ha_def]
    split_ifs <;> simp
  rw [hite]
  by_cases hbz : b = 0
  · rw [hbz, zero_div, div_zero, div_zero]
  · field_simp

/-! ## Part 6: the normalized GOOD-prefix fiber bound (by scaling, not re-proof) -/

/-- **GOOD-prefix true fiber bound, for the normalized law.** Exactly `good_prefix_true_fiber_bound`
(Milestone 11), transported to the normalized weight by dividing both sides of the raw-weight
inequality by the (positive) total mass and applying the event/prefix-mass scaling identities —
the per-fiber inequality is homogeneous of degree `1` in the weight (`Bgood` does not itself
depend on the mass), so no GOOD/BAD mathematics is re-derived. -/
theorem good_prefix_true_fiber_bound_normalized
    (Y H : ℕ) (hYpos : 0 < Y) (hMpos : 0 < harmonicWindowMass Y (Y + H))
    (t : ℕ) (ht : 1 ≤ t) (n : ℕ) (hn : 1 ≤ n) (c : ℝ)
    (sMaxNat : ℕ) (hsmall : 2 ^ (sMaxNat + 1) ≤ Y)
    (η : ℝ) (hη : 0 < η) (hHη : η * (Y : ℝ) ≤ (H : ℝ))
    (hthick : 4 * (2 : ℝ) ^ (sMaxNat + 1) ≤ η * (Y : ℝ))
    (c0 : ℝ) (Q : ℕ) (hQ1 : 1 ≤ Q) (hQrel : (Q : ℝ) ≥ (2 + c0) * (n : ℝ))
    (Kfuture : TaoMixingConstants c0) (hKfuture : TaoMixingProperty c0 Kfuture)
    (hbudget_param : 2 * (1 + 1 / η) * (2 : ℝ) ^ (sMaxNat + 2 * Q) ≤ Kfuture.Cres * (Y : ℝ))
    (v : Fin t → ℕ) (hgood : v ∈ goodPrefixEvent t (sMaxNat : ℝ))
    (hpos : 0 < prefixMass (normalizedHarmonicWindowWeight Y (Y + H)) (Y + H) t v) :
    genEventProb (normalizedHarmonicWindowWeight Y (Y + H))
        (((fun m => valuationVector (orbit m t) n) ⁻¹' geomPersistenceEvent collatzAlpha c n)
          ∩ {m | valuationVector m t = v})
      ≤ (Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n : ℝ)))
          + Kfuture.A * (2 : ℝ) ^ (-(Kfuture.c1 * (n : ℝ))))
        * prefixMass (normalizedHarmonicWindowWeight Y (Y + H)) (Y + H) t v := by
  have hM : harmonicWindowMass Y (Y + H) ≠ 0 := ne_of_gt hMpos
  have hposraw : 0 < prefixMass (harmonicWindowWeight Y (Y + H)) (Y + H) t v := by
    rw [prefixMass_normalizedHarmonicWindowWeight_eq] at hpos
    by_contra hcon
    push_neg at hcon
    have : prefixMass (harmonicWindowWeight Y (Y + H)) (Y + H) t v / harmonicWindowMass Y (Y + H)
        ≤ 0 := div_nonpos_of_nonpos_of_nonneg hcon hMpos.le
    linarith
  have hraw := good_prefix_true_fiber_bound Y H hYpos t ht n hn c sMaxNat hsmall η hη hHη hthick c0
    Q hQ1 hQrel Kfuture hKfuture hbudget_param v hgood hposraw
  have hdiv := (div_le_div_iff_of_pos_right hMpos).mpr hraw
  rw [← genEventProb_normalizedHarmonicWindowWeight_eq, mul_div_assoc,
    ← prefixMass_normalizedHarmonicWindowWeight_eq] at hdiv
  exact hdiv

/-! ## Part 7: the normalized BAD-prefix and EARLY-shift bounds -/

/-- The normalized weight vanishes off the odd naturals, by the same scaling identity applied
to `harmonicWindowWeight_odd_zero`. -/
theorem normalizedHarmonicWindowWeight_odd_zero (Y H : ℕ) :
    genEventProb (normalizedHarmonicWindowWeight Y (Y + H)) {m : ℕ | ¬ Odd m} = 0 := by
  rw [genEventProb_normalizedHarmonicWindowWeight_eq, harmonicWindowWeight_odd_zero, zero_div]

/-- **BAD-prefix true bound, for the normalized law.** `prefix_bad_tao_transfer_of_constants`
(Milestone 8) applied directly to the normalized weight — this theorem is already fully
generic in its weight parameter, so no re-derivation is needed, only the substitution of
`normalizedHarmonicWindowWeight` for `harmonicWindowWeight`. The residue-closeness hypothesis
is stated for the normalized weight, the mathematically natural object for a
"closeness-to-uniform" hypothesis to be about. -/
theorem bad_prefix_true_bound_normalized
    (Y H t : ℕ) (hMpos : 0 < harmonicWindowMass Y (Y + H))
    (ht : 1 ≤ t) (sMaxNat : ℕ)
    (theta : ℝ) (hθ0 : 0 < theta) (hθ1 : theta < Real.log 2)
    (cPrefix : ℝ) (Qpre : ℕ) (hQpre1 : 1 ≤ Qpre) (hQprerel : (Qpre : ℝ) ≥ (2 + cPrefix) * (t : ℝ))
    (Kprefix : TaoMixingConstants cPrefix) (hKprefix : TaoMixingProperty cPrefix Kprefix)
    (hresidue_prefix : taoL1TV
        (pushforward (genEventProb (normalizedHarmonicWindowWeight Y (Y + H)))
          (fun m => (m : ZMod (2 ^ Qpre))))
        (unifOddResidues Qpre)
      ≤ Kprefix.Cres * (2 : ℝ) ^ (-(Qpre : ℝ))) :
    genEventProb (normalizedHarmonicWindowWeight Y (Y + H))
        {m | valuationVector m t ∈ badPrefixEvent t (sMaxNat : ℝ)}
      ≤ Real.exp (-(theta * (sMaxNat : ℝ))) * (geomUpperMgf theta) ^ t
        + Kprefix.A * (2 : ℝ) ^ (-(Kprefix.c1 * (t : ℝ))) := by
  have hw_sum : ∑' m, normalizedHarmonicWindowWeight Y (Y + H) m = 1 := by
    simpa [genEventProb] using
      (genEventProb_normalizedHarmonicWindowWeight_univ Y (Y + H) hMpos)
  have htransfer := prefix_bad_tao_transfer_of_constants cPrefix Kprefix hKprefix
    (normalizedHarmonicWindowWeight Y (Y + H)) (normalizedHarmonicWindowWeight_nonneg Y (Y + H))
    (Y + H) (normalizedHarmonicWindowWeight_supp Y (Y + H)) hw_sum
    (normalizedHarmonicWindowWeight_odd_zero Y H) t ht (sMaxNat : ℝ) theta hθ0 hθ1 Qpre hQprerel
    hresidue_prefix
  have hpf : pushforward (genEventProb (normalizedHarmonicWindowWeight Y (Y + H)))
      (fun m => valuationVector m t) (badPrefixEvent t (sMaxNat : ℝ))
      = genEventProb (normalizedHarmonicWindowWeight Y (Y + H))
          {m | valuationVector m t ∈ badPrefixEvent t (sMaxNat : ℝ)} := by
    unfold pushforward
    rfl
  rw [hpf] at htransfer
  exact htransfer

/-- **EARLY-shift true bound, for the normalized law.** Same reasoning as
`bad_prefix_true_bound_normalized`: `early_shift_persistence_upper_bound_of_constants` is
already generic in its weight parameter. -/
theorem early_shift_true_bound_normalized
    (Y H : ℕ) (hMpos : 0 < harmonicWindowMass Y (Y + H))
    (c0 : ℝ) (Kearly : TaoMixingConstants c0) (hKearly : TaoMixingProperty c0 Kearly)
    (Qearly : ℕ) (t n : ℕ) (hn : 1 ≤ n) (c : ℝ)
    (hQrel : (Qearly : ℝ) ≥ (2 + c0) * ((t + n : ℕ) : ℝ))
    (hresidue_early : taoL1TV (pushforward (genEventProb (normalizedHarmonicWindowWeight Y (Y + H)))
        (fun m => (m : ZMod (2 ^ Qearly)))) (unifOddResidues Qearly)
      ≤ Kearly.Cres * (2 : ℝ) ^ (-(Qearly : ℝ))) :
    genEventProb (normalizedHarmonicWindowWeight Y (Y + H))
        {m : ℕ | valuationVector (orbit m t) n ∈ geomPersistenceEvent collatzAlpha c n}
      ≤ Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n : ℝ)))
        + Kearly.A * (2 : ℝ) ^ (-(Kearly.c1 * ((t + n : ℕ) : ℝ))) := by
  have hw_sum : ∑' m, normalizedHarmonicWindowWeight Y (Y + H) m = 1 := by
    simpa [genEventProb] using
      (genEventProb_normalizedHarmonicWindowWeight_univ Y (Y + H) hMpos)
  have htransfer := early_shift_persistence_upper_bound_of_constants c0 Kearly hKearly
    (normalizedHarmonicWindowWeight Y (Y + H)) (normalizedHarmonicWindowWeight_nonneg Y (Y + H))
    (Y + H) (normalizedHarmonicWindowWeight_supp Y (Y + H)) hw_sum
    (normalizedHarmonicWindowWeight_odd_zero Y H) t n hn c Qearly hQrel hresidue_early
  rwa [pushforward_jointShifted_eq_shiftEvent] at htransfer

/-! ## Part 8: normalized Milestone 11 -/

/-- **Fixed late-shift persistence, for the actual normalized harmonic probability law.** Same
statement and same four-term bound as `fixed_late_shift_persistence_upper_bound`, but for
`genEventProb (normalizedHarmonicWindowWeight Y (Y+H))` — the genuine probability law — instead
of the raw `harmonicWindowWeight`. Replaces the (generally false) hypothesis `hnorm :
genEventProb (harmonicWindowWeight Y (Y+H)) Set.univ = 1` by the honest, provable-when-true
hypothesis `hMpos : 0 < harmonicWindowMass Y (Y+H)`. The GOOD-prefix mathematics is *not*
re-derived — `good_prefix_true_fiber_bound_normalized` transports Milestone 11's own per-fiber
bound by exact scaling; the BAD-prefix mathematics is *not* re-derived either —
`bad_prefix_true_bound_normalized` reapplies the already-generic Milestone 8 transfer directly
to the normalized weight. Only the final GOOD/BAD combination step (subadditivity, monotonicity)
is repeated, verbatim, for the normalized weight. -/
theorem fixed_late_shift_persistence_upper_bound_normalized
    (Y H : ℕ) (hYpos : 0 < Y) (hMpos : 0 < harmonicWindowMass Y (Y + H))
    (t : ℕ) (ht : 1 ≤ t) (n : ℕ) (hn : 1 ≤ n) (c : ℝ)
    (sMaxNat : ℕ) (hsmall : 2 ^ (sMaxNat + 1) ≤ Y)
    (η : ℝ) (hη : 0 < η) (hHη : η * (Y : ℝ) ≤ (H : ℝ))
    (hthick : 4 * (2 : ℝ) ^ (sMaxNat + 1) ≤ η * (Y : ℝ))
    (c0 : ℝ) (Q : ℕ) (hQ1 : 1 ≤ Q) (hQrel : (Q : ℝ) ≥ (2 + c0) * (n : ℝ))
    (Kfuture : TaoMixingConstants c0) (hKfuture : TaoMixingProperty c0 Kfuture)
    (hbudget_param : 2 * (1 + 1 / η) * (2 : ℝ) ^ (sMaxNat + 2 * Q) ≤ Kfuture.Cres * (Y : ℝ))
    (theta : ℝ) (hθ0 : 0 < theta) (hθ1 : theta < Real.log 2)
    (cPrefix : ℝ) (Qpre : ℕ) (hQpre1 : 1 ≤ Qpre) (hQprerel : (Qpre : ℝ) ≥ (2 + cPrefix) * (t : ℝ))
    (Kprefix : TaoMixingConstants cPrefix) (hKprefix : TaoMixingProperty cPrefix Kprefix)
    (hresidue_prefix : taoL1TV
        (pushforward (genEventProb (normalizedHarmonicWindowWeight Y (Y + H)))
          (fun m => (m : ZMod (2 ^ Qpre))))
        (unifOddResidues Qpre)
      ≤ Kprefix.Cres * (2 : ℝ) ^ (-(Qpre : ℝ))) :
    genEventProb (normalizedHarmonicWindowWeight Y (Y + H))
        ((fun m => valuationVector (orbit m t) n) ⁻¹' geomPersistenceEvent collatzAlpha c n)
      ≤ (Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n : ℝ)))
          + Kfuture.A * (2 : ℝ) ^ (-(Kfuture.c1 * (n : ℝ))))
        + (Real.exp (-(theta * (sMaxNat : ℝ))) * (geomUpperMgf theta) ^ t
          + Kprefix.A * (2 : ℝ) ^ (-(Kprefix.c1 * (t : ℝ)))) := by
  classical
  have hw_nonneg : ∀ m, 0 ≤ normalizedHarmonicWindowWeight Y (Y + H) m :=
    normalizedHarmonicWindowWeight_nonneg Y (Y + H)
  have hw_supp : Function.support (normalizedHarmonicWindowWeight Y (Y + H)) ⊆ ↑(range (Y + H)) :=
    normalizedHarmonicWindowWeight_supp Y (Y + H)
  have hBgood_nonneg : 0 ≤ Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n : ℝ)))
      + Kfuture.A * (2 : ℝ) ^ (-(Kfuture.c1 * (n : ℝ))) := by
    have h1 : 0 ≤ Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n : ℝ))) := by positivity
    have h2 : 0 ≤ Kfuture.A * (2 : ℝ) ^ (-(Kfuture.c1 * (n : ℝ))) :=
      mul_nonneg Kfuture.hA.le (by positivity)
    linarith
  -- GOOD aggregation (Milestone 9), fed the normalized per-fiber bound.
  have hGOODagg := good_prefix_event_bound_of_conditional_bound
    (normalizedHarmonicWindowWeight Y (Y + H)) (Y + H) t hw_supp hw_nonneg
    (fun v => v ∈ goodPrefixEvent t (sMaxNat : ℝ))
    ((fun m => valuationVector (orbit m t) n) ⁻¹' geomPersistenceEvent collatzAlpha c n)
    (Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n : ℝ)))
      + Kfuture.A * (2 : ℝ) ^ (-(Kfuture.c1 * (n : ℝ))))
    hBgood_nonneg
    (fun v hgood hpos => good_prefix_true_fiber_bound_normalized Y H hYpos hMpos t ht n hn c
      sMaxNat hsmall η hη hHη hthick c0 Q hQ1 hQrel Kfuture hKfuture hbudget_param v hgood hpos)
  rw [prefixMass_tsum_eq_one (Y + H) t (normalizedHarmonicWindowWeight Y (Y + H)) hw_supp
    (genEventProb_normalizedHarmonicWindowWeight_univ Y (Y + H) hMpos), mul_one] at hGOODagg
  -- BAD bound (Milestone 8), reapplied directly to the normalized weight.
  have hBADbound := bad_prefix_true_bound_normalized Y H t hMpos ht sMaxNat theta hθ0 hθ1 cPrefix
    Qpre hQpre1 hQprerel Kprefix hKprefix hresidue_prefix
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
  have hmono := genEventProb_mono_of_supp (normalizedHarmonicWindowWeight Y (Y + H)) hw_nonneg
    (Y + H) hw_supp
    ((fun m => valuationVector (orbit m t) n) ⁻¹' geomPersistenceEvent collatzAlpha c n)
    ((((fun m => valuationVector (orbit m t) n) ⁻¹' geomPersistenceEvent collatzAlpha c n)
        ∩ {m | valuationVector m t ∈ goodPrefixEvent t (sMaxNat : ℝ)})
      ∪ {m | valuationVector m t ∈ badPrefixEvent t (sMaxNat : ℝ)}) hsubset
  have hsubadd := genEventProb_union_le_of_supp (normalizedHarmonicWindowWeight Y (Y + H)) hw_nonneg
    (Y + H) hw_supp
    (((fun m => valuationVector (orbit m t) n) ⁻¹' geomPersistenceEvent collatzAlpha c n)
      ∩ {m | valuationVector m t ∈ goodPrefixEvent t (sMaxNat : ℝ)})
    {m | valuationVector m t ∈ badPrefixEvent t (sMaxNat : ℝ)}
  linarith [hmono, hsubadd, hGOODagg, hBADbound]

/-! ## Part 9: normalized Milestone 12 -/

/-- **All-shifts averaged persistence, finite integer horizon, for the actual normalized
harmonic probability law.** Same statement and same EARLY/LATE finite-sum conclusion as
`all_shifts_averaged_persistence_finite`, but for `genEventProb (normalizedHarmonicWindowWeight
Y (Y+H))` instead of the raw `harmonicWindowWeight`, replacing `hnorm` by the honest hypothesis
`hMpos : 0 < harmonicWindowMass Y (Y+H)`. -/
theorem all_shifts_averaged_persistence_finite_normalized
    (Y H : ℕ) (hYpos : 0 < Y) (hMpos : 0 < harmonicWindowMass Y (Y + H))
    (Tearly Ttotal : ℕ) (hTearly_pos : 1 ≤ Tearly) (hTle : Tearly ≤ Ttotal)
    (n : ℕ) (hn : 1 ≤ n) (c : ℝ)
    (sMaxNat : ℕ) (hsmall : 2 ^ (sMaxNat + 1) ≤ Y)
    (η : ℝ) (hη : 0 < η) (hHη : η * (Y : ℝ) ≤ (H : ℝ))
    (hthick : 4 * (2 : ℝ) ^ (sMaxNat + 1) ≤ η * (Y : ℝ))
    -- FUTURE (LATE) block parameters, uniform over the whole late range:
    (c0 : ℝ) (Q : ℕ) (hQ1 : 1 ≤ Q) (hQrel : (Q : ℝ) ≥ (2 + c0) * (n : ℝ))
    (Kfuture : TaoMixingConstants c0) (hKfuture : TaoMixingProperty c0 Kfuture)
    (hbudget_param : 2 * (1 + 1 / η) * (2 : ℝ) ^ (sMaxNat + 2 * Q) ≤ Kfuture.Cres * (Y : ℝ))
    (theta : ℝ) (hθ0 : 0 < theta) (hθ1 : theta < Real.log 2)
    -- PREFIX (LATE) parameters, uniform over the whole late range via `hQprerel_uniform`:
    (cPrefix : ℝ) (hcPrefix : 0 < cPrefix)
    (Qpre : ℕ) (hQpre1 : 1 ≤ Qpre) (hQprerel_uniform : (Qpre : ℝ) ≥ (2 + cPrefix) * (Ttotal : ℝ))
    (Kprefix : TaoMixingConstants cPrefix) (hKprefix : TaoMixingProperty cPrefix Kprefix)
    (hresidue_prefix : taoL1TV
        (pushforward (genEventProb (normalizedHarmonicWindowWeight Y (Y + H)))
          (fun m => (m : ZMod (2 ^ Qpre))))
        (unifOddResidues Qpre)
      ≤ Kprefix.Cres * (2 : ℝ) ^ (-(Qpre : ℝ)))
    -- EARLY parameters, uniform over the whole early range via `hQrel_early_uniform`:
    (c0early : ℝ) (hc0early : 0 < c0early)
    (Kearly : TaoMixingConstants c0early) (hKearly : TaoMixingProperty c0early Kearly)
    (Qearly : ℕ)
    (hQrel_early_uniform : (Qearly : ℝ) ≥ (2 + c0early) * ((Tearly + n : ℕ) : ℝ))
    (hresidue_early : taoL1TV
        (pushforward (genEventProb (normalizedHarmonicWindowWeight Y (Y + H)))
          (fun m => (m : ZMod (2 ^ Qearly)))) (unifOddResidues Qearly)
      ≤ Kearly.Cres * (2 : ℝ) ^ (-(Qearly : ℝ))) :
    genEventProb (normalizedHarmonicWindowWeight Y (Y + H)) (allShiftsPersistenceEvent Ttotal n c)
      ≤ ∑ t ∈ range Tearly, (Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n : ℝ)))
            + Kearly.A * (2 : ℝ) ^ (-(Kearly.c1 * ((t + n : ℕ) : ℝ))))
        + ∑ t ∈ Ico Tearly Ttotal,
            ((Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n : ℝ)))
                + Kfuture.A * (2 : ℝ) ^ (-(Kfuture.c1 * (n : ℝ))))
              + (Real.exp (-(theta * (sMaxNat : ℝ))) * (geomUpperMgf theta) ^ t
                + Kprefix.A * (2 : ℝ) ^ (-(Kprefix.c1 * (t : ℝ))))) := by
  classical
  have hw_nonneg := normalizedHarmonicWindowWeight_nonneg Y (Y + H)
  have hw_supp := normalizedHarmonicWindowWeight_supp Y (Y + H)
  -- Step 1: rewrite the all-shifts event as a finite-Finset existential over `range Ttotal`.
  have hev_eq : allShiftsPersistenceEvent Ttotal n c
      = {m : ℕ | ∃ t ∈ range Ttotal,
          m ∈ {m : ℕ | valuationVector (orbit m t) n ∈ geomPersistenceEvent collatzAlpha c n}} := by
    unfold allShiftsPersistenceEvent
    ext m
    simp only [Set.mem_setOf_eq, Finset.mem_range]
  -- Step 2: split `range Ttotal` into the EARLY and LATE Finsets.
  have hrange_split : range Ttotal = range Tearly ∪ Ico Tearly Ttotal := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
      Finset.Ico_union_Ico_eq_Ico (Nat.zero_le Tearly) hTle]
  have hset_split :
      {m : ℕ | ∃ t ∈ range Ttotal,
          m ∈ {m : ℕ | valuationVector (orbit m t) n ∈ geomPersistenceEvent collatzAlpha c n}}
      = {m : ℕ | ∃ t ∈ range Tearly,
            m ∈ {m : ℕ | valuationVector (orbit m t) n ∈ geomPersistenceEvent collatzAlpha c n}}
        ∪ {m : ℕ | ∃ t ∈ Ico Tearly Ttotal,
            m ∈ {m : ℕ | valuationVector (orbit m t) n
              ∈ geomPersistenceEvent collatzAlpha c n}} := by
    ext m
    simp only [Set.mem_setOf_eq, Set.mem_union]
    constructor
    · rintro ⟨t, htT, hmE⟩
      rw [hrange_split, Finset.mem_union] at htT
      rcases htT with htT | htT
      · exact Or.inl ⟨t, htT, hmE⟩
      · exact Or.inr ⟨t, htT, hmE⟩
    · rintro (⟨t, htT, hmE⟩ | ⟨t, htT, hmE⟩)
      · exact ⟨t, hrange_split ▸ Finset.mem_union_left _ htT, hmE⟩
      · exact ⟨t, hrange_split ▸ Finset.mem_union_right _ htT, hmE⟩
  -- Step 3: bound the EARLY piece.
  have hearly_bound : genEventProb (normalizedHarmonicWindowWeight Y (Y + H))
      {m : ℕ | ∃ t ∈ range Tearly,
          m ∈ {m : ℕ | valuationVector (orbit m t) n ∈ geomPersistenceEvent collatzAlpha c n}}
      ≤ ∑ t ∈ range Tearly, (Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n : ℝ)))
          + Kearly.A * (2 : ℝ) ^ (-(Kearly.c1 * ((t + n : ℕ) : ℝ)))) := by
    refine le_trans (genEventProb_biUnion_le_sum_of_supp
      (normalizedHarmonicWindowWeight Y (Y + H)) hw_nonneg (Y + H) hw_supp (range Tearly)
      (fun t => {m : ℕ | valuationVector (orbit m t) n ∈ geomPersistenceEvent collatzAlpha c n}))
      ?_
    apply Finset.sum_le_sum
    intro t htT
    have htTearly : t < Tearly := Finset.mem_range.mp htT
    have hQrel_t : (Qearly : ℝ) ≥ (2 + c0early) * ((t + n : ℕ) : ℝ) := by
      have hcast : ((t + n : ℕ) : ℝ) ≤ ((Tearly + n : ℕ) : ℝ) := by
        exact_mod_cast Nat.add_le_add_right (le_of_lt htTearly) n
      nlinarith [hcast, hQrel_early_uniform]
    exact early_shift_true_bound_normalized Y H hMpos c0early Kearly hKearly Qearly t n hn c
      hQrel_t hresidue_early
  -- Step 4: bound the LATE piece.
  have hlate_bound : genEventProb (normalizedHarmonicWindowWeight Y (Y + H))
      {m : ℕ | ∃ t ∈ Ico Tearly Ttotal,
          m ∈ {m : ℕ | valuationVector (orbit m t) n ∈ geomPersistenceEvent collatzAlpha c n}}
      ≤ ∑ t ∈ Ico Tearly Ttotal,
          ((Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n : ℝ)))
              + Kfuture.A * (2 : ℝ) ^ (-(Kfuture.c1 * (n : ℝ))))
            + (Real.exp (-(theta * (sMaxNat : ℝ))) * (geomUpperMgf theta) ^ t
              + Kprefix.A * (2 : ℝ) ^ (-(Kprefix.c1 * (t : ℝ))))) := by
    refine le_trans (genEventProb_biUnion_le_sum_of_supp
      (normalizedHarmonicWindowWeight Y (Y + H)) hw_nonneg (Y + H) hw_supp (Ico Tearly Ttotal)
      (fun t => {m : ℕ | valuationVector (orbit m t) n ∈ geomPersistenceEvent collatzAlpha c n}))
      ?_
    apply Finset.sum_le_sum
    intro t htT
    have htmem := Finset.mem_Ico.mp htT
    have ht1 : 1 ≤ t := le_trans hTearly_pos htmem.1
    have hQprerel_t : (Qpre : ℝ) ≥ (2 + cPrefix) * (t : ℝ) := by
      have hcast : (t : ℝ) ≤ (Ttotal : ℝ) := by exact_mod_cast htmem.2.le
      nlinarith [hcast, hQprerel_uniform]
    have hEeq : {m : ℕ | valuationVector (orbit m t) n ∈ geomPersistenceEvent collatzAlpha c n}
        = (fun m => valuationVector (orbit m t) n) ⁻¹' geomPersistenceEvent collatzAlpha c n := rfl
    rw [hEeq]
    exact fixed_late_shift_persistence_upper_bound_normalized Y H hYpos hMpos t ht1 n hn c sMaxNat
      hsmall η hη hHη hthick c0 Q hQ1 hQrel Kfuture hKfuture hbudget_param theta hθ0 hθ1 cPrefix
      Qpre hQpre1 hQprerel_t Kprefix hKprefix hresidue_prefix
  -- Step 5: combine.
  rw [hev_eq, hset_split]
  calc genEventProb (normalizedHarmonicWindowWeight Y (Y + H))
        ({m : ℕ | ∃ t ∈ range Tearly,
              m ∈ {m : ℕ | valuationVector (orbit m t) n ∈ geomPersistenceEvent collatzAlpha c n}}
          ∪ {m : ℕ | ∃ t ∈ Ico Tearly Ttotal,
              m ∈ {m : ℕ | valuationVector (orbit m t) n
                ∈ geomPersistenceEvent collatzAlpha c n}})
      ≤ genEventProb (normalizedHarmonicWindowWeight Y (Y + H))
            {m : ℕ | ∃ t ∈ range Tearly,
                m ∈ {m : ℕ | valuationVector (orbit m t) n
                  ∈ geomPersistenceEvent collatzAlpha c n}}
          + genEventProb (normalizedHarmonicWindowWeight Y (Y + H))
              {m : ℕ | ∃ t ∈ Ico Tearly Ttotal,
                  m ∈ {m : ℕ | valuationVector (orbit m t) n
                    ∈ geomPersistenceEvent collatzAlpha c n}} :=
        genEventProb_union_le_of_supp (normalizedHarmonicWindowWeight Y (Y + H)) hw_nonneg (Y + H)
          hw_supp _ _
    _ ≤ _ := add_le_add hearly_bound hlate_bound

end TaoExternal
end EOC
