import EOC.TaoLike.LateShiftPersistence
import EOC.Periodic

/-!
# All-shifts averaged persistence (Milestone 12)

Combines Milestone 8's `early_shift_persistence_upper_bound_of_constants` (EARLY shifts, direct
joint-vector Tao transfer, no restart) and Milestone 11's `fixed_late_shift_persistence_upper_bound`
(LATE shifts, GOOD/BAD restart split) with a fresh, Tao/Collatz-independent finite-union bound
for `genEventProb`, into ONE finite-horizon theorem: under the TRUE harmonic seed law on
`[Y, Y+H)`, the probability that *some* shift `t < Ttotal` has its length-`n` future valuation
block persist below `c` is bounded by a finite sum of per-shift Tao/iid error terms.

**EPISTEMIC STATUS.** FORMALLY VERIFIED *conditional on* the external Tao mixing witnesses
`Kearly, Kfuture, Kprefix` (with their defining `TaoMixingProperty`) and their residue-closeness
/ information-budget hypotheses — the same kind of explicit external hypothesis Milestone 11
already required, now stated uniformly over the whole finite shift range rather than per shift.
This is a FINITE, INTEGER-HORIZON theorem: no logarithmic/dyadic substitution, no polynomial
`Y^(-γ)` conversion, no Borel–Cantelli, no density-zero conclusion, no pointwise EOC, no FOP, no
Collatz conjecture.
-/

namespace EOC
namespace TaoExternal

open Finset

/-! ## Part 0: the all-shifts persistence event -/

/-- **All-shifts persistence event.** The set of seeds `m` for which *some* shift `t < T` has
its restarted length-`n` future valuation block persist below `c`. -/
def allShiftsPersistenceEvent (T n : ℕ) (c : ℝ) : Set ℕ :=
  {m : ℕ | ∃ t < T, valuationVector (orbit m t) n ∈ geomPersistenceEvent collatzAlpha c n}

/-! ## Part 1: generic finite-union bound for `genEventProb` (Tao/Collatz-independent) -/

/-- **Finite union bound.** For a finitely-supported nonnegative weight `w`, the probability of
`∃ t ∈ Tset, m ∈ E t` is at most the sum, over `Tset`, of the individual event probabilities —
a plain finite-combinatorics fact about `genEventProb`, with no reference to Tao's hypothesis or
any Collatz-specific structure. -/
theorem genEventProb_biUnion_le_sum_of_supp (w : ℕ → ℝ) (hw_nonneg : ∀ m, 0 ≤ w m) (Nwin : ℕ)
    (hw_supp : Function.support w ⊆ ↑(range Nwin)) (Tset : Finset ℕ) (E : ℕ → Set ℕ) :
    genEventProb w {m : ℕ | ∃ t ∈ Tset, m ∈ E t} ≤ ∑ t ∈ Tset, genEventProb w (E t) := by
  rw [genEventProb_eq_finsum_of_supp w Nwin hw_supp {m | ∃ t ∈ Tset, m ∈ E t}]
  have heach : ∀ t ∈ Tset, genEventProb w (E t) = ∑ m ∈ range Nwin, Set.indicator (E t) w m :=
    fun t _ => genEventProb_eq_finsum_of_supp w Nwin hw_supp (E t)
  rw [Finset.sum_congr rfl heach, Finset.sum_comm]
  apply Finset.sum_le_sum
  intro m _
  by_cases hm : m ∈ {m : ℕ | ∃ t ∈ Tset, m ∈ E t}
  · obtain ⟨t0, ht0T, ht0E⟩ := hm
    have hmem : m ∈ {m : ℕ | ∃ t ∈ Tset, m ∈ E t} := ⟨t0, ht0T, ht0E⟩
    calc Set.indicator {m : ℕ | ∃ t ∈ Tset, m ∈ E t} w m
        = w m := Set.indicator_of_mem hmem w
      _ = Set.indicator (E t0) w m := (Set.indicator_of_mem ht0E w).symm
      _ ≤ ∑ t ∈ Tset, Set.indicator (E t) w m :=
          Finset.single_le_sum (fun t _ => Set.indicator_nonneg (fun x _ => hw_nonneg x) m) ht0T
  · rw [Set.indicator_of_notMem hm]
    apply Finset.sum_nonneg
    intro t _
    exact Set.indicator_nonneg (fun x _ => hw_nonneg x) m

/-! ## Part 2: EARLY-shift event matching -/

/-- **Orbit flow / restart compatibility.** The length-`n` suffix of the length-`(t+n)`
valuation vector is exactly the length-`n` valuation vector of the restarted state
`orbit m t` — via the orbit flow property `orbit_add`. -/
theorem suffixVector_valuationVector_eq (m t n : ℕ) :
    suffixVector t n (valuationVector m (t + n)) = valuationVector (orbit m t) n := by
  funext i
  unfold suffixVector valuationVector
  have hcoe : (Fin.natAdd t i : ℕ) = t + i := by simp
  rw [hcoe, orbit_add m t i]

/-- **EARLY-shift event identification.** `early_shift_persistence_upper_bound_of_constants`'s
pushforward event coincides exactly with the per-shift event used in
`allShiftsPersistenceEvent`. -/
theorem pushforward_jointShifted_eq_shiftEvent (w : ℕ → ℝ) (t n : ℕ) (c : ℝ) :
    pushforward (genEventProb w) (fun m => valuationVector m (t + n))
        (jointShiftedPersistenceEvent t n c)
      = genEventProb w
          {m : ℕ | valuationVector (orbit m t) n ∈ geomPersistenceEvent collatzAlpha c n} := by
  unfold pushforward jointShiftedPersistenceEvent
  congr 1
  ext m
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  rw [suffixVector_valuationVector_eq m t n]

/-- The harmonic window weight vanishes off the odd naturals, so its total mass is unaffected by
restricting to `{m | ¬ Odd m}`. -/
theorem harmonicWindowWeight_odd_zero (Y H : ℕ) :
    genEventProb (harmonicWindowWeight Y (Y + H)) {m : ℕ | ¬ Odd m} = 0 := by
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

/-! ## Part 3: the EARLY-shift true bound -/

/-- **EARLY-shift true bound.** Under the TRUE harmonic seed law on `[Y, Y+H)`, direct
joint-vector Tao transfer (Milestone 8, fixed-witness form) bounds the probability that the
length-`n` future valuation block after `t` accelerated steps persists — for a *fixed* early
shift `t`, no restart, no GOOD/BAD split. `Kearly` is supplied by the caller and reused
identically across every early shift. -/
theorem early_shift_true_bound
    (Y H : ℕ) (c0 : ℝ) (Kearly : TaoMixingConstants c0) (hKearly : TaoMixingProperty c0 Kearly)
    (Qearly : ℕ) (t n : ℕ) (hn : 1 ≤ n) (c : ℝ)
    (hQrel : (Qearly : ℝ) ≥ (2 + c0) * ((t + n : ℕ) : ℝ))
    (hresidue_early : taoL1TV (pushforward (genEventProb (harmonicWindowWeight Y (Y + H)))
        (fun m => (m : ZMod (2 ^ Qearly)))) (unifOddResidues Qearly)
      ≤ Kearly.Cres * (2 : ℝ) ^ (-(Qearly : ℝ))) :
    genEventProb (harmonicWindowWeight Y (Y + H))
        {m : ℕ | valuationVector (orbit m t) n ∈ geomPersistenceEvent collatzAlpha c n}
      ≤ Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n : ℝ)))
        + Kearly.A * (2 : ℝ) ^ (-(Kearly.c1 * ((t + n : ℕ) : ℝ))) := by
  have hw_nonneg := harmonicWindowWeight_nonneg Y (Y + H)
  have hw_supp := harmonicWindowWeight_supp Y (Y + H)
  have htransfer := early_shift_persistence_upper_bound_of_constants c0 Kearly hKearly
    (harmonicWindowWeight Y (Y + H)) hw_nonneg (Y + H) hw_supp (harmonicWindowWeight_odd_zero Y H)
    t n hn c Qearly hQrel hresidue_early
  rwa [pushforward_jointShifted_eq_shiftEvent] at htransfer

/-! ## Part 4: the combined integer-horizon theorem -/

/-- **All-shifts averaged persistence, finite integer horizon.** Under the TRUE harmonic seed
law on `[Y, Y+H)`, the probability that *some* shift `t < Ttotal` has its restarted length-`n`
future valuation block persist below `c` is bounded by the sum of the EARLY-range per-shift
Tao/iid bounds (`t < Tearly`, direct joint-vector transfer, Milestone 8) plus the LATE-range
per-shift Tao/iid bounds (`Tearly ≤ t < Ttotal`, GOOD/BAD restart split, Milestone 11).

`Kearly` is reused, unmodified, across every early shift; `Kfuture` and `Kprefix` are reused,
unmodified, across every late shift. Every per-shift hypothesis of the two underlying theorems
that does not genuinely depend on `t` (residue-closeness, information budget, window thickness,
normalization) is stated ONCE, uniformly over the whole shift range, and the two hypotheses
that do depend on `t` (`hQrel` for EARLY, `hQprerel` for LATE) are derived here from a single
uniform bound via monotonicity in `t`. -/
theorem all_shifts_averaged_persistence_finite
    (Y H : ℕ) (hYpos : 0 < Y)
    (Tearly Ttotal : ℕ) (hTearly_pos : 1 ≤ Tearly) (hTle : Tearly ≤ Ttotal)
    (n : ℕ) (hn : 1 ≤ n) (c : ℝ)
    (sMaxNat : ℕ) (hsmall : 2 ^ (sMaxNat + 1) ≤ Y)
    (η : ℝ) (hη : 0 < η) (hHη : η * (Y : ℝ) ≤ (H : ℝ))
    (hthick : 4 * (2 : ℝ) ^ (sMaxNat + 1) ≤ η * (Y : ℝ))
    (hnorm : genEventProb (harmonicWindowWeight Y (Y + H)) Set.univ = 1)
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
        (pushforward (genEventProb (harmonicWindowWeight Y (Y + H)))
          (fun m => (m : ZMod (2 ^ Qpre))))
        (unifOddResidues Qpre)
      ≤ Kprefix.Cres * (2 : ℝ) ^ (-(Qpre : ℝ)))
    -- EARLY parameters, uniform over the whole early range via `hQrel_early_uniform`:
    (c0early : ℝ) (hc0early : 0 < c0early)
    (Kearly : TaoMixingConstants c0early) (hKearly : TaoMixingProperty c0early Kearly)
    (Qearly : ℕ)
    (hQrel_early_uniform : (Qearly : ℝ) ≥ (2 + c0early) * ((Tearly + n : ℕ) : ℝ))
    (hresidue_early : taoL1TV (pushforward (genEventProb (harmonicWindowWeight Y (Y + H)))
        (fun m => (m : ZMod (2 ^ Qearly)))) (unifOddResidues Qearly)
      ≤ Kearly.Cres * (2 : ℝ) ^ (-(Qearly : ℝ))) :
    genEventProb (harmonicWindowWeight Y (Y + H)) (allShiftsPersistenceEvent Ttotal n c)
      ≤ ∑ t ∈ range Tearly, (Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n : ℝ)))
            + Kearly.A * (2 : ℝ) ^ (-(Kearly.c1 * ((t + n : ℕ) : ℝ))))
        + ∑ t ∈ Ico Tearly Ttotal,
            ((Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n : ℝ)))
                + Kfuture.A * (2 : ℝ) ^ (-(Kfuture.c1 * (n : ℝ))))
              + (Real.exp (-(theta * (sMaxNat : ℝ))) * (geomUpperMgf theta) ^ t
                + Kprefix.A * (2 : ℝ) ^ (-(Kprefix.c1 * (t : ℝ))))) := by
  classical
  have hw_nonneg := harmonicWindowWeight_nonneg Y (Y + H)
  have hw_supp := harmonicWindowWeight_supp Y (Y + H)
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
  have hearly_bound : genEventProb (harmonicWindowWeight Y (Y + H))
      {m : ℕ | ∃ t ∈ range Tearly,
          m ∈ {m : ℕ | valuationVector (orbit m t) n ∈ geomPersistenceEvent collatzAlpha c n}}
      ≤ ∑ t ∈ range Tearly, (Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n : ℝ)))
          + Kearly.A * (2 : ℝ) ^ (-(Kearly.c1 * ((t + n : ℕ) : ℝ)))) := by
    refine le_trans (genEventProb_biUnion_le_sum_of_supp (harmonicWindowWeight Y (Y + H))
      hw_nonneg (Y + H) hw_supp (range Tearly)
      (fun t => {m : ℕ | valuationVector (orbit m t) n ∈ geomPersistenceEvent collatzAlpha c n}))
      ?_
    apply Finset.sum_le_sum
    intro t htT
    have htTearly : t < Tearly := Finset.mem_range.mp htT
    have hQrel_t : (Qearly : ℝ) ≥ (2 + c0early) * ((t + n : ℕ) : ℝ) := by
      have hcast : ((t + n : ℕ) : ℝ) ≤ ((Tearly + n : ℕ) : ℝ) := by
        exact_mod_cast Nat.add_le_add_right (le_of_lt htTearly) n
      nlinarith [hcast, hQrel_early_uniform]
    exact early_shift_true_bound Y H c0early Kearly hKearly Qearly t n hn c hQrel_t hresidue_early
  -- Step 4: bound the LATE piece.
  have hlate_bound : genEventProb (harmonicWindowWeight Y (Y + H))
      {m : ℕ | ∃ t ∈ Ico Tearly Ttotal,
          m ∈ {m : ℕ | valuationVector (orbit m t) n ∈ geomPersistenceEvent collatzAlpha c n}}
      ≤ ∑ t ∈ Ico Tearly Ttotal,
          ((Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n : ℝ)))
              + Kfuture.A * (2 : ℝ) ^ (-(Kfuture.c1 * (n : ℝ))))
            + (Real.exp (-(theta * (sMaxNat : ℝ))) * (geomUpperMgf theta) ^ t
              + Kprefix.A * (2 : ℝ) ^ (-(Kprefix.c1 * (t : ℝ))))) := by
    refine le_trans (genEventProb_biUnion_le_sum_of_supp (harmonicWindowWeight Y (Y + H))
      hw_nonneg (Y + H) hw_supp (Ico Tearly Ttotal)
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
    exact fixed_late_shift_persistence_upper_bound Y H hYpos t ht1 n hn c sMaxNat hsmall η hη hHη
      hthick hnorm c0 Q hQ1 hQrel Kfuture hKfuture hbudget_param theta hθ0 hθ1 cPrefix Qpre hQpre1
      hQprerel_t Kprefix hKprefix hresidue_prefix
  -- Step 5: combine.
  rw [hev_eq, hset_split]
  calc genEventProb (harmonicWindowWeight Y (Y + H))
        ({m : ℕ | ∃ t ∈ range Tearly,
              m ∈ {m : ℕ | valuationVector (orbit m t) n ∈ geomPersistenceEvent collatzAlpha c n}}
          ∪ {m : ℕ | ∃ t ∈ Ico Tearly Ttotal,
              m ∈ {m : ℕ | valuationVector (orbit m t) n
                ∈ geomPersistenceEvent collatzAlpha c n}})
      ≤ genEventProb (harmonicWindowWeight Y (Y + H))
            {m : ℕ | ∃ t ∈ range Tearly,
                m ∈ {m : ℕ | valuationVector (orbit m t) n
                  ∈ geomPersistenceEvent collatzAlpha c n}}
          + genEventProb (harmonicWindowWeight Y (Y + H))
              {m : ℕ | ∃ t ∈ Ico Tearly Ttotal,
                  m ∈ {m : ℕ | valuationVector (orbit m t) n
                    ∈ geomPersistenceEvent collatzAlpha c n}} :=
        genEventProb_union_le_of_supp (harmonicWindowWeight Y (Y + H)) hw_nonneg (Y + H) hw_supp _ _
    _ ≤ _ := add_le_add hearly_bound hlate_bound

end TaoExternal
end EOC
