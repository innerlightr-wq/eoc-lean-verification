import EOC.TaoLike.ConditionalMixing

/-!
# Prefix partition / conditional restart bridge (Milestone 9)

Investigates and formalizes the missing bridge identified as Milestone 8's LATE obstruction:
Milestone 7's `conditional_shifted_persistence_upper_bound[_bits]` is a statement about ONE
fixed realized prefix/restart cylinder `(d, t, r)`; there was no theorem connecting that
fixed-prefix conditional restart law back to a genuine global starting-seed law through a
finite law-of-total-probability decomposition over realized prefixes.

This file is deterministic finite probability/cylinder bookkeeping. It does **not** use
`TaoMixingHypothesis` anywhere (no mixing claim is needed to prove a partition identity), does
**not** prove the late-shift persistence theorem, and does **not** prove any union-over-shifts
or logarithmic-density statement — those remain for later milestones.
-/

namespace EOC
namespace TaoExternal

open Finset

/-! ## Part 1: finite prefix partition and prefix mass (generic global weight `w`)

`genEventProb_pushforward_fiber_general` (Milestone 5) already IS the fiber/partition
statement specialized to `F := fun m => valuationVector m t`: it expresses
`pushforward (genEventProb w) (valuationVector · t)` as `genEventProb` of exactly the
fiber-sum ("prefix mass") weight below. No new partition lemma needs to be (re-)proved. -/

/-- The **prefix mass**: the total `w`-weight of odd-support seeds `m < Nwin` realizing the
length-`t` valuation prefix `v`. -/
noncomputable def prefixMass (w : ℕ → ℝ) (Nwin t : ℕ) (v : Fin t → ℕ) : ℝ :=
  ∑ j ∈ range Nwin, if valuationVector j t = v then w j else 0

theorem pushforward_eq_genEventProb_prefixMass (Nwin t : ℕ) (w : ℕ → ℝ)
    (hw_supp : Function.support w ⊆ ↑(range Nwin)) :
    pushforward (genEventProb w) (fun m => valuationVector m t)
      = genEventProb (prefixMass w Nwin t) :=
  genEventProb_pushforward_fiber_general Nwin w hw_supp (fun m => valuationVector m t)

/-- **Prefix mass normalization**: if the global law has total mass `1`, the prefix masses sum
to `1` over the (finitely many) realized prefixes. Immediate from
`pushforward_eq_genEventProb_prefixMass` applied to `Set.univ`, plus `genEventProb_univ`. -/
theorem prefixMass_tsum_eq_one (Nwin t : ℕ) (w : ℕ → ℝ)
    (hw_supp : Function.support w ⊆ ↑(range Nwin))
    (hw_univ : genEventProb w Set.univ = 1) :
    ∑' v : Fin t → ℕ, prefixMass w Nwin t v = 1 := by
  have h := congrFun (pushforward_eq_genEventProb_prefixMass Nwin t w hw_supp) Set.univ
  have hlhs : pushforward (genEventProb w) (fun m => valuationVector m t) Set.univ
      = genEventProb w Set.univ := by
    unfold pushforward
    rw [Set.preimage_univ]
  rw [hlhs, hw_univ] at h
  unfold genEventProb at h
  simpa using h.symm

/-! ## Part 2: the conditional law on one prefix cylinder -/

/-- The **normalized conditional weight** on the prefix cylinder `{m | valuationVector m t = v}`
(zero elsewhere). -/
noncomputable def prefixConditionalWeight (w : ℕ → ℝ) (Nwin t : ℕ) (v : Fin t → ℕ) (m : ℕ) : ℝ :=
  (if valuationVector m t = v then w m else 0) / prefixMass w Nwin t v

/-- **Finite conditional-probability identity.** `genEventProb` of the normalized conditional
weight recovers exactly `P(E ∩ cylinder) / P(cylinder)`, for every event `E` — no positivity
hypothesis is needed (both sides are `0` when the mass is `0`, by real division convention). -/
theorem genEventProb_prefixConditionalWeight_eq (w : ℕ → ℝ) (Nwin t : ℕ) (v : Fin t → ℕ)
    (E : Set ℕ) :
    genEventProb (prefixConditionalWeight w Nwin t v) E
      = genEventProb w (E ∩ {m | valuationVector m t = v}) / prefixMass w Nwin t v := by
  unfold genEventProb prefixConditionalWeight
  have hpt : ∀ m, Set.indicator E (fun m => (if valuationVector m t = v then w m else 0)
        / prefixMass w Nwin t v) m
      = Set.indicator (E ∩ {m | valuationVector m t = v}) w m / prefixMass w Nwin t v := by
    intro m
    by_cases hmE : m ∈ E
    · by_cases hmv : valuationVector m t = v
      · simp [Set.indicator, hmE, hmv, Set.mem_inter_iff]
      · simp [Set.indicator, hmE, hmv, Set.mem_inter_iff]
    · simp [Set.indicator, hmE, Set.mem_inter_iff]
  simp_rw [hpt, div_eq_mul_inv]
  rw [tsum_mul_right]

/-! ## Part 3: law of total probability and GOOD-prefix aggregation -/

/-- `genEventProb` of the `E`-restricted weight recovers `P(E ∩ S)` for any set `S` — the
general identity making the rest of this section a matter of bookkeeping, not new probability
theory. -/
theorem genEventProb_indicator_inter (w : ℕ → ℝ) (E S : Set ℕ) :
    genEventProb (Set.indicator E w) S = genEventProb w (E ∩ S) := by
  unfold genEventProb
  congr 1
  funext m
  by_cases hS : m ∈ S <;> by_cases hE : m ∈ E <;>
    simp [Set.indicator, hS, hE, Set.mem_inter_iff]

/-- The joint mass of `E` and a prefix cylinder, expressed as the prefix mass of the
`E`-restricted weight. -/
theorem prefixMass_indicator_eq (w : ℕ → ℝ) (Nwin t : ℕ)
    (hw_supp : Function.support w ⊆ ↑(range Nwin)) (v : Fin t → ℕ) (E : Set ℕ) :
    prefixMass (Set.indicator E w) Nwin t v
      = genEventProb w (E ∩ {m | valuationVector m t = v}) := by
  have hsupp' : Function.support (Set.indicator E w) ⊆ ↑(range Nwin) :=
    fun m hm => hw_supp (fun h0 => hm (by simp [Set.indicator, h0]))
  have h := congrFun (pushforward_eq_genEventProb_prefixMass Nwin t (Set.indicator E w) hsupp') {v}
  unfold pushforward at h
  rw [genEventProb_indicator_inter] at h
  rw [genEventProb_singleton] at h
  rw [← h]
  congr 2

/-- **Law of total probability over prefixes.** The `E`-mass of the global law equals the sum,
over all realized prefixes, of the joint `E`-and-cylinder mass. -/
theorem genEventProb_eq_tsum_prefixMass_indicator (w : ℕ → ℝ) (Nwin t : ℕ)
    (hw_supp : Function.support w ⊆ ↑(range Nwin)) (E : Set ℕ) :
    genEventProb w E = ∑' v : Fin t → ℕ, genEventProb w (E ∩ {m | valuationVector m t = v}) := by
  have hsupp' : Function.support (Set.indicator E w) ⊆ ↑(range Nwin) :=
    fun m hm => hw_supp (fun h0 => hm (by simp [Set.indicator, h0]))
  have h := congrFun (pushforward_eq_genEventProb_prefixMass Nwin t (Set.indicator E w) hsupp')
    Set.univ
  unfold pushforward at h
  rw [Set.preimage_univ, genEventProb_indicator_inter, Set.inter_univ] at h
  rw [h]
  unfold genEventProb
  simp_rw [Set.indicator_univ]
  exact tsum_congr (fun v => prefixMass_indicator_eq w Nwin t hw_supp v E)

open Classical in
/-- **GOOD-prefix aggregation.** If the conditional `E`-probability on every positive-mass
GOOD prefix is bounded by `B`, the joint mass of `E` and the union of GOOD cylinders is
bounded by `B` times the total GOOD mass — the exact aggregation step Milestone 8 needed to
combine Milestone 7's fixed-prefix bound over all admissible prefixes. -/
theorem good_prefix_event_bound_of_conditional_bound
    (w : ℕ → ℝ) (Nwin t : ℕ) (hw_supp : Function.support w ⊆ ↑(range Nwin))
    (hw_nonneg : ∀ m, 0 ≤ w m) (Good : (Fin t → ℕ) → Prop) (E : Set ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ v : Fin t → ℕ, Good v → 0 < prefixMass w Nwin t v →
        genEventProb w (E ∩ {m | valuationVector m t = v}) ≤ B * prefixMass w Nwin t v) :
    genEventProb w (E ∩ {m | Good (valuationVector m t)})
      ≤ B * ∑' v : Fin t → ℕ, prefixMass w Nwin t v := by
  have hsupp' : Function.support (Set.indicator E w) ⊆ ↑(range Nwin) :=
    fun m hm => hw_supp (fun h0 => hm (by simp [Set.indicator, h0]))
  -- Step 1: rewrite the LHS as a sum-over-prefixes, via the E-restricted weight's prefix mass.
  have hEq : genEventProb w (E ∩ {m | Good (valuationVector m t)})
      = ∑' v : Fin t → ℕ,
          if Good v then genEventProb w (E ∩ {m | valuationVector m t = v}) else 0 := by
    rw [← genEventProb_indicator_inter]
    have h := congrFun (pushforward_eq_genEventProb_prefixMass Nwin t (Set.indicator E w) hsupp')
      {v | Good v}
    unfold pushforward at h
    have hset : (fun m => valuationVector m t) ⁻¹' {v | Good v}
        = {m | Good (valuationVector m t)} := rfl
    rw [hset] at h
    rw [h]
    unfold genEventProb
    refine tsum_congr (fun v => ?_)
    by_cases hv : Good v
    · simp only [Set.indicator, Set.mem_setOf_eq, hv, ite_true]
      exact prefixMass_indicator_eq w Nwin t hw_supp v E
    · simp only [Set.indicator, Set.mem_setOf_eq, hv, ite_false]
  rw [hEq, ← tsum_mul_left]
  -- Step 2: basic nonnegativity facts, and finite support (⊆ the realized-prefix image).
  have hmass_nonneg : ∀ v : Fin t → ℕ, 0 ≤ prefixMass w Nwin t v := by
    intro v; unfold prefixMass; apply Finset.sum_nonneg
    intro j _; split_ifs; exacts [hw_nonneg j, le_refl 0]
  have hjoint_le_mass : ∀ v : Fin t → ℕ,
      genEventProb w (E ∩ {m | valuationVector m t = v}) ≤ prefixMass w Nwin t v := by
    intro v
    rw [← prefixMass_indicator_eq w Nwin t hw_supp v E]
    unfold prefixMass
    apply Finset.sum_le_sum
    intro j _
    split_ifs with hj
    · exact Set.indicator_le_self' (fun x _ => hw_nonneg x) j
    · exact le_refl 0
  have hjoint_nonneg : ∀ v : Fin t → ℕ,
      0 ≤ genEventProb w (E ∩ {m | valuationVector m t = v}) := by
    intro v
    rw [← prefixMass_indicator_eq w Nwin t hw_supp v E]
    unfold prefixMass
    apply Finset.sum_nonneg
    intro j _; split_ifs
    · exact Set.indicator_nonneg (fun x _ => hw_nonneg x) j
    · exact le_refl 0
  set S := (range Nwin).image (fun j => valuationVector j t) with hS_def
  have hmass_zero_of_not_mem : ∀ v : Fin t → ℕ, v ∉ S → prefixMass w Nwin t v = 0 := by
    intro v hvni
    unfold prefixMass
    apply Finset.sum_eq_zero
    intro j hj
    rw [if_neg]
    intro hfj
    exact hvni (hS_def ▸ Finset.mem_image.mpr ⟨j, hj, hfj⟩)
  have hsupp_lhs : Function.support (fun v : Fin t → ℕ =>
      if Good v then genEventProb w (E ∩ {m | valuationVector m t = v}) else 0) ⊆ ↑S := by
    intro v hv
    by_contra hvni
    apply hv
    by_cases hv' : Good v
    · simp only [hv', ite_true]
      exact le_antisymm ((hmass_zero_of_not_mem v hvni) ▸ hjoint_le_mass v) (hjoint_nonneg v)
    · simp [hv']
  have hsupp_rhs : Function.support (fun v : Fin t → ℕ => B * prefixMass w Nwin t v) ⊆ ↑S := by
    intro v hv
    by_contra hvni
    apply hv
    change B * prefixMass w Nwin t v = 0
    rw [hmass_zero_of_not_mem v hvni, mul_zero]
  -- Step 3: convert to Finset sums over the finite realized-prefix image and compare termwise.
  rw [tsum_eq_sum' hsupp_lhs, tsum_eq_sum' hsupp_rhs]
  apply Finset.sum_le_sum
  intro v _
  by_cases hv : Good v
  · by_cases hpos : 0 < prefixMass w Nwin t v
    · simp only [hv, ite_true]; exact hbound v hv hpos
    · push_neg at hpos
      have hmass0 : prefixMass w Nwin t v = 0 := le_antisymm hpos (hmass_nonneg v)
      have hjoint0 : genEventProb w (E ∩ {m | valuationVector m t = v}) = 0 :=
        le_antisymm (hmass0 ▸ hjoint_le_mass v) (hjoint_nonneg v)
      simp only [hv, ite_true, hjoint0, hmass0, mul_zero, le_refl]
  · simp only [hv, ite_false]
    exact mul_nonneg hB (hmass_nonneg v)

/-! ## Part 4: exact cylinder parametrization (`Realizes d t m ↔ Odd m ∧ m ≡ r mod 2^(S d t+1)`)

Via `EOC.realizerCongruence` (Realizer.lean): realizing a length-`t` word is EXACTLY a single
congruence class modulo `2^(S d t+1)`, since `3^t` is coprime to `2^(S d t+1)` and hence
cancellable. Combined with the existing `cylinder_window_reindex` (ResidueTV.lean), this gives
the exact finite `k`-parametrization of every same-prefix seed in a window — no new
window-counting machinery needs to be built, only this congruence-class identification. -/

theorem realizes_iff_modEq (d : ℕ → ℕ) (t r m : ℕ) (hd_pos : ∀ i < t, 1 ≤ d i)
    (hr : Realizes d t r) :
    Realizes d t m ↔ Odd m ∧ m ≡ r [MOD 2 ^ (S d t + 1)] := by
  have hcop : Nat.Coprime (2 ^ (S d t + 1)) (3 ^ t) :=
    Nat.Coprime.pow (S d t + 1) t (by decide)
  have hrc_r : 3 ^ t * r + q d t ≡ 2 ^ S d t [MOD 2 ^ (S d t + 1)] :=
    (realizerCongruence d t r hr.1 hd_pos).mp hr
  constructor
  · intro hm
    refine ⟨hm.1, ?_⟩
    have hrc_m : 3 ^ t * m + q d t ≡ 2 ^ S d t [MOD 2 ^ (S d t + 1)] :=
      (realizerCongruence d t m hm.1 hd_pos).mp hm
    have heq : 3 ^ t * m + q d t ≡ 3 ^ t * r + q d t [MOD 2 ^ (S d t + 1)] :=
      hrc_m.trans hrc_r.symm
    have heq2 : 3 ^ t * m ≡ 3 ^ t * r [MOD 2 ^ (S d t + 1)] := heq.add_right_cancel' (q d t)
    exact Nat.ModEq.cancel_left_of_coprime hcop heq2
  · rintro ⟨hmodd, hmeq⟩
    apply (realizerCongruence d t m hmodd hd_pos).mpr
    have heq2 : 3 ^ t * m ≡ 3 ^ t * r [MOD 2 ^ (S d t + 1)] := hmeq.mul_left (3 ^ t)
    have heq3 : 3 ^ t * m + q d t ≡ 3 ^ t * r + q d t [MOD 2 ^ (S d t + 1)] :=
      heq2.add_right (q d t)
    exact heq3.trans hrc_r

/-- **Every reindexed cylinder point in the window realizes `d`.** The provable half of the
window parametrization: combining `cylinder_window_reindex` with `cylinder_restart` shows
every `r + 2^(S d t+1)*(kmin+j)`, `j < N`, both lies in `[Y,Z)` and realizes `d`.

**What is NOT proved (identified gap, not forced):** the converse — that every `m ∈ [Y,Z)`
realizing `d` is one of these `N` points, i.e. that `kmin, N` from `cylinder_window_reindex`
are *exhaustive*, not merely sufficient. `realizes_iff_modEq` above reduces this to `m = r +
Dcyl*k` for a unique `k`, and the remaining question is exactly `kmin ≤ k < kmin + N`. This is
mathematically true by `cylinder_window_reindex`'s construction (`kmin` is literally the
ceiling `(Y-r+Dcyl-1)/Dcyl`, `N` sized so `A0 + Dcyl*N` reaches `Z`), but the *current*
statement of `cylinder_window_reindex` packages `kmin, N` existentially and only exposes the
one-directional membership fact plus the real-valued size bound — neither is enough to derive
`k < kmin + N` from `m < Z` (or `kmin ≤ k` from `Y ≤ m`) without re-deriving the lemma's own
internal construction. Completing this exhaustiveness is the precise remaining step for the
central bridge theorem (Part 5's `E`/`possibility A` case) and would require either
strengthening `cylinder_window_reindex` (e.g. exposing `kmin`'s minimality) or a fresh
from-scratch bound; deliberately not forced here, per the "do not assume the converse" and
"do not force an equality that is mathematically false" instructions. -/
theorem cylinder_point_realizes (d : ℕ → ℕ) (t r Y Z : ℕ) (hr : Realizes d t r)
    (hYr : r ≤ Y) (hYZ : Y ≤ Z) :
    ∃ kmin N : ℕ,
      (∀ j < N, Y ≤ r + 2 ^ (S d t + 1) * (kmin + j) ∧ r + 2 ^ (S d t + 1) * (kmin + j) < Z) ∧
      (Z : ℝ) - (Y : ℝ) ≤ ((N : ℝ) + 2) * ((2 ^ (S d t + 1) : ℕ) : ℝ) ∧
      (∀ j < N, Realizes d t (r + 2 ^ (S d t + 1) * (kmin + j))) := by
  obtain ⟨kmin, N, hmem, hNlb⟩ :=
    cylinder_window_reindex r (2 ^ (S d t + 1)) Y Z (by positivity) hYr hYZ
  refine ⟨kmin, N, hmem, hNlb, fun j _ => (cylinder_restart d t r (kmin + j) hr).1⟩

end TaoExternal
end EOC
