import EOC.CurryInterface

/-!
# Discharging `PowerSavingImpliesSummable`: the dyadic summation

This is Curry's Proposition 3.1 *given* his Theorem 2.3 — the three-line step
"sum Theorem 2.3 over dyadic blocks", formalized.

```
#(𝒪 ∩ [2^k, 2^{k+1}))  ≤  C·2^{kβ}(k+1)log 2 ,        β < 1
⟹   Σ_{m ∈ 𝒪 ∩ [2^k,2^{k+1})} 1/m  ≤  C·log2·(k+1)·(2^{β}/2)^k
⟹   Σ_{m ∈ 𝒪} 1/m  <  ∞ ,
```

and injectivity of the orbit turns the value-set sum into the orbit-indexed sum
`Σ_n 1/y_n` that `ReciprocalSummable` names.

**What this does and does not do.** It removes one item from the list of unformalized inputs. It is
*not* a new exclusion mechanism and does not touch the open arithmetic target. After it, the
explicit external input in this part of the chain is exactly **Curry's windowed sparsity theorem
itself** (`CurryInterface.WindowedSparsity`), audited on paper in
`docs/CURRY_INDEPENDENT_AUDIT.md` and still not formalized.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace PowerSavingSummable

open CurryFoundation CurryInterface HarmonicPacking Finset

/-! ## 1. Two small arithmetic bridges -/

/-- `(2^k)^β = (2^β)^k`: a natural power under an `rpow` is an `rpow` under a natural power. -/
private theorem pow_rpow_comm (k : ℕ) (β : ℝ) : ((2 : ℝ) ^ k) ^ β = ((2 : ℝ) ^ β) ^ k := by
  rw [← Real.rpow_natCast (2 : ℝ) k, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_natCast ((2 : ℝ) ^ β) k, ← Real.rpow_mul (by norm_num)]
  ring_nf

/-- `log(2·2^k) = (k+1)·log 2`. -/
private theorem log_two_mul_pow (k : ℕ) :
    Real.log (2 * (2 : ℝ) ^ k) = ((k : ℝ) + 1) * Real.log 2 := by
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  ring

/-! ## 2. The dyadic block of a positive integer

`Nat.log 2 m = k` exactly pins `m` to `[2^k, 2^{k+1})`, which is the window Theorem 2.3 is applied
to. -/

private theorem mem_block {m : ℕ} (hm : 1 ≤ m) :
    2 ^ Nat.log 2 m ≤ m ∧ m < 2 ^ Nat.log 2 m + 2 ^ Nat.log 2 m := by
  refine ⟨Nat.pow_log_le_self 2 (by omega), ?_⟩
  have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) m
  have hp : (2 : ℕ) ^ (Nat.log 2 m + 1) = 2 ^ Nat.log 2 m + 2 ^ Nat.log 2 m := by
    rw [pow_succ]; ring
  omega

/-! ## 3. The dyadic summation -/

/-- **Curry Proposition 3.1, given Theorem 2.3.**

A power-saving count on the value set of a divergent positive accelerated orbit gives reciprocal
summability of the orbit-indexed series. -/
theorem powerSaving_implies_summable : PowerSavingImpliesSummable := by
  rintro M hM hdiv ⟨β, hβ1, C, hC0, hcount⟩
  have hinj : ∀ i j, orbit M i = orbit M j → i = j :=
    (injective_iff_divergent M).mpr hdiv
  have hpos : ∀ i, 1 ≤ orbit M i := fun i => (odd_orbit hM i).pos
  -- the geometric ratio
  set ρ : ℝ := (2 : ℝ) ^ β with hρdef
  have hρpos : 0 < ρ := Real.rpow_pos_of_pos (by norm_num) β
  have hρlt : ρ < 2 := by
    have : (2 : ℝ) ^ β < (2 : ℝ) ^ (1 : ℝ) :=
      (Real.rpow_lt_rpow_left_iff (by norm_num)).mpr hβ1
    rwa [Real.rpow_one] at this
  set q : ℝ := ρ / 2 with hqdef
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by rw [hqdef]; linarith
  -- the majorant
  set w : ℕ → ℝ := fun k => C * Real.log 2 * (((k : ℝ) + 1) * q ^ k) with hwdef
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hwnonneg : ∀ k, 0 ≤ w k := by
    intro k; rw [hwdef]; have : (0:ℝ) ≤ q ^ k := pow_nonneg hq0 k; positivity
  have hwsum : Summable w := by
    have h1 : Summable (fun k : ℕ => ((k : ℝ) + 1) * q ^ k) := by
      have ha : Summable (fun k : ℕ => (k : ℝ) ^ 1 * q ^ k) :=
        summable_pow_mul_geometric_of_norm_lt_one 1 (by rwa [Real.norm_eq_abs, abs_of_nonneg hq0])
      have hb : Summable (fun k : ℕ => q ^ k) :=
        summable_geometric_of_lt_one hq0 hq1
      simpa [pow_one, add_mul] using ha.add hb
    exact h1.mul_left _
  -- the uniform bound on partial sums
  refine summable_of_sum_range_le (c := 1 + ∑' k, w k) (fun n => by positivity) ?_
  intro n
  -- split `range n` into dyadic fibres
  set K : ℕ := (range n).sup (fun i => Nat.log 2 (orbit M i)) + 1 with hKdef
  have hmaps : ∀ i ∈ range n, Nat.log 2 (orbit M i) ∈ range K := by
    intro i hi
    rw [mem_range, hKdef]
    exact Nat.lt_succ_of_le (Finset.le_sup (f := fun i => Nat.log 2 (orbit M i)) hi)
  have hsplit := Finset.sum_fiberwise_of_maps_to hmaps (fun i => 1 / (orbit M i : ℝ))
  rw [← hsplit]
  -- bound each fibre
  have hfib : ∀ k ∈ range K,
      (∑ i ∈ (range n).filter (fun i => Nat.log 2 (orbit M i) = k), 1 / (orbit M i : ℝ))
        ≤ (if k = 0 then 1 else w k) := by
    intro k _
    set F : Finset ℕ := (range n).filter (fun i => Nat.log 2 (orbit M i) = k) with hFdef
    -- every element of the fibre has value in `[2^k, 2^k + 2^k)`
    have hval : ∀ i ∈ F, 2 ^ k ≤ orbit M i ∧ orbit M i < 2 ^ k + 2 ^ k := by
      intro i hi
      have hk : Nat.log 2 (orbit M i) = k := (Finset.mem_filter.mp hi).2
      have := mem_block (hpos i)
      rw [hk] at this
      exact this
    -- so each term is at most `2^{-k}`
    have hterm : ∀ i ∈ F, 1 / (orbit M i : ℝ) ≤ 1 / (2 : ℝ) ^ k := by
      intro i hi
      have h1 : ((2 : ℝ) ^ k) ≤ (orbit M i : ℝ) := by exact_mod_cast (hval i hi).1
      exact one_div_le_one_div_of_le (by positivity) h1
    have hsum_le : (∑ i ∈ F, 1 / (orbit M i : ℝ)) ≤ (F.card : ℝ) * (1 / (2 : ℝ) ^ k) := by
      calc (∑ i ∈ F, 1 / (orbit M i : ℝ)) ≤ ∑ _i ∈ F, 1 / (2 : ℝ) ^ k :=
            Finset.sum_le_sum hterm
        _ = (F.card : ℝ) * (1 / (2 : ℝ) ^ k) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    by_cases hk0 : k = 0
    · -- block `0` is `{1}`, so injectivity gives at most one index
      subst hk0
      rw [if_pos rfl]
      have hone : ∀ i ∈ F, orbit M i = 1 := by
        intro i hi; have := hval i hi; simp only [pow_zero] at this; omega
      have hcard : F.card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha b hb
        exact hinj a b ((hone a ha).trans (hone b hb).symm)
      have : (F.card : ℝ) ≤ 1 := by exact_mod_cast hcard
      calc (∑ i ∈ F, 1 / (orbit M i : ℝ)) ≤ (F.card : ℝ) * (1 / (2 : ℝ) ^ 0) := hsum_le
        _ ≤ 1 := by simpa using this
    · -- blocks `k ≥ 1`: apply the counting hypothesis at `a = X = 2^k`
      simp only [if_neg hk0]
      have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      have h2k : 2 ≤ 2 ^ k := by
        calc (2:ℕ) = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
      set T : Set ℕ := Set.range (orbit M) ∩ Set.Ico (2 ^ k) (2 ^ k + 2 ^ k) with hTdef
      have hTfin : T.Finite := Set.Finite.subset (Set.finite_Ico _ _) (Set.inter_subset_right)
      -- the fibre injects into `T`
      have hsub : F.image (orbit M) ⊆ hTfin.toFinset := by
        intro x hx
        rw [Finset.mem_image] at hx
        obtain ⟨i, hi, rfl⟩ := hx
        rw [Set.Finite.mem_toFinset, hTdef]
        exact ⟨⟨i, rfl⟩, (hval i hi).1, (hval i hi).2⟩
      have hcardF : (F.card : ℝ) ≤ (T.ncard : ℝ) := by
        have h1 : F.card = (F.image (orbit M)).card :=
          (Finset.card_image_of_injOn (fun a _ b _ h => hinj a b h)).symm
        have h2 : (F.image (orbit M)).card ≤ hTfin.toFinset.card := Finset.card_le_card hsub
        have h3 : hTfin.toFinset.card = T.ncard := (Set.ncard_eq_toFinset_card T hTfin).symm
        exact_mod_cast h1 ▸ (h2.trans_eq h3)
      -- the counting hypothesis, rewritten
      have hC := hcount (2 ^ k) (2 ^ k) (by omega) h2k
      have hcast : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by push_cast; ring
      rw [hcast] at hC
      rw [show ((2:ℕ) ^ k + 2 ^ k) = (2:ℕ) ^ k + 2 ^ k from rfl] at hC
      have hCT : (T.ncard : ℝ) ≤ C * ((2 : ℝ) ^ k) ^ β * Real.log (2 * (2 : ℝ) ^ k) := by
        rw [hTdef]; exact hC
      -- assemble
      have hfinal : (F.card : ℝ) * (1 / (2 : ℝ) ^ k) ≤ w k := by
        have hstep : (F.card : ℝ) ≤ C * ρ ^ k * (((k : ℝ) + 1) * Real.log 2) := by
          calc (F.card : ℝ) ≤ (T.ncard : ℝ) := hcardF
            _ ≤ C * ((2 : ℝ) ^ k) ^ β * Real.log (2 * (2 : ℝ) ^ k) := hCT
            _ = C * ρ ^ k * (((k : ℝ) + 1) * Real.log 2) := by
                rw [pow_rpow_comm, log_two_mul_pow, hρdef]
        have hpk : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
        have : (F.card : ℝ) * (1 / (2 : ℝ) ^ k)
            ≤ (C * ρ ^ k * (((k : ℝ) + 1) * Real.log 2)) * (1 / (2 : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_right hstep (by positivity)
        refine this.trans (le_of_eq ?_)
        simp only [hwdef, hqdef, div_pow]
        field_simp
      exact hsum_le.trans hfinal
  -- sum the fibre bounds
  calc (∑ k ∈ range K, ∑ i ∈ (range n).filter (fun i => Nat.log 2 (orbit M i) = k),
          1 / (orbit M i : ℝ))
      ≤ ∑ k ∈ range K, (if k = 0 then 1 else w k) := Finset.sum_le_sum hfib
    _ ≤ 1 + ∑' k, w k := by
        have hle : ∀ k ∈ range K, (if k = 0 then (1:ℝ) else w k) ≤ (if k = 0 then 1 else 0) + w k := by
          intro k _
          by_cases hk : k = 0
          · simp [hk, hwnonneg 0]
          · simp [hk]
        refine (Finset.sum_le_sum hle).trans ?_
        rw [Finset.sum_add_distrib]
        have hA : (∑ k ∈ range K, (if k = 0 then (1:ℝ) else 0)) ≤ 1 := by
          rw [Finset.sum_ite_eq' (range K) 0 (fun _ => (1:ℝ))]
          split <;> norm_num
        have hB : (∑ k ∈ range K, w k) ≤ ∑' k, w k :=
          hwsum.sum_le_tsum _ (fun i _ => hwnonneg i)
        linarith

/-- **With the bridge discharged**, Curry's windowed sparsity theorem alone yields the reciprocal
summability the divergence reduction consumes. -/
theorem curry_summability_of_windowed' (hws : WindowedSparsity) : CurryReciprocalSummability :=
  curry_summability_of_windowed powerSaving_implies_summable hws

/-- **The reduction, with the windowed sparsity theorem as the only external input.**

If no positive odd seed is zero-confined at every horizon, then no positive accelerated orbit
diverges.

**Two hypotheses, of different kinds — do not conflate them.**

* `hws : WindowedSparsity` is the **external theorem** (Curry Thm 2.3): audited on paper in
  `docs/CURRY_INDEPENDENT_AUDIT.md`, not formalized. Formalizing it would remove the external
  dependency.
* `hDE` is the **open mathematical hypothesis** — universal drift exit, i.e. the divergence target
  itself. Nothing here discharges it, and formalizing Curry's theorem would not.

So this theorem is a *reduction*, not an exclusion: it converts "no zero-confined positive seed"
into "no divergent orbit", given an audited external counting theorem. -/
theorem no_divergent_orbit_of_windowed (hws : WindowedSparsity)
    (hDE : ∀ m0 : ℕ, Odd m0 → ∃ N, ¬ Confined 0 (orbWord m0) N)
    {M : ℕ} (hM : Odd M) : ¬ DivergentOrbit M :=
  no_divergent_orbit_of_universal_drift_exit (curry_summability_of_windowed' hws) hDE hM

end PowerSavingSummable
end EOC
