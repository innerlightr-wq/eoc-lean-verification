import EOC.MultiWhiteContraction
import EOC.FinalChain

/-!
# The conditional chain with multi-pair white contraction

Same arithmetic input (`PowerOfTwoDangerousWindowSparsityAt`), stronger analytic engine: the rate
condition `γ j ln 2 ≤ 8 k d²/N₀` of the one-pair route is replaced by
`γ j ln 2 ≤ (4/3)(1 − cos πd)(K_b − (θ' + γ) j)`, with no `N₀` and no bad-block count `n`.

* `lowFreqDecay_of_sparsityAt_multi` — frontier ⇒ `LowFreqDecay` (constant `4`).
* `ExplicitPairDataMulti`, `weightedFourier_of_explicitMulti` — per-pair explicit data ⇒ `WeightedFourier`.
* `exceptional_bound_of_frontier_and_scalar_multi` — the exceptional-set bound with the scalar tail
  conditions of `FinalChain`/`BinomialTail`.

No `sorry`, `admit`, `axiom`, `opaque`, or `native_decide`.
-/

namespace EOC
namespace MultiWhiteChain

open Finset CapacityBounds FiniteValuationWord PrefixCollision ShellwiseChain

theorem lowFreqDecay_of_sparsityAt_multi {U j σ δ t Us K N0 Kb : ℕ} {d a b A θ' γ : ℝ}
    (hj : 300 ≤ j) (hev : 2 ∣ j) (hlo : collatzBarrier 0 j ≤ σ + δ) (hδ : δ ≤ j / 300)
    (hσ : σ ≤ collatzBarrier U j) (hq63 : 63 * σ + 37 ≤ 100 * j)
    (hK : 0 < K) (hKlog : (K : ℝ) ≤ A * Real.logb 2 j + 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : 0 ≤ A)
    (hbudget : Kb + 31 * j / 100 + σ / (N0 + 2) ≤ j / 2) (hd0 : 0 ≤ d) (hθ : 1 / 6 < θ')
    (hlarge :
      (3 * (2 + 3 / 5 * a + 4 / 5 * A + (2 + 3 / 5 * b + 4 / 5 * 1) / 8) / (θ' - 1 / 6)) ^ 2 ≤ j)
    (hγδ : γ * j ≤ ((j / 300 - δ : ℕ) : ℝ))
    (hγc : γ * j * Real.log 2 ≤ 4 * (1 - Real.cos (Real.pi * d)) / 3 * (Kb - (θ' + γ) * j))
    (h : FrontierRegion.PowerOfTwoDangerousWindowSparsityAt U j σ t Us K d a b) :
    DecayInterface.LowFreqDecay (collatzBarrier U) j σ t Us 4 γ := by
  have hlow := ShapeRegion.lower_barrier j (by omega)
  have hjσ : j < σ := by omega
  have h2 : σ + 2 ≤ 2 * j := by omega
  have hC : (0 : ℝ) ≤ 2 + 3 / 5 * a + 4 / 5 * A + (2 + 3 / 5 * b + 4 / 5 * 1) / 8 := by positivity
  have hpress := FrontierRegion.summedPressure_of_sparsityAt hj hev hjσ hσ hq63 (by omega) hK hKlog hb h
  have habs := LogAbsorb.rpow_log_absorb hC hθ (by exact_mod_cast (by omega : 0 < j)) hlarge
  have hshape := ShapeRegion.shapeTail_region (N0 := N0) (K := Kb) hj hev hlo hδ hσ h2 hbudget
  refine MultiWhite.lowFreqDecay_multi (collatzBarrier U) (M := (2 : ℝ) ^ (θ' * j))
    (Λ := (θ' + γ) * j) (by omega) (FrontierRegion.shellP_nonempty_of (by omega) hjσ.le hσ) hd0
    hshape (fun u hu => (hpress u hu).trans ?_) ?_
  · have hP : (0 : ℝ) ≤ ((PrefixCollision.shellP (collatzBarrier U) j σ).card : ℝ) :=
      Nat.cast_nonneg _
    gcongr
  · have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hρ : ((2 : ℝ) ^ (j / 300 - δ))⁻¹ ≤ (2 : ℝ) ^ (-(γ * j)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_neg (by norm_num)]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hM : (2 : ℝ) ^ (θ' * j) * (2 : ℝ) ^ (-((θ' + γ) * j)) = (2 : ℝ) ^ (-(γ * j)) := by
      rw [← Real.rpow_add (by norm_num)]; congr 1; ring
    have hE : Real.exp (-(4 * (1 - Real.cos (Real.pi * d)) / 3 * (Kb - (θ' + γ) * j))) ≤
        (2 : ℝ) ^ (-(γ * j)) := by
      rw [Real.rpow_def_of_pos (by norm_num)]
      apply Real.exp_le_exp.mpr
      nlinarith
    have hp : (0 : ℝ) ≤ (2 : ℝ) ^ (-(γ * j)) := by positivity
    linarith

/-- **Per-pair explicit data, multi-pair engine.** -/
def ExplicitPairDataMulti (U N j s σ : ℕ) (ε : ℝ) : Prop :=
  ∃ (δ K N0 Kb : ℕ) (d ca cb A θ' γ : ℝ),
    300 ≤ j ∧ 2 ∣ j ∧ collatzBarrier 0 j ≤ σ + δ ∧ δ ≤ j / 300 ∧ σ ≤ collatzBarrier U j ∧
    63 * σ + 37 ≤ 100 * j ∧ 0 < K ∧ (K : ℝ) ≤ A * Real.logb 2 j + 1 ∧ 0 ≤ ca ∧ 0 ≤ cb ∧
    0 ≤ A ∧ Kb + 31 * j / 100 + σ / (N0 + 2) ≤ j / 2 ∧ 0 ≤ d ∧ 1 / 6 < θ' ∧
    (3 * (2 + 3 / 5 * ca + 4 / 5 * A + (2 + 3 / 5 * cb + 4 / 5 * 1) / 8) / (θ' - 1 / 6)) ^ 2 ≤ j ∧
    γ * j ≤ ((j / 300 - δ : ℕ) : ℝ) ∧
    γ * j * Real.log 2 ≤ 4 * (1 - Real.cos (Real.pi * d)) / 3 * (Kb - (θ' + γ) * j) ∧
    j < N ∧ σ ≤ s ∧ N - j ≤ s - σ ∧ s - σ ≤ collatzBarrier U N - σ ∧ U ≤ σ ∧
    (1 + ((σ + 1 : ℕ) : ℝ) / 2) * (((σ + (s - σ) : ℕ) : ℝ) + 1) * 4 * 4 ^ (s - σ) *
        ((N - j : ℕ) : ℝ) ≤
      ε ^ 2 * (Nat.choose (s - σ - 1) (N - j - 1) : ℝ) * (2 : ℝ) ^ (γ * j) ∧
    FrontierRegion.PowerOfTwoDangerousWindowSparsityAt U j σ (s - σ) (σ + (s - σ)) K d ca cb

theorem weightedFourier_of_explicitMulti {U N j s σ : ℕ} {ε : ℝ}
    (h : ExplicitPairDataMulti U N j s σ ε) :
    WeightedChain.WeightedFourier (collatzBarrier U) N j s σ ε := by
  obtain ⟨δ, K, N0, Kb, d, ca, cb, A, θ', γ, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    h13, h14, h15, h16, h17, hjN, hσs, hLt, ht, hU, hnum, hfr⟩ := h
  have hdecay := lowFreqDecay_of_sparsityAt_multi h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
    h15 h16 h17 hfr
  exact DecayInterface.weightedFourier_of_lowFreqDecay_and_sieve (collatzBarrier U) N j s σ
    (σ + (s - σ)) ε 4 γ (fun _ => 1) (fun _ _ => le_rfl) (fun _ _ => show 1 < j by omega)
    (fun _ _ => FinalChain.hX_one (by omega)) hdecay
    (ConditionalChain.hfin_of_split (collatzBarrier U) N j s σ (σ + (s - σ)) ε 4 γ (by norm_num)
      (fun _ => 1) (FinalChain.hsplit_of_allShells (fun _ => 1) hjN h5 hσs hLt ht hnum))

open Classical in
/-- **Exceptional-set bound, multi-pair engine, scalar tail form.** -/
theorem exceptional_bound_of_frontier_and_scalar_multi (U K j0 xs : ℕ) {N : ℕ} (A ε κ : ℝ)
    (hε : 0 ≤ ε) (hκ : 0 ≤ κ) (hj2 : 2 ≤ j0) (hjN : j0 < N)
    (hbK : collatzBarrier U j0 < K) (hKN : K ≤ collatzBarrier U N) (hNA : A * K ≤ N)
    (hL : N - j0 < collatzBarrier U N - collatzBarrier U j0 + 1)
    (hρ : BinomialTail.fbar j0 (collatzBarrier U j0) (N - j0)
      (collatzBarrier U N - collatzBarrier U j0 + 1) (xs + 1) < 1)
    (hscalar : (N : ℝ) * (∏ y ∈ range (xs + 1), BinomialTail.fbar j0 (collatzBarrier U j0) (N - j0)
        (collatzBarrier U N - collatzBarrier U j0 + 1) y) /
        (1 - BinomialTail.fbar j0 (collatzBarrier U j0) (N - j0)
          (collatzBarrier U N - collatzBarrier U j0 + 1) (xs + 1)) ≤
      κ * ((2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (collatzBarrier U N + 1)))
    (hgood : ∀ s σ, K ≤ s → σ < K → collatzBarrier U j0 ≤ σ + xs → N - j0 ≤ s - σ →
      s - σ ≤ collatzBarrier U N - σ → ExplicitPairDataMulti U N j0 s σ ε) :
    (((range (2 ^ K)).filter fun μ =>
        Odd μ ∧ ∀ M, Confined (U : ℝ) (fun i => a (orbit μ i)) M).card : ℝ) ≤
      (1 + ε + κ) * Real.exp (TaoExternal.lambdaStar * U) / 2 *
        ((2 ^ K : ℕ) : ℝ) ^ (1 - TaoExternal.I0 * A) := by
  have hjb : j0 ≤ collatzBarrier U j0 := le_collatzBarrier U j0
  have hbB : collatzBarrier U j0 ≤ collatzBarrier U N := ShellCounts.collatzBarrier_mono U hjN.le
  set good : ℕ → ℕ → Prop := fun s σ => collatzBarrier U j0 ≤ σ + xs ∧ N - j0 ≤ s - σ ∧
    s - σ ≤ collatzBarrier U N - σ
  -- the binomial tail inequality from the scalar condition
  have htail : (N : ℝ) * ∑ σ ∈ range K, (if σ + xs < collatzBarrier U j0 then
      (Nat.choose (σ - 1) (j0 - 1) : ℝ) * Nat.choose (collatzBarrier U N - σ) (N - j0) else 0) ≤
      κ * Nat.choose (collatzBarrier U N - 1) (N - 1) *
        ((2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (collatzBarrier U N + 1)) := by
    have ht := BinomialTail.deficit_tail_le (K := K) xs hj2 hjb (by omega) hbB hjN hL hρ
    set P := ∏ y ∈ range (xs + 1), BinomialTail.fbar j0 (collatzBarrier U j0) (N - j0)
      (collatzBarrier U N - collatzBarrier U j0 + 1) y
    set ρ := BinomialTail.fbar j0 (collatzBarrier U j0) (N - j0)
      (collatzBarrier U N - collatzBarrier U j0 + 1) (xs + 1)
    set Cc : ℝ := ((collatzBarrier U N - 1).choose (N - 1) : ℝ)
    have hC0 : 0 ≤ Cc := by positivity
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    calc _ ≤ N * (Cc * P / (1 - ρ)) := mul_le_mul_of_nonneg_left ht hN0
      _ = Cc * (N * P / (1 - ρ)) := by ring
      _ ≤ Cc * (κ * ((2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (collatzBarrier U N + 1))) :=
          mul_le_mul_of_nonneg_left hscalar hC0
      _ = _ := by ring
  have hbad := FinalChain.badPairMassBound_of_binomialTail good (by omega) hjN hKN
    (fun s σ _ _ h1 h2 h3 => ⟨h1, h2, h3⟩) htail
  refine WeightedChain.weighted_phi_decay_implies_exceptional_bound U K j0 A (1 + ε + κ)
    (fun s σ => @ite ℝ (good s σ) (Classical.propDecidable _) (1 + ε) ((2 : ℝ) ^ (s + 1 - K)))
    (by linarith) (by omega) hjN hbK
    hNA ?_ (FinalChain.hweight_of_badMass U N K j0 good ε κ hε (by omega) hjN hbK hbad)
  intro s σ hKs hσK
  by_cases hg : good s σ
  · left
    exact ⟨ε, hε, by simp [hg], weightedFourier_of_explicitMulti (hgood s σ hKs hσK hg.1 hg.2.1 hg.2.2)⟩
  · right
    simp [hg]

end MultiWhiteChain
end EOC
