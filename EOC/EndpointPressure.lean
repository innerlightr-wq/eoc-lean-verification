import EOC.MultiWhiteChain

/-!
# Frequency-summed endpoint pressure

The weakest pressure input consumed by the multi-white argument is the already frequency-summed
odd-dark moment.  This module gives that input an arithmetic-frontier name, proves the old
dangerous-window frontier implies it, and records the still more concrete sufficient formulation
in terms of the pinned geometric-kernel coefficient.

The core interface contains no window threshold, dangerous fraction, universal window ceiling,
per-frequency bound, or supremum over start states.
-/

namespace EOC
namespace EndpointPressure

open Finset LocalWindow PressureBridge CapacityBounds

/-- The weakest pressure proposition used by the current multi-white chain.  It is parameterized
by the exponential rate `θ` and polynomial loss `C`, and sums frequencies before imposing a bound. -/
abbrev PowerOfTwoSummedPressureAt (U j σ t Us : ℕ) (d θ C : ℝ) : Prop :=
  AverageOddDark.SummedOddDarkPressure (collatzBarrier U) j σ t Us d 3 θ C

/-- A concrete pinned-kernel sufficient condition for `PowerOfTwoSummedPressureAt`.

The factor `σ j / p` is exactly the loss in `PressureBridge.sum_pow_nodd_le_geo`.  The kernel is
pinned at start state `0` and endpoint `σ`; there is no supremum over either state and no
per-frequency requirement. -/
def PowerOfTwoPinnedKernelPressureAt (U j σ t Us : ℕ) (d θ C : ℝ) : Prop :=
  ∀ u ≤ Us,
    ((σ : ℝ) * j / (((j : ℝ) - 1) / ((σ : ℝ) - 1))) *
        (∑ lam ∈ ShellDecomposition.cshell (σ + 1) t u,
          ker (geoW (((j : ℝ) - 1) / ((σ : ℝ) - 1))
            (((σ : ℝ) - j) / ((σ : ℝ) - 1))
            (oddW (collatzBarrier U) (σ + 1 + t) d 3 lam) σ)
            0 (j / 2) ⟨0, by omega⟩ ⟨σ, by omega⟩) ≤
      2 ^ (u + 1) * (2 : ℝ) ^ (C * Real.logb 2 j + θ * j)

/-- Pinned, frequency-summed geometric-kernel pressure implies the exact odd-dark pressure moment
consumed downstream. -/
theorem summedPressure_of_pinnedKernel {U j σ t Us : ℕ} {d θ C : ℝ}
    (hj : 2 ≤ j) (hev : 2 ∣ j) (hjσ : j < σ) (hσ : σ ≤ collatzBarrier U j)
    (h : PowerOfTwoPinnedKernelPressureAt U j σ t Us d θ C) :
    PowerOfTwoSummedPressureAt U j σ t Us d θ C := by
  intro u hu
  set A : ℝ := (σ : ℝ) * j / (((j : ℝ) - 1) / ((σ : ℝ) - 1))
  set P := PrefixCollision.shellP (collatzBarrier U) j σ
  have hP : (0 : ℝ) ≤ (P.card : ℝ) := Nat.cast_nonneg _
  have hpoint : ∀ lam ∈ ShellDecomposition.cshell (σ + 1) t u,
      ∑ Q ∈ P, (3 : ℝ) ^ OddBlack.Nodd (collatzBarrier U) (σ + 1 + t) d lam Q ≤
        A * ker (geoW (((j : ℝ) - 1) / ((σ : ℝ) - 1))
          (((σ : ℝ) - j) / ((σ : ℝ) - 1))
          (oddW (collatzBarrier U) (σ + 1 + t) d 3 lam) σ)
          0 (j / 2) ⟨0, by omega⟩ ⟨σ, by omega⟩ * P.card := by
    intro lam _
    simpa [A, P] using
      (sum_pow_nodd_le_geo (collatzBarrier U) (m := σ + 1 + t) (d := d) (s := 3)
        (lam := lam) hj (by omega) (collatz_chord U (by omega)) hjσ hσ (by norm_num))
  calc
    ∑ lam ∈ ShellDecomposition.cshell (σ + 1) t u,
        ∑ Q ∈ P, (3 : ℝ) ^ OddBlack.Nodd (collatzBarrier U) (σ + 1 + t) d lam Q
        ≤ ∑ lam ∈ ShellDecomposition.cshell (σ + 1) t u,
          A * ker (geoW (((j : ℝ) - 1) / ((σ : ℝ) - 1))
            (((σ : ℝ) - j) / ((σ : ℝ) - 1))
            (oddW (collatzBarrier U) (σ + 1 + t) d 3 lam) σ)
            0 (j / 2) ⟨0, by omega⟩ ⟨σ, by omega⟩ * P.card :=
          sum_le_sum hpoint
    _ = (A * (∑ lam ∈ ShellDecomposition.cshell (σ + 1) t u,
          ker (geoW (((j : ℝ) - 1) / ((σ : ℝ) - 1))
            (((σ : ℝ) - j) / ((σ : ℝ) - 1))
            (oddW (collatzBarrier U) (σ + 1 + t) d 3 lam) σ)
            0 (j / 2) ⟨0, by omega⟩ ⟨σ, by omega⟩)) * P.card := by
          rw [← sum_mul, ← mul_sum]
    _ ≤ (2 ^ (u + 1) * (2 : ℝ) ^ (C * Real.logb 2 j + θ * j)) * P.card := by
          apply mul_le_mul_of_nonneg_right
          · simpa [PowerOfTwoPinnedKernelPressureAt, A] using h u hu
          · exact hP
    _ = _ := by ring

/-- The legacy dangerous-window frontier implies the weakest summed-pressure frontier at rate
`1/6`. -/
theorem summedPressure_of_dangerousWindowSparsity {U j σ t Us K : ℕ} {d a b A : ℝ}
    (hj : 300 ≤ j) (hev : 2 ∣ j) (hjσ : j < σ) (hσ : σ ≤ collatzBarrier U j)
    (hq63 : 63 * σ + 37 ≤ 100 * j) (h2 : σ + 1 ≤ 2 * j) (hK : 0 < K)
    (hKlog : (K : ℝ) ≤ A * Real.logb 2 j + 1) (hb : 0 ≤ b)
    (h : FrontierRegion.PowerOfTwoDangerousWindowSparsityAt U j σ t Us K d a b) :
    PowerOfTwoSummedPressureAt U j σ t Us d (1 / 6)
      (2 + 3 / 5 * a + 4 / 5 * A + (2 + 3 / 5 * b + 4 / 5 * 1) / 8) :=
  FrontierRegion.summedPressure_of_sparsityAt hj hev hjσ hσ hq63 h2 hK hKlog hb h

/-- A finite abstract rate profile showing why aggregate pressure does not imply a `2/9`
dangerous-window count at threshold `1/10`: all three windows have rate `11/100`, their average
is below `1/6`, but every window is dangerous.  This is an abstract separation, not a realization
by the power-of-two kernels. -/
theorem aggregate_rate_counterexample :
    (3 : ℝ) * (11 / 100) < 3 * (1 / 6) ∧
      (2 / 9 : ℝ) * 3 < 3 := by
  norm_num

/-- Frequency-summed pressure gives multi-white `LowFreqDecay` directly, with no dangerous-window
language. -/
theorem lowFreqDecay_of_summedPressure {U j σ δ t Us N0 Kb : ℕ}
    {d θ C θ' γ : ℝ}
    (hj : 300 ≤ j) (hev : 2 ∣ j) (hlo : collatzBarrier 0 j ≤ σ + δ)
    (hδ : δ ≤ j / 300) (hσ : σ ≤ collatzBarrier U j) (h2 : σ + 2 ≤ 2 * j)
    (hbudget : Kb + 31 * j / 100 + σ / (N0 + 2) ≤ j / 2)
    (hd0 : 0 ≤ d) (hC : 0 ≤ C) (hθ : θ < θ')
    (hlarge : (3 * C / (θ' - θ)) ^ 2 ≤ j)
    (hγδ : γ * j ≤ ((j / 300 - δ : ℕ) : ℝ))
    (hγc : γ * j * Real.log 2 ≤
      4 * (1 - Real.cos (Real.pi * d)) / 3 * (Kb - (θ' + γ) * j))
    (h : PowerOfTwoSummedPressureAt U j σ t Us d θ C) :
    DecayInterface.LowFreqDecay (collatzBarrier U) j σ t Us 4 γ := by
  have hlow := ShapeRegion.lower_barrier j (by omega)
  have hjσ : j < σ := by omega
  have habs := LogAbsorb.rpow_log_absorb hC hθ (by exact_mod_cast (by omega : 0 < j)) hlarge
  have hshape := ShapeRegion.shapeTail_region (N0 := N0) (K := Kb)
    hj hev hlo hδ hσ h2 hbudget
  refine MultiWhite.lowFreqDecay_multi (collatzBarrier U) (M := (2 : ℝ) ^ (θ' * j))
    (Λ := (θ' + γ) * j) (by omega)
    (FrontierRegion.shellP_nonempty_of (by omega) hjσ.le hσ) hd0 hshape
    (fun u hu => (h u hu).trans ?_) ?_
  · have hP : (0 : ℝ) ≤ ((PrefixCollision.shellP (collatzBarrier U) j σ).card : ℝ) :=
      Nat.cast_nonneg _
    gcongr
  · have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hρ : ((2 : ℝ) ^ (j / 300 - δ))⁻¹ ≤ (2 : ℝ) ^ (-(γ * j)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_neg (by norm_num)]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hM : (2 : ℝ) ^ (θ' * j) * (2 : ℝ) ^ (-((θ' + γ) * j)) =
        (2 : ℝ) ^ (-(γ * j)) := by
      rw [← Real.rpow_add (by norm_num)]; congr 1; ring
    have hE : Real.exp (-(4 * (1 - Real.cos (Real.pi * d)) / 3 *
        (Kb - (θ' + γ) * j))) ≤ (2 : ℝ) ^ (-(γ * j)) := by
      rw [Real.rpow_def_of_pos (by norm_num)]
      apply Real.exp_le_exp.mpr
      nlinarith
    have hp : (0 : ℝ) ≤ (2 : ℝ) ^ (-(γ * j)) := by positivity
    linarith

/-- Explicit per-pair data with the weakest summed-pressure input. -/
def ExplicitPairDataSummed (U N j s σ : ℕ) (ε : ℝ) : Prop :=
  ∃ (δ N0 Kb : ℕ) (d θ C θ' γ : ℝ),
    300 ≤ j ∧ 2 ∣ j ∧ collatzBarrier 0 j ≤ σ + δ ∧ δ ≤ j / 300 ∧
    σ ≤ collatzBarrier U j ∧ σ + 2 ≤ 2 * j ∧
    Kb + 31 * j / 100 + σ / (N0 + 2) ≤ j / 2 ∧
    0 ≤ d ∧ 0 ≤ C ∧ θ < θ' ∧ (3 * C / (θ' - θ)) ^ 2 ≤ j ∧
    γ * j ≤ ((j / 300 - δ : ℕ) : ℝ) ∧
    γ * j * Real.log 2 ≤
      4 * (1 - Real.cos (Real.pi * d)) / 3 * (Kb - (θ' + γ) * j) ∧
    j < N ∧ σ ≤ s ∧ N - j ≤ s - σ ∧
    s - σ ≤ collatzBarrier U N - σ ∧ U ≤ σ ∧
    (1 + ((σ + 1 : ℕ) : ℝ) / 2) * (((σ + (s - σ) : ℕ) : ℝ) + 1) *
        4 * 4 ^ (s - σ) * ((N - j : ℕ) : ℝ) ≤
      ε ^ 2 * (Nat.choose (s - σ - 1) (N - j - 1) : ℝ) * (2 : ℝ) ^ (γ * j) ∧
    PowerOfTwoSummedPressureAt U j σ (s - σ) (σ + (s - σ)) d θ C

theorem weightedFourier_of_explicitSummed {U N j s σ : ℕ} {ε : ℝ}
    (h : ExplicitPairDataSummed U N j s σ ε) :
    WeightedChain.WeightedFourier (collatzBarrier U) N j s σ ε := by
  obtain ⟨δ, N0, Kb, d, θ, C, θ', γ, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    h10, h11, h12, h13, hjN, hσs, hLt, ht, hU, hnum, hpress⟩ := h
  have hdecay := lowFreqDecay_of_summedPressure h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    h11 h12 h13 hpress
  exact DecayInterface.weightedFourier_of_lowFreqDecay_and_sieve (collatzBarrier U) N j s σ
    (σ + (s - σ)) ε 4 γ (fun _ => 1) (fun _ _ => le_rfl)
    (fun _ _ => show 1 < j by omega) (fun _ _ => FinalChain.hX_one (by omega)) hdecay
    (ConditionalChain.hfin_of_split (collatzBarrier U) N j s σ (σ + (s - σ)) ε 4 γ
      (by norm_num) (fun _ => 1)
      (FinalChain.hsplit_of_allShells (fun _ => 1) hjN h5 hσs hLt ht hnum))

open Classical in
/-- Generic final scalar-tail theorem whose good-pair input is already `WeightedFourier`. -/
theorem exceptional_bound_of_weightedFourier_and_scalar
    (U K j0 xs : ℕ) {N : ℕ} (A ε κ : ℝ)
    (hε : 0 ≤ ε) (hκ : 0 ≤ κ) (hj2 : 2 ≤ j0) (hjN : j0 < N)
    (hbK : collatzBarrier U j0 < K) (hKN : K ≤ collatzBarrier U N) (hNA : A * K ≤ N)
    (hL : N - j0 < collatzBarrier U N - collatzBarrier U j0 + 1)
    (hρ : BinomialTail.fbar j0 (collatzBarrier U j0) (N - j0)
      (collatzBarrier U N - collatzBarrier U j0 + 1) (xs + 1) < 1)
    (hscalar : (N : ℝ) * (∏ y ∈ range (xs + 1),
        BinomialTail.fbar j0 (collatzBarrier U j0) (N - j0)
          (collatzBarrier U N - collatzBarrier U j0 + 1) y) /
        (1 - BinomialTail.fbar j0 (collatzBarrier U j0) (N - j0)
          (collatzBarrier U N - collatzBarrier U j0 + 1) (xs + 1)) ≤
      κ * ((2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (collatzBarrier U N + 1)))
    (hgood : ∀ s σ, K ≤ s → σ < K → collatzBarrier U j0 ≤ σ + xs →
      N - j0 ≤ s - σ → s - σ ≤ collatzBarrier U N - σ →
      WeightedChain.WeightedFourier (collatzBarrier U) N j0 s σ ε) :
    (((range (2 ^ K)).filter fun μ =>
        Odd μ ∧ ∀ M, Confined (U : ℝ) (fun i => a (orbit μ i)) M).card : ℝ) ≤
      (1 + ε + κ) * Real.exp (TaoExternal.lambdaStar * U) / 2 *
        ((2 ^ K : ℕ) : ℝ) ^ (1 - TaoExternal.I0 * A) := by
  have hjb : j0 ≤ collatzBarrier U j0 := le_collatzBarrier U j0
  have hbB : collatzBarrier U j0 ≤ collatzBarrier U N :=
    ShellCounts.collatzBarrier_mono U hjN.le
  set good : ℕ → ℕ → Prop := fun s σ => collatzBarrier U j0 ≤ σ + xs ∧
    N - j0 ≤ s - σ ∧ s - σ ≤ collatzBarrier U N - σ
  have htail : (N : ℝ) * ∑ σ ∈ range K, (if σ + xs < collatzBarrier U j0 then
      (Nat.choose (σ - 1) (j0 - 1) : ℝ) * Nat.choose (collatzBarrier U N - σ) (N - j0) else 0) ≤
      κ * Nat.choose (collatzBarrier U N - 1) (N - 1) *
        ((2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (collatzBarrier U N + 1)) := by
    have ht := BinomialTail.deficit_tail_le (K := K) xs hj2 hjb (by omega) hbB hjN hL hρ
    set P := ∏ y ∈ range (xs + 1), BinomialTail.fbar j0 (collatzBarrier U j0)
      (N - j0) (collatzBarrier U N - collatzBarrier U j0 + 1) y
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
    (fun s σ => @ite ℝ (good s σ) (Classical.propDecidable _) (1 + ε)
      ((2 : ℝ) ^ (s + 1 - K))) (by linarith) (by omega) hjN hbK hNA ?_
    (FinalChain.hweight_of_badMass U N K j0 good ε κ hε (by omega) hjN hbK hbad)
  intro s σ hKs hσK
  by_cases hg : good s σ
  · left
    exact ⟨ε, hε, by simp [hg], hgood s σ hKs hσK hg.1 hg.2.1 hg.2.2⟩
  · right
    simp [hg]

open Classical in
/-- Final exceptional-set theorem from the frequency-summed pressure frontier. -/
theorem exceptional_bound_of_summedPressure_and_scalar
    (U K j0 xs : ℕ) {N : ℕ} (A ε κ : ℝ)
    (hε : 0 ≤ ε) (hκ : 0 ≤ κ) (hj2 : 2 ≤ j0) (hjN : j0 < N)
    (hbK : collatzBarrier U j0 < K) (hKN : K ≤ collatzBarrier U N) (hNA : A * K ≤ N)
    (hL : N - j0 < collatzBarrier U N - collatzBarrier U j0 + 1)
    (hρ : BinomialTail.fbar j0 (collatzBarrier U j0) (N - j0)
      (collatzBarrier U N - collatzBarrier U j0 + 1) (xs + 1) < 1)
    (hscalar : (N : ℝ) * (∏ y ∈ range (xs + 1),
        BinomialTail.fbar j0 (collatzBarrier U j0) (N - j0)
          (collatzBarrier U N - collatzBarrier U j0 + 1) y) /
        (1 - BinomialTail.fbar j0 (collatzBarrier U j0) (N - j0)
          (collatzBarrier U N - collatzBarrier U j0 + 1) (xs + 1)) ≤
      κ * ((2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (collatzBarrier U N + 1)))
    (hgood : ∀ s σ, K ≤ s → σ < K → collatzBarrier U j0 ≤ σ + xs →
      N - j0 ≤ s - σ → s - σ ≤ collatzBarrier U N - σ →
      ExplicitPairDataSummed U N j0 s σ ε) :
    (((range (2 ^ K)).filter fun μ =>
        Odd μ ∧ ∀ M, Confined (U : ℝ) (fun i => a (orbit μ i)) M).card : ℝ) ≤
      (1 + ε + κ) * Real.exp (TaoExternal.lambdaStar * U) / 2 *
        ((2 ^ K : ℕ) : ℝ) ^ (1 - TaoExternal.I0 * A) :=
  exceptional_bound_of_weightedFourier_and_scalar U K j0 xs A ε κ hε hκ hj2 hjN
    hbK hKN hNA hL hρ hscalar
    (fun s σ hKs hσK hx hLt ht =>
      weightedFourier_of_explicitSummed (hgood s σ hKs hσK hx hLt ht))

end EndpointPressure
end EOC
