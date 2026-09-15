import EOC.DecayInterface

/-!
# Positive density of good angles ⇒ low-frequency decay ⇒ `WeightedFourier`

Abstract, honest conditional layer.

* `avg_prod_le`: product-of-contractions lemma.  For weighted "paths" `P ∈ T` with block factors
  `0 ≤ W P r ≤ 1` and `W P r ≤ κ` on good blocks, the weighted sum of `∏_{r<R} W P r` is at most
  `κ^k · (total weight) + (weight of paths with fewer than k good blocks)`.  Squared version
  `avg_prod_sq_le`.
* `PositiveDensityGoodAngles` (a `Prop`, analytic input — NOT proved here) and
  `avg_prod_sq_le_of_goodAngles`: average `∏ W² ≤ κ^{2k} + ρ`.
* `BlockCubeHyp` (a `Prop`, kept as a hypothesis — the block-cube bound of `BlockCube.lean` is not
  instantiated for `Ψ` along coarse 3-block classes here): `‖Ψ λ‖² ≤ |P_σ|² · (weighted average of
  ∏ W(λ)²)` on low shells.
* `lowFreqDecay_of_goodAngles`: `BlockCubeHyp` + `PositiveDensityGoodAngles` for every low frequency
  ⇒ `DecayInterface.LowFreqDecay`; `weightedFourier_of_goodAngles`: ⇒ `WeightedFourier` via
  `DecayInterface.weightedFourier_of_lowFreqDecay_and_sieve`.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace GoodAngles

open Finset SwapBound TwistExpansion PrefixCollision WeightedChain ShellDecomposition

/-! ## 1. Product of contractions -/

section Product

variable {ι : Type*}

/-- A product of factors in `[0,1]` is at most the product over the good factors, which is at most
`κ^{#good}`. -/
theorem prod_le_pow_card_good (W : ℕ → ℝ) (good : ℕ → Prop) [DecidablePred good] (R : ℕ)
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hW0 : ∀ r, 0 ≤ W r) (hW1 : ∀ r, W r ≤ 1)
    (hgood : ∀ r, good r → W r ≤ κ) :
    ∏ r ∈ range R, W r ≤ κ ^ ((range R).filter good).card := by
  rw [← prod_filter_mul_prod_filter_not (range R) good]
  have hbad : ∏ r ∈ (range R).filter (fun r => ¬ good r), W r ≤ 1 :=
    prod_le_one (fun r _ => hW0 r) (fun r _ => hW1 r)
  have hgood0 : 0 ≤ ∏ r ∈ (range R).filter good, W r := prod_nonneg fun r _ => hW0 r
  have hgoodκ : ∏ r ∈ (range R).filter good, W r ≤ κ ^ ((range R).filter good).card := by
    rw [← prod_const]
    exact prod_le_prod (fun r _ => hW0 r) (fun r hr => hgood r (mem_filter.mp hr).2)
  calc (∏ r ∈ (range R).filter good, W r) * ∏ r ∈ (range R).filter (fun r => ¬ good r), W r
      ≤ (∏ r ∈ (range R).filter good, W r) * 1 := mul_le_mul_of_nonneg_left hbad hgood0
    _ = ∏ r ∈ (range R).filter good, W r := mul_one _
    _ ≤ κ ^ ((range R).filter good).card := hgoodκ

/-- **Product-of-contractions lemma.**  Weighted sum of `∏_{r<R} W P r` is at most
`κ^k · ∑ w + ∑_{P bad} w P`, where `P` is bad if it has fewer than `k` good blocks. -/
theorem avg_prod_le (T : Finset ι) (w : ι → ℝ) (W : ι → ℕ → ℝ) (good : ι → ℕ → Prop)
    [∀ P, DecidablePred (good P)] (R k : ℕ) {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hw : ∀ P ∈ T, 0 ≤ w P) (hW0 : ∀ P ∈ T, ∀ r, 0 ≤ W P r) (hW1 : ∀ P ∈ T, ∀ r, W P r ≤ 1)
    (hgood : ∀ P ∈ T, ∀ r, good P r → W P r ≤ κ) :
    ∑ P ∈ T, w P * ∏ r ∈ range R, W P r ≤
      κ ^ k * ∑ P ∈ T, w P +
        ∑ P ∈ T.filter (fun P => ((range R).filter (good P)).card < k), w P := by
  classical
  set bad : ι → Prop := fun P => ((range R).filter (good P)).card < k
  have hterm : ∀ P ∈ T, w P * ∏ r ∈ range R, W P r ≤
      κ ^ k * w P + (if bad P then w P else 0) := by
    intro P hP
    have hprod1 : ∏ r ∈ range R, W P r ≤ 1 :=
      prod_le_one (fun r _ => hW0 P hP r) (fun r _ => hW1 P hP r)
    have hκk : 0 ≤ κ ^ k * w P := mul_nonneg (pow_nonneg hκ0 k) (hw P hP)
    by_cases hb : bad P
    · rw [if_pos hb]
      calc w P * ∏ r ∈ range R, W P r ≤ w P * 1 := mul_le_mul_of_nonneg_left hprod1 (hw P hP)
        _ = w P := mul_one _
        _ ≤ κ ^ k * w P + w P := le_add_of_nonneg_left hκk
    · rw [if_neg hb, add_zero]
      have hk : k ≤ ((range R).filter (good P)).card := not_lt.mp hb
      have h1 := prod_le_pow_card_good (W P) (good P) R hκ0 (hW0 P hP) (hW1 P hP) (hgood P hP)
      have h2 : κ ^ ((range R).filter (good P)).card ≤ κ ^ k := pow_le_pow_of_le_one hκ0 hκ1 hk
      calc w P * ∏ r ∈ range R, W P r ≤ w P * κ ^ k :=
            mul_le_mul_of_nonneg_left (h1.trans h2) (hw P hP)
        _ = κ ^ k * w P := mul_comm _ _
  calc ∑ P ∈ T, w P * ∏ r ∈ range R, W P r
      ≤ ∑ P ∈ T, (κ ^ k * w P + (if bad P then w P else 0)) := sum_le_sum hterm
    _ = κ ^ k * ∑ P ∈ T, w P + ∑ P ∈ T.filter bad, w P := by
        rw [sum_add_distrib, ← mul_sum, sum_filter]

/-- **Squared version**: factors `W²`, contraction `κ²` on good blocks. -/
theorem avg_prod_sq_le (T : Finset ι) (w : ι → ℝ) (W : ι → ℕ → ℝ) (good : ι → ℕ → Prop)
    [∀ P, DecidablePred (good P)] (R k : ℕ) {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hw : ∀ P ∈ T, 0 ≤ w P) (hW0 : ∀ P ∈ T, ∀ r, 0 ≤ W P r) (hW1 : ∀ P ∈ T, ∀ r, W P r ≤ 1)
    (hgood : ∀ P ∈ T, ∀ r, good P r → W P r ≤ κ) :
    ∑ P ∈ T, w P * ∏ r ∈ range R, W P r ^ 2 ≤
      κ ^ (2 * k) * ∑ P ∈ T, w P +
        ∑ P ∈ T.filter (fun P => ((range R).filter (good P)).card < k), w P := by
  have h := avg_prod_le T w (fun P r => W P r ^ 2) good R k (κ := κ ^ 2) (sq_nonneg κ)
    (pow_le_one₀ hκ0 hκ1) hw (fun P hP r => sq_nonneg _)
    (fun P hP r => pow_le_one₀ (hW0 P hP r) (hW1 P hP r))
    (fun P hP r hr => pow_le_pow_left₀ (hW0 P hP r) (hgood P hP r hr) 2)
  simpa [← pow_mul] using h

end Product

/-! ## 2. Positive density of good angles (analytic input, NOT proved) -/

section Density

variable {ι : Type*}

/-- **Positive density of good angles** (hypothesis): factors in `[0,1]`, contraction `≤ κ` on
good blocks, and the weight of paths with fewer than `k` good blocks is at most `ρ` times the total
weight. -/
def PositiveDensityGoodAngles (T : Finset ι) (w : ι → ℝ) (W : ι → ℕ → ℝ) (good : ι → ℕ → Prop)
    [∀ P, DecidablePred (good P)] (R k : ℕ) (ρ κ : ℝ) : Prop :=
  (∀ P ∈ T, ∀ r, 0 ≤ W P r ∧ W P r ≤ 1) ∧ (∀ P ∈ T, ∀ r, good P r → W P r ≤ κ) ∧
    ∑ P ∈ T.filter (fun P => ((range R).filter (good P)).card < k), w P ≤ ρ * ∑ P ∈ T, w P

/-- **Good angles ⇒ average squared product `≤ (κ^{2k} + ρ) · ∑ w`.** -/
theorem avg_prod_sq_le_of_goodAngles (T : Finset ι) (w : ι → ℝ) (W : ι → ℕ → ℝ)
    (good : ι → ℕ → Prop) [∀ P, DecidablePred (good P)] (R k : ℕ) {ρ κ : ℝ}
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hw : ∀ P ∈ T, 0 ≤ w P)
    (h : PositiveDensityGoodAngles T w W good R k ρ κ) :
    ∑ P ∈ T, w P * ∏ r ∈ range R, W P r ^ 2 ≤ (κ ^ (2 * k) + ρ) * ∑ P ∈ T, w P := by
  obtain ⟨hW, hgood, hbad⟩ := h
  have := avg_prod_sq_le T w W good R k hκ0 hκ1 hw (fun P hP r => (hW P hP r).1)
    (fun P hP r => (hW P hP r).2) hgood
  linarith

end Density

/-! ## 3. Chain to `LowFreqDecay` and `WeightedFourier` -/

section Chain

variable (b : ℕ → ℕ)

/-- **Block-cube hypothesis** (NOT instantiated here): for every frequency `λ` in the centered shells
`u ≤ U`, `‖Ψ λ‖² ≤ |P_σ|² · (∑_c w c ∏_{r<R} W λ c r²) / ∑_c w c`, for a class family `T` with
weights `w ≥ 0` of positive total and block factors `W λ c r` (e.g. coarse 3-block classes,
`w c = |C_c|`, `W = |T_r|/|C_r|`). -/
def BlockCubeHyp {κι : Type*} (j0 σ t U : ℕ) (T : Finset κι) (w : κι → ℝ)
    (W : ℕ → κι → ℕ → ℝ) (R : ℕ) : Prop :=
  0 < ∑ c ∈ T, w c ∧
    ∀ u ≤ U, ∀ lam ∈ cshell (σ + 1) t u,
      ‖Psi (shellP b j0 σ) (σ + 1) t (yPrime j0 σ t) lam‖ ^ 2 ≤
        ((shellP b j0 σ).card : ℝ) ^ 2 *
          ((∑ c ∈ T, w c * ∏ r ∈ range R, W lam c r ^ 2) / ∑ c ∈ T, w c)

/-- **Good angles on every low frequency ⇒ `LowFreqDecay`.**  If the block-cube hypothesis holds
and `PositiveDensityGoodAngles` holds (with fixed `k, ρ, κ`) at every frequency of the shells
`u ≤ U`, and `0 ≤ C`, `κ^{2k} + ρ ≤ C · 2^{−γ j0}`, then `LowFreqDecay b j0 σ t U C γ`. -/
theorem lowFreqDecay_of_goodAngles {κι : Type*} (j0 σ t U : ℕ) (T : Finset κι) (w : κι → ℝ)
    (W : ℕ → κι → ℕ → ℝ) (good : ℕ → κι → ℕ → Prop) [∀ lam c, DecidablePred (good lam c)]
    (R k : ℕ) {ρ κ C γ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hw : ∀ c ∈ T, 0 ≤ w c)
    (hcube : BlockCubeHyp b j0 σ t U T w W R)
    (hdens : ∀ u ≤ U, ∀ lam ∈ cshell (σ + 1) t u,
      PositiveDensityGoodAngles T w (W lam) (good lam) R k ρ κ)
    (hC0 : 0 ≤ C) (hrate : κ ^ (2 * k) + ρ ≤ C * (2 : ℝ) ^ (-(γ * j0))) :
    DecayInterface.LowFreqDecay b j0 σ t U C γ := by
  obtain ⟨hpos, hbd⟩ := hcube
  intro u hu
  set P2 : ℝ := ((shellP b j0 σ).card : ℝ) ^ 2
  have hP2 : 0 ≤ P2 := by positivity
  have hpt : ∀ lam ∈ cshell (σ + 1) t u,
      ‖Psi (shellP b j0 σ) (σ + 1) t (yPrime j0 σ t) lam‖ ^ 2 ≤ P2 * (C * (2 : ℝ) ^ (-(γ * j0))) := by
    intro lam hlam
    have havg := avg_prod_sq_le_of_goodAngles T w (W lam) (good lam) R k hκ0 hκ1 hw
      (hdens u hu lam hlam)
    have hdiv : (∑ c ∈ T, w c * ∏ r ∈ range R, W lam c r ^ 2) / ∑ c ∈ T, w c ≤ κ ^ (2 * k) + ρ :=
      (div_le_iff₀ hpos).mpr havg
    calc ‖Psi (shellP b j0 σ) (σ + 1) t (yPrime j0 σ t) lam‖ ^ 2
        ≤ P2 * ((∑ c ∈ T, w c * ∏ r ∈ range R, W lam c r ^ 2) / ∑ c ∈ T, w c) :=
          hbd u hu lam hlam
      _ ≤ P2 * (κ ^ (2 * k) + ρ) := mul_le_mul_of_nonneg_left hdiv hP2
      _ ≤ P2 * (C * (2 : ℝ) ^ (-(γ * j0))) := mul_le_mul_of_nonneg_left hrate hP2
  have hX : 0 ≤ C * (2 : ℝ) ^ (-(γ * j0)) := mul_nonneg hC0 (by positivity)
  have hcard : ((cshell (σ + 1) t u).card : ℝ) ≤ 2 ^ (u + 1) := by
    exact_mod_cast card_cshell_le (σ + 1) t u
  calc ∑ lam ∈ cshell (σ + 1) t u, ‖Psi (shellP b j0 σ) (σ + 1) t (yPrime j0 σ t) lam‖ ^ 2
      ≤ ∑ lam ∈ cshell (σ + 1) t u, P2 * (C * (2 : ℝ) ^ (-(γ * j0))) := sum_le_sum hpt
    _ = ((cshell (σ + 1) t u).card : ℝ) * (P2 * (C * (2 : ℝ) ^ (-(γ * j0)))) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ 2 ^ (u + 1) * (P2 * (C * (2 : ℝ) ^ (-(γ * j0)))) :=
        mul_le_mul_of_nonneg_right hcard (mul_nonneg hP2 hX)
    _ = 2 ^ (u + 1) * C * (2 : ℝ) ^ (-(γ * j0)) * ((shellP b j0 σ).card : ℝ) ^ 2 := by
        simp only [P2]; ring

/-- **Good angles on low shells + (C3) sieve elsewhere ⇒ `WeightedFourier`.** -/
theorem weightedFourier_of_goodAngles {κι : Type*} (N j0 s σ U : ℕ) (ε : ℝ) (Nsplit : ℕ → ℕ)
    (T : Finset κι) (w : κι → ℝ) (W : ℕ → κι → ℕ → ℝ) (good : ℕ → κι → ℕ → Prop)
    [∀ lam c, DecidablePred (good lam c)] (R k : ℕ) {ρ κ C γ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hw : ∀ c ∈ T, 0 ≤ w c)
    (hcube : BlockCubeHyp b j0 σ (s - σ) U T w W R)
    (hdens : ∀ u ≤ U, ∀ lam ∈ cshell (σ + 1) (s - σ) u,
      PositiveDensityGoodAngles T w (W lam) (good lam) R k ρ κ)
    (hC0 : 0 ≤ C) (hrate : κ ^ (2 * k) + ρ ≤ C * (2 : ℝ) ^ (-(γ * j0)))
    (hN1 : ∀ u ∈ range (σ + 1 + (s - σ)), 1 ≤ Nsplit u)
    (hNj : ∀ u ∈ range (σ + 1 + (s - σ)), Nsplit u < j0)
    (hX : ∀ u ∈ range (σ + 1 + (s - σ)), 2 * PsiSieve.Xmax b (Nsplit u) ≤ 2 ^ (σ + 1 + (s - σ)))
    (hfin : (1 + ((σ + 1 : ℕ) : ℝ) / 2) * ∑ u ∈ range (σ + 1 + (s - σ)),
        min 1 (2 ^ (s - σ) / (2 * 2 ^ u)) *
          DecayInterface.mixedBound b j0 σ Nsplit (fun u => u ≤ U)
            (fun u => 2 ^ (u + 1) * C * (2 : ℝ) ^ (-(γ * j0)) * ((shellP b j0 σ).card : ℝ) ^ 2) u ≤
      ε ^ 2 * ((shellP b j0 σ).card : ℝ) ^ 2 * (shellV b N j0 σ (s - σ)).card / 2 ^ (s - σ)) :
    WeightedFourier b N j0 s σ ε :=
  DecayInterface.weightedFourier_of_lowFreqDecay_and_sieve b N j0 s σ U ε C γ Nsplit hN1 hNj hX
    (lowFreqDecay_of_goodAngles b j0 σ (s - σ) U T w W good R k hκ0 hκ1 hw hcube hdens hC0 hrate)
    hfin

end Chain

end GoodAngles
end EOC
