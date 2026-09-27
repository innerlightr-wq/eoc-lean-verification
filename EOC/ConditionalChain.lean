import EOC.FrontierRegion

/-!
# From the arithmetic frontier to `WeightedFourier` and the exceptional-set bound

`DecayInterface.weightedFourier_of_lowFreqDecay_and_sieve` needs, besides `LowFreqDecay`, one
shell-sum inequality `hfin` mixing the decay bound on shells `u ≤ Us` with the (C3) sieve on
shells `u > Us`.
This file splits `hfin` into its two genuinely different parts and composes the chain.

* `min_mul_pow_le` — `min 1 (2^t/(2·2^u)) · 2^{u+1} ≤ 2^t`: every low shell costs at most `2^t`
  times the per-frequency decay bound, whatever `u` is.
* **`hfin_of_split`** — the low-frequency half of `hfin` is **bookkeeping**: it is implied by
  `(1 + (σ+1)/2) · ((Us + 1) · 2^t · D + S_high) ≤ ε² |P_σ|² |V_{σ,s}| / 2^t`, where
  `D = C 2^{−γ j₀} |P_σ|²` and `S_high` is the weighted (C3) sieve sum over the shells `u > Us`
  only.
* **`weightedFourier_of_sparsityAt`** — `PowerOfTwoDangerousWindowSparsityAt` on the shell
  `(U, σ)` with `t = s − σ`, the parameter conditions of
  `FrontierRegion.lowFreqDecay_of_sparsityAt`, a sieve split `N_u` for the high shells, and the
  split inequality give `WeightedFourier`.
* `PairInputs` — the complete list of per-pair inputs of the previous theorem;
  **`exceptional_bound_of_pairInputs`** — if every pair `(s, σ)`, `σ < K ≤ s`, either has
  `PairInputs` with `1 + ε ≤ c s σ` or pays the trivial `2^{s+1−K} ≤ c s σ`, and the Haar-weighted
  condition `hweight` holds, then `#(E_U ∩ [0, 2^K)) ≤ (C e^{λ* U}/2) (2^K)^{1 − I₀ A}`.

What remains explicit is exactly: the arithmetic Prop on the shells used (OPEN), the high-shell
sieve sum and the counting inequality inside `PairInputs` (quantitative, not yet proved), and
`hweight` (Haar-weight large deviations, not yet proved).  No `sorry`, `admit`, `axiom`, `opaque`,
or `native_decide`.
-/

namespace EOC
namespace ConditionalChain

open Finset TwistExpansion PrefixCollision WeightedChain ShellDecomposition DecayInterface
  CapacityBounds FiniteValuationWord

/-- A low shell weight times the shell size is at most `2^t`. -/
theorem min_mul_pow_le (t u : ℕ) :
    min 1 ((2 : ℝ) ^ t / (2 * 2 ^ u)) * 2 ^ (u + 1) ≤ 2 ^ t := by
  have h2u : (0 : ℝ) < 2 * 2 ^ u := by positivity
  have e : (2 : ℝ) ^ (u + 1) = 2 * 2 ^ u := by rw [pow_succ]; ring
  rw [e]
  calc min 1 ((2 : ℝ) ^ t / (2 * 2 ^ u)) * (2 * 2 ^ u)
      ≤ (2 : ℝ) ^ t / (2 * 2 ^ u) * (2 * 2 ^ u) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) h2u.le
    _ = 2 ^ t := by field_simp

variable (b : ℕ → ℕ)

/-- **Split form of `hfin`.** The low shells `u ≤ Us` contribute at most `(Us + 1) · 2^t · D`. -/
theorem hfin_of_split (N j0 s σ Us : ℕ) (ε C γ : ℝ) (hC : 0 ≤ C) (Nsplit : ℕ → ℕ)
    (hsplit : (1 + ((σ + 1 : ℕ) : ℝ) / 2) *
        (((Us : ℝ) + 1) * 2 ^ (s - σ) * (C * (2 : ℝ) ^ (-(γ * j0)) * ((shellP b j0 σ).card : ℝ) ^ 2)
          + ∑ u ∈ range (σ + 1 + (s - σ)), (if Us < u then
              min 1 (2 ^ (s - σ) / (2 * 2 ^ u)) *
                (2 * PsiShellBound.sieveBound b j0 σ (Nsplit u) (2 ^ u) ^ 2) else 0)) ≤
      ε ^ 2 * ((shellP b j0 σ).card : ℝ) ^ 2 * (shellV b N j0 σ (s - σ)).card / 2 ^ (s - σ)) :
    (1 + ((σ + 1 : ℕ) : ℝ) / 2) * ∑ u ∈ range (σ + 1 + (s - σ)),
        min 1 (2 ^ (s - σ) / (2 * 2 ^ u)) *
          mixedBound b j0 σ Nsplit (fun u => u ≤ Us)
            (fun u => 2 ^ (u + 1) * C * (2 : ℝ) ^ (-(γ * j0)) * ((shellP b j0 σ).card : ℝ) ^ 2) u ≤
      ε ^ 2 * ((shellP b j0 σ).card : ℝ) ^ 2 * (shellV b N j0 σ (s - σ)).card / 2 ^ (s - σ) := by
  refine le_trans ?_ hsplit
  have hpre : (0 : ℝ) ≤ 1 + ((σ + 1 : ℕ) : ℝ) / 2 := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hpre
  set t := s - σ
  set D : ℝ := C * (2 : ℝ) ^ (-(γ * j0)) * ((shellP b j0 σ).card : ℝ) ^ 2 with hD
  have hD0 : 0 ≤ D := by positivity
  set hi : ℕ → ℝ := fun u => if Us < u then
    min 1 (2 ^ t / (2 * 2 ^ u)) * (2 * PsiShellBound.sieveBound b j0 σ (Nsplit u) (2 ^ u) ^ 2)
    else 0
  set lo : ℕ → ℝ := fun u => if u ≤ Us then 2 ^ t * D else 0
  have hterm : ∀ u ∈ range (σ + 1 + t),
      min 1 (2 ^ t / (2 * 2 ^ u)) *
          mixedBound b j0 σ Nsplit (fun u => u ≤ Us)
            (fun u => 2 ^ (u + 1) * C * (2 : ℝ) ^ (-(γ * j0)) * ((shellP b j0 σ).card : ℝ) ^ 2) u ≤
        lo u + hi u := by
    intro u _
    have hw0 : (0 : ℝ) ≤ min 1 (2 ^ t / (2 * 2 ^ u)) := le_min zero_le_one (by positivity)
    unfold mixedBound
    by_cases hu : u ≤ Us
    · simp only [hu, ↓reduceIte, lo, hi, show ¬ Us < u by omega, add_zero]
      calc min 1 (2 ^ t / (2 * 2 ^ u)) *
            min (2 ^ (u + 1) * C * (2 : ℝ) ^ (-(γ * j0)) * ((shellP b j0 σ).card : ℝ) ^ 2)
              (2 * PsiShellBound.sieveBound b j0 σ (Nsplit u) (2 ^ u) ^ 2)
          ≤ min 1 (2 ^ t / (2 * 2 ^ u)) *
              (2 ^ (u + 1) * C * (2 : ℝ) ^ (-(γ * j0)) * ((shellP b j0 σ).card : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left (min_le_left _ _) hw0
        _ = (min 1 (2 ^ t / (2 * 2 ^ u)) * 2 ^ (u + 1)) * D := by rw [hD]; ring
        _ ≤ 2 ^ t * D := mul_le_mul_of_nonneg_right (min_mul_pow_le t u) hD0
    · simp only [hu, ↓reduceIte, lo, hi, show Us < u by omega, zero_add]
      exact le_rfl
  refine (sum_le_sum hterm).trans ?_
  rw [sum_add_distrib]
  refine add_le_add ?_ le_rfl
  -- the low part: at most `Us + 1` shells, each `2^t D`
  have hlo : ∑ u ∈ range (σ + 1 + t), lo u ≤ ∑ u ∈ range (Us + 1), 2 ^ t * D := by
    calc ∑ u ∈ range (σ + 1 + t), lo u
        = ∑ u ∈ (range (σ + 1 + t)).filter (fun u => u ≤ Us), 2 ^ t * D := by
          rw [sum_filter]
      _ ≤ ∑ u ∈ range (Us + 1), 2 ^ t * D := by
          refine sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
          intro u hu
          simp only [mem_filter, mem_range] at hu ⊢
          omega
  refine hlo.trans (le_of_eq ?_)
  rw [sum_const, card_range, nsmul_eq_mul]
  push_cast
  ring

/-- **`PowerOfTwoDangerousWindowSparsityAt ⇒ WeightedFourier`** on one shell pair `(s, σ)`,
`t = s − σ`, with the split form of `hfin` (low shells: decay bound; high shells: (C3) sieve). -/
theorem weightedFourier_of_sparsityAt {U N j s σ δ Us K N0 Kb k n : ℕ}
    {d ca cb A θ' ν γ ε : ℝ} (Nsplit : ℕ → ℕ)
    (hj : 300 ≤ j) (hev : 2 ∣ j) (hlo : collatzBarrier 0 j ≤ σ + δ) (hδ : δ ≤ j / 300)
    (hσ : σ ≤ collatzBarrier U j) (hq63 : 63 * σ + 37 ≤ 100 * j)
    (hK : 0 < K) (hKlog : (K : ℝ) ≤ A * Real.logb 2 j + 1) (ha : 0 ≤ ca) (hb : 0 ≤ cb)
    (hA : 0 ≤ A) (hbudget : Kb + 31 * j / 100 + σ / (N0 + 2) ≤ j / 2) (hkn : k + n ≤ Kb)
    (hN : 2 ≤ N0) (hd0 : 0 ≤ d) (hd1 : d ≤ 1 / 2) (hθ : 1 / 6 < θ')
    (hlarge :
      (3 * (2 + 3 / 5 * ca + 4 / 5 * A + (2 + 3 / 5 * cb + 4 / 5 * 1) / 8) / (θ' - 1 / 6)) ^ 2 ≤ j)
    (hn : ν * j ≤ n) (hγ : θ' + γ ≤ ν * Real.logb 2 ((1 + 3) / 2))
    (hγδ : γ * j ≤ ((j / 300 - δ : ℕ) : ℝ)) (hγk : γ * j * Real.log 2 ≤ 8 * k * d ^ 2 / N0)
    (hN1 : ∀ u ∈ range (σ + 1 + (s - σ)), 1 ≤ Nsplit u)
    (hNj : ∀ u ∈ range (σ + 1 + (s - σ)), Nsplit u < j)
    (hX : ∀ u ∈ range (σ + 1 + (s - σ)),
      2 * PsiSieve.Xmax (collatzBarrier U) (Nsplit u) ≤ 2 ^ (σ + 1 + (s - σ)))
    (hsplit : (1 + ((σ + 1 : ℕ) : ℝ) / 2) *
        (((Us : ℝ) + 1) * 2 ^ (s - σ) *
            (4 * (2 : ℝ) ^ (-(γ * j)) * ((shellP (collatzBarrier U) j σ).card : ℝ) ^ 2)
          + ∑ u ∈ range (σ + 1 + (s - σ)), (if Us < u then
              min 1 (2 ^ (s - σ) / (2 * 2 ^ u)) *
                (2 * PsiShellBound.sieveBound (collatzBarrier U) j σ (Nsplit u) (2 ^ u) ^ 2)
              else 0)) ≤
      ε ^ 2 * ((shellP (collatzBarrier U) j σ).card : ℝ) ^ 2 *
        (shellV (collatzBarrier U) N j σ (s - σ)).card / 2 ^ (s - σ))
    (h : FrontierRegion.PowerOfTwoDangerousWindowSparsityAt U j σ (s - σ) Us K d ca cb) :
    WeightedFourier (collatzBarrier U) N j s σ ε := by
  have hdecay := FrontierRegion.lowFreqDecay_of_sparsityAt (t := s - σ) hj hev hlo hδ hσ hq63 hK
    hKlog ha hb hA hbudget hkn hN hd0 hd1 hθ hlarge hn hγ hγδ hγk h
  exact weightedFourier_of_lowFreqDecay_and_sieve (collatzBarrier U) N j s σ Us ε 4 γ Nsplit
    hN1 hNj hX hdecay
    (hfin_of_split (collatzBarrier U) N j s σ Us ε 4 γ (by norm_num) Nsplit hsplit)

/-- **All per-pair inputs** of `weightedFourier_of_sparsityAt`, bundled: the arithmetic frontier on
the shell, the region and rate conditions, a sieve split, and the split shell inequality. -/
def PairInputs (U N j s σ : ℕ) (ε : ℝ) : Prop :=
  ∃ (δ Us K N0 Kb k n : ℕ) (d ca cb A θ' ν γ : ℝ) (Nsplit : ℕ → ℕ),
    300 ≤ j ∧ 2 ∣ j ∧ collatzBarrier 0 j ≤ σ + δ ∧ δ ≤ j / 300 ∧ σ ≤ collatzBarrier U j ∧
    63 * σ + 37 ≤ 100 * j ∧ 0 < K ∧ (K : ℝ) ≤ A * Real.logb 2 j + 1 ∧ 0 ≤ ca ∧ 0 ≤ cb ∧
    0 ≤ A ∧ Kb + 31 * j / 100 + σ / (N0 + 2) ≤ j / 2 ∧ k + n ≤ Kb ∧ 2 ≤ N0 ∧ 0 ≤ d ∧ d ≤ 1 / 2 ∧
    1 / 6 < θ' ∧
    (3 * (2 + 3 / 5 * ca + 4 / 5 * A + (2 + 3 / 5 * cb + 4 / 5 * 1) / 8) / (θ' - 1 / 6)) ^ 2 ≤ j ∧
    ν * j ≤ n ∧ θ' + γ ≤ ν * Real.logb 2 ((1 + 3) / 2) ∧ γ * j ≤ ((j / 300 - δ : ℕ) : ℝ) ∧
    γ * j * Real.log 2 ≤ 8 * k * d ^ 2 / N0 ∧
    (∀ u ∈ range (σ + 1 + (s - σ)), 1 ≤ Nsplit u) ∧
    (∀ u ∈ range (σ + 1 + (s - σ)), Nsplit u < j) ∧
    (∀ u ∈ range (σ + 1 + (s - σ)),
      2 * PsiSieve.Xmax (collatzBarrier U) (Nsplit u) ≤ 2 ^ (σ + 1 + (s - σ))) ∧
    (1 + ((σ + 1 : ℕ) : ℝ) / 2) *
        (((Us : ℝ) + 1) * 2 ^ (s - σ) *
            (4 * (2 : ℝ) ^ (-(γ * j)) * ((shellP (collatzBarrier U) j σ).card : ℝ) ^ 2)
          + ∑ u ∈ range (σ + 1 + (s - σ)), (if Us < u then
              min 1 (2 ^ (s - σ) / (2 * 2 ^ u)) *
                (2 * PsiShellBound.sieveBound (collatzBarrier U) j σ (Nsplit u) (2 ^ u) ^ 2)
              else 0)) ≤
      ε ^ 2 * ((shellP (collatzBarrier U) j σ).card : ℝ) ^ 2 *
        (shellV (collatzBarrier U) N j σ (s - σ)).card / 2 ^ (s - σ) ∧
    FrontierRegion.PowerOfTwoDangerousWindowSparsityAt U j σ (s - σ) Us K d ca cb

theorem weightedFourier_of_pairInputs {U N j s σ : ℕ} {ε : ℝ} (h : PairInputs U N j s σ ε) :
    WeightedFourier (collatzBarrier U) N j s σ ε := by
  obtain ⟨δ, Us, K, N0, Kb, k, n, d, ca, cb, A, θ', ν, γ, Nsplit, h1, h2, h3, h4, h5, h6, h7, h8,
    h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26,
    h27⟩ := h
  exact weightedFourier_of_sparsityAt Nsplit h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
    h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27

open Classical in
/-- **The conditional exceptional-set bound.** Every post-fresh pair `(s, σ)` (`σ < K ≤ s`) either
carries `PairInputs` with `1 + ε ≤ c s σ`, or pays the trivial constant `2^{s+1−K}`; with the
Haar-weighted condition, `#(E_U ∩ [0, 2^K)) ≤ (C e^{λ* U}/2) (2^K)^{1 − I₀ A}` for `N ≥ A K`. -/
theorem exceptional_bound_of_pairInputs (U K j0 : ℕ) {N : ℕ} (A C : ℝ)
    (c : ℕ → ℕ → ℝ) (hC : 1 ≤ C) (hj1 : 1 ≤ j0) (hjN : j0 < N) (hbK : collatzBarrier U j0 < K)
    (hNA : A * K ≤ N)
    (hpair : ∀ s σ, K ≤ s → σ < K →
      (∃ ε : ℝ, 0 ≤ ε ∧ 1 + ε ≤ c s σ ∧ PairInputs U N j0 s σ ε) ∨
        (2 : ℝ) ^ (s + 1 - K) ≤ c s σ)
    (hweight : ∑ s ∈ Icc K (collatzBarrier U N), ∑ σ ∈ range K,
        c s σ * ShellwiseChain.haarShare (collatzBarrier U) N j0 K s σ ≤
      C * ∑ w ∈ (CapacityBounds.confinedWords N (collatzBarrier U)).filter (fun w => K ≤ w.total),
        (2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (w.total + 1)) :
    (((range (2 ^ K)).filter fun μ =>
        Odd μ ∧ ∀ M, Confined (U : ℝ) (fun i => a (orbit μ i)) M).card : ℝ) ≤
      C * Real.exp (TaoExternal.lambdaStar * U) / 2 *
        ((2 ^ K : ℕ) : ℝ) ^ (1 - TaoExternal.I0 * A) := by
  refine weighted_phi_decay_implies_exceptional_bound U K j0 A C c hC hj1 hjN hbK hNA ?_ hweight
  intro s σ hKs hσK
  rcases hpair s σ hKs hσK with ⟨ε, hε, hc, hP⟩ | h
  · exact Or.inl ⟨ε, hε, hc, weightedFourier_of_pairInputs hP⟩
  · exact Or.inr h

end ConditionalChain
end EOC
