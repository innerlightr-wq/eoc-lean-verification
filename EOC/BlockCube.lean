import EOC.WeightedChain

/-!
# Block cubes: class Cauchy–Schwarz, product structure, full-group Parseval, and the plug-in
# interface for block-average estimates

Abstract tools for bounding the characteristic sums `Ψ = Φ` of `WeightedChain` by block cubes.

* `norm_sq_sum_le_classes` — **class Cauchy–Schwarz**: for a finite family with class labels
  `κ`, `‖∑_{i∈T} e(θ_i)‖^2 ≤ |T| · ∑_c ‖∑_{i∈T, κ i = c} e(θ_i)‖^2 / |{i ∈ T : κ i = c}|`.
* `norm_sum_piFinset_eq_prod` — **product structure**: a phase additive over coordinates of a
  product set factors, `‖∑_{f ∈ ∏_r B_r} e(∑_r θ_r(f r))‖ = ∏_r ‖∑_{x∈B_r} e(θ_r x)‖`.
* `sum_sq_norm_eq_of_injOn` — **full-group Parseval / orthogonality**: for `y` injective on `T`
  with values `< 2^M`, `∑_{λ<2^M} ‖∑_{i∈T} e(λ y_i / 2^M)‖^2 = 2^M |T|`.
* `yPrime_injOn` and `sum_sq_norm_Psi_eq` — the prefix phases `y'_P` are injective on the prefix
  shell, so the full-group average of `‖Ψ‖^2` is exactly `|P_σ|` (the ideal value).
* `BlockAverageBound` and `weightedFourier_of_blockAverageBound` — the plug-in interface: a
  pointwise majorant `‖Ψ(λ)‖^2 ≤ |P_σ|^2 B(λ)` on the `WeightedFourier` frequency set whose
  weighted sum satisfies the `WeightedFourier` budget implies `WeightedFourier`.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace BlockCube

open Finset SwapBound

/-! ## Class Cauchy–Schwarz -/

/-- **Class Cauchy–Schwarz.** Splitting a finite exponential sum into classes and applying
Cauchy–Schwarz (Sedrakyan's form) across classes. -/
theorem norm_sq_sum_le_classes {ι β : Type*} [DecidableEq β] (T : Finset ι) (κ : ι → β)
    (θ : ι → ℝ) :
    ‖∑ i ∈ T, ee (θ i)‖ ^ 2 ≤
      (T.card : ℝ) * ∑ c ∈ T.image κ,
        ‖∑ i ∈ T.filter (fun i => κ i = c), ee (θ i)‖ ^ 2 /
          ((T.filter (fun i => κ i = c)).card : ℝ) := by
  set F : β → ℝ := fun c => ‖∑ i ∈ T.filter (fun i => κ i = c), ee (θ i)‖
  set n : β → ℝ := fun c => ((T.filter (fun i => κ i = c)).card : ℝ)
  have hfib : ∑ i ∈ T, ee (θ i) = ∑ c ∈ T.image κ, ∑ i ∈ T.filter (fun i => κ i = c), ee (θ i) :=
    (sum_fiberwise_of_maps_to (fun i hi => mem_image_of_mem κ hi) _).symm
  have hn_pos : ∀ c ∈ T.image κ, 0 < n c := by
    intro c hc
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hc
    exact Nat.cast_pos.mpr (card_pos.mpr ⟨i, mem_filter.mpr ⟨hi, rfl⟩⟩)
  have hn_sum : ∑ c ∈ T.image κ, n c = T.card := by
    simp only [n]
    rw [← Nat.cast_sum, ← card_eq_sum_card_fiberwise (fun i hi => mem_image_of_mem κ hi)]
  have htri : ‖∑ i ∈ T, ee (θ i)‖ ≤ ∑ c ∈ T.image κ, F c := by
    rw [hfib]; exact norm_sum_le _ _
  have hsed := sq_sum_div_le_sum_sq_div (T.image κ) F hn_pos
  rw [hn_sum] at hsed
  rcases (Nat.cast_nonneg (T.card) : (0 : ℝ) ≤ T.card).eq_or_lt with h0 | hpos
  · -- empty family
    have hTe : T = ∅ := by
      have : T.card = 0 := by exact_mod_cast h0.symm
      exact card_eq_zero.mp this
    subst hTe
    simp
  · have h1 : ‖∑ i ∈ T, ee (θ i)‖ ^ 2 ≤ (∑ c ∈ T.image κ, F c) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htri 2
    have h2 : (∑ c ∈ T.image κ, F c) ^ 2 ≤ (T.card : ℝ) * ∑ c ∈ T.image κ, F c ^ 2 / n c := by
      rw [div_le_iff₀ hpos] at hsed
      linarith
    exact h1.trans h2

/-! ## Product structure -/

theorem ee_sum {κ : Type*} (s : Finset κ) (f : κ → ℝ) :
    ee (∑ r ∈ s, f r) = ∏ r ∈ s, ee (f r) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ee]
  | insert a s ha ih => rw [sum_insert ha, prod_insert ha, TwistExpansion.ee_add, ih]

/-- **Product structure.** If the class is a product set `∏_r B_r` and the phase is additive over
the coordinates, the class sum factors, and so does its norm. -/
theorem norm_sum_piFinset_eq_prod {R : ℕ} {κ : Fin R → Type*}
    (B : ∀ r, Finset (κ r)) (θ : ∀ r, κ r → ℝ) :
    ‖∑ f ∈ Fintype.piFinset B, ee (∑ r, θ r (f r))‖ = ∏ r, ‖∑ x ∈ B r, ee (θ r x)‖ := by
  have h : ∑ f ∈ Fintype.piFinset B, ee (∑ r, θ r (f r)) =
      ∏ r, ∑ x ∈ B r, ee (θ r x) := by
    rw [prod_univ_sum]
    exact sum_congr rfl fun f _ => ee_sum _ _
  rw [h, norm_prod]

/-! ## Full-group Parseval -/

/-- **Full-group orthogonality.** For `y` injective on `T` with values below `2^M`, the
average of `‖∑_T e(λ y_i/2^M)‖^2` over all `λ < 2^M` is exactly `|T|`. -/
theorem sum_sq_norm_eq_of_injOn {ι : Type*} (T : Finset ι) (M : ℕ) (y : ι → ℕ)
    (hy : ∀ i ∈ T, y i < 2 ^ M) (hinj : Set.InjOn y ↑T) :
    ∑ lam ∈ range (2 ^ M), ‖∑ i ∈ T, ee ((lam : ℝ) * y i / 2 ^ M)‖ ^ 2 =
      2 ^ M * (T.card : ℝ) := by
  rw [TwistExpansion.sum_sq_norm_ee_eq_card_pairs T M y hy]
  congr 2
  have hset : (T ×ˢ T).filter (fun p => y p.1 = y p.2) = T.diag := by
    ext ⟨a, c⟩
    simp only [mem_filter, mem_product, mem_diag]
    constructor
    · rintro ⟨⟨ha, hc⟩, he⟩; exact ⟨ha, hinj ha hc he⟩
    · rintro ⟨ha, rfl⟩; exact ⟨⟨ha, ha⟩, rfl⟩
  rw [hset, diag_card]

open PrefixCollision WeightedChain

variable {b : ℕ → ℕ} {j0 σ : ℕ}

/-- The prefix phases `y'_P` are injective on the prefix shell (their low parts are the least
realizers, which determine the word). -/
theorem yPrime_injOn (t : ℕ) (hj1 : 1 ≤ j0) :
    Set.InjOn (yPrime j0 σ t) ↑(shellP b j0 σ) := by
  intro P hP Q hQ he
  have hP' : P ∈ shellP b j0 σ := hP
  have hQ' : Q ∈ shellP b j0 σ := hQ
  have hr : leastRealizer P.toInfinite j0 = leastRealizer Q.toInfinite j0 := by
    rw [← yPrime_mod t hj1 hP', ← yPrime_mod t hj1 hQ', he]
  have hRP := SuffixTransport.leastRealizer_realizes_all P.toInfinite j0 (pos_of_shellP hj1 hP')
  have hRQ := SuffixTransport.leastRealizer_realizes_all Q.toInfinite j0 (pos_of_shellP hj1 hQ')
  rw [hr] at hRP
  exact ResidueDiscrepancy.word_eq_of_realizes hRP hRQ

/-- **Full-group value of the prefix characteristic sums.** Over all `λ < 2^(σ+1+t)`, the
average of `‖Ψ(λ)‖^2` is exactly `|P_σ|` (the random / ideal value). -/
theorem sum_sq_norm_Psi_eq (t : ℕ) (hj1 : 1 ≤ j0) :
    ∑ lam ∈ range (2 ^ (σ + 1 + t)),
      ‖TwistExpansion.Psi (shellP b j0 σ) (σ + 1) t (yPrime j0 σ t) lam‖ ^ 2 =
      2 ^ (σ + 1 + t) * ((shellP b j0 σ).card : ℝ) := by
  unfold TwistExpansion.Psi
  exact sum_sq_norm_eq_of_injOn _ (σ + 1 + t) _ (fun P _ => yPrime_lt j0 σ t P)
    (yPrime_injOn t hj1)

/-! ## The plug-in interface -/

/-- **Block-average bound** for the pair `(σ, s)` with majorant `B`: on the `WeightedFourier`
frequency set, `‖Ψ(λ)‖^2 ≤ |P_σ|^2 B(λ)`, and the twist-weighted sum of `B` fits the
`WeightedFourier` budget. -/
def BlockAverageBound (b : ℕ → ℕ) (N j0 s σ : ℕ) (ε : ℝ) (B : ℕ → ℝ) : Prop :=
  (∀ g ∈ Ico 1 (2 ^ (s - σ)), ∀ k ∈ range (2 ^ (σ + 1)),
      ‖TwistExpansion.Psi (shellP b j0 σ) (σ + 1) (s - σ) (yPrime j0 σ (s - σ))
          (g + 2 ^ (s - σ) * k)‖ ^ 2 ≤
        ((shellP b j0 σ).card : ℝ) ^ 2 * B (g + 2 ^ (s - σ) * k)) ∧
    (1 + ((σ + 1 : ℕ) : ℝ) / 2) * ∑ g ∈ Ico 1 (2 ^ (s - σ)), ∑ k ∈ range (2 ^ (σ + 1)),
        ‖TwistExpansion.coef (σ + 1) (s - σ) (g + 2 ^ (s - σ) * k)‖ *
          (((shellP b j0 σ).card : ℝ) ^ 2 * B (g + 2 ^ (s - σ) * k)) ≤
      ε ^ 2 * ((shellP b j0 σ).card : ℝ) ^ 2 * (shellV b N j0 σ (s - σ)).card / 2 ^ (s - σ)

/-- **Interface theorem.** A block-average bound implies the `WeightedFourier` hypothesis. -/
theorem weightedFourier_of_blockAverageBound {N s : ℕ} {ε : ℝ} {B : ℕ → ℝ}
    (h : BlockAverageBound b N j0 s σ ε B) : WeightedFourier b N j0 s σ ε := by
  obtain ⟨hpt, hbud⟩ := h
  unfold WeightedFourier
  refine le_trans ?_ hbud
  have hc : (0 : ℝ) ≤ 1 + ((σ + 1 : ℕ) : ℝ) / 2 := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hc
  refine sum_le_sum fun g hg => sum_le_sum fun k hk => ?_
  exact mul_le_mul_of_nonneg_left (hpt g hg k hk) (norm_nonneg _)

end BlockCube
end EOC
