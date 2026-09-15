import EOC.PrefixCollision

/-!
# Shellwise version of the prefix-collision chain

`PrefixCollision.PrefixCollisionBound` asks for one collision constant `ε` on *every* fresh prefix
shell `σ < K` and post-fresh word shell `s ≥ K`.  On degenerate prefix shells (e.g. `σ = j0`,
the single all-ones prefix) the collision excess is `≈ 2^t`, so that hypothesis can only hold
with `ε ≳ 2^{t/2}`.  This file gives a usable chain in which each pair `(s, σ)` carries its own
constant `c s σ`, and only the Haar-weighted average of the constants must be bounded.

* `incCount b N j0 K s σ` — the incidence count `∑_{P ∈ P_{j0,σ}} ∑_{v ∈ V_{σ,s}} [r_{P·v} < 2^K]`;
  `haarShare b N j0 K s σ = ∑_P ∑_v 2^K (1/2)^(s+1)` (its Haar share); `haarShare_nonneg`,
  `haarShare_eq`.
* `split_count_le_trivial` — for `s ≥ K`: `incCount ≤ 2^(s+1−K) · haarShare` (trivial bound).
* `CollisionAt b N j0 s σ ε` — the per-pair collision condition of
  `PrefixCollision.split_count_le`.
* `incCount_le_of_collision_or_trivial` — for `σ < K ≤ s`: if either `CollisionAt … ε` with
  `0 ≤ ε`, `1 + ε ≤ c`, or `2^(s+1−K) ≤ c`, then `incCount ≤ c · haarShare`.
* `ShellwiseBound b N j0 K c` — `incCount ≤ c s σ · haarShare` for all `σ < K ≤ s`.
* `sum_fresh_split` — for `s ≥ K > b j0`, the word shell sum splits over `σ ∈ range K`.
* `sum_haarShare` — `∑_{σ < K} haarShare s σ = #(W ∩ {S = s}) · 2^K (1/2)^(s+1)`.
* `leastRealizerBound_of_shellwise` — `ShellwiseBound` plus the weighted condition
  `∑_{s ∈ [K, b N]} ∑_{σ < K} c s σ · haarShare s σ ≤ C · ∑_{w ∈ W, S_w ≥ K} 2^K (1/2)^(S_w+1)`
  gives the hypothesis of `ResidueDiscrepancy.exceptional_count_le_of_leastRealizerBound`.
* `weighted_of_le` — the weighted condition holds whenever `c s σ ≤ C` on the index set.
* `exceptional_count_le_of_shellwise` — **full chain**:
  `#(E_U ∩ [0, 2^K)) ≤ (C e^{λ* U}/2) · (2^K)^{1 − I₀ A}`.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace ShellwiseChain

open Finset CapacityBounds FiniteValuationWord PrefixCollision

/-- The incidence count of the pair `(P_{j0,σ}, V_{σ,s})`: pairs whose concatenation has least
realizer below `2^K`. -/
noncomputable def incCount (b : ℕ → ℕ) (N j0 K s σ : ℕ) : ℝ :=
  ∑ P ∈ shellP b j0 σ, ∑ v ∈ shellV b N j0 σ (s - σ),
    (if leastRealizer (concat N P v).toInfinite N < 2 ^ K then 1 else 0 : ℝ)

/-- The Haar share of the pair `(P_{j0,σ}, V_{σ,s})`. -/
noncomputable def haarShare (b : ℕ → ℕ) (N j0 K s σ : ℕ) : ℝ :=
  ∑ _P ∈ shellP b j0 σ, ∑ _v ∈ shellV b N j0 σ (s - σ), (2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (s + 1)

theorem haarShare_nonneg (b : ℕ → ℕ) (N j0 K s σ : ℕ) : 0 ≤ haarShare b N j0 K s σ :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => by positivity

theorem haarShare_eq (b : ℕ → ℕ) (N j0 K s σ : ℕ) :
    haarShare b N j0 K s σ = ((shellP b j0 σ).card : ℝ) * (shellV b N j0 σ (s - σ)).card *
      ((2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (s + 1)) := by
  simp only [haarShare, sum_const, nsmul_eq_mul]
  ring

/-- **Trivial bound.** For `s ≥ K`, the incidence count is at most `2^(s+1−K)` times its Haar
share (each pair contributes at most `1 = 2^(s+1−K) · 2^K 2^{-(s+1)}`). -/
theorem split_count_le_trivial (b : ℕ → ℕ) (N j0 : ℕ) {K s : ℕ} (σ : ℕ) (hKs : K ≤ s) :
    incCount b N j0 K s σ ≤ 2 ^ (s + 1 - K) * haarShare b N j0 K s σ := by
  have hone : (2 : ℝ) ^ (s + 1 - K) * ((2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (s + 1)) = 1 := by
    rw [one_div_pow, ← mul_assoc, ← pow_add, show s + 1 - K + K = s + 1 by omega]
    field_simp
  unfold incCount haarShare
  rw [mul_sum]
  refine sum_le_sum fun P _ => ?_
  rw [mul_sum]
  refine sum_le_sum fun v _ => ?_
  rw [hone]
  split_ifs <;> norm_num

/-- The per-pair collision condition of `PrefixCollision.split_count_le`. -/
def CollisionAt (b : ℕ → ℕ) (N j0 s σ : ℕ) (ε : ℝ) : Prop :=
  (2 : ℝ) ^ (s - σ) * ∑ z : ZMod (2 ^ (s - σ)), prefixCount b j0 σ (s - σ) z ^ 2 ≤
    ((shellP b j0 σ).card : ℝ) ^ 2 * (1 + ε ^ 2 * (shellV b N j0 σ (s - σ)).card / 2 ^ (s - σ))

/-- **Per pair, either alternative.** For `σ < K ≤ s`: a collision bound with `1 + ε ≤ c`, or the
trivial `2^(s+1−K) ≤ c`, gives `incCount ≤ c · haarShare`. -/
theorem incCount_le_of_collision_or_trivial (b : ℕ → ℕ) {N j0 : ℕ} (hj1 : 1 ≤ j0) (hjN : j0 < N)
    {K s σ : ℕ} (hKs : K ≤ s) (hσK : σ < K) {c : ℝ}
    (h : (∃ ε : ℝ, 0 ≤ ε ∧ 1 + ε ≤ c ∧ CollisionAt b N j0 s σ ε) ∨ (2 : ℝ) ^ (s + 1 - K) ≤ c) :
    incCount b N j0 K s σ ≤ c * haarShare b N j0 K s σ := by
  have hH := haarShare_nonneg b N j0 K s σ
  rcases h with ⟨ε, hε, hc, hcoll⟩ | hc
  · have h1 : incCount b N j0 K s σ ≤ (1 + ε) * haarShare b N j0 K s σ :=
      split_count_le b hj1 hjN ε hε hKs hσK hcoll
    exact h1.trans (mul_le_mul_of_nonneg_right hc hH)
  · exact (split_count_le_trivial b N j0 σ hKs).trans (mul_le_mul_of_nonneg_right hc hH)

/-- **Shellwise hypothesis**: each fresh prefix shell `σ < K` and post-fresh word shell `s ≥ K`
has incidence count at most `c s σ` times its Haar share. -/
def ShellwiseBound (b : ℕ → ℕ) (N j0 K : ℕ) (c : ℕ → ℕ → ℝ) : Prop :=
  ∀ s σ, K ≤ s → σ < K → incCount b N j0 K s σ ≤ c s σ * haarShare b N j0 K s σ

/-- For `s ≥ K > b j0`, a sum over the word shell `s` splits over the fresh prefix shells
`σ < K` (shells `σ ≥ K` are empty). -/
theorem sum_fresh_split {R : Type*} [AddCommMonoid R] (b : ℕ → ℕ) {N j0 : ℕ} (hj1 : 1 ≤ j0)
    (hjN : j0 < N) {K s : ℕ} (hbK : b j0 < K) (hKs : K ≤ s) (F : FiniteValuationWord N → R) :
    ∑ w ∈ (confinedWords N b).filter (fun w => w.total = s), F w =
      ∑ σ ∈ range K, ∑ P ∈ shellP b j0 σ, ∑ v ∈ shellV b N j0 σ (s - σ),
        F (concat N P v) := by
  rw [sum_shell_eq_sum_split b hj1 hjN s, ← sum_range_add_sum_Ico _ (by omega : K ≤ s + 1)]
  have hz : ∑ σ ∈ Ico K (s + 1), ∑ P ∈ shellP b j0 σ, ∑ v ∈ shellV b N j0 σ (s - σ),
      F (concat N P v) = 0 := by
    refine sum_eq_zero fun σ hσ => ?_
    rw [shellP_eq_empty hj1 (by have := (mem_Ico.mp hσ).1; omega)]
    simp
  rw [hz, add_zero]

/-- The Haar shares of a word shell add up to its Haar mass. -/
theorem sum_haarShare (b : ℕ → ℕ) {N j0 : ℕ} (hj1 : 1 ≤ j0) (hjN : j0 < N) {K s : ℕ}
    (hbK : b j0 < K) (hKs : K ≤ s) :
    ∑ σ ∈ range K, haarShare b N j0 K s σ =
      (((confinedWords N b).filter (fun w => w.total = s)).card : ℝ) *
        ((2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (s + 1)) := by
  have h := sum_fresh_split b hj1 hjN hbK hKs
    (fun _ => (2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (s + 1))
  rw [sum_const, nsmul_eq_mul] at h
  rw [h]
  rfl

/-- The post-fresh words of a fixed total `s ≥ K`. -/
theorem fiber_eq (W : Finset (FiniteValuationWord N)) {K s : ℕ} (hKs : K ≤ s) :
    (W.filter fun w => K ≤ w.total).filter (fun w => w.total = s) =
      W.filter fun w => w.total = s := by
  ext w
  simp only [mem_filter]
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3 ▸ hKs⟩, h3⟩

theorem total_mem_Icc {b : ℕ → ℕ} {N : ℕ} (hN : 1 ≤ N) {K : ℕ} {w : FiniteValuationWord N}
    (hw : w ∈ (confinedWords N b).filter fun w => K ≤ w.total) : w.total ∈ Icc K (b N) := by
  obtain ⟨hW, hK⟩ := mem_filter.mp hw
  exact mem_Icc.mpr ⟨hK, total_le_of_barrierConfined hN ((mem_confinedWords hN).mp hW).2⟩

/-- The Haar mass of the post-fresh words, organized by word shell and prefix shell. -/
theorem haar_mass_eq (b : ℕ → ℕ) {N j0 : ℕ} (hj1 : 1 ≤ j0) (hjN : j0 < N) {K : ℕ}
    (hbK : b j0 < K) :
    ∑ w ∈ (confinedWords N b).filter (fun w => K ≤ w.total),
        (2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (w.total + 1) =
      ∑ s ∈ Icc K (b N), ∑ σ ∈ range K, haarShare b N j0 K s σ := by
  set W := confinedWords N b
  have hmap : ∀ w ∈ W.filter (fun w => K ≤ w.total), w.total ∈ Icc K (b N) :=
    fun w hw => total_mem_Icc (by omega) hw
  rw [← sum_fiberwise_of_maps_to hmap]
  refine sum_congr rfl fun s hs => ?_
  have hKs : K ≤ s := (mem_Icc.mp hs).1
  rw [fiber_eq W hKs, sum_haarShare b hj1 hjN hbK hKs,
    sum_congr rfl fun w hw => by rw [(mem_filter.mp hw).2], sum_const, nsmul_eq_mul]

open Classical in
/-- **Shellwise bound ⇒ least-realizer counting bound.** -/
theorem leastRealizerBound_of_shellwise (U N K j0 : ℕ) (c : ℕ → ℕ → ℝ) (C : ℝ)
    (hj1 : 1 ≤ j0) (hjN : j0 < N) (hbK : collatzBarrier U j0 < K)
    (hsw : ShellwiseBound (collatzBarrier U) N j0 K c)
    (hweight : ∑ s ∈ Icc K (collatzBarrier U N), ∑ σ ∈ range K,
        c s σ * haarShare (collatzBarrier U) N j0 K s σ ≤
      C * ∑ w ∈ (confinedWords N (collatzBarrier U)).filter (fun w => K ≤ w.total),
        (2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (w.total + 1)) :
    ((((confinedWords N (collatzBarrier U)).filter fun w =>
        K ≤ w.total ∧ leastRealizer w.toInfinite N < 2 ^ K).card : ℕ) : ℝ) ≤
      C * ∑ w ∈ (confinedWords N (collatzBarrier U)).filter (fun w => K ≤ w.total),
        (2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (w.total + 1) := by
  set b := collatzBarrier U
  set W := confinedWords N b
  set D := W.filter fun w => K ≤ w.total
  have hmap : ∀ w ∈ D, w.total ∈ Icc K (b N) := fun w hw => total_mem_Icc (by omega) hw
  have hL : ((W.filter fun w => K ≤ w.total ∧ leastRealizer w.toInfinite N < 2 ^ K).card : ℝ) =
      ∑ w ∈ D, (if leastRealizer w.toInfinite N < 2 ^ K then 1 else 0 : ℝ) := by
    rw [sum_boole, filter_filter]
  rw [hL, ← sum_fiberwise_of_maps_to hmap]
  refine le_trans ?_ hweight
  refine sum_le_sum fun s hs => ?_
  have hKs : K ≤ s := (mem_Icc.mp hs).1
  rw [fiber_eq W hKs, sum_fresh_split b hj1 hjN hbK hKs]
  exact sum_le_sum fun σ hσ => hsw s σ hKs (mem_range.mp hσ)

/-- The weighted condition holds with `C` whenever every constant `c s σ` on the index set is at
most `C`. -/
theorem weighted_of_le (U N K j0 : ℕ) (c : ℕ → ℕ → ℝ) (C : ℝ) (hj1 : 1 ≤ j0) (hjN : j0 < N)
    (hbK : collatzBarrier U j0 < K)
    (hc : ∀ s ∈ Icc K (collatzBarrier U N), ∀ σ ∈ range K, c s σ ≤ C) :
    ∑ s ∈ Icc K (collatzBarrier U N), ∑ σ ∈ range K,
        c s σ * haarShare (collatzBarrier U) N j0 K s σ ≤
      C * ∑ w ∈ (confinedWords N (collatzBarrier U)).filter (fun w => K ≤ w.total),
        (2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (w.total + 1) := by
  rw [haar_mass_eq (collatzBarrier U) hj1 hjN hbK, mul_sum]
  refine sum_le_sum fun s hs => ?_
  rw [mul_sum]
  exact sum_le_sum fun σ hσ =>
    mul_le_mul_of_nonneg_right (hc s hs σ hσ) (haarShare_nonneg _ _ _ _ _ _)

open Classical in
/-- **The full shellwise chain.** Shellwise bound + weighted condition (e.g. `weighted_of_le`),
`1 ≤ C`, `N ≥ A K` ⇒ `#(E_U ∩ [0, 2^K)) ≤ (C e^{λ* U}/2) · (2^K)^{1 − I₀ A}`. -/
theorem exceptional_count_le_of_shellwise (U K j0 : ℕ) {N : ℕ} (A C : ℝ) (c : ℕ → ℕ → ℝ)
    (hC : 1 ≤ C) (hj1 : 1 ≤ j0) (hjN : j0 < N) (hbK : collatzBarrier U j0 < K)
    (hNA : A * K ≤ N) (hsw : ShellwiseBound (collatzBarrier U) N j0 K c)
    (hweight : ∑ s ∈ Icc K (collatzBarrier U N), ∑ σ ∈ range K,
        c s σ * haarShare (collatzBarrier U) N j0 K s σ ≤
      C * ∑ w ∈ (confinedWords N (collatzBarrier U)).filter (fun w => K ≤ w.total),
        (2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (w.total + 1)) :
    (((range (2 ^ K)).filter fun μ =>
        Odd μ ∧ ∀ M, Confined (U : ℝ) (fun i => a (orbit μ i)) M).card : ℝ) ≤
      C * Real.exp (TaoExternal.lambdaStar * U) / 2 *
        ((2 ^ K : ℕ) : ℝ) ^ (1 - TaoExternal.I0 * A) :=
  ResidueDiscrepancy.exceptional_count_le_of_leastRealizerBound U K (by omega) A C hC hNA
    (leastRealizerBound_of_shellwise U N K j0 c C hj1 hjN hbK hsw hweight)

end ShellwiseChain
end EOC
