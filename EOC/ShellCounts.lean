import EOC.ShellwiseChain

/-!
# Binomial sandwich for the suffix shells `V_{σ,s}`

`hfin` (inside `ConditionalChain.PairInputs`) divides by `|V_{σ,s}|`, where
`V_{σ,s} = shellV b N j0 σ t` is the set of positive words of length `L = N − j0`, total `t = s − σ`,
confined by the **shifted barrier** `i ↦ b (j0 + i) − σ`.

* `shift_chord` — for the Collatz barrier `b = collatzBarrier U` and `σ ≤ b j0`, the shifted barrier
  dominates every chord from `(0,0)` to `(L, b N − σ)`.  This is the hypothesis of the cycle-lemma
  count `CapacityBounds.shell_choose_le_mul_card`.
* **`choose_le_mul_card_shellV`** — `C(t−1, L−1) ≤ L · |V_{σ,s}|` for `L ≤ t ≤ b N − σ`: the suffix
  shell is within the factor `L` of all compositions.
* `card_shellV_le_choose` — `|V_{σ,s}| ≤ C(t−1, L−1)` (all barriers); `shellV_eq_empty_of_lt` —
  `V = ∅` if `t < L`; the same upper bound for prefix shells `P_σ`.

No `sorry`, `admit`, `axiom`, `opaque`, or `native_decide`.
-/

namespace EOC
namespace ShellCounts

open Finset CapacityBounds FiniteValuationWord PrefixCollision

theorem collatzBarrier_mono (U : ℕ) {i j : ℕ} (hij : i ≤ j) :
    collatzBarrier U i ≤ collatzBarrier U j := by
  unfold collatzBarrier
  apply Nat.floor_le_floor
  have : (i : ℝ) ≤ j := by exact_mod_cast hij
  nlinarith [alpha_pos]

/-- **Chord condition for the shifted Collatz barrier.** -/
theorem shift_chord (U j0 σ L : ℕ) (hσ : σ ≤ collatzBarrier U j0) (hL : 0 < L) :
    ∀ i ≤ L, ∀ p : ℕ, L * p ≤ i * shiftBarrier (collatzBarrier U) j0 σ L →
      p ≤ shiftBarrier (collatzBarrier U) j0 σ i := by
  intro i hi p hp
  unfold shiftBarrier at *
  have hσi : σ ≤ collatzBarrier U (j0 + i) := hσ.trans (collatzBarrier_mono U (by omega))
  have hσL : σ ≤ collatzBarrier U (j0 + L) := hσ.trans (collatzBarrier_mono U (by omega))
  suffices h : p + σ ≤ collatzBarrier U (j0 + i) by omega
  unfold collatzBarrier
  rw [Nat.le_floor_iff (barrier_arg_nonneg U _)]
  have hσr : (σ : ℝ) ≤ j0 * alpha + U := by
    have := hσ; unfold collatzBarrier at this
    exact (Nat.le_floor_iff (barrier_arg_nonneg U j0)).mp this
  have hBL : ((collatzBarrier U (j0 + L) : ℕ) : ℝ) ≤ ((j0 + L : ℕ) : ℝ) * alpha + U :=
    Nat.floor_le (barrier_arg_nonneg U _)
  have hp' : (L : ℝ) * p ≤ i * (((collatzBarrier U (j0 + L) : ℕ) : ℝ) - σ) := by
    have h1 : ((L * p : ℕ) : ℝ) ≤ ((i * (collatzBarrier U (j0 + L) - σ) : ℕ) : ℝ) := by
      exact_mod_cast hp
    push_cast [Nat.cast_sub hσL] at h1
    linarith
  have hir : (i : ℝ) ≤ L := by exact_mod_cast hi
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hgap : (0 : ℝ) ≤ j0 * alpha + U - σ := by linarith
  have h2 : (L : ℝ) * p ≤ i * (((j0 + L : ℕ) : ℝ) * alpha + U - σ) :=
    hp'.trans (mul_le_mul_of_nonneg_left (by linarith) hi0)
  push_cast at h2 ⊢
  have h3 : (i : ℝ) * (j0 * alpha + U - σ) ≤ L * (j0 * alpha + U - σ) :=
    mul_le_mul_of_nonneg_right hir hgap
  have key : (L : ℝ) * (p + σ) ≤ L * ((j0 + i) * alpha + U) := by nlinarith
  exact le_of_mul_le_mul_left key hLr

/-- **Suffix-shell lower bound.** `C(t−1, L−1) ≤ L · |V_{σ,s}|` for `L ≤ t ≤ b_U N − σ`,
`L = N − j0`. -/
theorem choose_le_mul_card_shellV {U N j0 σ t : ℕ} (hjN : j0 < N) (hσ : σ ≤ collatzBarrier U j0)
    (hLt : N - j0 ≤ t) (ht : t ≤ collatzBarrier U N - σ) :
    Nat.choose (t - 1) (N - j0 - 1) ≤ (N - j0) * (shellV (collatzBarrier U) N j0 σ t).card := by
  have hL : 1 ≤ N - j0 := by omega
  have hK : shiftBarrier (collatzBarrier U) j0 σ (N - j0) = collatzBarrier U N - σ := by
    unfold shiftBarrier; rw [show j0 + (N - j0) = N by omega]
  exact shell_choose_le_mul_card hL _ (shift_chord U j0 σ (N - j0) hσ (by omega)) hLt (hK ▸ ht)

/-- Any shell of confined words is contained in the composition shell. -/
theorem filter_total_subset_shellWords {L : ℕ} (hL : 1 ≤ L) (K : ℕ → ℕ) (t : ℕ) :
    (confinedWords L K).filter (fun w => w.total = t) ⊆ shellWords L t := by
  intro w hw
  obtain ⟨hW, ht⟩ := mem_filter.mp hw
  exact mem_shellWords.mpr ⟨((mem_confinedWords hL).mp hW).1, ht⟩

theorem card_filter_total_le_choose {L : ℕ} (hL : 1 ≤ L) (K : ℕ → ℕ) {t : ℕ} (hLt : L ≤ t) :
    ((confinedWords L K).filter (fun w => w.total = t)).card ≤ Nat.choose (t - 1) (L - 1) := by
  rw [← card_shellWords hL hLt]
  exact card_le_card (filter_total_subset_shellWords hL K t)

theorem filter_total_eq_empty_of_lt {L : ℕ} (hL : 1 ≤ L) (K : ℕ → ℕ) {t : ℕ} (ht : t < L) :
    (confinedWords L K).filter (fun w => w.total = t) = ∅ := by
  refine eq_empty_of_forall_notMem fun w hw => ?_
  obtain ⟨hW, htot⟩ := mem_filter.mp hw
  have := le_total_of_positive ((mem_confinedWords hL).mp hW).1
  omega

/-- **Suffix-shell upper bound** (any barrier): `|V_{σ,s}| ≤ C(t−1, L−1)`. -/
theorem card_shellV_le_choose (b : ℕ → ℕ) {N j0 σ t : ℕ} (hjN : j0 < N) (hLt : N - j0 ≤ t) :
    (shellV b N j0 σ t).card ≤ Nat.choose (t - 1) (N - j0 - 1) :=
  card_filter_total_le_choose (by omega) _ hLt

theorem shellV_eq_empty_of_lt (b : ℕ → ℕ) {N j0 σ t : ℕ} (hjN : j0 < N) (ht : t < N - j0) :
    shellV b N j0 σ t = ∅ :=
  filter_total_eq_empty_of_lt (by omega) _ ht

/-- **Prefix-shell upper bound** (any barrier): `|P_σ| ≤ C(σ−1, j0−1)`. -/
theorem card_shellP_le_choose (b : ℕ → ℕ) {j0 σ : ℕ} (hj : 1 ≤ j0) (hjσ : j0 ≤ σ) :
    (shellP b j0 σ).card ≤ Nat.choose (σ - 1) (j0 - 1) :=
  card_filter_total_le_choose hj _ hjσ

/-- **Prefix-shell lower bound** (Collatz barrier): `C(σ−1, j0−1) ≤ j0 · |P_σ|`. -/
theorem choose_le_mul_card_shellP {U j0 σ : ℕ} (hj : 1 ≤ j0) (hjσ : j0 ≤ σ)
    (hσ : σ ≤ collatzBarrier U j0) :
    Nat.choose (σ - 1) (j0 - 1) ≤ j0 * (shellP (collatzBarrier U) j0 σ).card :=
  shell_choose_le_mul_card hj _ (collatz_chord U (by omega)) hjσ hσ

end ShellCounts
end EOC
