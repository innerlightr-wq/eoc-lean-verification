import EOC.SwapBound
import EOC.PrefixCollision

/-!
# Swap bound for confined prefix words

Connects the abstract transfer sums of `EOC.SwapBound` to sums over the confined prefix shells
`PrefixCollision.shellP b j0 σ` (positive words of length `j0`, `S_j ≤ b j` for `1 ≤ j ≤ j0`,
digits in the box `[1, b j0]`, total `σ`).

* `cont b σ i n S` — admissible digit strings of length `n` from state `S` at step `i`
  (digits in `[1, σ]`, `S + S_{k+1} ≤ b (i+k+1)` for `k < n`, `S + S_n = σ`).
* `T_eq_sum_cont` — **path-sum identity** for every `i n S`:
  `SwapBound.T b φ σ i n S = ∑_{v ∈ cont b σ i n S} ∏_{k<n} e(φ (i+k) (S + S_k(v)))`.
* `T_zero_eq_N`, `N_eq_card_cont` — with zero phases `T` is the count `N`, so
  `N b σ i n S = #cont b σ i n S`.
* `cont_zero_eq_shellP` — `cont b σ 0 j0 0 = shellP b j0 σ` (no extra hypotheses: the box
  `[1, b j0]` and the box `[1, σ]` cut out the same words once the barrier and total hold).
* `T_eq_sum_shellP`, `N_eq_card_shellP` — the word-level forms
  `SwapBound.T b φ σ 0 j0 0 = ∑_{P ∈ shellP b j0 σ} ∏_{i<j0} e(φ i (P.prefixSum i))` and
  `N b σ 0 j0 0 = #shellP b j0 σ`.
* `collatzPhase`, `norm_sum_shellP_le_G`, `norm_sum_shellP_le_pow_mul_card` — for the Collatz
  phases `φ i S = −frac(h · u_i · 2^S / 2^m)` (any naturals `u_i`), the confined characteristic
  sum is bounded by the swap DP `G`, and by `κ^r · #shellP` under the good-block hypotheses of
  `SwapBound.norm_T_le_pow_mul_N`.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace SwapCollatz

open Finset FiniteValuationWord CapacityBounds PrefixCollision SwapBound

variable (b : ℕ → ℕ) (σ : ℕ)

/-! ## Digit strings and their partial sums -/

theorem toInfinite_cons_succ {n : ℕ} (d : ℕ) (v : Fin n → ℕ) (k : ℕ) :
    FiniteValuationWord.toInfinite (Fin.cons d v : Fin (n + 1) → ℕ) (k + 1) =
      FiniteValuationWord.toInfinite v k := by
  by_cases hk : k < n
  · rw [toInfinite_apply_of_lt _ (by omega), toInfinite_apply_of_lt _ hk]
    exact Fin.cons_succ (α := fun _ => ℕ) d v ⟨k, hk⟩
  · rw [toInfinite_apply_of_le _ (by omega), toInfinite_apply_of_le _ (by omega)]

theorem toInfinite_cons_zero {n : ℕ} (d : ℕ) (v : Fin n → ℕ) :
    FiniteValuationWord.toInfinite (Fin.cons d v : Fin (n + 1) → ℕ) 0 = d := by
  rw [toInfinite_apply_of_lt _ (by omega)]
  exact Fin.cons_zero (α := fun _ => ℕ) d v

/-- `S_{k+1}(d :: v) = d + S_k(v)`. -/
theorem s_cons_succ {n : ℕ} (d : ℕ) (v : Fin n → ℕ) (k : ℕ) :
    s (FiniteValuationWord.toInfinite (Fin.cons d v : Fin (n + 1) → ℕ)) (k + 1) =
      d + s (FiniteValuationWord.toInfinite v) k := by
  unfold s
  rw [sum_range_succ', toInfinite_cons_zero, add_comm]
  congr 1
  exact sum_congr rfl fun j _ => toInfinite_cons_succ d v j

/-- Admissible digit strings of length `n` from state `S` at step `i` reaching `σ`. -/
def cont (i n S : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset fun _ => Icc 1 σ).filter fun v =>
    (∀ k < n, S + s (FiniteValuationWord.toInfinite v) (k + 1) ≤ b (i + k + 1)) ∧
      S + s (FiniteValuationWord.toInfinite v) n = σ

theorem mem_cont {i n S : ℕ} {v : Fin n → ℕ} :
    v ∈ cont b σ i n S ↔ (∀ a, 1 ≤ v a ∧ v a ≤ σ) ∧
      (∀ k < n, S + s (FiniteValuationWord.toInfinite v) (k + 1) ≤ b (i + k + 1)) ∧
      S + s (FiniteValuationWord.toInfinite v) n = σ := by
  simp [cont, Fintype.mem_piFinset]

theorem mem_cont_cons {i n S d : ℕ} {v : Fin n → ℕ} :
    (Fin.cons d v : Fin (n + 1) → ℕ) ∈ cont b σ i (n + 1) S ↔
      d ∈ Icc 1 (b (i + 1) - S) ∧ v ∈ cont b σ (i + 1) n (S + d) := by
  rw [mem_cont, mem_cont, mem_Icc, Fin.forall_fin_succ, s_cons_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  constructor
  · rintro ⟨⟨hd, hv⟩, hbar, htot⟩
    have h0 := hbar 0 (by omega)
    rw [s_cons_succ, s_zero] at h0
    simp only [add_zero] at h0
    refine ⟨⟨hd.1, by omega⟩, hv, fun k hk => ?_, by omega⟩
    have hk' := hbar (k + 1) (by omega)
    rw [s_cons_succ] at hk'
    rw [show i + 1 + k + 1 = i + (k + 1) + 1 by omega]
    omega
  · rintro ⟨⟨hd1, hd2⟩, hv, hbar, htot⟩
    refine ⟨⟨⟨hd1, by omega⟩, hv⟩, fun k hk => ?_, by omega⟩
    rcases k with _ | k
    · rw [s_cons_succ, s_zero]; simp only [add_zero]; omega
    · rw [s_cons_succ]
      have := hbar k (by omega)
      rw [show i + 1 + k + 1 = i + (k + 1) + 1 by omega] at this
      omega

/-- Splitting a sum over `cont … (n+1)` by the first digit. -/
theorem sum_cont_succ {M : Type*} [AddCommMonoid M] (i n S : ℕ) (F : (Fin (n + 1) → ℕ) → M) :
    ∑ w ∈ cont b σ i (n + 1) S, F w =
      ∑ d ∈ Icc 1 (b (i + 1) - S), ∑ v ∈ cont b σ (i + 1) n (S + d),
        F (Fin.cons d v : Fin (n + 1) → ℕ) := by
  rw [sum_sigma']
  refine sum_bij' (fun w _ => (⟨w 0, Fin.tail w⟩ : (_ : ℕ) × (Fin n → ℕ)))
    (fun x _ => (Fin.cons x.1 x.2 : Fin (n + 1) → ℕ)) ?_ ?_ ?_ ?_ ?_
  · intro w hw
    rw [mem_sigma]
    have h := (mem_cont_cons b σ (d := w 0) (v := Fin.tail w)).mp
      (by rw [Fin.cons_self_tail]; exact hw)
    exact h
  · intro x hx
    rw [mem_sigma] at hx
    exact (mem_cont_cons b σ).mpr hx
  · intro w _; simp
  · intro x _; simp
  · intro w _; simp

/-! ## The path-sum identity -/

/-- **Path-sum identity.**
`SwapBound.T b φ σ i n S = ∑_{v ∈ cont} ∏_{k<n} e(φ (i+k) (S + S_k(v)))`. -/
theorem T_eq_sum_cont (φ : ℕ → ℕ → ℝ) :
    ∀ n i S, SwapBound.T b φ σ i n S = ∑ v ∈ cont b σ i n S,
      ∏ k ∈ range n, ee (φ (i + k) (S + s (FiniteValuationWord.toInfinite v) k))
  | 0, i, S => by
      simp only [SwapBound.T, range_zero, prod_empty, sum_const, nsmul_eq_mul, mul_one]
      by_cases h : S = σ
      · have hc : cont b σ i 0 S = {Fin.elim0} := by
          ext v
          simp only [mem_cont, mem_singleton, IsEmpty.forall_iff, true_and]
          constructor
          · intro _; funext a; exact a.elim0
          · intro _; simp [s, h]
        rw [hc]; simp [h]
      · have hc : cont b σ i 0 S = ∅ := by
          ext v
          simp only [mem_cont, IsEmpty.forall_iff, true_and, Finset.notMem_empty, iff_false]
          simp [s, h]
        rw [hc]; simp [h]
  | n + 1, i, S => by
      rw [sum_cont_succ, SwapBound.T, mul_sum]
      refine sum_congr rfl fun d _ => ?_
      rw [T_eq_sum_cont φ n (i + 1) (S + d), mul_sum]
      refine sum_congr rfl fun v _ => ?_
      rw [prod_range_succ', s_zero, add_zero, add_zero, mul_comm]
      congr 1
      refine prod_congr rfl fun k _ => ?_
      rw [s_cons_succ]
      congr 2 <;> omega

/-- With zero phases the transfer sum is the path count. -/
theorem T_zero_eq_N :
    ∀ n i S, SwapBound.T b (fun _ _ => 0) σ i n S = (SwapBound.N b σ i n S : ℂ)
  | 0, i, S => by simp only [SwapBound.T, SwapBound.N]; split_ifs <;> simp
  | n + 1, i, S => by
      simp only [SwapBound.T, SwapBound.N]
      have : ee 0 = 1 := by simp [ee]
      rw [Complex.ofReal_sum, this, one_mul]
      exact sum_congr rfl fun d _ => T_zero_eq_N n (i + 1) (S + d)

theorem N_eq_card_cont (n i S : ℕ) : SwapBound.N b σ i n S = (cont b σ i n S).card := by
  have h := T_eq_sum_cont b σ (fun _ _ => 0) n i S
  rw [T_zero_eq_N] at h
  have hee : ee 0 = 1 := by simp [ee]
  simp only [hee, prod_const_one, sum_const, nsmul_eq_mul, mul_one] at h
  exact_mod_cast h

/-! ## Word level -/

theorem cont_zero_eq_shellP (j0 : ℕ) : cont b σ 0 j0 0 = shellP b j0 σ := by
  ext P
  rw [mem_cont, shellP, mem_filter, confinedWords, mem_filter, mem_box]
  simp only [zero_add, BarrierConfined, mem_Icc]
  have hps : ∀ j ≤ j0, FiniteValuationWord.prefixSum P j = s (FiniteValuationWord.toInfinite P) j :=
    fun j hj => FiniteValuationWord.prefixSum_eq_s P hj
  have htot : FiniteValuationWord.total P = s (FiniteValuationWord.toInfinite P) j0 := hps j0 le_rfl
  constructor
  · rintro ⟨hbox, hbar, hσ⟩
    have hbarj : ∀ j, 1 ≤ j ∧ j ≤ j0 → FiniteValuationWord.prefixSum P j ≤ b j := by
      rintro j ⟨h1, h2⟩
      obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      rw [hps _ h2]; exact hbar k (by omega)
    refine ⟨⟨fun a => ⟨(hbox a).1, ?_⟩, hbarj⟩, by rw [htot]; exact hσ⟩
    rcases Nat.eq_zero_or_pos j0 with h0 | hpos
    · exact absurd a.isLt (by omega)
    · have hle := digit_le_total P a
      have hT := hbarj j0 ⟨hpos, le_rfl⟩
      rw [total] at hle
      omega
  · rintro ⟨⟨hbox, hbar⟩, hσ⟩
    refine ⟨fun a => ⟨(hbox a).1, ?_⟩, fun k hk => ?_, by rw [← htot]; exact hσ⟩
    · have hle := digit_le_total P a
      rw [htot] at hle; omega
    · rw [← hps _ (by omega)]; exact hbar (k + 1) ⟨by omega, by omega⟩

/-- **Word-level path-sum identity.**
`SwapBound.T b φ σ 0 j0 0 = ∑_{P ∈ shellP b j0 σ} ∏_{i<j0} e(φ i (S_i(P)))`. -/
theorem T_eq_sum_shellP (φ : ℕ → ℕ → ℝ) (j0 : ℕ) :
    SwapBound.T b φ σ 0 j0 0 =
      ∑ P ∈ shellP b j0 σ, ∏ i ∈ range j0, ee (φ i (FiniteValuationWord.prefixSum P i)) := by
  rw [T_eq_sum_cont, cont_zero_eq_shellP]
  refine sum_congr rfl fun P _ => prod_congr rfl fun k hk => ?_
  rw [zero_add, zero_add, FiniteValuationWord.prefixSum_eq_s P (by have := mem_range.mp hk; omega)]

theorem N_eq_card_shellP (j0 : ℕ) : SwapBound.N b σ 0 j0 0 = (shellP b j0 σ).card := by
  rw [N_eq_card_cont, cont_zero_eq_shellP]

/-! ## The Collatz phases -/

/-- Collatz phase `φ i S = −frac(h · u_i · 2^S / 2^m)` (`u_i` any naturals, e.g. the residues of
`3^{−(i+1)}` modulo `2^m`). -/
noncomputable def collatzPhase (h m : ℕ) (u : ℕ → ℕ) (i S : ℕ) : ℝ :=
  -Int.fract (((h * u i * 2 ^ S : ℕ) : ℝ) / 2 ^ m)

/-- The confined characteristic sum is dominated by the swap DP. -/
theorem norm_sum_shellP_le_G (h m : ℕ) (u : ℕ → ℕ) (j0 : ℕ) :
    ‖∑ P ∈ shellP b j0 σ, ∏ i ∈ range j0,
        ee (collatzPhase h m u i (FiniteValuationWord.prefixSum P i))‖ ≤
      SwapBound.G b (collatzPhase h m u) σ 0 j0 0 := by
  rw [← T_eq_sum_shellP]
  exact norm_T_le_G b (collatzPhase h m u) σ j0 0 0

/-- **Good-block decay for confined words.** Under the hypotheses of
`SwapBound.norm_T_le_pow_mul_N`, `‖∑_{P ∈ shellP} ∏ e(φ_i(S_i P))‖ ≤ κ^(r 0 j0 0) · #shellP`. -/
theorem norm_sum_shellP_le_pow_mul_card (h m : ℕ) (u : ℕ → ℕ) (j0 : ℕ) (κ : ℝ) (hκ0 : 0 ≤ κ)
    (hκ1 : κ ≤ 1) (good : ℕ → ℕ → ℕ → Prop) [∀ i S u, Decidable (good i S u)]
    (hgood : ∀ i S u', good i S u' →
      blockWeight b (collatzPhase h m u) i S u' ≤ κ * (blockSet b i S u').card)
    (r : ℕ → ℕ → ℕ → ℕ) (hr0 : ∀ i S, r i 0 S = 0) (hr1 : ∀ i S, r i 1 S = 0)
    (hstep : ∀ i n S u', u' ∈ range (b (i + 2) + 1) → (blockSet b i S u').Nonempty →
      SwapBound.N b σ (i + 2) n (S + u') ≠ 0 →
      r i (n + 2) S ≤ r (i + 2) n (S + u') + if good i S u' then 1 else 0) :
    ‖∑ P ∈ shellP b j0 σ, ∏ i ∈ range j0,
        ee (collatzPhase h m u i (FiniteValuationWord.prefixSum P i))‖ ≤
      κ ^ r 0 j0 0 * (shellP b j0 σ).card := by
  rw [← T_eq_sum_shellP, ← N_eq_card_shellP]
  exact norm_T_le_pow_mul_N b (collatzPhase h m u) σ κ hκ0 hκ1 good hgood r hr0 hr1 hstep j0 0 0

end SwapCollatz
end EOC
