import Mathlib

/-!
# A binomial tail bound for the prefix-deficit sum

`FinalChain.badPairMassBound_of_binomialTail` reduces `hweight` to
`N · ∑_{σ < K, σ + x* < b} C(σ−1, j0−1) C(B−σ, L) ≤ κ · C(B−1, N−1) · 2^K 2^{−(B+1)}`
(`b = b_U j0`, `B = b_U N`, `L = N − j0`).  This file reduces that sum to a scalar product.

With `x = b − σ` and `a x = C(b−x−1, j0−1) · C(B−b+x, L)`:

* `choose_mul_choose_le_choose` — Vandermonde single term, so `a 0 ≤ C(B−1, N−1)`;
* `a_succ_le` — exact ratio identity: `a (x+1) ≤ fbar x · a x` with
  `fbar x = (b−j0)/(b−1) · (M0+x)/(M0+x−L)`, `M0 = B − b + 1`;
* **`deficit_tail_le`** — `∑_{σ<K, σ+x*<b} C(σ−1,j0−1) C(B−σ,L) ≤ C(B−1,N−1) · ∏_{y ≤ x*} fbar y / (1 − fbar (x*+1))`
  whenever `fbar (x*+1) < 1`.

No `sorry`, `admit`, `axiom`, `opaque`, or `native_decide`.
-/

namespace EOC
namespace BinomialTail

open Finset

/-- Vandermonde, one term. -/
theorem choose_mul_choose_le_choose (m n i j : ℕ) :
    m.choose i * n.choose j ≤ (m + n).choose (i + j) := by
  rw [Nat.add_choose_eq]
  have hmem : (i, j) ∈ HasAntidiagonal.antidiagonal (i + j) := by simp
  exact single_le_sum (f := fun ij : ℕ × ℕ => m.choose ij.1 * n.choose ij.2)
    (fun _ _ => Nat.zero_le _) hmem

variable (j0 b L M0 : ℕ)

/-- The tail term as a function of the deficit `x = b − σ`. -/
def a (x : ℕ) : ℝ := ((b - x - 1).choose (j0 - 1) : ℝ) * ((M0 - 1 + x).choose L : ℝ)

/-- The ratio majorant. -/
noncomputable def fbar (x : ℕ) : ℝ :=
  ((b : ℝ) - j0) / ((b : ℝ) - 1) * (((M0 : ℝ) + x) / ((M0 : ℝ) + x - L))

theorem a_nonneg (x : ℕ) : 0 ≤ a j0 b L M0 x := by unfold a; positivity

theorem fbar_nonneg (hjb : j0 ≤ b) (hb : 2 ≤ b) (hL : L < M0) (x : ℕ) : 0 ≤ fbar j0 b L M0 x := by
  unfold fbar
  have hj : (j0 : ℝ) ≤ b := by exact_mod_cast hjb
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hL' : (L : ℝ) < M0 := by exact_mod_cast hL
  have hx : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have h1 : (0 : ℝ) ≤ (b : ℝ) - j0 := by linarith
  have h2 : (0 : ℝ) < (b : ℝ) - 1 := by linarith
  have h3 : (0 : ℝ) < (M0 : ℝ) + x - L := by linarith
  have h4 : (0 : ℝ) ≤ (M0 : ℝ) + x := by positivity
  exact mul_nonneg (div_nonneg h1 h2.le) (div_nonneg h4 h3.le)

theorem fbar_antitone (hjb : j0 ≤ b) (hb : 2 ≤ b) (hL : L < M0) {x y : ℕ} (hxy : x ≤ y) :
    fbar j0 b L M0 y ≤ fbar j0 b L M0 x := by
  unfold fbar
  have h1 : (0 : ℝ) ≤ ((b : ℝ) - j0) / ((b : ℝ) - 1) := by
    have : (j0 : ℝ) ≤ b := by exact_mod_cast hjb
    have : (2 : ℝ) ≤ b := by exact_mod_cast hb
    apply div_nonneg <;> linarith
  apply mul_le_mul_of_nonneg_left _ h1
  have hLr : (L : ℝ) < M0 := by exact_mod_cast hL
  have hx : (x : ℝ) ≤ y := by exact_mod_cast hxy
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have hdx : (0 : ℝ) < (M0 : ℝ) + x - L := by linarith
  have hdy : (0 : ℝ) < (M0 : ℝ) + y - L := by linarith
  rw [div_le_div_iff₀ hdy hdx]
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  nlinarith

/-- **Ratio step.** `a (x+1) ≤ fbar x · a x`. -/
theorem a_succ_le (hj2 : 2 ≤ j0) (hjb : j0 ≤ b) (hb : 2 ≤ b) (hL : L < M0) (x : ℕ) :
    a j0 b L M0 (x + 1) ≤ fbar j0 b L M0 x * a j0 b L M0 x := by
  have hj : 1 ≤ j0 := by omega
  unfold a
  -- second factor: C(m+1, L) (m+1−L) = C(m, L) (m+1),  m = M0 − 1 + x
  set m := M0 - 1 + x with hm
  have hm1 : M0 - 1 + (x + 1) = m + 1 := by rw [hm]; omega
  rw [hm1]
  have hsec : ((m + 1).choose L : ℝ) * ((m : ℝ) + 1 - L) = (m.choose L : ℝ) * ((m : ℝ) + 1) := by
    have h := Nat.choose_mul_succ_eq m L
    have hLm : L ≤ m + 1 := by rw [hm]; omega
    have h' : ((m.choose L * (m + 1) : ℕ) : ℝ) = (((m + 1).choose L * (m + 1 - L) : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast [Nat.cast_sub hLm] at h'
    linarith
  have hmr : (m : ℝ) + 1 = (M0 : ℝ) + x := by
    have : m + 1 = M0 + x := by rw [hm]; omega
    exact_mod_cast this
  have hden2 : (0 : ℝ) < (M0 : ℝ) + x - L := by
    have : (L : ℝ) < M0 := by exact_mod_cast hL
    have : (0 : ℝ) ≤ x := Nat.cast_nonneg x
    linarith
  have hsec' : ((m + 1).choose L : ℝ) = (m.choose L : ℝ) * (((M0 : ℝ) + x) / ((M0 : ℝ) + x - L)) := by
    rw [hmr] at hsec
    field_simp
    linarith
  -- first factor
  by_cases hcase : j0 - 1 ≤ b - x - 2
  · set n := b - x - 2 with hn
    have hn1 : b - x - 1 = n + 1 := by rw [hn]; omega
    have hn1' : b - (x + 1) - 1 = n := by rw [hn]; omega
    rw [hn1, hn1']
    have hfirst : (n.choose (j0 - 1) : ℝ) * ((n : ℝ) + 1) =
        ((n + 1).choose (j0 - 1) : ℝ) * ((n : ℝ) + 1 - (j0 - 1 : ℕ)) := by
      have h := Nat.choose_mul_succ_eq n (j0 - 1)
      have h' : ((n.choose (j0 - 1) * (n + 1) : ℕ) : ℝ) =
          (((n + 1).choose (j0 - 1) * (n + 1 - (j0 - 1)) : ℕ) : ℝ) := by exact_mod_cast h
      push_cast [Nat.cast_sub (show j0 - 1 ≤ n + 1 by omega)] at h'
      linarith
    have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hj1r : ((j0 - 1 : ℕ) : ℝ) = (j0 : ℝ) - 1 := by
      rw [Nat.cast_sub hj]; simp
    rw [hj1r] at hfirst
    have hfirst' : (n.choose (j0 - 1) : ℝ) =
        ((n + 1).choose (j0 - 1) : ℝ) * (((n : ℝ) + 1 - (j0 - 1)) / ((n : ℝ) + 1)) := by
      field_simp; linarith
    -- (n+1 − (j0−1))/(n+1) ≤ (b − j0)/(b − 1)
    have hnb : (n : ℝ) + 1 ≤ (b : ℝ) - 1 := by
      have : n + 1 + 1 ≤ b := by rw [hn]; omega
      have : ((n + 1 + 1 : ℕ) : ℝ) ≤ b := by exact_mod_cast this
      push_cast at this; linarith
    have hj0r : (1 : ℝ) ≤ j0 := by exact_mod_cast hj
    have hratio : ((n : ℝ) + 1 - (j0 - 1)) / ((n : ℝ) + 1) ≤ ((b : ℝ) - j0) / ((b : ℝ) - 1) := by
      have hb1 : (0 : ℝ) < (b : ℝ) - 1 := by linarith
      rw [div_le_div_iff₀ hnpos hb1]
      nlinarith
    have hq0 : (0 : ℝ) ≤ ((n : ℝ) + 1 - (j0 - 1)) / ((n : ℝ) + 1) := by
      apply div_nonneg _ hnpos.le
      have : j0 - 1 ≤ n + 1 := by omega
      have : ((j0 - 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast this
      push_cast [Nat.cast_sub hj] at this; linarith
    have hS : (0 : ℝ) ≤ (((M0 : ℝ) + x) / ((M0 : ℝ) + x - L)) := by
      apply div_nonneg _ hden2.le; positivity
    rw [hfirst', hsec']
    unfold fbar
    have hA : (0 : ℝ) ≤ ((n + 1).choose (j0 - 1) : ℝ) := by positivity
    have hB : (0 : ℝ) ≤ (m.choose L : ℝ) := by positivity
    calc ((n + 1).choose (j0 - 1) : ℝ) * (((n : ℝ) + 1 - (j0 - 1)) / ((n : ℝ) + 1)) *
          ((m.choose L : ℝ) * (((M0 : ℝ) + x) / ((M0 : ℝ) + x - L)))
        ≤ ((n + 1).choose (j0 - 1) : ℝ) * (((b : ℝ) - j0) / ((b : ℝ) - 1)) *
          ((m.choose L : ℝ) * (((M0 : ℝ) + x) / ((M0 : ℝ) + x - L))) := by
          gcongr
      _ = _ := by ring
  · -- the first factor of `a (x+1)` vanishes
    have hz : (b - (x + 1) - 1).choose (j0 - 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [hz]
    simp only [Nat.cast_zero, zero_mul]
    exact mul_nonneg (fbar_nonneg j0 b L M0 hjb hb hL x) (a_nonneg j0 b L M0 x)

/-- Iterated ratio bound. -/
theorem a_le_prod (hj : 2 ≤ j0) (hjb : j0 ≤ b) (hb : 2 ≤ b) (hL : L < M0) (x : ℕ) :
    a j0 b L M0 x ≤ a j0 b L M0 0 * ∏ y ∈ range x, fbar j0 b L M0 y := by
  induction x with
  | zero => simp
  | succ x ih =>
    rw [prod_range_succ]
    calc a j0 b L M0 (x + 1) ≤ fbar j0 b L M0 x * a j0 b L M0 x := a_succ_le j0 b L M0 hj hjb hb hL x
      _ ≤ fbar j0 b L M0 x * (a j0 b L M0 0 * ∏ y ∈ range x, fbar j0 b L M0 y) :=
          mul_le_mul_of_nonneg_left ih (fbar_nonneg j0 b L M0 hjb hb hL x)
      _ = _ := by ring

/-- **Deficit tail.** For `fbar (x*+1) < 1`:
`∑_{x ∈ (x*, x* + n]} a x ≤ a 0 · ∏_{y ≤ x*} fbar y / (1 − fbar (x*+1))`. -/
theorem sum_a_tail_le (hj : 2 ≤ j0) (hjb : j0 ≤ b) (hb : 2 ≤ b) (hL : L < M0) (xs n : ℕ)
    (hρ : fbar j0 b L M0 (xs + 1) < 1) :
    ∑ k ∈ range n, a j0 b L M0 (xs + 1 + k) ≤
      a j0 b L M0 0 * (∏ y ∈ range (xs + 1), fbar j0 b L M0 y) / (1 - fbar j0 b L M0 (xs + 1)) := by
  set ρ := fbar j0 b L M0 (xs + 1)
  set P := ∏ y ∈ range (xs + 1), fbar j0 b L M0 y
  have hρ0 : 0 ≤ ρ := fbar_nonneg j0 b L M0 hjb hb hL _
  have hP0 : 0 ≤ P := prod_nonneg fun y _ => fbar_nonneg j0 b L M0 hjb hb hL y
  have ha0 : 0 ≤ a j0 b L M0 0 := a_nonneg j0 b L M0 0
  have hterm : ∀ k, a j0 b L M0 (xs + 1 + k) ≤ a j0 b L M0 0 * P * ρ ^ k := by
    intro k
    refine (a_le_prod j0 b L M0 hj hjb hb hL (xs + 1 + k)).trans ?_
    rw [prod_range_add, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ ha0
    refine mul_le_mul_of_nonneg_left ?_ hP0
    calc ∏ y ∈ range k, fbar j0 b L M0 (xs + 1 + y) ≤ ∏ _y ∈ range k, ρ :=
          prod_le_prod (fun y _ => fbar_nonneg j0 b L M0 hjb hb hL _)
            (fun y _ => fbar_antitone j0 b L M0 hjb hb hL (by omega))
      _ = ρ ^ k := by simp
  calc ∑ k ∈ range n, a j0 b L M0 (xs + 1 + k) ≤ ∑ k ∈ range n, a j0 b L M0 0 * P * ρ ^ k :=
        sum_le_sum fun k _ => hterm k
    _ = a j0 b L M0 0 * P * ∑ k ∈ range n, ρ ^ k := by rw [mul_sum]
    _ ≤ a j0 b L M0 0 * P * (ρ ^ 0 / (1 - ρ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg ha0 hP0)
        have := geom_sum_Ico_le_of_lt_one (m := 0) (n := n) hρ0 hρ
        simpa using this
    _ = _ := by rw [pow_zero]; ring

/-- **Deficit tail in the original variables.**  With `M0 = B − b + 1`, `L = N − j0`,
`∑_{σ<K, σ + x* < b} C(σ−1, j0−1) C(B−σ, L) ≤ C(B−1, N−1) · ∏_{y ≤ x*} fbar y / (1 − fbar (x*+1))`. -/
theorem deficit_tail_le {j0 b B N K : ℕ} (xs : ℕ) (hj : 2 ≤ j0) (hjb : j0 ≤ b) (hb : 2 ≤ b)
    (hbB : b ≤ B) (hjN : j0 < N) (hL : N - j0 < B - b + 1)
    (hρ : fbar j0 b (N - j0) (B - b + 1) (xs + 1) < 1) :
    ∑ σ ∈ range K, (if σ + xs < b then
        ((σ - 1).choose (j0 - 1) : ℝ) * ((B - σ).choose (N - j0) : ℝ) else 0) ≤
      ((B - 1).choose (N - 1) : ℝ) *
        (∏ y ∈ range (xs + 1), fbar j0 b (N - j0) (B - b + 1) y) /
          (1 - fbar j0 b (N - j0) (B - b + 1) (xs + 1)) := by
  set L := N - j0
  set M0 := B - b + 1
  set f : ℕ → ℝ := fun σ => a j0 b L M0 (b - σ)
  -- 1. restrict to σ < b − xs and rewrite the summand
  have h1 : ∑ σ ∈ range K, (if σ + xs < b then
        ((σ - 1).choose (j0 - 1) : ℝ) * ((B - σ).choose L : ℝ) else 0) ≤
      ∑ σ ∈ range (b - xs), f σ := by
    rw [← sum_filter]
    have heq : ∀ σ ∈ (range K).filter (fun σ => σ + xs < b),
        ((σ - 1).choose (j0 - 1) : ℝ) * ((B - σ).choose L : ℝ) = f σ := by
      intro σ hσ
      have := (mem_filter.mp hσ).2
      simp only [f, a]
      rw [show b - (b - σ) - 1 = σ - 1 by omega, show M0 - 1 + (b - σ) = B - σ by omega]
    rw [sum_congr rfl heq]
    exact sum_le_sum_of_subset_of_nonneg
      (fun σ hσ => by have := (mem_filter.mp hσ).2; exact mem_range.mpr (by omega))
      (fun σ _ _ => a_nonneg j0 b L M0 _)
  -- 2. reflect
  have h2 : ∑ σ ∈ range (b - xs), f σ = ∑ k ∈ range (b - xs), a j0 b L M0 (xs + 1 + k) := by
    rw [← sum_range_reflect]
    refine sum_congr rfl fun k hk => ?_
    have := mem_range.mp hk
    simp only [f]
    congr 1
    omega
  -- 3. tail bound and Vandermonde
  have h3 := sum_a_tail_le j0 b L M0 hj hjb hb hL xs (b - xs) hρ
  have h4 : a j0 b L M0 0 ≤ ((B - 1).choose (N - 1) : ℝ) := by
    simp only [a, Nat.sub_zero, show M0 - 1 + 0 = B - b by omega]
    have hv := choose_mul_choose_le_choose (b - 1) (B - b) (j0 - 1) L
    rw [show b - 1 + (B - b) = B - 1 by omega, show j0 - 1 + L = N - 1 by omega] at hv
    exact_mod_cast hv
  have hP0 : 0 ≤ ∏ y ∈ range (xs + 1), fbar j0 b L M0 y :=
    prod_nonneg fun y _ => fbar_nonneg j0 b L M0 hjb hb hL y
  have hden : 0 < 1 - fbar j0 b L M0 (xs + 1) := by linarith
  calc _ ≤ ∑ σ ∈ range (b - xs), f σ := h1
    _ = _ := h2
    _ ≤ _ := h3
    _ ≤ ((B - 1).choose (N - 1) : ℝ) * (∏ y ∈ range (xs + 1), fbar j0 b L M0 y) /
          (1 - fbar j0 b L M0 (xs + 1)) := by
        apply div_le_div_of_nonneg_right _ hden.le
        exact mul_le_mul_of_nonneg_right h4 hP0

end BinomialTail
end EOC
