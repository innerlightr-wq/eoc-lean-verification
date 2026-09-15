import EOC.Carry
import EOC.TwistExpansion

/-!
# First divergence, late-divergence orthogonality, resonance counts

* `q_sub_valuation` — **first-divergence valuation** of the carry constant
  `q d j = ∑_{l<j} 3^{j−1−l} 2^{s d l}`: if two positive words `d, e` agree on `[0, i)`,
  differ at `i`, and `i + 1 < j`, then with `μ = s d i + min (d i) (e i)`,
  `2^μ ∣ q d j − q e j` and `¬ 2^(μ+1) ∣ q d j − q e j` (in `ℤ`).  Only the terms `l ≥ i+1` differ;
  the `l = i+1` term has valuation exactly `μ`, all later ones valuation `≥ μ + 1`.
* `sum_ee_shell_eq_zero` — **late-divergence orthogonality on a dyadic frequency block**: if
  `Lg ≤ M`, `2^(M−Lg) ∣ Δ` and `¬ 2^M ∣ Δ`, then `∑_{ℓ < 2^Lg} e(ℓ Δ / 2^M) = 0`.
* `card_filter_three_pow_dvd_le` — **resonance count**:
  `#{λ < 2^t : 3^k ∣ λ} ≤ 2^t / 3^k + 1`.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace FirstDivergence

open Finset

/-! ## First-divergence valuation -/

theorem s_eq_of_agree {d e : ℕ → ℕ} {i : ℕ} (hagree : ∀ l < i, d l = e l) {l : ℕ} (hl : l ≤ i) :
    s d l = s e l := by
  unfold s
  exact sum_congr rfl fun m hm => hagree m (lt_of_lt_of_le (mem_range.mp hm) hl)

theorem s_mono' (d : ℕ → ℕ) {a b : ℕ} (h : a ≤ b) : s d a ≤ s d b := by
  unfold s
  exact sum_le_sum_of_subset (range_subset_range.mpr h)

/-- Partial sums after the divergence step exceed `s d i + d i` strictly. -/
theorem s_ge_of_late {d : ℕ → ℕ} {i j l : ℕ} (hij : i + 1 < j) (hd : ∀ m < j, 1 ≤ d m)
    (hl : i + 2 ≤ l) : s d i + d i + 1 ≤ s d l := by
  have h1 : s d (i + 2) = s d i + d i + d (i + 1) := by rw [s_succ, s_succ]
  have h2 := s_mono' d hl
  have h3 := hd (i + 1) hij
  omega

theorem q_sub_eq_sum (d e : ℕ → ℕ) (j : ℕ) :
    (q d j : ℤ) - q e j =
      ∑ l ∈ range j, (3 : ℤ) ^ (j - 1 - l) * ((2 : ℤ) ^ s d l - 2 ^ s e l) := by
  rw [q_eq_C, q_eq_C]
  unfold C
  push_cast
  rw [← sum_sub_distrib]
  exact sum_congr rfl fun l _ => by ring

/-- **First-divergence valuation.** -/
theorem q_sub_valuation {d e : ℕ → ℕ} {i j : ℕ} (hagree : ∀ l < i, d l = e l) (hne : d i ≠ e i)
    (hij : i + 1 < j) (hd : ∀ l < j, 1 ≤ d l) (he : ∀ l < j, 1 ≤ e l) :
    (2 : ℤ) ^ (s d i + min (d i) (e i)) ∣ (q d j : ℤ) - q e j ∧
      ¬ (2 : ℤ) ^ (s d i + min (d i) (e i) + 1) ∣ (q d j : ℤ) - q e j := by
  set μ := s d i + min (d i) (e i) with hμ
  set D : ℕ → ℤ := fun l => (3 : ℤ) ^ (j - 1 - l) * ((2 : ℤ) ^ s d l - 2 ^ s e l) with hD
  have hsum : (q d j : ℤ) - q e j = D (i + 1) + ∑ l ∈ (range j).erase (i + 1), D l := by
    rw [q_sub_eq_sum, add_sum_erase _ _ (mem_range.mpr hij)]
  have hsi : s e i = s d i := (s_eq_of_agree hagree le_rfl).symm
  -- the remaining terms are divisible by 2^(μ+1)
  have hrest : (2 : ℤ) ^ (μ + 1) ∣ ∑ l ∈ (range j).erase (i + 1), D l := by
    refine dvd_sum fun l hl => ?_
    obtain ⟨hl1, hl2⟩ := mem_erase.mp hl
    rcases Nat.lt_or_ge l (i + 1) with h | h
    · have : s d l = s e l := s_eq_of_agree hagree (by omega)
      simp [hD, this]
    · have hl' : i + 2 ≤ l := by omega
      have hdl := s_ge_of_late hij hd hl'
      have hel := s_ge_of_late hij he hl'
      have hdvd1 : (2 : ℤ) ^ (μ + 1) ∣ 2 ^ s d l :=
        pow_dvd_pow 2 (by have := min_le_left (d i) (e i); omega)
      have hdvd2 : (2 : ℤ) ^ (μ + 1) ∣ 2 ^ s e l :=
        pow_dvd_pow 2 (by have := min_le_right (d i) (e i); omega)
      exact Dvd.dvd.mul_left (dvd_sub hdvd1 hdvd2) _
  -- the divergence term is 3^c 2^μ u with u odd
  set u : ℤ := 2 ^ (d i - min (d i) (e i)) - 2 ^ (e i - min (d i) (e i)) with hu
  have hT : D (i + 1) = 2 ^ μ * (3 ^ (j - 1 - (i + 1)) * u) := by
    simp only [hD, hu, s_succ, hsi]
    have ha : s d i + d i = μ + (d i - min (d i) (e i)) := by
      have := min_le_left (d i) (e i); omega
    have hb : s d i + e i = μ + (e i - min (d i) (e i)) := by
      have := min_le_right (d i) (e i); omega
    rw [ha, hb, pow_add, pow_add]
    ring
  have hodd : Odd u := by
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · rw [hu, min_eq_left h.le, Nat.sub_self, pow_zero]
      have : Even ((2 : ℤ) ^ (e i - d i)) :=
        (Int.even_pow.mpr ⟨even_two, by omega⟩)
      exact odd_one.sub_even this
    · rw [hu, min_eq_right h.le, Nat.sub_self, pow_zero]
      have : Even ((2 : ℤ) ^ (d i - e i)) :=
        (Int.even_pow.mpr ⟨even_two, by omega⟩)
      exact this.sub_odd odd_one
  have hw : Odd ((3 : ℤ) ^ (j - 1 - (i + 1)) * u) :=
    (Odd.pow (by decide : Odd (3 : ℤ))).mul hodd
  refine ⟨?_, ?_⟩
  · rw [hsum]
    refine dvd_add ?_ ((pow_dvd_pow 2 (Nat.le_succ μ)).trans hrest)
    rw [hT]; exact dvd_mul_right _ _
  · intro hdiv
    rw [hsum] at hdiv
    have hTd : (2 : ℤ) ^ (μ + 1) ∣ D (i + 1) := (dvd_add_left hrest).mp hdiv
    rw [hT, pow_succ] at hTd
    have h2 : (2 : ℤ) ∣ 3 ^ (j - 1 - (i + 1)) * u :=
      (mul_dvd_mul_iff_left (by positivity : (2 : ℤ) ^ μ ≠ 0)).mp hTd
    exact (Int.not_even_iff_odd.mpr hw) (even_iff_two_dvd.mpr h2)

/-! ## Late-divergence orthogonality on a dyadic frequency block -/

/-- If `Lg ≤ M`, `2^(M−Lg) ∣ Δ` and `¬ 2^M ∣ Δ`, the frequency block `ℓ < 2^Lg` is orthogonal:
`∑_{ℓ < 2^Lg} e(ℓ Δ / 2^M) = 0`. -/
theorem sum_ee_shell_eq_zero {M Lg : ℕ} (hLM : Lg ≤ M) {Δ : ℤ} (hdvd : (2 : ℤ) ^ (M - Lg) ∣ Δ)
    (hnd : ¬ (2 : ℤ) ^ M ∣ Δ) :
    ∑ ℓ ∈ range (2 ^ Lg), SwapBound.ee ((ℓ : ℝ) * (Δ : ℝ) / (2 : ℝ) ^ M) = 0 := by
  obtain ⟨δ, hδ⟩ := hdvd
  have hcongr : ∀ ℓ ∈ range (2 ^ Lg), SwapBound.ee ((ℓ : ℝ) * (Δ : ℝ) / (2 : ℝ) ^ M) =
      SwapBound.ee ((ℓ : ℝ) * (δ : ℝ) / ((2 ^ Lg : ℕ) : ℝ)) := by
    intro ℓ _
    congr 1
    rw [hδ]
    have hM : (2 : ℝ) ^ M = 2 ^ (M - Lg) * 2 ^ Lg := by
      rw [← pow_add]; congr 1; omega
    push_cast
    rw [hM]
    field_simp
  rw [sum_congr rfl hcongr, TwistExpansion.sum_ee_orth _ (by positivity)]
  split_ifs with h
  · exfalso
    obtain ⟨c, hc⟩ := h
    apply hnd
    refine ⟨c, ?_⟩
    push_cast at hc
    rw [hδ, hc, show (2 : ℤ) ^ M = 2 ^ (M - Lg) * 2 ^ Lg by rw [← pow_add]; congr 1; omega]
    ring
  · rfl

/-! ## Resonance count -/

theorem card_filter_dvd_le (n p : ℕ) :
    ((range n).filter fun x => p ∣ x).card ≤ n / p + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have hsub : ((range (N + 1)).filter fun x => p ∣ x) ⊆
      insert 0 ((range N.succ).filter fun x => x ≠ 0 ∧ p ∣ x) := by
    intro x hx
    rw [mem_filter, mem_range] at hx
    rw [mem_insert, mem_filter, mem_range]
    by_cases h0 : x = 0
    · exact Or.inl h0
    · exact Or.inr ⟨by omega, h0, hx.2⟩
  calc ((range (N + 1)).filter fun x => p ∣ x).card
      ≤ (insert 0 ((range N.succ).filter fun x => x ≠ 0 ∧ p ∣ x)).card := card_le_card hsub
    _ ≤ ((range N.succ).filter fun x => x ≠ 0 ∧ p ∣ x).card + 1 := card_insert_le _ _
    _ = N / p + 1 := by rw [Nat.card_multiples']
    _ ≤ (N + 1) / p + 1 := Nat.add_le_add_right (Nat.div_le_div_right (Nat.le_succ N)) 1

/-- `#{λ < 2^t : 3^k ∣ λ} ≤ 2^t / 3^k + 1`. -/
theorem card_filter_three_pow_dvd_le (t k : ℕ) :
    ((range (2 ^ t)).filter fun lam => 3 ^ k ∣ lam).card ≤ 2 ^ t / 3 ^ k + 1 :=
  card_filter_dvd_le (2 ^ t) (3 ^ k)

end FirstDivergence
end EOC
