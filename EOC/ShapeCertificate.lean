import EOC.ShapeBridge

/-!
# An explicit super-eigenvector certificate for the block kernel

`EOC.ShapeBridge.shapeTail_of_superEigen` reduces `ShapeTail` to exhibiting `h > 0` and `M` with

  `∑_y blockW(l,x,y) · h(l+1,y) ≤ M · h(l,x)`.

This file supplies them, in closed form and with no free parameters:

  **`h(l,x) = 2^(σ-x)`,  `u = 3`,  `M = 3/2`.**

The verification is a dyadic computation.  Writing `w = b(2l+1) - x` for the headroom and
`k = y - x - 1`, the block weight is `min(k,w)` tilted by `u` exactly when `min(k,w) ≤ 1`, so the row
sum is `2^(σ-x) · ∑_{k≥1} min(k,w)·tilt·2^{-k-1}`, and

* if `w ≤ 1`: every weight is `≤ 1` and every tilt is `3`, giving `3·∑_{k≥1} 2^{-k-1} = 3/2`;
* if `w ≥ 2`: the `k = 1` term is `3·2^{-2} = 3/4` and the rest is `∑_{k≥2} k·2^{-k-1} = 3/4`.

Both cases give exactly `3/2`, so the certificate is tight at `λ = 2`.  The resulting bound is
`ker ≤ (3/2)^R · 2^σ`, i.e. `log₂ = R log₂(3/2) + σ ≈ 3.755` bits per block against a budget of
`3.82`–`3.87` (`T/R = 0.60`, `J = 200`–`300`); see `scratch/shapetail_2026-09-16`.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace ShapeCertificate

open Finset BlockCubeInstance OddBlack ShapeTailRed ShapeBridge LocalWindow

variable (b : ℕ → ℕ)

/-! ## 1. The block choice set is an interval -/

theorem card_Bset (l x y : ℕ) :
    (Bset b l x y).card = min (y - x - 1) (b (2 * l + 1) - x) := by
  classical
  rcases le_or_gt y (x + 1) with hy | hy
  · have : Bset b l x y = ∅ := by
      apply eq_empty_of_forall_notMem
      intro z hz
      simp only [Bset, mem_filter, mem_Ioo] at hz
      omega
    rw [this]
    simp only [card_empty]
    omega
  rcases le_or_gt (b (2 * l + 1)) x with hc | hc
  · have : Bset b l x y = ∅ := by
      apply eq_empty_of_forall_notMem
      intro z hz
      simp only [Bset, mem_filter, mem_Ioo] at hz
      omega
    rw [this]
    simp only [card_empty]
    omega
  · -- the set is `Ioo x (min y (cap+1))`
    have hEq : Bset b l x y = Ioo x (min y (b (2 * l + 1) + 1)) := by
      ext z
      simp only [Bset, mem_filter, mem_Ioo, lt_min_iff]
      omega
    rw [hEq, Nat.card_Ioo]
    omega

/-! ## 2. Two exact dyadic identities -/

/-- `∑_{i<n} 2^{-(i+2)} = 1/2 - 2^{-(n+1)}`. -/
theorem sum_inv_two_pow_eq (n : ℕ) :
    ∑ i ∈ range n, (1 : ℝ) / 2 ^ (i + 2) = 1 / 2 - 1 / 2 ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [sum_range_succ, ih]
    have hp : (0 : ℝ) < 2 ^ n := by positivity
    rw [pow_succ, pow_succ, pow_succ]
    field_simp
    ring

theorem sum_inv_two_pow_le (n : ℕ) :
    ∑ i ∈ range n, (1 : ℝ) / 2 ^ (i + 2) ≤ 1 / 2 := by
  rw [sum_inv_two_pow_eq]
  have : (0 : ℝ) < 1 / 2 ^ (n + 1) := by positivity
  linarith

/-- `∑_{i<n} (i+2)·2^{-(i+3)} = 3/4 - (n+3)·2^{-(n+2)}`. -/
theorem sum_succ_mul_inv_two_pow_eq (n : ℕ) :
    ∑ i ∈ range n, ((i : ℝ) + 2) / 2 ^ (i + 3) = 3 / 4 - ((n : ℝ) + 3) / 2 ^ (n + 2) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [sum_range_succ, ih]
    have hp : (0 : ℝ) < 2 ^ n := by positivity
    push_cast
    rw [pow_succ, pow_succ, pow_succ, pow_succ]
    field_simp
    ring

theorem sum_succ_mul_inv_two_pow_le (n : ℕ) :
    ∑ i ∈ range n, ((i : ℝ) + 2) / 2 ^ (i + 3) ≤ 3 / 4 := by
  rw [sum_succ_mul_inv_two_pow_eq]
  have : (0 : ℝ) ≤ ((n : ℝ) + 3) / 2 ^ (n + 2) := by positivity
  linarith

/-! ## 3. The certificate -/

/-- The certificate weight `h(l,x) = 2^(σ-x)`. -/
noncomputable def hcert (σ : ℕ) : ℕ → Fin (σ + 1) → ℝ := fun _ x => (2 : ℝ) ^ (σ - (x : ℕ))

theorem hcert_pos (σ : ℕ) (l : ℕ) (y : Fin (σ + 1)) : 0 < hcert σ l y := by
  unfold hcert; positivity

/-- **The super-eigenvector inequality.**  With tilt `u = 3` and `h = 2^(σ-x)`, the block kernel
satisfies `∑_y blockW(l,x,y) h(l+1,y) ≤ (3/2) h(l,x)` at every layer and every state. -/
theorem blockW_superEigen (σ : ℕ) (l : ℕ) (x : Fin (σ + 1)) :
    ∑ y : Fin (σ + 1), blockW b 3 σ l x y * hcert σ (l + 1) y ≤ (3 / 2) * hcert σ l x := by
  classical
  set X := (x : ℕ) with hX
  set w := b (2 * l + 1) - X with hw
  have hXσ : X ≤ σ := by have := x.isLt; omega
  -- rewrite the sum over `Fin (σ+1)` as a sum over `range (σ+1)`
  have hfin : ∑ y : Fin (σ + 1), blockW b 3 σ l x y * hcert σ (l + 1) y
      = ∑ y ∈ range (σ + 1), ((min (y - X - 1) w : ℕ) : ℝ) *
          (if min (y - X - 1) w ≤ 1 then (3 : ℝ) else 1) * (2 : ℝ) ^ (σ - y) := by
    rw [← Fin.sum_univ_eq_sum_range (fun y => ((min (y - X - 1) w : ℕ) : ℝ) *
      (if min (y - X - 1) w ≤ 1 then (3 : ℝ) else 1) * (2 : ℝ) ^ (σ - y)) (σ + 1)]
    refine sum_congr rfl fun y _ => ?_
    unfold blockW hcert
    rw [card_Bset]
  -- terms with `y ≤ X + 1` vanish, so the sum runs over `Ico (X+2) (σ+1)`
  have hset : ∑ y ∈ range (σ + 1), ((min (y - X - 1) w : ℕ) : ℝ) *
        (if min (y - X - 1) w ≤ 1 then (3 : ℝ) else 1) * (2 : ℝ) ^ (σ - y)
      = ∑ y ∈ Ico (X + 2) (σ + 1), ((min (y - X - 1) w : ℕ) : ℝ) *
        (if min (y - X - 1) w ≤ 1 then (3 : ℝ) else 1) * (2 : ℝ) ^ (σ - y) := by
    rw [← sum_filter_add_sum_filter_not (range (σ + 1)) (fun y => X + 2 ≤ y)]
    have hz : ∑ y ∈ (range (σ + 1)).filter (fun y => ¬ X + 2 ≤ y),
        ((min (y - X - 1) w : ℕ) : ℝ) *
          (if min (y - X - 1) w ≤ 1 then (3 : ℝ) else 1) * (2 : ℝ) ^ (σ - y) = 0 := by
      refine sum_eq_zero fun y hy => ?_
      obtain ⟨hy1, hy2⟩ := mem_filter.mp hy
      have : min (y - X - 1) w = 0 := by omega
      rw [this]
      simp
    have heq : (range (σ + 1)).filter (fun y => X + 2 ≤ y) = Ico (X + 2) (σ + 1) := by
      ext y
      simp only [mem_filter, mem_range, mem_Ico]
      omega
    rw [hz, add_zero, heq]
  rw [hfin, hset, Finset.sum_Ico_eq_sum_range]
  -- reindex: `y = X + 2 + i`
  have hterm : ∀ i ∈ range (σ + 1 - (X + 2)),
      ((min (X + 2 + i - X - 1) w : ℕ) : ℝ) *
        (if min (X + 2 + i - X - 1) w ≤ 1 then (3 : ℝ) else 1) * (2 : ℝ) ^ (σ - (X + 2 + i))
      = (2 : ℝ) ^ (σ - X) * ((((min (i + 1) w : ℕ)) : ℝ) *
          (if min (i + 1) w ≤ 1 then (3 : ℝ) else 1) / 2 ^ (i + 2)) := by
    intro i hi
    have hi' : i < σ + 1 - (X + 2) := mem_range.mp hi
    have hidx : X + 2 + i - X - 1 = i + 1 := by omega
    have hpow : (2 : ℝ) ^ (σ - X) = (2 : ℝ) ^ (σ - (X + 2 + i)) * 2 ^ (i + 2) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hidx, hpow]
    have h2 : (0 : ℝ) < 2 ^ (i + 2) := by positivity
    field_simp
  rw [sum_congr rfl hterm, ← mul_sum]
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (σ - X) := by positivity
  rw [show (3 : ℝ) / 2 * hcert σ l x = (2 : ℝ) ^ (σ - X) * (3 / 2) by
    unfold hcert; rw [← hX]; ring]
  refine mul_le_mul_of_nonneg_left ?_ hpow.le
  set N := σ + 1 - (X + 2) with hN
  rcases le_or_gt w 1 with hw1 | hw2
  · -- headroom ≤ 1: every weight is ≤ 1 and every tilt is 3
    have hb : ∀ i ∈ range N, (((min (i + 1) w : ℕ)) : ℝ) *
        (if min (i + 1) w ≤ 1 then (3 : ℝ) else 1) / 2 ^ (i + 2) ≤ (3 : ℝ) / 2 ^ (i + 2) := by
      intro i _
      have hmin : min (i + 1) w ≤ 1 := by omega
      have hm : ((min (i + 1) w : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hmin
      have hnn : (0 : ℝ) ≤ ((min (i + 1) w : ℕ) : ℝ) := Nat.cast_nonneg _
      have hnum : ((min (i + 1) w : ℕ) : ℝ) *
          (if min (i + 1) w ≤ 1 then (3 : ℝ) else 1) ≤ 3 := by
        rw [if_pos hmin]
        nlinarith
      gcongr
    refine le_trans (sum_le_sum hb) ?_
    have hrw : ∑ i ∈ range N, (3 : ℝ) / 2 ^ (i + 2)
        = 3 * ∑ i ∈ range N, (1 : ℝ) / 2 ^ (i + 2) := by
      rw [mul_sum]
      refine sum_congr rfl fun i _ => ?_
      ring
    rw [hrw]
    have := sum_inv_two_pow_le N
    linarith
  · -- headroom ≥ 2: peel the first term, the rest is untilted
    rcases Nat.eq_zero_or_pos N with hN0 | hNpos
    · rw [hN0]
      norm_num
    obtain ⟨m, hm⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
    rw [hm, sum_range_succ']
    have hb : ∀ i ∈ range m, (((min (i + 1 + 1) w : ℕ)) : ℝ) *
        (if min (i + 1 + 1) w ≤ 1 then (3 : ℝ) else 1) / 2 ^ (i + 1 + 2)
        ≤ ((i : ℝ) + 2) / 2 ^ (i + 3) := by
      intro i _
      have hmin : ¬ (min (i + 1 + 1) w ≤ 1) := by omega
      rw [if_neg hmin, mul_one]
      have hidx : i + 1 + 2 = i + 3 := by omega
      rw [hidx]
      have hle : ((min (i + 1 + 1) w : ℕ) : ℝ) ≤ (i : ℝ) + 2 := by
        have hnat : min (i + 1 + 1) w ≤ i + 2 := le_trans (min_le_left _ _) (by omega)
        exact_mod_cast hnat
      gcongr
    have hfirst : (((min (0 + 1) w : ℕ)) : ℝ) *
        (if min (0 + 1) w ≤ 1 then (3 : ℝ) else 1) / 2 ^ (0 + 2) = 3 / 4 := by
      have hmw : min (0 + 1) w = 1 := by omega
      rw [hmw]
      norm_num
    rw [hfirst]
    have htail := sum_succ_mul_inv_two_pow_le m
    have hsum := sum_le_sum hb
    linarith


/-! ## 4. `ShapeTail` with the certificate discharged -/

open ShapeBridge in
/-- **`ShapeTail` from the explicit certificate.**  No super-eigenvector hypothesis remains: with
tilt `u = 3` the shape tail holds with any `ρ₁` satisfying the single arithmetic inequality
`j₀ · (3/2)^(j₀/2) · 2^σ ≤ ρ₁ · 3^T · C(σ-1, j₀-1)`. -/
theorem shapeTail_of_arith {j0 σ t N0 K T : ℕ} {ρ₁ : ℝ}
    (hj : 1 ≤ j0) (hρ : 0 ≤ ρ₁) (hj2 : 2 * (j0 / 2) = j0)
    (hchord : ∀ j ≤ j0, ∀ p : ℕ, j0 * p ≤ j * b j0 → p ≤ b j)
    (hjσ : j0 ≤ σ) (hσ : σ ≤ b j0)
    (hK : K + T + σ / (N0 + 2) ≤ j0 / 2)
    (harith : (j0 : ℝ) * ((3 / 2 : ℝ) ^ (j0 / 2) * (2 : ℝ) ^ σ)
      ≤ ρ₁ * 3 ^ T * (Nat.choose (σ - 1) (j0 - 1) : ℝ)) :
    ShapeTail b j0 σ N0 K ρ₁ := by
  refine shapeTail_of_superEigen b (t := t) (h := hcert σ) (M := 3 / 2) hj (by norm_num) hρ hj2
    hchord hjσ hσ hK (hcert_pos σ) (by norm_num) (fun l x => blockW_superEigen b σ l x) ?_
  -- the boundary ratio is `2^σ`
  have hx : hcert σ 0 (⟨0, by omega⟩ : Fin (σ + 1)) = (2 : ℝ) ^ σ := by
    unfold hcert; norm_num
  have hz : hcert σ (0 + j0 / 2) (⟨σ, by omega⟩ : Fin (σ + 1)) = 1 := by
    unfold hcert; simp
  rw [hx, hz, div_one]
  exact harith

end ShapeCertificate
end EOC
