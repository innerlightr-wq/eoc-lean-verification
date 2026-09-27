import EOC.AverageOddDark

/-!
# ShapeTail off the top shell and at positive barrier offsets

`ShapeCertificate.shapeTail_of_arith` reduces `ShapeTail` for **any** barrier `b` (satisfying the
chord condition) and **any** shell `j₀ ≤ σ ≤ b j₀` to the single inequality `j₀ · 3^(j₀/2) · 2^(σ+e)
≤ 2^(j₀/2) · 3^T · C(σ−1, j₀−1)` (`ShapeUnconditional.Arith j₀ σ e`).  The barrier enters only
through the side conditions, not through the inequality.  This file moves the proved top-shell
certificate `Arith j (b₀ j) (j/300)` to a region of shells:

* `arith_down` — one shell down costs one rate bit: `Arith j s (e+1) → Arith j (s−1) e` when `s − 1
  ≤ 4 (s − j)` (from `C(s−2, j−1)(s−1) = C(s−1, j−1)(s−j)`);
* `arith_up` — shells up are free: `Arith j s e → Arith j (s+1) e` when `s + 2 ≤ 2j`;
* `arith_mono` — a smaller rate exponent is easier;
* `barrier_offset` — `collatzBarrier U j = collatzBarrier 0 j + U`;
* `lower_barrier` — `79 j < 50 (b₀ j + 1)`, i.e. `b₀ j > 1.58 j − 1`;
* **`arith_region`** — `Arith j σ (j/300 − δ)` for every even `j ≥ 300` and every shell with `b₀ j ≤
  σ + δ`, `δ ≤ j/300`, `σ + 2 ≤ 2j`;
* **`shapeTail_region`** — `ShapeTail (collatzBarrier U) j σ N₀ K (2^{−(j/300 − δ)})` on the same
  region, for every barrier offset `U` with `σ ≤ b_U j`, under the budget `K + ⌊31j/100⌋ +
  ⌊σ/(N₀+2)⌋ ≤ j/2`.

So the region needed downstream — shells within `δ ≤ j/300` below the zero-offset top shell, and the
whole range up to the offset-`U` top shell while `σ ≤ 2j − 2` — carries an exponentially small shape
tail with rate `j/300 − δ`.  No `sorry`, `admit`, `axiom`, `opaque`, or `native_decide`.
-/

namespace EOC
namespace ShapeRegion

open Finset CapacityBounds OddBlack ShapeCertificate ShapeUnconditional

/-- One shell down costs one rate bit. -/
theorem arith_down {j s e : ℕ} (hj : 1 ≤ j) (hjs : j + 1 ≤ s) (h4 : s - 1 ≤ 4 * (s - j))
    (h : Arith j s (e + 1)) : Arith j (s - 1) e := by
  unfold Arith at h ⊢
  set X := j * 3 ^ (j / 2) * 2 ^ (s - 1 + e)
  set Y := 2 ^ (j / 2) * 3 ^ (31 * j / 100)
  have hsplit : j * 3 ^ (j / 2) * 2 ^ (s + (e + 1)) = 4 * X := by
    simp only [X]
    rw [show s + (e + 1) = (s - 1 + e) + 2 by omega, pow_add]
    ring
  rw [hsplit] at h
  -- C(s−2, j−1)·(s−1) = C(s−1, j−1)·(s−j)
  have hc := Nat.choose_mul_succ_eq (s - 2) (j - 1)
  rw [show s - 2 + 1 = s - 1 by omega, show s - 1 - (j - 1) = s - j by omega] at hc
  have hpos : 0 < s - 1 := by omega
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc X * (s - 1) ≤ X * (4 * (s - j)) := Nat.mul_le_mul_left _ h4
    _ = (4 * X) * (s - j) := by ring
    _ ≤ (Y * (s - 1).choose (j - 1)) * (s - j) := Nat.mul_le_mul_right _ h
    _ = Y * ((s - 1).choose (j - 1) * (s - j)) := by ring
    _ = Y * (s - 2).choose (j - 1) * (s - 1) := by rw [← hc]; ring

/-- Shells up are free while `s + 2 ≤ 2j`. -/
theorem arith_up {j s e : ℕ} (hj : 1 ≤ j) (hjs : j ≤ s) (h2 : s + 2 ≤ 2 * j)
    (h : Arith j s e) : Arith j (s + 1) e := by
  unfold Arith at h ⊢
  set X := j * 3 ^ (j / 2) * 2 ^ (s + e)
  set Y := 2 ^ (j / 2) * 3 ^ (31 * j / 100)
  have hsplit : j * 3 ^ (j / 2) * 2 ^ (s + 1 + e) = 2 * X := by
    simp only [X]
    rw [show s + 1 + e = (s + e) + 1 by omega, pow_succ]
    ring
  rw [hsplit, show s + 1 - 1 = s by omega]
  -- C(s−1, j−1)·s = C(s, j−1)·(s−j+1)
  have hc := Nat.choose_mul_succ_eq (s - 1) (j - 1)
  rw [show s - 1 + 1 = s by omega, show s - (j - 1) = s - j + 1 by omega] at hc
  have hpos : 0 < s - j + 1 := by omega
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc 2 * X * (s - j + 1) = X * (2 * (s - j + 1)) := by ring
    _ ≤ X * s := Nat.mul_le_mul_left _ (by omega)
    _ ≤ (Y * (s - 1).choose (j - 1)) * s := Nat.mul_le_mul_right _ h
    _ = Y * ((s - 1).choose (j - 1) * s) := by ring
    _ = Y * s.choose (j - 1) * (s - j + 1) := by rw [hc]; ring

/-- A smaller rate exponent is easier. -/
theorem arith_mono {j s e e' : ℕ} (hee : e' ≤ e) (h : Arith j s e) : Arith j s e' := by
  unfold Arith at h ⊢
  refine le_trans ?_ h
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- The offset barrier is the zero-offset barrier shifted by `U`. -/
theorem barrier_offset (U j : ℕ) : collatzBarrier U j = collatzBarrier 0 j + U := by
  unfold collatzBarrier
  have h := Nat.floor_add_natCast (barrier_arg_nonneg 0 j) U
  simp only [Nat.cast_zero, add_zero] at h ⊢
  exact h

/-- `79 j < 50 (b₀ j + 1)` (from `2^79 < 3^50`), i.e. `b₀ j > 1.58 j − 1`. -/
theorem lower_barrier (j : ℕ) (hj : 1 ≤ j) : 79 * j < 50 * (collatzBarrier 0 j + 1) := by
  have h2 := (barrier_pow_bounds j).2
  have hk : 2 ^ 79 < 3 ^ 50 := by decide +kernel
  apply lt_of_two_pow_lt
  calc 2 ^ (79 * j) = (2 ^ 79) ^ j := by rw [← pow_mul]
    _ < (3 ^ 50) ^ j := Nat.pow_lt_pow_left hk (by omega)
    _ = (3 ^ j) ^ 50 := by rw [← pow_mul, ← pow_mul, mul_comm]
    _ ≤ (2 ^ (collatzBarrier 0 j + 1)) ^ 50 := Nat.pow_le_pow_left h2.le _
    _ = 2 ^ (50 * (collatzBarrier 0 j + 1)) := by rw [← pow_mul, mul_comm]

/-- Descent from the top shell: `Arith j (b₀ j − δ) (j/300 − δ)` for `δ ≤ j/300`. -/
theorem arith_below {j : ℕ} (hj : 300 ≤ j) (hev : 2 ∣ j) :
    ∀ δ, δ ≤ j / 300 → Arith j (collatzBarrier 0 j - δ) (j / 300 - δ) := by
  have hlow := lower_barrier j (by omega)
  intro δ
  induction δ with
  | zero => intro _; simpa using arith_allEven hj hev
  | succ δ ih =>
    intro hδ
    have h := ih (by omega)
    rw [show j / 300 - δ = (j / 300 - (δ + 1)) + 1 by omega] at h
    have h' := arith_down (s := collatzBarrier 0 j - δ) (by omega) (by omega) (by omega) h
    rwa [show collatzBarrier 0 j - δ - 1 = collatzBarrier 0 j - (δ + 1) by omega] at h'

/-- Ascent from the top shell is free while `σ + 2 ≤ 2j`. -/
theorem arith_above {j e : ℕ} (hj : 300 ≤ j) (h0 : Arith j (collatzBarrier 0 j) e) :
    ∀ k, collatzBarrier 0 j + k + 2 ≤ 2 * j → Arith j (collatzBarrier 0 j + k) e := by
  intro k
  induction k with
  | zero => intro _; simpa using h0
  | succ k ih =>
    intro hk
    have h := arith_up (s := collatzBarrier 0 j + k) (by omega)
      (by have := le_collatzBarrier 0 j; omega) (by omega) (ih (by omega))
    rwa [show collatzBarrier 0 j + k + 1 = collatzBarrier 0 j + (k + 1) by omega] at h

/-- **The certificate on the whole region.** For even `j ≥ 300`, every shell `σ` with `b₀ j ≤ σ +
δ`, `δ ≤ j/300` and `σ + 2 ≤ 2j` satisfies `Arith j σ (j/300 − δ)`. -/
theorem arith_region {j σ δ : ℕ} (hj : 300 ≤ j) (hev : 2 ∣ j) (hlo : collatzBarrier 0 j ≤ σ + δ)
    (hδ : δ ≤ j / 300) (h2 : σ + 2 ≤ 2 * j) : Arith j σ (j / 300 - δ) := by
  rcases le_or_gt σ (collatzBarrier 0 j) with hσ | hσ
  · have h := arith_below hj hev (collatzBarrier 0 j - σ) (by omega)
    rw [show collatzBarrier 0 j - (collatzBarrier 0 j - σ) = σ by omega] at h
    exact arith_mono (by omega) h
  · have h := arith_above hj (arith_allEven hj hev) (σ - collatzBarrier 0 j) (by omega)
    rw [show collatzBarrier 0 j + (σ - collatzBarrier 0 j) = σ by omega] at h
    exact arith_mono (by omega) h

/-- **ShapeTail on the region, at any barrier offset.** For even `j ≥ 300`, barrier offset `U`, and
a shell `σ` with `b₀ j ≤ σ + δ`, `δ ≤ j/300`, `σ ≤ b_U j`, `σ + 2 ≤ 2j`, and budget `K + ⌊31j/100⌋ +
⌊σ/(N₀+2)⌋ ≤ j/2`, the shape tail holds with `ρ₁ = 2^{−(j/300 − δ)}`. -/
theorem shapeTail_region {U j σ δ N0 K : ℕ} (hj : 300 ≤ j) (hev : 2 ∣ j)
    (hlo : collatzBarrier 0 j ≤ σ + δ) (hδ : δ ≤ j / 300) (hhi : σ ≤ collatzBarrier U j)
    (h2 : σ + 2 ≤ 2 * j) (hK : K + 31 * j / 100 + σ / (N0 + 2) ≤ j / 2) :
    ShapeTail (collatzBarrier U) j σ N0 K ((2 : ℝ) ^ (j / 300 - δ))⁻¹ := by
  have h := arith_region hj hev hlo hδ h2
  unfold Arith at h
  have hjσ : j ≤ σ := by
    have := lower_barrier j (by omega)
    omega
  exact shapeTail_of_arith (collatzBarrier U) (t := 0) (T := 31 * j / 100)
    (by omega) (by positivity) (by omega) (collatz_chord U (by omega)) hjσ hhi hK (real_of_nat h)

/-- The zero-offset special case below the top shell. -/
theorem shapeTail_lowerShell {j δ N0 K : ℕ} (hj : 300 ≤ j) (hev : 2 ∣ j) (hδ : δ ≤ j / 300)
    (hK : K + 31 * j / 100 + (collatzBarrier 0 j - δ) / (N0 + 2) ≤ j / 2) :
    ShapeTail (collatzBarrier 0) j (collatzBarrier 0 j - δ) N0 K ((2 : ℝ) ^ (j / 300 - δ))⁻¹ := by
  have hlt := ShapeUnconditional.barrier_lt j (by omega)
  exact shapeTail_region hj hev (by omega) hδ (by omega) (by omega) hK

end ShapeRegion
end EOC
