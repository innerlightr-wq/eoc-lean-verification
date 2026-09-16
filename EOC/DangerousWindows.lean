import EOC.PressureBridge

/-!
# Dangerous windows ⇒ `SummedOddDarkPressure`

`PressureBridge.sum_pow_nodd_le_geo` bounds the odd-dark moment by the geometric (killed `P*`)
kernel.  This file turns **per-window** mass bounds into the summed pressure hypothesis consumed by
`AverageOddDark.lowFreqDecay_of_summedPressure`, leaving a single count of dangerous windows.

* `val_le_prod_windows` — heterogeneous window product: if the `K`-block window starting at
  `i K` has mass `≤ M i` from every state, then the `W K`-block mass is `≤ ∏_{i<W} M i`
  (with a remainder factor in `val_le_prod_windows_rem`).
* `val_one_le` — **universal one-block ceiling**: for the geometric odd-dark weight with
  `p = 1 − q`, every row sum is `≤ 1 + (s−1) q` (geometric series; no environment input).
* `q_le` — for the Collatz barrier and `j ≥ 300`, `q = (σ−j)/(σ−1) ≤ 37/100`, so `1 + 2q ≤ 2^{4/5}`:
  the dangerous-window ceiling is **2/5 bits per step**.
* `summedPressure_of_dangerousWindows` — if for every low frequency all but `|bad| ≤ φ W + E` of the
  `W` disjoint `K`-windows have mass `≤ 2^{2Kθ_d}`, then `SummedOddDarkPressure` holds with
  `θ = θ_d + φ (2/5 − θ_d)` and any `C` with
  `log₂(σ j / p) + (4/5 − 2θ_d) K E + (4/5) K ≤ C log₂ j`.
  At `θ_d = 1/10` the target `θ ≤ 1/6` is exactly `φ ≤ 2/9`.

No `sorry`, `admit`, `axiom`, `opaque`, or `native_decide`.
-/

namespace EOC
namespace DangerousWindows

open Finset LocalWindow PressureBridge CapacityBounds

/-! ## 1. Heterogeneous window products -/

section Windows

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem val_nonneg {w : ℕ → S → S → ℝ} (hw : ∀ l x y, 0 ≤ w l x y) (l n : ℕ) (x : S) :
    0 ≤ val w l n x := sum_nonneg fun y _ => ker_nonneg hw l n x y

/-- **Heterogeneous window product.** -/
theorem val_le_prod_windows {w : ℕ → S → S → ℝ} (hw : ∀ l x y, 0 ≤ w l x y) {K : ℕ}
    (M : ℕ → ℝ) (hM : ∀ i, 0 ≤ M i) :
    ∀ W, (∀ i < W, ∀ y, val w (i * K) K y ≤ M i) →
      ∀ x, val w 0 (W * K) x ≤ ∏ i ∈ range W, M i := by
  intro W
  induction W with
  | zero =>
    intro _ x
    simp only [Nat.zero_mul, prod_range_zero]
    unfold LocalWindow.val
    simp only [ker_zero]
    rw [sum_ite_eq]
    simp
  | succ W ih =>
    intro hwin x
    rw [show (W + 1) * K = W * K + K by ring, val_add, prod_range_succ]
    have hW := hwin W (by omega)
    calc ∑ y, ker w 0 (W * K) x y * val w (0 + W * K) K y
        ≤ ∑ y, ker w 0 (W * K) x y * M W := by
          refine sum_le_sum fun y _ => mul_le_mul_of_nonneg_left ?_ (ker_nonneg hw _ _ _ _)
          simpa using hW y
      _ = val w 0 (W * K) x * M W := by rw [← sum_mul]; rfl
      _ ≤ (∏ i ∈ range W, M i) * M W :=
          mul_le_mul_of_nonneg_right (ih (fun i hi y => hwin i (by omega) y) x) (hM W)

/-- Window product with a remainder of `ρ` blocks. -/
theorem val_le_prod_windows_rem {w : ℕ → S → S → ℝ} (hw : ∀ l x y, 0 ≤ w l x y) {K W ρ : ℕ}
    (M : ℕ → ℝ) (hM : ∀ i, 0 ≤ M i) (hwin : ∀ i < W, ∀ y, val w (i * K) K y ≤ M i)
    {Mrem : ℝ} (hrem : ∀ y, val w (W * K) ρ y ≤ Mrem) (x : S) :
    val w 0 (W * K + ρ) x ≤ (∏ i ∈ range W, M i) * Mrem := by
  rw [val_add]
  calc ∑ y, ker w 0 (W * K) x y * val w (0 + W * K) ρ y
      ≤ ∑ y, ker w 0 (W * K) x y * Mrem :=
        sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (by simpa using hrem y)
          (ker_nonneg hw _ _ _ _)
    _ = val w 0 (W * K) x * Mrem := by rw [← sum_mul]; rfl
    _ ≤ (∏ i ∈ range W, M i) * Mrem := by
        have h0 : 0 ≤ Mrem := le_trans (val_nonneg hw _ _ x) (hrem x)
        exact mul_le_mul_of_nonneg_right (val_le_prod_windows hw M hM W hwin x) h0

end Windows

/-! ## 2. Geometric partial sums -/

theorem sum_succ_mul_pow_mul_sq (q : ℝ) (N : ℕ) :
    (∑ k ∈ range N, ((k : ℝ) + 1) * q ^ k) * (1 - q) ^ 2 =
      1 - ((N : ℝ) + 1) * q ^ N + N * q ^ (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, add_mul, ih]; push_cast; ring

theorem sum_mul_pow_mul_sq (q : ℝ) (N : ℕ) :
    (∑ k ∈ range N, (k : ℝ) * q ^ k) * (1 - q) ^ 2 =
      q - (N : ℝ) * q ^ N + ((N : ℝ) - 1) * q ^ (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, add_mul, ih]; push_cast; ring

theorem geom_bound {q s : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hs : 1 ≤ s) (N : ℕ) :
    (1 - q) ^ 2 * ∑ k ∈ range N, q ^ k * (((k : ℝ) + 1) + (s - 1) * k) ≤ 1 + (s - 1) * q := by
  have h1 := sum_succ_mul_pow_mul_sq q N
  have h2 := sum_mul_pow_mul_sq q N
  have hqN : 0 ≤ q ^ N := pow_nonneg hq0 N
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have e : (1 - q) ^ 2 * ∑ k ∈ range N, q ^ k * (((k : ℝ) + 1) + (s - 1) * k) =
      (∑ k ∈ range N, ((k : ℝ) + 1) * q ^ k) * (1 - q) ^ 2 +
        (s - 1) * ((∑ k ∈ range N, (k : ℝ) * q ^ k) * (1 - q) ^ 2) := by
    rw [mul_comm, sum_mul, sum_mul, sum_mul, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun k _ => ?_; ring
  rw [e, h1, h2]
  have hA : ((N : ℝ) + 1) * q ^ N - N * q ^ (N + 1) ≥ 0 := by
    rw [pow_succ]; nlinarith [mul_nonneg hN hqN, mul_nonneg (mul_nonneg hN hqN) hq0]
  have hB : (N : ℝ) * q ^ N - ((N : ℝ) - 1) * q ^ (N + 1) ≥ 0 := by
    rw [pow_succ]; nlinarith [mul_nonneg hN hqN, mul_nonneg (mul_nonneg hN hqN) hq0]
  nlinarith

/-! ## 3. The universal one-block ceiling -/

section Ceiling

variable (b : ℕ → ℕ)

theorem card_Bset_le (r x y : ℕ) : (ShapeBridge.Bset b r x y).card ≤ y - x - 1 := by
  unfold ShapeBridge.Bset
  exact (card_filter_le _ _).trans (by rw [Nat.card_Ioo])

open Classical in
theorem oddW_le {m : ℕ} {d s : ℝ} {lam : ℕ} (hs : 1 ≤ s) (r x y : ℕ) :
    oddW b m d s lam r x y ≤ ((y - x - 1 : ℕ) : ℝ) + (s - 1) * ((y - x - 2 : ℕ) : ℝ) := by
  unfold oddW
  set B := ShapeBridge.Bset b r x y
  have hsplit : ∑ z ∈ B, (if z + 1 ∈ B ∧ OddBlack.Dark m d lam r z then s else 1) ≤
      ∑ z ∈ B, (1 + (s - 1) * (if z + 1 ∈ B then 1 else 0)) := by
    refine sum_le_sum fun z _ => ?_
    by_cases h1 : z + 1 ∈ B
    · by_cases h2 : OddBlack.Dark m d lam r z <;> simp [h1, h2]; linarith
    · simp [h1]
  have hel : (B.filter (fun z => z + 1 ∈ B)).card ≤ y - x - 2 := by
    have hsub : B.filter (fun z => z + 1 ∈ B) ⊆ Ioo x (y - 1) := by
      intro z hz
      simp only [B, ShapeBridge.Bset, mem_filter, mem_Ioo] at hz ⊢
      omega
    exact (card_le_card hsub).trans (by rw [Nat.card_Ioo]; omega)
  calc _ ≤ _ := hsplit
    _ = (B.card : ℝ) + (s - 1) * ((B.filter (fun z => z + 1 ∈ B)).card : ℝ) := by
        rw [sum_add_distrib, sum_const, nsmul_eq_mul, mul_one, ← mul_sum, sum_ite, sum_const_zero,
          add_zero, sum_const, nsmul_eq_mul, mul_one]
    _ ≤ _ := by
        have h1 : (B.card : ℝ) ≤ ((y - x - 1 : ℕ) : ℝ) := by exact_mod_cast card_Bset_le b r x y
        have h2 : ((B.filter (fun z => z + 1 ∈ B)).card : ℝ) ≤ ((y - x - 2 : ℕ) : ℝ) := by
          exact_mod_cast hel
        nlinarith

theorem oddW_eq_zero_of_lt {m : ℕ} {d s : ℝ} {lam : ℕ} {r x y : ℕ} (hy : y < x + 2) :
    oddW b m d s lam r x y = 0 := by
  unfold oddW
  have : ShapeBridge.Bset b r x y = ∅ := by
    apply eq_empty_of_forall_notMem
    intro z hz
    simp only [ShapeBridge.Bset, mem_filter, mem_Ioo] at hz
    omega
  rw [this, sum_empty]

/-- **Universal one-block ceiling** for the geometric odd-dark weight: `val ≤ 1 + (s−1) q`. -/
theorem val_one_le {σ m : ℕ} {d s q : ℝ} {lam : ℕ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hs : 1 ≤ s)
    (l : ℕ) (x : Fin (σ + 1)) :
    val (geoW (1 - q) q (oddW b m d s lam) σ) l 1 x ≤ 1 + (s - 1) * q := by
  have hs1 := LocalWindow.val_succ (geoW (1 - q) q (oddW b m d s lam) σ) l 0 x
  rw [zero_add] at hs1
  rw [hs1]
  have hval0 : ∀ y : Fin (σ + 1), val (geoW (1 - q) q (oddW b m d s lam) σ) (l + 1) 0 y = 1 := by
    intro y; unfold LocalWindow.val; simp [ker_zero]
  simp only [hval0, mul_one]
  set X := (x : ℕ)
  -- rewrite as a range sum and drop the vanishing terms
  have hterm : ∀ y : ℕ, y < σ + 1 →
      (1 - q) ^ 2 * q ^ ((y : ℤ) - X - 2) * oddW b m d s lam l X y ≤
        (if X + 2 ≤ y then (1 - q) ^ 2 * (q ^ (y - X - 2) * (((y - X - 2 : ℕ) : ℝ) + 1 +
          (s - 1) * ((y - X - 2 : ℕ) : ℝ))) else 0) := by
    intro y _
    split_ifs with hy
    · have hz : ((y : ℤ) - X - 2) = ((y - X - 2 : ℕ) : ℤ) := by omega
      rw [hz, zpow_natCast]
      have hW := oddW_le b (m := m) (d := d) (lam := lam) hs l X y
      have e1 : ((y - X - 1 : ℕ) : ℝ) = ((y - X - 2 : ℕ) : ℝ) + 1 := by
        rw [show y - X - 1 = (y - X - 2) + 1 by omega]; push_cast; ring
      rw [e1] at hW
      have hpos : 0 ≤ (1 - q) ^ 2 * q ^ (y - X - 2) := by positivity
      calc (1 - q) ^ 2 * q ^ (y - X - 2) * oddW b m d s lam l X y
          ≤ (1 - q) ^ 2 * q ^ (y - X - 2) * (((y - X - 2 : ℕ) : ℝ) + 1 +
              (s - 1) * ((y - X - 2 : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left hW hpos
        _ = _ := by ring
    · rw [oddW_eq_zero_of_lt b (by omega), mul_zero]
  calc ∑ y : Fin (σ + 1), geoW (1 - q) q (oddW b m d s lam) σ l x y
      = ∑ y ∈ range (σ + 1), (1 - q) ^ 2 * q ^ ((y : ℤ) - X - 2) * oddW b m d s lam l X y := by
        rw [← Fin.sum_univ_eq_sum_range (fun y => (1 - q) ^ 2 * q ^ ((y : ℤ) - X - 2) *
          oddW b m d s lam l X y) (σ + 1)]
        rfl
    _ ≤ ∑ y ∈ range (σ + 1), (if X + 2 ≤ y then (1 - q) ^ 2 * (q ^ (y - X - 2) *
          (((y - X - 2 : ℕ) : ℝ) + 1 + (s - 1) * ((y - X - 2 : ℕ) : ℝ))) else 0) :=
        sum_le_sum fun y hy => hterm y (mem_range.mp hy)
    _ ≤ (1 - q) ^ 2 * ∑ k ∈ range (σ + 1), q ^ k * (((k : ℝ) + 1) + (s - 1) * k) := by
        rw [sum_ite, sum_const_zero, add_zero, ← mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hinj : ∀ a ∈ (range (σ + 1)).filter (fun y => X + 2 ≤ y),
            ∀ c ∈ (range (σ + 1)).filter (fun y => X + 2 ≤ y), a - X - 2 = c - X - 2 → a = c := by
          intro a ha c hc h
          simp only [mem_filter] at ha hc
          omega
        rw [← sum_image (f := fun k : ℕ => q ^ k * (((k : ℝ) + 1) + (s - 1) * k)) hinj]
        refine sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => by positivity
        intro k hk
        obtain ⟨a, ha, rfl⟩ := mem_image.mp hk
        simp only [mem_filter, mem_range] at ha ⊢
        omega
    _ ≤ 1 + (s - 1) * q := geom_bound hq0 hq1 hs _

/-- `K`-block ceiling. -/
theorem val_le_ceiling {σ m : ℕ} {d s q : ℝ} {lam : ℕ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hs : 1 ≤ s)
    (K l : ℕ) (x : Fin (σ + 1)) :
    val (geoW (1 - q) q (oddW b m d s lam) σ) l K x ≤ (1 + (s - 1) * q) ^ K := by
  have hw : ∀ l (x y : Fin (σ + 1)), 0 ≤ geoW (1 - q) q (oddW b m d s lam) σ l x y := by
    intro l x y; unfold geoW
    have := oddW_nonneg b (m := m) (d := d) (lam := lam) (by linarith : (0 : ℝ) ≤ s) l x y
    have : 0 ≤ q ^ ((y : ℤ) - x - 2) := zpow_nonneg hq0 _
    positivity
  have h := val_le_pow_of_window hw (K := 1) (M := 1 + (s - 1) * q)
    (fun l y => val_one_le b hq0 hq1 hs l y) K l x
  simpa using h

end Ceiling

/-! ## 4. The Collatz barrier: `q ≤ 37/100` and the `2/5` ceiling -/

theorem q_le {j : ℕ} (hj : 300 ≤ j) :
    ((collatzBarrier 0 j : ℝ) - j) / ((collatzBarrier 0 j : ℝ) - 1) ≤ 37 / 100 := by
  have h1 := ShapeUnconditional.barrier_lt j (by omega)
  have h2 := le_collatzBarrier 0 j
  have h3 : 63 * collatzBarrier 0 j + 37 ≤ 100 * j := by omega
  have h4 : (63 : ℝ) * collatzBarrier 0 j + 37 ≤ 100 * j := by exact_mod_cast h3
  have hσ : (1 : ℝ) < collatzBarrier 0 j := by
    have : (300 : ℝ) ≤ collatzBarrier 0 j := by exact_mod_cast (le_trans hj h2)
    linarith
  rw [div_le_iff₀ (by linarith)]
  linarith

theorem ceiling_le_rpow : (174 / 100 : ℝ) ≤ (2 : ℝ) ^ ((4 : ℝ) / 5) := by
  have hb : (0 : ℝ) ≤ (2 : ℝ) ^ ((4 : ℝ) / 5) := by positivity
  refine le_of_pow_le_pow_left₀ (n := 5) (by norm_num) hb ?_
  rw [← Real.rpow_natCast ((2 : ℝ) ^ ((4 : ℝ) / 5)) 5, ← Real.rpow_mul (by norm_num)]
  norm_num

theorem barrier_gt {j : ℕ} (hj : 2 ≤ j) : j < collatzBarrier 0 j := by
  have h3 := (ShapeUnconditional.barrier_pow_bounds j).2
  have h8 : 2 ^ (j + 1) ≤ 3 ^ j := by
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
    have hk : 2 ^ k ≤ 3 ^ k := Nat.pow_le_pow_left (by norm_num) k
    calc 2 ^ (k + 2 + 1) = 8 * 2 ^ k := by ring
      _ ≤ 9 * 3 ^ k := by omega
      _ = 3 ^ (k + 2) := by ring
  exact ShapeUnconditional.lt_of_two_pow_lt (lt_of_le_of_lt h8 h3) |> fun h => by omega

/-! ## 5. Dangerous windows ⇒ `SummedOddDarkPressure` -/

open Classical in
/-- **Dangerous-window wrapper.**  Let `σ = ⌊jα⌋`, `p = (j−1)/(σ−1)`, `q = (σ−j)/(σ−1)`, and
split the `j/2` pair blocks into `W` disjoint windows of `K` blocks plus `ρ ≤ K` remainder blocks.
If, for every frequency of every shell `u ≤ U`, all windows outside a set `bad` with
`|bad| ≤ φ W + E` have geometric mass `≤ 2^{2Kθ_d}` from every state, then
`SummedOddDarkPressure` holds with rate
`θ_d + φ (2/5 − θ_d)` and any `C` absorbing `log₂(σ j / p) + (4/5 − 2θ_d) K E + (4/5) K`.
Dangerous windows are paid for by the proved universal ceiling `2^{(4/5) K}`. -/
theorem summedPressure_of_dangerousWindows {j t U K W ρ : ℕ} {d θd φ E C : ℝ}
    (hj : 300 ≤ j) (hev : 2 ∣ j) (hR : j / 2 = W * K + ρ) (hρ : ρ ≤ K)
    (hθ0 : 0 ≤ θd) (hθ1 : θd ≤ 2 / 5) (hφ : 0 ≤ φ)
    (hC : Real.logb 2 ((collatzBarrier 0 j : ℝ) * j /
          (((j : ℝ) - 1) / ((collatzBarrier 0 j : ℝ) - 1))) +
        (4 / 5 - 2 * θd) * K * E + 4 / 5 * K ≤ C * Real.logb 2 j)
    (hwin : ∀ u ≤ U, ∀ lam ∈ ShellDecomposition.cshell (collatzBarrier 0 j + 1) t u,
      ∃ bad : Finset ℕ, (bad.card : ℝ) ≤ φ * W + E ∧
        ∀ i < W, i ∉ bad → ∀ y : Fin (collatzBarrier 0 j + 1),
          val (geoW (((j : ℝ) - 1) / ((collatzBarrier 0 j : ℝ) - 1))
              (((collatzBarrier 0 j : ℝ) - j) / ((collatzBarrier 0 j : ℝ) - 1))
              (oddW (collatzBarrier 0) (collatzBarrier 0 j + 1 + t) d 3 lam)
              (collatzBarrier 0 j)) (i * K) K y ≤ (2 : ℝ) ^ (2 * (K : ℝ) * θd)) :
    AverageOddDark.SummedOddDarkPressure (collatzBarrier 0) j (collatzBarrier 0 j) t U d 3
      (θd + φ * (2 / 5 - θd)) C := by
  set σ := collatzBarrier 0 j with hσdef
  set p : ℝ := ((j : ℝ) - 1) / ((σ : ℝ) - 1) with hp
  set q : ℝ := ((σ : ℝ) - j) / ((σ : ℝ) - 1) with hq
  have hjσ : j < σ := barrier_gt (by omega)
  have hσ1 : (1 : ℝ) < σ := by exact_mod_cast (by omega : 1 < σ)
  have hj1 : (1 : ℝ) < j := by exact_mod_cast (by omega : 1 < j)
  have hjσr : (j : ℝ) < σ := by exact_mod_cast hjσ
  have hq0 : 0 ≤ q := div_nonneg (by linarith) (by linarith)
  have hq37 : q ≤ 37 / 100 := q_le hj
  have hden : (σ : ℝ) - 1 ≠ 0 := by linarith
  have hpq : p = 1 - q := by
    rw [hp, hq, eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hden]; ring
  have hp0 : 0 < p := by rw [hpq]; linarith
  have hceil : (1 + (3 - 1) * q) ≤ (2 : ℝ) ^ ((4 : ℝ) / 5) := by
    have := ceiling_le_rpow; linarith
  set P := PrefixCollision.shellP (collatzBarrier 0) j σ
  set G := Real.logb 2 ((σ : ℝ) * j / p)
  set θ := θd + φ * (2 / 5 - θd)
  have hPc : (0 : ℝ) ≤ (P.card : ℝ) := Nat.cast_nonneg _
  -- per-frequency bound
  have hone : ∀ u ≤ U, ∀ lam ∈ ShellDecomposition.cshell (σ + 1) t u,
      ∑ Q ∈ P, (3 : ℝ) ^ OddBlack.Nodd (collatzBarrier 0) (σ + 1 + t) d lam Q ≤
        (2 : ℝ) ^ (C * Real.logb 2 j + θ * j) * P.card := by
    intro u hu lam hlam
    obtain ⟨bad, hbad, hsafe⟩ := hwin u hu lam hlam
    set w := geoW p q (oddW (collatzBarrier 0) (σ + 1 + t) d 3 lam) σ with hw
    have hw0 : ∀ l (x y : Fin (σ + 1)), 0 ≤ w l x y := by
      intro l x y; rw [hw]; unfold geoW
      have := oddW_nonneg (collatzBarrier 0) (m := σ + 1 + t) (d := d) (lam := lam)
        (by norm_num : (0 : ℝ) ≤ 3) l x y
      have : 0 ≤ q ^ ((y : ℤ) - x - 2) := zpow_nonneg hq0 _
      positivity
    have hcap : ∀ l n (x : Fin (σ + 1)), val w l n x ≤ (2 : ℝ) ^ ((4 : ℝ) / 5 * n) := by
      intro l n x
      have h := val_le_ceiling (collatzBarrier 0) (m := σ + 1 + t) (d := d) (lam := lam)
        (σ := σ) hq0 (by linarith) (by norm_num : (1 : ℝ) ≤ 3) n l x
      rw [← hpq] at h
      calc val w l n x ≤ (1 + (3 - 1) * q) ^ n := h
        _ ≤ ((2 : ℝ) ^ ((4 : ℝ) / 5)) ^ n := pow_le_pow_left₀ (by linarith) hceil n
        _ = (2 : ℝ) ^ ((4 : ℝ) / 5 * n) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    -- window exponents
    let a : ℕ → ℝ := fun i => 2 * (K : ℝ) * θd + (if i ∈ bad then (4 / 5 - 2 * θd) * K else 0)
    have hwin' : ∀ i < W, ∀ y, val w (i * K) K y ≤ (2 : ℝ) ^ a i := by
      intro i hi y
      by_cases hb : i ∈ bad
      · have := hcap (i * K) K y
        simp only [a, hb, ite_true]
        convert this using 2; ring
      · simp only [a, hb, ite_false, add_zero]
        exact hsafe i hi hb y
    have hprod := val_le_prod_windows_rem hw0 (fun i => (2 : ℝ) ^ a i) (fun i => by positivity)
      hwin' (fun y => hcap (W * K) ρ y) ⟨0, by omega⟩
    rw [← Real.rpow_sum_of_pos (by norm_num), ← Real.rpow_add (by norm_num)] at hprod
    have hsum : ∑ i ∈ range W, a i ≤ 2 * (K : ℝ) * θd * W + (4 / 5 - 2 * θd) * K * (φ * W + E) := by
      simp only [a, sum_add_distrib, sum_const, card_range, nsmul_eq_mul, sum_ite]
      have hcard : ((filter (fun i => i ∈ bad) (range W)).card : ℝ) ≤ φ * W + E := by
        refine le_trans ?_ hbad
        exact_mod_cast card_le_card (fun i hi => (mem_filter.mp hi).2)
      have hc0 : 0 ≤ (4 / 5 - 2 * θd) * (K : ℝ) := by
        have : (0 : ℝ) ≤ K := Nat.cast_nonneg K
        nlinarith
      nlinarith
    -- bridge
    have hbr := sum_pow_nodd_le_geo (collatzBarrier 0) (m := σ + 1 + t) (d := d) (s := 3)
      (lam := lam)
      (by omega) (by omega) (collatz_chord 0 (by omega)) hjσ le_rfl (by norm_num)
    have hkv : ker w 0 (j / 2) ⟨0, by omega⟩ ⟨σ, by omega⟩ ≤ val w 0 (j / 2) ⟨0, by omega⟩ := by
      unfold LocalWindow.val
      exact single_le_sum (fun y _ => ker_nonneg hw0 _ _ _ y) (mem_univ _)
    rw [← hR] at hprod
    have hjK : 2 * ((W : ℝ) * K) + 2 * ρ = j := by
      have : 2 * (W * K) + 2 * ρ = j := by omega
      exact_mod_cast this
    have hρK : (ρ : ℝ) ≤ K := by exact_mod_cast hρ
    have hexp : G + (∑ i ∈ range W, a i + 4 / 5 * ρ) ≤ C * Real.logb 2 j + θ * j := by
      have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
      have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
      have hρ0 : (0 : ℝ) ≤ ρ := Nat.cast_nonneg ρ
      have h25 : 0 ≤ 2 / 5 - θd := by linarith
      have hA : 2 * (K : ℝ) * θd * W + (4 / 5 - 2 * θd) * K * (φ * W + E) + 4 / 5 * ρ ≤
          θ * j + ((4 / 5 - 2 * θd) * K * E + 4 / 5 * K) := by
        simp only [θ]
        rw [← hjK]
        nlinarith [mul_nonneg (mul_nonneg hφ h25) hρ0, mul_nonneg hθ0 hρ0]
      linarith
    have hGpos : (σ : ℝ) * j / p = (2 : ℝ) ^ G := by
      rw [Real.rpow_logb (by norm_num) (by norm_num) (by positivity)]
    calc ∑ Q ∈ P, (3 : ℝ) ^ OddBlack.Nodd (collatzBarrier 0) (σ + 1 + t) d lam Q
        ≤ (σ : ℝ) * j / p * ker w 0 (j / 2) ⟨0, by omega⟩ ⟨σ, by omega⟩ * P.card := hbr
      _ ≤ (σ : ℝ) * j / p * (2 : ℝ) ^ (∑ i ∈ range W, a i + 4 / 5 * ρ) * P.card :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hkv.trans hprod) (by positivity)) hPc
      _ = (2 : ℝ) ^ (G + (∑ i ∈ range W, a i + 4 / 5 * ρ)) * P.card := by
          rw [hGpos, ← Real.rpow_add (by norm_num)]
      _ ≤ _ := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp) hPc
  -- sum over the frequency shell
  intro u hu
  have hcard : ((ShellDecomposition.cshell (σ + 1) t u).card : ℝ) ≤ 2 ^ (u + 1) := by
    exact_mod_cast ShellDecomposition.card_cshell_le (σ + 1) t u
  have hB : (0 : ℝ) ≤ (2 : ℝ) ^ (C * Real.logb 2 j + θ * j) * P.card := by positivity
  calc _ ≤ ∑ lam ∈ ShellDecomposition.cshell (σ + 1) t u,
        (2 : ℝ) ^ (C * Real.logb 2 j + θ * j) * P.card := sum_le_sum fun lam hl => hone u hu lam hl
    _ = _ * _ := by rw [sum_const, nsmul_eq_mul]
    _ ≤ 2 ^ (u + 1) * ((2 : ℝ) ^ (C * Real.logb 2 j + θ * j) * P.card) :=
        mul_le_mul_of_nonneg_right hcard hB
    _ = _ := by ring

/-- At `θ_d = 1/10` the dangerous fraction `φ = 2/9` gives exactly the target rate `1/6`. -/
theorem rate_at_tenth : (1 / 10 : ℝ) + 2 / 9 * (2 / 5 - 1 / 10) = 1 / 6 := by norm_num

/-! ## 6. The concrete `1/10, 2/9, 1/6` chain with a logarithmic excess -/

theorem logb_bridge_le {j : ℕ} (hj : 300 ≤ j) :
    Real.logb 2 ((collatzBarrier 0 j : ℝ) * j / (((j : ℝ) - 1) / ((collatzBarrier 0 j : ℝ) - 1)))
      ≤ 2 * Real.logb 2 j + 2 := by
  set σ := collatzBarrier 0 j
  have h1 := ShapeUnconditional.barrier_lt j (by omega)
  have h2 : σ + 1 ≤ 2 * j := by omega
  have hjσ : j < σ := barrier_gt (by omega)
  have hj0 : (300 : ℝ) ≤ j := by exact_mod_cast hj
  have hσ2 : (σ : ℝ) + 1 ≤ 2 * j := by exact_mod_cast h2
  have hσj : (j : ℝ) < σ := by exact_mod_cast hjσ
  have hpos : 0 < (σ : ℝ) * j / (((j : ℝ) - 1) / ((σ : ℝ) - 1)) := by
    apply div_pos (mul_pos (by linarith) (by linarith)); apply div_pos <;> linarith
  have hle : (σ : ℝ) * j / (((j : ℝ) - 1) / ((σ : ℝ) - 1)) ≤ 2 ^ (2 : ℝ) * (j : ℝ) ^ (2 : ℕ) := by
    rw [div_div_eq_mul_div, div_le_iff₀ (by linarith)]
    have : (σ : ℝ) - 1 ≤ 2 * ((j : ℝ) - 1) := by linarith
    have h3 : (σ : ℝ) * ((σ : ℝ) - 1) ≤ (2 * j) * (2 * ((j : ℝ) - 1)) :=
      mul_le_mul (by linarith) this (by linarith) (by linarith)
    norm_num
    nlinarith [h3]
  calc _ ≤ Real.logb 2 (2 ^ (2 : ℝ) * (j : ℝ) ^ (2 : ℕ)) :=
        Real.logb_le_logb_of_le (by norm_num) hpos hle
    _ = 2 * Real.logb 2 j + 2 := by
        rw [Real.logb_mul (by positivity) (by positivity),
          Real.logb_rpow (by norm_num) (by norm_num), Real.logb_pow]
        push_cast; ring

theorem eight_le_logb {j : ℕ} (hj : 300 ≤ j) : (8 : ℝ) ≤ Real.logb 2 j := by
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
  have : (256 : ℝ) ≤ j := by exact_mod_cast (by omega : 256 ≤ j)
  norm_num; linarith

/-- **The concrete chain.**  Dangerous threshold `1/10`, allowed fraction `2/9`, universal ceiling
`2/5`, output rate exactly `1/6`.  The excess over `(2/9) W` may be `(a log₂ j + b)/K` windows (its
pressure cost is `(3/5)(a log₂ j + b)` bits, logarithmic for any `K`), and `K ≤ k₁ log₂ j + k₀`.
The logarithmic constant is explicit. -/
theorem summedPressure_of_tenth_twoNinths {j t U K W ρ : ℕ} {d a b k₁ k₀ : ℝ}
    (hj : 300 ≤ j) (hev : 2 ∣ j) (hR : j / 2 = W * K + ρ) (hρ : ρ ≤ K) (hK : 0 < K)
    (hb : 0 ≤ b) (hk₀ : 0 ≤ k₀) (hKlog : (K : ℝ) ≤ k₁ * Real.logb 2 j + k₀)
    (hwin : ∀ u ≤ U, ∀ lam ∈ ShellDecomposition.cshell (collatzBarrier 0 j + 1) t u,
      ∃ bad : Finset ℕ, (bad.card : ℝ) ≤ 2 / 9 * W + (a * Real.logb 2 j + b) / K ∧
        ∀ i < W, i ∉ bad → ∀ y : Fin (collatzBarrier 0 j + 1),
          val (geoW (((j : ℝ) - 1) / ((collatzBarrier 0 j : ℝ) - 1))
              (((collatzBarrier 0 j : ℝ) - j) / ((collatzBarrier 0 j : ℝ) - 1))
              (oddW (collatzBarrier 0) (collatzBarrier 0 j + 1 + t) d 3 lam)
              (collatzBarrier 0 j)) (i * K) K y ≤ (2 : ℝ) ^ (2 * (K : ℝ) * (1 / 10))) :
    AverageOddDark.SummedOddDarkPressure (collatzBarrier 0) j (collatzBarrier 0 j) t U d 3 (1 / 6)
      (2 + 3 / 5 * a + 4 / 5 * k₁ + (2 + 3 / 5 * b + 4 / 5 * k₀) / 8) := by
  have hθ : (1 / 6 : ℝ) = 1 / 10 + 2 / 9 * (2 / 5 - 1 / 10) := by norm_num
  rw [hθ]
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  refine summedPressure_of_dangerousWindows (E := (a * Real.logb 2 j + b) / K) hj hev hR hρ
    (by norm_num) (by norm_num) (by norm_num) ?_ hwin
  have hL := logb_bridge_le hj
  have h8 := eight_le_logb hj
  have hKE : (4 / 5 - 2 * (1 / 10 : ℝ)) * K * ((a * Real.logb 2 j + b) / K) =
      3 / 5 * (a * Real.logb 2 j + b) := by field_simp; ring
  rw [hKE]
  have hconst : 2 + 3 / 5 * b + 4 / 5 * k₀ ≤ (2 + 3 / 5 * b + 4 / 5 * k₀) / 8 * Real.logb 2 j := by
    have h0 : 0 ≤ 2 + 3 / 5 * b + 4 / 5 * k₀ := by linarith
    nlinarith
  nlinarith

/-! ## 7. The `u = 0` companion frequency -/

/-- `λ` and `2^m − λ` have the same dark pairs. -/
theorem dark_companion {m : ℕ} {d : ℝ} {lam r z : ℕ} (hl : lam ≤ 2 ^ m) :
    OddBlack.Dark m d (2 ^ m - lam) r z ↔ OddBlack.Dark m d lam r z := by
  unfold OddBlack.Dark WhiteContraction.pairPhase
  obtain ⟨z1, h1⟩ := WhiteContraction.collatzPhase_sub_succ (2 ^ m - lam) m
    (WeightedChain.uInv m) (2 * r + 1) z
  obtain ⟨z2, h2⟩ :=
    WhiteContraction.collatzPhase_sub_succ lam m (WeightedChain.uInv m) (2 * r + 1) z
  rw [h1, h2, WhiteContraction.distZ_add_int, WhiteContraction.distZ_add_int]
  set u := WeightedChain.uInv m (2 * r + 1)
  have hcast : (((2 ^ m - lam) * u * 2 ^ z : ℕ) : ℝ) / 2 ^ m =
      -((((lam * u * 2 ^ z : ℕ) : ℝ) / 2 ^ m)) + ((u * 2 ^ z : ℕ) : ℤ) := by
    have hsub : ((2 ^ m - lam : ℕ) : ℝ) = 2 ^ m - lam := by push_cast [hl]; ring
    push_cast [hsub]
    field_simp
    ring
  rw [hcast, WhiteContraction.distZ_add_int, WhiteContraction.distZ_neg]

open Classical in
/-- Consequently the odd-dark counts of `λ` and `2^m − λ` coincide. -/
theorem nodd_companion (b : ℕ → ℕ) {m : ℕ} {d : ℝ} {lam : ℕ} (hl : lam ≤ 2 ^ m) {j : ℕ}
    (P : FiniteValuationWord j) :
    OddBlack.Nodd b m d (2 ^ m - lam) P = OddBlack.Nodd b m d lam P := by
  have hfun : OddBlack.OwnDark b m d (2 ^ m - lam) P = OddBlack.OwnDark b m d lam P := by
    funext r
    exact propext (by simp only [OddBlack.OwnDark, dark_companion hl])
  simp only [OddBlack.Nodd, hfun]

end DangerousWindows
end EOC
