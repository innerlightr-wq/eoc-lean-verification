import EOC.ArithmeticFrontier
import EOC.ShapeRegion

/-!
# The arithmetic frontier on every shell and barrier offset used downstream

`weighted_phi_decay_implies_exceptional_bound` needs `WeightedFourier` for the barrier
`collatzBarrier U` on **every** prefix shell that carries Haar weight, not only on the top shell `σ
= ⌊j log₂ 3⌋` at `U = 0` handled by `ArithmeticFrontier`.  This file removes that restriction from
the pressure side of the chain.

* `PowerOfTwoDangerousWindowSparsityAt U j σ t Us K d a b` — the named arithmetic input at barrier
  offset `U` and prefix shell `σ` (the `ArithmeticFrontier` Prop is the case `U = 0`, `σ =
  collatzBarrier 0 j`, `ofAt`).  **OPEN**, exactly like the top-shell Prop.
* `q_le_of`, `logb_bridge_le_of` — the two numerical facts of `DangerousWindows`, for any shell with
  `63σ + 37 ≤ 100 j` (so the one-block ceiling is still `2/5` bits per step) and `σ + 1 ≤ 2j`.
* `summedPressure_at` — dangerous windows ⇒ `SummedOddDarkPressure` for barrier `collatzBarrier U`
  and shell `σ` (same proof as `summedPressure_of_dangerousWindows`, all barrier data abstract).
* `summedPressure_of_sparsityAt` — the `1/10, 2/9, 1/6` instance with logarithmic windows.
* `shellP_nonempty_of` — every shell `j ≤ σ ≤ b_U j` is nonempty.
* **`lowFreqDecay_of_sparsityAt`** — `PowerOfTwoDangerousWindowSparsityAt ⇒ LowFreqDecay` on the
  region `b₀ j ≤ σ + δ`, `δ ≤ j/300`, `σ ≤ b_U j`, `63σ + 37 ≤ 100j`, using
  `ShapeRegion.shapeTail_region`, with rate `γ` subject to `γ j ≤ j/300 − δ` (shape tail) and the
  white-contraction and pressure conditions of the top-shell theorem.

The arithmetic hypothesis stays a hypothesis.  No `sorry`, `admit`, `axiom`, `opaque`, or
`native_decide`.
-/

namespace EOC
namespace FrontierRegion

open Finset LocalWindow PressureBridge CapacityBounds DangerousWindows

/-- **`PowerOfTwoDangerousWindowSparsityAt`** — the dangerous-window count at barrier offset `U` and
prefix shell `σ`.  OPEN: not known to follow from equidistribution; not claimed equivalent to any
named digit conjecture. -/
def PowerOfTwoDangerousWindowSparsityAt (U j σ t Us K : ℕ) (d a b : ℝ) : Prop :=
  ∀ u ≤ Us, ∀ lam ∈ ShellDecomposition.cshell (σ + 1) t u,
    ∃ bad : Finset ℕ,
      (bad.card : ℝ) ≤ 2 / 9 * ((j / 2 / K : ℕ) : ℝ) + (a * Real.logb 2 j + b) / K ∧
      ∀ i < j / 2 / K, i ∉ bad → ∀ y : Fin (σ + 1),
        val (geoW (((j : ℝ) - 1) / ((σ : ℝ) - 1)) (((σ : ℝ) - j) / ((σ : ℝ) - 1))
            (oddW (collatzBarrier U) (σ + 1 + t) d 3 lam) σ) (i * K) K y
          ≤ (2 : ℝ) ^ (2 * (K : ℝ) * (1 / 10))

/-- The top-shell Prop is the `U = 0`, `σ = b₀ j` case. -/
theorem ofAt {j t Us K : ℕ} {d a b : ℝ} :
    ArithmeticFrontier.PowerOfTwoDangerousWindowSparsity j t Us K d a b ↔
      PowerOfTwoDangerousWindowSparsityAt 0 j (collatzBarrier 0 j) t Us K d a b := Iff.rfl

theorem q_le_of {j σ : ℕ} (hj : 300 ≤ j) (hq : 63 * σ + 37 ≤ 100 * j) (hjσ : j < σ) :
    ((σ : ℝ) - j) / ((σ : ℝ) - 1) ≤ 37 / 100 := by
  have h4 : (63 : ℝ) * σ + 37 ≤ 100 * j := by exact_mod_cast hq
  have hσ : (1 : ℝ) < σ := by
    have : (300 : ℝ) < σ := by exact_mod_cast (lt_of_le_of_lt hj hjσ)
    linarith
  rw [div_le_iff₀ (by linarith)]
  linarith

theorem logb_bridge_le_of {j σ : ℕ} (hj : 300 ≤ j) (h2 : σ + 1 ≤ 2 * j) (hjσ : j < σ) :
    Real.logb 2 ((σ : ℝ) * j / (((j : ℝ) - 1) / ((σ : ℝ) - 1))) ≤ 2 * Real.logb 2 j + 2 := by
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

/-- **Dangerous windows ⇒ summed pressure**, for barrier offset `U` and shell `σ`. -/
theorem summedPressure_at {U j σ t Us K W ρ : ℕ} {d θd φ E C : ℝ}
    (hj : 300 ≤ j) (hev : 2 ∣ j) (hjσ : j < σ) (hσ : σ ≤ collatzBarrier U j)
    (hq63 : 63 * σ + 37 ≤ 100 * j) (hR : j / 2 = W * K + ρ) (hρ : ρ ≤ K)
    (hθ0 : 0 ≤ θd) (hθ1 : θd ≤ 2 / 5) (hφ : 0 ≤ φ)
    (hC : Real.logb 2 ((σ : ℝ) * j / (((j : ℝ) - 1) / ((σ : ℝ) - 1))) +
        (4 / 5 - 2 * θd) * K * E + 4 / 5 * K ≤ C * Real.logb 2 j)
    (hwin : ∀ u ≤ Us, ∀ lam ∈ ShellDecomposition.cshell (σ + 1) t u,
      ∃ bad : Finset ℕ, (bad.card : ℝ) ≤ φ * W + E ∧
        ∀ i < W, i ∉ bad → ∀ y : Fin (σ + 1),
          val (geoW (((j : ℝ) - 1) / ((σ : ℝ) - 1)) (((σ : ℝ) - j) / ((σ : ℝ) - 1))
              (oddW (collatzBarrier U) (σ + 1 + t) d 3 lam) σ) (i * K) K y ≤
            (2 : ℝ) ^ (2 * (K : ℝ) * θd)) :
    AverageOddDark.SummedOddDarkPressure (collatzBarrier U) j σ t Us d 3
      (θd + φ * (2 / 5 - θd)) C := by
  set p : ℝ := ((j : ℝ) - 1) / ((σ : ℝ) - 1) with hp
  set q : ℝ := ((σ : ℝ) - j) / ((σ : ℝ) - 1) with hq
  have hσ1 : (1 : ℝ) < σ := by exact_mod_cast (by omega : 1 < σ)
  have hj1 : (1 : ℝ) < j := by exact_mod_cast (by omega : 1 < j)
  have hjσr : (j : ℝ) < σ := by exact_mod_cast hjσ
  have hq0 : 0 ≤ q := div_nonneg (by linarith) (by linarith)
  have hq37 : q ≤ 37 / 100 := q_le_of hj hq63 hjσ
  have hden : (σ : ℝ) - 1 ≠ 0 := by linarith
  have hpq : p = 1 - q := by
    rw [hp, hq, eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hden]; ring
  have hp0 : 0 < p := by rw [hpq]; linarith
  have hceil : (1 + (3 - 1) * q) ≤ (2 : ℝ) ^ ((4 : ℝ) / 5) := by
    have := ceiling_le_rpow; linarith
  set P := PrefixCollision.shellP (collatzBarrier U) j σ
  set G := Real.logb 2 ((σ : ℝ) * j / p)
  set θ := θd + φ * (2 / 5 - θd)
  have hPc : (0 : ℝ) ≤ (P.card : ℝ) := Nat.cast_nonneg _
  -- per-frequency bound
  have hone : ∀ u ≤ Us, ∀ lam ∈ ShellDecomposition.cshell (σ + 1) t u,
      ∑ Q ∈ P, (3 : ℝ) ^ OddBlack.Nodd (collatzBarrier U) (σ + 1 + t) d lam Q ≤
        (2 : ℝ) ^ (C * Real.logb 2 j + θ * j) * P.card := by
    intro u hu lam hlam
    obtain ⟨bad, hbad, hsafe⟩ := hwin u hu lam hlam
    set w := geoW p q (oddW (collatzBarrier U) (σ + 1 + t) d 3 lam) σ with hw
    have hw0 : ∀ l (x y : Fin (σ + 1)), 0 ≤ w l x y := by
      intro l x y; rw [hw]; unfold geoW
      have := oddW_nonneg (collatzBarrier U) (m := σ + 1 + t) (d := d) (lam := lam)
        (by norm_num : (0 : ℝ) ≤ 3) l x y
      have : 0 ≤ q ^ ((y : ℤ) - x - 2) := zpow_nonneg hq0 _
      positivity
    have hcap : ∀ l n (x : Fin (σ + 1)), val w l n x ≤ (2 : ℝ) ^ ((4 : ℝ) / 5 * n) := by
      intro l n x
      have h := val_le_ceiling (collatzBarrier U) (m := σ + 1 + t) (d := d) (lam := lam)
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
    have hbr := sum_pow_nodd_le_geo (collatzBarrier U) (m := σ + 1 + t) (d := d) (s := 3)
      (lam := lam)
      (by omega) (by omega) (collatz_chord U (by omega)) hjσ hσ (by norm_num)
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
    calc ∑ Q ∈ P, (3 : ℝ) ^ OddBlack.Nodd (collatzBarrier U) (σ + 1 + t) d lam Q
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


/-- **`PowerOfTwoDangerousWindowSparsityAt ⇒ SummedOddDarkPressure (1/6)`** for logarithmic windows.
-/
theorem summedPressure_of_sparsityAt {U j σ t Us K : ℕ} {d a b A : ℝ}
    (hj : 300 ≤ j) (hev : 2 ∣ j) (hjσ : j < σ) (hσ : σ ≤ collatzBarrier U j)
    (hq63 : 63 * σ + 37 ≤ 100 * j) (h2 : σ + 1 ≤ 2 * j) (hK : 0 < K)
    (hKlog : (K : ℝ) ≤ A * Real.logb 2 j + 1) (hb : 0 ≤ b)
    (h : PowerOfTwoDangerousWindowSparsityAt U j σ t Us K d a b) :
    AverageOddDark.SummedOddDarkPressure (collatzBarrier U) j σ t Us d 3 (1 / 6)
      (2 + 3 / 5 * a + 4 / 5 * A + (2 + 3 / 5 * b + 4 / 5 * 1) / 8) := by
  have hR : j / 2 = (j / 2 / K) * K + (j / 2) % K := by
    have := Nat.div_add_mod (j / 2) K; rw [mul_comm] at this; omega
  have hρ : (j / 2) % K ≤ K := (Nat.mod_lt _ hK).le
  have hθ : (1 / 6 : ℝ) = 1 / 10 + 2 / 9 * (2 / 5 - 1 / 10) := by norm_num
  rw [hθ]
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  refine summedPressure_at (E := (a * Real.logb 2 j + b) / K) hj hev hjσ hσ hq63 hR hρ
    (by norm_num) (by norm_num) (by norm_num) ?_ h
  have hL := logb_bridge_le_of hj h2 hjσ
  have h8 := eight_le_logb hj
  have hKE : (4 / 5 - 2 * (1 / 10 : ℝ)) * K * ((a * Real.logb 2 j + b) / K) =
      3 / 5 * (a * Real.logb 2 j + b) := by field_simp; ring
  rw [hKE]
  have hconst : 2 + 3 / 5 * b + 4 / 5 * 1 ≤ (2 + 3 / 5 * b + 4 / 5 * 1) / 8 * Real.logb 2 j := by
    have h0 : 0 ≤ 2 + 3 / 5 * b + 4 / 5 * (1 : ℝ) := by linarith
    nlinarith
  nlinarith

/-- Every shell `j ≤ σ ≤ b_U j` is nonempty. -/
theorem shellP_nonempty_of {U j σ : ℕ} (hj : 1 ≤ j) (hjσ : j ≤ σ) (hσ : σ ≤ collatzBarrier U j) :
    (PrefixCollision.shellP (collatzBarrier U) j σ).Nonempty := by
  have h := shell_choose_le_mul_card hj (collatzBarrier U) (collatz_chord U (by omega)) hjσ hσ
  have hc : 1 ≤ (σ - 1).choose (j - 1) := Nat.choose_pos (by omega)
  rw [← Finset.card_pos]
  have : 0 < j * (PrefixCollision.shellP (collatzBarrier U) j σ).card := lt_of_lt_of_le hc h
  exact Nat.pos_of_mul_pos_left this

/-- **`PowerOfTwoDangerousWindowSparsityAt ⇒ LowFreqDecay` on the downstream shell region.** Barrier
offset `U`, shell `σ` with `b₀ j ≤ σ + δ`, `δ ≤ j/300`, `σ ≤ b_U j`, `63σ + 37 ≤ 100 j`; the shape
tail is `ShapeRegion.shapeTail_region`, so the rate must also satisfy `γ j ≤ j/300 − δ`. -/
theorem lowFreqDecay_of_sparsityAt {U j σ δ t Us K N0 Kb k n : ℕ} {d a b A θ' ν γ : ℝ}
    (hj : 300 ≤ j) (hev : 2 ∣ j) (hlo : collatzBarrier 0 j ≤ σ + δ) (hδ : δ ≤ j / 300)
    (hσ : σ ≤ collatzBarrier U j) (hq63 : 63 * σ + 37 ≤ 100 * j)
    (hK : 0 < K) (hKlog : (K : ℝ) ≤ A * Real.logb 2 j + 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : 0 ≤ A)
    (hbudget : Kb + 31 * j / 100 + σ / (N0 + 2) ≤ j / 2) (hkn : k + n ≤ Kb)
    (hN : 2 ≤ N0) (hd0 : 0 ≤ d) (hd1 : d ≤ 1 / 2) (hθ : 1 / 6 < θ')
    (hlarge :
      (3 * (2 + 3 / 5 * a + 4 / 5 * A + (2 + 3 / 5 * b + 4 / 5 * 1) / 8) / (θ' - 1 / 6)) ^ 2 ≤ j)
    (hn : ν * j ≤ n) (hγ : θ' + γ ≤ ν * Real.logb 2 ((1 + 3) / 2))
    (hγδ : γ * j ≤ ((j / 300 - δ : ℕ) : ℝ))
    (hγk : γ * j * Real.log 2 ≤ 8 * k * d ^ 2 / N0)
    (h : PowerOfTwoDangerousWindowSparsityAt U j σ t Us K d a b) :
    DecayInterface.LowFreqDecay (collatzBarrier U) j σ t Us 4 γ := by
  have hlow := ShapeRegion.lower_barrier j (by omega)
  have hjσ : j < σ := by omega
  have h2 : σ + 2 ≤ 2 * j := by omega
  have hC : (0 : ℝ) ≤ 2 + 3 / 5 * a + 4 / 5 * A + (2 + 3 / 5 * b + 4 / 5 * 1) / 8 := by positivity
  have hpress := summedPressure_of_sparsityAt hj hev hjσ hσ hq63 (by omega) hK hKlog hb h
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (by omega : 1 ≤ j)
  have habs := LogAbsorb.rpow_log_absorb hC hθ (by linarith) hlarge
  refine AverageOddDark.lowFreqDecay_of_shape_and_summedPressure (collatzBarrier U) (k := k)
    (n := n) (M := (2 : ℝ) ^ (θ' * j)) (by omega) (shellP_nonempty_of (by omega) hjσ.le hσ)
    hd0 hd1 hN (by norm_num) (by positivity)
    (AverageOddDark.shapeTail_mono hkn (ShapeRegion.shapeTail_region hj hev hlo hδ hσ h2 hbudget))
    (fun u hu => (hpress u hu).trans ?_) ?_
  · have hP : (0 : ℝ) ≤ ((PrefixCollision.shellP (collatzBarrier U) j σ).card : ℝ) :=
      Nat.cast_nonneg _
    gcongr
  · have h2' := AverageOddDark.pressure_term_le (by norm_num : (1 : ℝ) ≤ 3) hn hγ
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have e1 : (2 : ℝ) ^ (-(γ * j)) = Real.exp (-(γ * j * Real.log 2)) := by
      rw [Real.rpow_def_of_pos (by norm_num)]; ring_nf
    have hkap : WhiteContraction.kappa d N0 ^ (2 * k) ≤ (2 : ℝ) ^ (-(γ * j)) := by
      rw [e1]
      exact (AverageOddDark.kappa_pow_le_exp hd0 hd1 hN k).trans
        (Real.exp_le_exp.mpr (by linarith))
    have hρ : ((2 : ℝ) ^ (j / 300 - δ))⁻¹ ≤ (2 : ℝ) ^ (-(γ * j)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_neg (by norm_num)]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hp : (0 : ℝ) ≤ (2 : ℝ) ^ (-(γ * j)) := by positivity
    linarith

end FrontierRegion
end EOC
