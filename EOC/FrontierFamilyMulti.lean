import EOC.MultiWhiteChain
import EOC.ExceptionalPowerBound

/-!
# Explicit family for the multi-pair white-contraction chain

Same construction as `FrontierFamily`, run through `MultiWhiteChain` (no `N₀` loss):

* `j₀ = P m` with `P = 1 080 000`, `L = m`, `N = (P+1) m`, `x* = 4m`, `K = b₀(j₀) + 1`, `U = 0`;
* `γ = 1/60 000` (so `γ j₀ = 18 m`), `θ' = 1/6 + 1/1000`, `d = 1/108`, `N₀ + 2 = P`,
  `K_b = 205 198 m` (shape-good block budget);
* frontier window `K_win = ⌊7 log₂ j₀⌋`, allowance constants `a = b = 2`; `ε = κ = 1`;

for every `m ≥ 1000`.  Final exponent `H₂(1/α) − I₀/(2·10⁶)`.

No `sorry`, `admit`, `axiom`, `opaque`, or `native_decide`.
-/

namespace EOC
namespace FrontierFamilyMulti

open Finset CapacityBounds FiniteValuationWord PrefixCollision

/-! ## 1. Rational bounds on `α = log₂ 3` -/

theorem alpha_ge : (79 / 50 : ℝ) ≤ alpha := by
  unfold alpha
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by norm_num)]
  have h : ((2 : ℝ) ^ ((79 : ℝ) / 50)) ^ (50 : ℕ) = 2 ^ (79 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have h0 : (0 : ℝ) ≤ (2 : ℝ) ^ ((79 : ℝ) / 50) := by positivity
  have hpow : ((2 : ℝ) ^ ((79 : ℝ) / 50)) ^ (50 : ℕ) ≤ (3 : ℝ) ^ (50 : ℕ) := by
    rw [h]; norm_num
  exact (pow_le_pow_iff_left₀ h0 (by norm_num) (by norm_num)).mp hpow

theorem alpha_le : alpha ≤ (317 / 200 : ℝ) := by
  unfold alpha
  rw [Real.logb_le_iff_le_rpow (by norm_num) (by norm_num)]
  have h : ((2 : ℝ) ^ ((317 : ℝ) / 200)) ^ (200 : ℕ) = 2 ^ (317 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have h0 : (0 : ℝ) ≤ (2 : ℝ) ^ ((317 : ℝ) / 200) := by positivity
  have hpow : (3 : ℝ) ^ (200 : ℕ) ≤ ((2 : ℝ) ^ ((317 : ℝ) / 200)) ^ (200 : ℕ) := by
    rw [h]
    have hn : (3 : ℕ) ^ 200 ≤ 2 ^ 317 := Nat.le_of_ble_eq_true (by rfl)
    exact_mod_cast hn
  exact (pow_le_pow_iff_left₀ (by norm_num) h0 (by norm_num)).mp hpow

theorem two_rpow_alpha : (2 : ℝ) ^ alpha = 3 := by
  unfold alpha; rw [Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)]

/-! ## 2. The barrier at offset `0` -/

theorem barrier_le (j : ℕ) : (collatzBarrier 0 j : ℝ) ≤ j * alpha := by
  have := Nat.floor_le (barrier_arg_nonneg 0 j)
  unfold collatzBarrier; simpa using this

theorem barrier_gt (j : ℕ) : (j : ℝ) * alpha - 1 < collatzBarrier 0 j := by
  have := Nat.lt_floor_add_one ((j : ℝ) * alpha + (0 : ℕ))
  unfold collatzBarrier; push_cast at this ⊢; linarith

/-! ## 3. The tail ratio majorant -/

theorem g_le_of {M L y : ℝ} (hL : 0 < L) (hM : 79 / 50 * L ≤ M) (hy : 0 ≤ y) :
    (M + y) / (M + y - L) ≤ 79 / 29 := by
  have hd : 0 < M + y - L := by linarith
  rw [div_le_iff₀ hd]; linarith

theorem g_le_of' {M L y : ℝ} (hL : 0 < L) (hM : 79 / 50 * L ≤ M) (hy : L ≤ y) :
    (M + y) / (M + y - L) ≤ 129 / 79 := by
  have hd : 0 < M + y - L := by linarith
  rw [div_le_iff₀ hd]; linarith

theorem g_nonneg {M L y : ℝ} (hL : 0 < L) (hM : 79 / 50 * L ≤ M) (hy : 0 ≤ y) :
    0 ≤ (M + y) / (M + y - L) := by
  have hd : 0 < M + y - L := by linarith
  apply div_nonneg _ hd.le; linarith

theorem q_le {j b : ℕ} (hb : 2 ≤ b) (hjb : j ≤ b) (h63 : 63 * b + 37 ≤ 100 * j) :
    0 ≤ ((b : ℝ) - j) / ((b : ℝ) - 1) ∧ ((b : ℝ) - j) / ((b : ℝ) - 1) ≤ 37 / 100 := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hjb' : (j : ℝ) ≤ b := by exact_mod_cast hjb
  have h63' : (63 : ℝ) * b + 37 ≤ 100 * j := by exact_mod_cast h63
  have hd : (0 : ℝ) < (b : ℝ) - 1 := by linarith
  refine ⟨div_nonneg (by linarith) hd.le, ?_⟩
  rw [div_le_iff₀ hd]; linarith

theorem fbar_le_r0 {j b L M0 : ℕ} (hb : 2 ≤ b) (hjb : j ≤ b) (h63 : 63 * b + 37 ≤ 100 * j)
    (hL : 1 ≤ L) (hM : 79 / 50 * (L : ℝ) ≤ M0) (y : ℕ) :
    BinomialTail.fbar j b L M0 y ≤ 37 / 100 * (79 / 29) := by
  unfold BinomialTail.fbar
  obtain ⟨hq0, hq⟩ := q_le hb hjb h63
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hy : (0 : ℝ) ≤ y := Nat.cast_nonneg y
  exact mul_le_mul hq (g_le_of hLr hM hy) (g_nonneg hLr hM hy) (by norm_num)

theorem fbar_le_r1 {j b L M0 : ℕ} (hb : 2 ≤ b) (hjb : j ≤ b) (h63 : 63 * b + 37 ≤ 100 * j)
    (hL : 1 ≤ L) (hM : 79 / 50 * (L : ℝ) ≤ M0) {y : ℕ} (hy : L ≤ y) :
    BinomialTail.fbar j b L M0 y ≤ 37 / 100 * (129 / 79) := by
  unfold BinomialTail.fbar
  obtain ⟨hq0, hq⟩ := q_le hb hjb h63
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hy' : (L : ℝ) ≤ y := by exact_mod_cast hy
  have hy0 : (0 : ℝ) ≤ y := Nat.cast_nonneg y
  exact mul_le_mul hq (g_le_of' hLr hM hy') (g_nonneg hLr hM hy0) (by norm_num)

theorem fbar_nonneg' {j b L M0 : ℕ} (hb : 2 ≤ b) (hjb : j ≤ b) (h63 : 63 * b + 37 ≤ 100 * j)
    (hL : 1 ≤ L) (hM : 79 / 50 * (L : ℝ) ≤ M0) (y : ℕ) : 0 ≤ BinomialTail.fbar j b L M0 y := by
  unfold BinomialTail.fbar
  obtain ⟨hq0, _⟩ := q_le hb hjb h63
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  exact mul_nonneg hq0 (g_nonneg hLr hM (Nat.cast_nonneg y))

/-- **Product bound.** `∏_{y ≤ 4L} fbar y ≤ r₀^L · r₁^{3L}`. -/
theorem prod_fbar_le {j b L M0 : ℕ} (hb : 2 ≤ b) (hjb : j ≤ b) (h63 : 63 * b + 37 ≤ 100 * j)
    (hL : 1 ≤ L) (hM : 79 / 50 * (L : ℝ) ≤ M0) :
    ∏ y ∈ range (4 * L + 1), BinomialTail.fbar j b L M0 y ≤
      (37 / 100 * (79 / 29) : ℝ) ^ L * (37 / 100 * (129 / 79) : ℝ) ^ (3 * L) := by
  have hsplit : 4 * L + 1 = L + (3 * L + 1) := by ring
  rw [hsplit, prod_range_add]
  have h0 := fun y => fbar_nonneg' hb hjb h63 hL hM y
  refine mul_le_mul ?_ ?_ (prod_nonneg fun y _ => h0 _) (by positivity)
  · calc ∏ y ∈ range L, BinomialTail.fbar j b L M0 y ≤ ∏ _y ∈ range L, (37 / 100 * (79 / 29) : ℝ) :=
          prod_le_prod (fun y _ => h0 y) (fun y _ => fbar_le_r0 hb hjb h63 hL hM y)
      _ = _ := by simp
  · calc ∏ k ∈ range (3 * L + 1), BinomialTail.fbar j b L M0 (L + k)
        ≤ ∏ _k ∈ range (3 * L + 1), (37 / 100 * (129 / 79) : ℝ) :=
          prod_le_prod (fun y _ => h0 _) (fun k _ => fbar_le_r1 hb hjb h63 hL hM (by omega))
      _ = (37 / 100 * (129 / 79) : ℝ) ^ (3 * L + 1) := by simp
      _ ≤ _ := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

/-! ## 4. Numerical growth lemmas -/

/-- The family constant `P`. -/
def P : ℕ := 1080000

theorem six_mul_pow_le {m : ℕ} (hm : 100 ≤ m) :
    6 * (P + 1) * m * 67 ^ m ≤ 100 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => unfold P; norm_num
  | succ m hm ih =>
    calc 6 * (P + 1) * (m + 1) * 67 ^ (m + 1)
        = (6 * (P + 1) * m * 67 ^ m) * 67 + 6 * (P + 1) * 67 ^ m * 67 := by ring
      _ ≤ 100 ^ m * 67 + 100 ^ m * 33 := by
          have h1 : 6 * (P + 1) * 67 ^ m * 67 ≤ 6 * (P + 1) * m * 67 ^ m * 33 := by
            have : 67 ≤ m * 33 := by omega
            calc 6 * (P + 1) * 67 ^ m * 67 = 6 * (P + 1) * 67 ^ m * 67 := rfl
              _ ≤ 6 * (P + 1) * 67 ^ m * (m * 33) := Nat.mul_le_mul_left _ this
              _ = 6 * (P + 1) * m * 67 ^ m * 33 := by ring
          have h2 := Nat.mul_le_mul_right 33 ih
          have h3 := Nat.mul_le_mul_right 67 ih
          omega
      _ = 100 ^ (m + 1) := by ring

theorem pair_poly_le' {m : ℕ} (hm : 10 ≤ m) : 32 * P ^ 2 * m ^ 3 ≤ 2 ^ (6 * m) := by
  induction m, hm using Nat.le_induction with
  | base => unfold P; norm_num
  | succ m hm ih =>
    have h8 : (m + 1) ^ 3 ≤ 8 * m ^ 3 := by
      have : m + 1 ≤ 2 * m := by omega
      calc (m + 1) ^ 3 ≤ (2 * m) ^ 3 := Nat.pow_le_pow_left this 3
        _ = 8 * m ^ 3 := by ring
    calc 32 * P ^ 2 * (m + 1) ^ 3 ≤ 32 * P ^ 2 * (8 * m ^ 3) := Nat.mul_le_mul_left _ h8
      _ = 8 * (32 * P ^ 2 * m ^ 3) := by ring
      _ ≤ 8 * 2 ^ (6 * m) := Nat.mul_le_mul_left _ ih
      _ ≤ 2 ^ 6 * 2 ^ (6 * m) := Nat.mul_le_mul_right _ (by norm_num)
      _ = 2 ^ (6 * (m + 1)) := by rw [← pow_add]; ring_nf

theorem pair_poly_le {m : ℕ} (hm : 100 ≤ m) : 32 * P ^ 2 * m ^ 3 ≤ 2 ^ (6 * m) :=
  pair_poly_le' (by omega)

/-! ## 5. Barrier facts for the family -/

section Family

variable {m : ℕ}

theorem j_ge (hm : 100 ≤ m) : (108000000 : ℝ) ≤ ((P * m : ℕ) : ℝ) := by
  have : 108000000 ≤ P * m := by unfold P; omega
  exact_mod_cast this

theorem b_ge_j (m : ℕ) : P * m ≤ collatzBarrier 0 (P * m) := le_collatzBarrier 0 _

theorem h63_fam (hm : 100 ≤ m) : 63 * collatzBarrier 0 (P * m) + 37 ≤ 100 * (P * m) := by
  have hb := barrier_le (P * m)
  have hj := j_ge hm
  have hα := alpha_le
  have hj0 : (0 : ℝ) ≤ ((P * m : ℕ) : ℝ) := Nat.cast_nonneg _
  have h : (63 : ℝ) * collatzBarrier 0 (P * m) + 37 ≤ 100 * ((P * m : ℕ) : ℝ) := by nlinarith
  exact_mod_cast h

/-- `B − b` lies in `(m α − 1, m α + 1)`, where `b = b₀(Pm)`, `B = b₀(Pm + m)`. -/
theorem gap_bounds (m : ℕ) :
    (m : ℝ) * alpha - 1 < (collatzBarrier 0 (P * m + m) : ℝ) - collatzBarrier 0 (P * m) ∧
      (collatzBarrier 0 (P * m + m) : ℝ) - collatzBarrier 0 (P * m) < m * alpha + 1 := by
  have h1 := barrier_le (P * m)
  have h2 := barrier_gt (P * m)
  have h3 := barrier_le (P * m + m)
  have h4 := barrier_gt (P * m + m)
  push_cast at *
  constructor <;> nlinarith

theorem bB_le (m : ℕ) : collatzBarrier 0 (P * m) ≤ collatzBarrier 0 (P * m + m) :=
  ShellCounts.collatzBarrier_mono 0 (by omega)

theorem gap_ge (hm : 1 ≤ m) : m ≤ collatzBarrier 0 (P * m + m) - collatzBarrier 0 (P * m) := by
  obtain ⟨h1, _⟩ := gap_bounds m
  have hα := alpha_ge
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hle := bB_le m
  have h : (m : ℝ) - 1 < ((collatzBarrier 0 (P * m + m) - collatzBarrier 0 (P * m) : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub hle]; nlinarith
  have : m - 1 < collatzBarrier 0 (P * m + m) - collatzBarrier 0 (P * m) := by
    have h' : ((m - 1 : ℕ) : ℝ) < ((collatzBarrier 0 (P * m + m) - collatzBarrier 0 (P * m) : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub hm]; linarith
    exact_mod_cast h'
  omega

theorem M0_ge (hm : 1 ≤ m) :
    79 / 50 * (m : ℝ) ≤ ((collatzBarrier 0 (P * m + m) - collatzBarrier 0 (P * m) + 1 : ℕ) : ℝ) := by
  obtain ⟨h1, _⟩ := gap_bounds m
  have hα := alpha_ge
  have hle := bB_le m
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  push_cast [Nat.cast_sub hle]
  nlinarith

theorem two_pow_gap_le (m : ℕ) :
    (2 : ℝ) ^ (collatzBarrier 0 (P * m + m) - collatzBarrier 0 (P * m)) ≤ 2 * 3 ^ m := by
  obtain ⟨_, h2⟩ := gap_bounds m
  have hle := bB_le m
  have hc : (((collatzBarrier 0 (P * m + m) - collatzBarrier 0 (P * m) : ℕ) : ℝ)) ≤ m * alpha + 1 := by
    push_cast [Nat.cast_sub hle]; linarith
  calc (2 : ℝ) ^ (collatzBarrier 0 (P * m + m) - collatzBarrier 0 (P * m))
      = (2 : ℝ) ^ (((collatzBarrier 0 (P * m + m) - collatzBarrier 0 (P * m) : ℕ) : ℝ)) :=
        (Real.rpow_natCast _ _).symm
    _ ≤ (2 : ℝ) ^ ((m : ℝ) * alpha + 1) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hc
    _ = 2 * 3 ^ m := by
        rw [Real.rpow_add (by norm_num), Real.rpow_one, mul_comm ((m : ℝ)) alpha,
          Real.rpow_mul_natCast (by norm_num), two_rpow_alpha]
        ring

/-! ## 6. The scalar tail conditions -/

theorem scalar_rho (hm : 100 ≤ m) :
    BinomialTail.fbar (P * m) (collatzBarrier 0 (P * m)) (P * m + m - P * m)
      (collatzBarrier 0 (P * m + m) - collatzBarrier 0 (P * m) + 1) (4 * m + 1) ≤
      37 / 100 * (129 / 79) := by
  rw [show P * m + m - P * m = m by omega]
  have hb2 : 2 ≤ collatzBarrier 0 (P * m) := le_trans (by unfold P; omega) (b_ge_j m)
  exact fbar_le_r1 hb2 (b_ge_j m) (h63_fam hm) (by omega) (M0_ge (by omega)) (by omega)

theorem scalar_main (hm : 100 ≤ m) :
    ((P * m + m : ℕ) : ℝ) *
        (∏ y ∈ range (4 * m + 1), BinomialTail.fbar (P * m) (collatzBarrier 0 (P * m))
          (P * m + m - P * m) (collatzBarrier 0 (P * m + m) - collatzBarrier 0 (P * m) + 1) y) /
        (1 - BinomialTail.fbar (P * m) (collatzBarrier 0 (P * m)) (P * m + m - P * m)
          (collatzBarrier 0 (P * m + m) - collatzBarrier 0 (P * m) + 1) (4 * m + 1)) ≤
      1 * ((2 : ℝ) ^ (collatzBarrier 0 (P * m) + 1) *
        (1 / 2 : ℝ) ^ (collatzBarrier 0 (P * m + m) + 1)) := by
  set b := collatzBarrier 0 (P * m)
  set B := collatzBarrier 0 (P * m + m)
  have hLm : P * m + m - P * m = m := by omega
  rw [hLm]
  have hb2 : 2 ≤ b := le_trans (by unfold P; omega) (b_ge_j m)
  have hM := M0_ge (m := m) (by omega)
  have h63 := h63_fam hm
  set r0 : ℝ := 37 / 100 * (79 / 29)
  set r1 : ℝ := 37 / 100 * (129 / 79)
  set Pr := ∏ y ∈ range (4 * m + 1), BinomialTail.fbar (P * m) b m (B - b + 1) y
  set ρ := BinomialTail.fbar (P * m) b m (B - b + 1) (4 * m + 1)
  have hρ : ρ ≤ r1 := fbar_le_r1 hb2 (b_ge_j m) h63 (by omega) hM (by omega)
  have hρ0 : 0 ≤ ρ := fbar_nonneg' hb2 (b_ge_j m) h63 (by omega) hM _
  have hPr : Pr ≤ r0 ^ m * r1 ^ (3 * m) := prod_fbar_le hb2 (b_ge_j m) h63 (by omega) hM
  have hPr0 : 0 ≤ Pr := prod_nonneg fun y _ => fbar_nonneg' hb2 (b_ge_j m) h63 (by omega) hM y
  have hden : (3127 / 7900 : ℝ) ≤ 1 - ρ := by
    have h1r : r1 ≤ 4773 / 7900 := by simp only [r1]; norm_num
    have h2 : ρ ≤ 4773 / 7900 := hρ.trans h1r
    clear_value ρ r1
    linarith
  -- RHS
  have hBb := bB_le m
  have hRHS : (2 : ℝ) ^ (b + 1) * (1 / 2 : ℝ) ^ (B + 1) = 1 / (2 : ℝ) ^ (B - b) := by
    have hB : B + 1 = (B - b) + (b + 1) := by omega
    rw [hB, one_div_pow, pow_add]
    field_simp
    rw [pow_add, pow_succ]; ring
  rw [one_mul, hRHS]
  have hgap := two_pow_gap_le m
  have hgpos : (0 : ℝ) < (2 : ℝ) ^ (B - b) := by positivity
  -- numerical core: 6 (P+1) m (67/100)^m ≤ 1
  have hcore : (6 : ℝ) * ((P + 1 : ℕ) : ℝ) * m * (67 / 100 : ℝ) ^ m ≤ 1 := by
    have h := six_mul_pow_le hm
    have h' : ((6 * (P + 1) * m * 67 ^ m : ℕ) : ℝ) ≤ ((100 ^ m : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    have h100 : (0 : ℝ) < 100 ^ m := by positivity
    rw [div_pow, show ((P + 1 : ℕ) : ℝ) = (P : ℝ) + 1 by push_cast; ring]
    calc (6 : ℝ) * ((P : ℝ) + 1) * m * (67 ^ m / 100 ^ m) = (6 * ((P : ℝ) + 1) * m * 67 ^ m) / 100 ^ m := by ring
      _ ≤ 1 := by rw [div_le_one h100]; linarith
  have hr : (3 : ℝ) ^ m * (r0 ^ m * r1 ^ (3 * m)) ≤ (67 / 100 : ℝ) ^ m := by
    rw [pow_mul, ← mul_pow, ← mul_pow]
    apply pow_le_pow_left₀ (by norm_num [r0, r1])
    norm_num [r0, r1]
  have hN : ((P * m + m : ℕ) : ℝ) = ((P + 1 : ℕ) : ℝ) * m := by push_cast; ring
  rw [hN, le_div_iff₀ hgpos]
  have hNpos : (0 : ℝ) ≤ ((P + 1 : ℕ) : ℝ) * m := by positivity
  have h1 : ((P + 1 : ℕ) : ℝ) * m * Pr / (1 - ρ) ≤ ((P + 1 : ℕ) : ℝ) * m * (r0 ^ m * r1 ^ (3 * m)) / (3127 / 7900) := by
    apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hPr hNpos) (by norm_num) hden
  calc ((P + 1 : ℕ) : ℝ) * m * Pr / (1 - ρ) * (2 : ℝ) ^ (B - b)
      ≤ ((P + 1 : ℕ) : ℝ) * m * (r0 ^ m * r1 ^ (3 * m)) / (3127 / 7900) * (2 * 3 ^ m) :=
        mul_le_mul h1 hgap hgpos.le (by positivity)
    _ = (15800 / 3127) * ((P + 1 : ℕ) : ℝ) * m * ((3 : ℝ) ^ m * (r0 ^ m * r1 ^ (3 * m))) := by ring
    _ ≤ (15800 / 3127) * ((P + 1 : ℕ) : ℝ) * m * (67 / 100 : ℝ) ^ m := by
        apply mul_le_mul_of_nonneg_left hr; positivity
    _ ≤ 6 * ((P + 1 : ℕ) : ℝ) * m * (67 / 100 : ℝ) ^ m := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
        apply mul_le_mul_of_nonneg_right (by norm_num) (Nat.cast_nonneg _)
    _ ≤ 1 := hcore

theorem b_le_two_j (m : ℕ) : collatzBarrier 0 (P * m) ≤ 2 * (P * m) := by
  have hb := barrier_le (P * m)
  have hα := alpha_le
  have hj0 : (0 : ℝ) ≤ ((P * m : ℕ) : ℝ) := Nat.cast_nonneg _
  have h : (collatzBarrier 0 (P * m) : ℝ) ≤ 2 * ((P * m : ℕ) : ℝ) := by nlinarith
  exact_mod_cast h

theorem B_le_two_N (m : ℕ) : collatzBarrier 0 (P * m + m) ≤ 2 * (P * m + m) := by
  have hb := barrier_le (P * m + m)
  have hα := alpha_le
  have hj0 : (0 : ℝ) ≤ ((P * m + m : ℕ) : ℝ) := Nat.cast_nonneg _
  have h : (collatzBarrier 0 (P * m + m) : ℝ) ≤ 2 * ((P * m + m : ℕ) : ℝ) := by nlinarith
  exact_mod_cast h

theorem gap_le_two (hm : 3 ≤ m) : collatzBarrier 0 (P * m + m) - collatzBarrier 0 (P * m) ≤ 2 * m := by
  obtain ⟨_, h2⟩ := gap_bounds m
  have hα := alpha_le
  have hle := bB_le m
  have hmr : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have h : ((collatzBarrier 0 (P * m + m) - collatzBarrier 0 (P * m) : ℕ) : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub hle]; nlinarith
  exact_mod_cast h

/-- The frontier window size of the family. -/
noncomputable def Kwin (m : ℕ) : ℕ := ⌊7 * Real.logb 2 ((P * m : ℕ) : ℝ)⌋₊

theorem hnum_fam (hm : 100 ≤ m) {s σ : ℕ} (hσb : σ ≤ collatzBarrier 0 (P * m))
    (hx : collatzBarrier 0 (P * m) ≤ σ + 4 * m) (hLt : m ≤ s - σ)
    (ht : s - σ ≤ collatzBarrier 0 (P * m + m) - σ) :
    (1 + ((σ + 1 : ℕ) : ℝ) / 2) * (((σ + (s - σ) : ℕ) : ℝ) + 1) * 4 * 4 ^ (s - σ) *
        ((P * m + m - P * m : ℕ) : ℝ) ≤
      1 ^ 2 * (Nat.choose (s - σ - 1) (P * m + m - P * m - 1) : ℝ) *
        (2 : ℝ) ^ ((1 / 60000 : ℝ) * ((P * m : ℕ) : ℝ)) := by
  have hLm : P * m + m - P * m = m := by omega
  rw [hLm]
  set t := s - σ with htdef
  have hgap := gap_le_two (m := m) (by omega)
  have hbB := bB_le m
  have ht6 : t ≤ 6 * m := by omega
  have hs : σ + t ≤ 2 * (P * m + m) := by have := B_le_two_N m; omega
  have hσ2 : σ ≤ 2 * (P * m) := hσb.trans (b_le_two_j m)
  have hexp : (1 / 60000 : ℝ) * ((P * m : ℕ) : ℝ) = ((18 * m : ℕ) : ℝ) := by
    push_cast; unfold P; ring
  rw [hexp, Real.rpow_natCast]
  have hC : (1 : ℝ) ≤ (Nat.choose (t - 1) (m - 1) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hpoly := pair_poly_le hm
  have hpoly' : (32 : ℝ) * (P : ℝ) ^ 2 * (m : ℝ) ^ 3 ≤ (2 : ℝ) ^ (6 * m) := by exact_mod_cast hpoly
  have hPm : (2 : ℝ) ≤ (P : ℝ) * m := by
    have : 2 ≤ P * m := by unfold P; omega
    exact_mod_cast this
  have hA1 : 1 + ((σ + 1 : ℕ) : ℝ) / 2 ≤ 2 * ((P : ℝ) * m) := by
    have : (σ : ℝ) ≤ 2 * ((P : ℝ) * m) := by exact_mod_cast hσ2
    push_cast; linarith
  have hA2 : ((σ + t : ℕ) : ℝ) + 1 ≤ 4 * ((P : ℝ) * m) := by
    have : ((σ + t : ℕ) : ℝ) ≤ 2 * ((P : ℝ) * m + m) := by exact_mod_cast hs
    have hmP : (m : ℝ) ≤ (P : ℝ) * m / 2 := by
      have : (2 : ℝ) * m ≤ (P : ℝ) * m := by
        have : 2 * m ≤ P * m := by unfold P; omega
        exact_mod_cast this
      linarith
    linarith
  have h4 : (4 : ℝ) ^ t ≤ (2 : ℝ) ^ (12 * m) := by
    calc (4 : ℝ) ^ t ≤ 4 ^ (6 * m) := pow_le_pow_right₀ (by norm_num) ht6
      _ = 2 ^ (12 * m) := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  calc (1 + ((σ + 1 : ℕ) : ℝ) / 2) * (((σ + t : ℕ) : ℝ) + 1) * 4 * 4 ^ t * (m : ℝ)
      ≤ (2 * ((P : ℝ) * m)) * (4 * ((P : ℝ) * m)) * 4 * 2 ^ (12 * m) * m := by
        gcongr
    _ = (32 * (P : ℝ) ^ 2 * (m : ℝ) ^ 3) * 2 ^ (12 * m) := by ring
    _ ≤ (2 : ℝ) ^ (6 * m) * 2 ^ (12 * m) := mul_le_mul_of_nonneg_right hpoly' (by positivity)
    _ = 1 * 2 ^ (18 * m) := by rw [← pow_add]; ring_nf
    _ ≤ 1 ^ 2 * (Nat.choose (t - 1) (m - 1) : ℝ) * 2 ^ (18 * m) := by
        rw [one_pow, one_mul]
        have h2p : (0 : ℝ) < (2 : ℝ) ^ (18 * m) := by positivity
        nlinarith [hC, h2p]

/-- `(4226/10⁷) ≤ 1 − cos(π/108)`. -/
theorem one_sub_cos_ge : (4226 / 10000000 : ℝ) ≤ 1 - Real.cos (Real.pi * (1 / 108)) := by
  have hpi1 := Real.pi_gt_d2
  have hpi2 := Real.pi_lt_d2
  set x := Real.pi * (1 / 108) with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : |x| ≤ 1 := by rw [abs_of_nonneg hx0]; simp only [hx]; linarith
  have hb := Real.cos_bound hx1
  rw [abs_of_nonneg hx0] at hb
  have hlo : (314 / 10800 : ℝ) ≤ x := by simp only [hx]; linarith
  have hhi : x ≤ (315 / 10800 : ℝ) := by simp only [hx]; linarith
  have hx2 : (314 / 10800 : ℝ) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by norm_num) hlo 2
  have hx4 : x ^ 4 ≤ (315 / 10800 : ℝ) ^ 4 := pow_le_pow_left₀ hx0 hhi 4
  have h := (abs_le.mp hb).2
  linarith

theorem pairData_fam (hm : 1000 ≤ m) {s σ : ℕ} (hσK : σ < collatzBarrier 0 (P * m) + 1)
    (hx : collatzBarrier 0 (P * m) ≤ σ + 4 * m) (hLt : P * m + m - P * m ≤ s - σ)
    (ht : s - σ ≤ collatzBarrier 0 (P * m + m) - σ)
    (hfr : FrontierRegion.PowerOfTwoDangerousWindowSparsityAt 0 (P * m) σ (s - σ) (σ + (s - σ))
      (Kwin m) (1 / 108) 2 2) :
    MultiWhiteChain.ExplicitPairDataMulti 0 (P * m + m) (P * m) s σ 1 := by
  have hm100 : 100 ≤ m := by omega
  have hσb : σ ≤ collatzBarrier 0 (P * m) := by omega
  have hLm : P * m + m - P * m = m := by omega
  have h63 := h63_fam hm100
  have hjpos : (2 : ℝ) ≤ ((P * m : ℕ) : ℝ) := by have := j_ge hm100; linarith
  have hlog : (1 : ℝ) ≤ Real.logb 2 ((P * m : ℕ) : ℝ) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]; simpa using hjpos
  refine ⟨4 * m, Kwin m, 1079998, 205198 * m, 1 / 108, 2, 2, 7, 1 / 6 + 1 / 1000, 1 / 60000,
    ?_, ?_, ?_, ?_, hσb, ?_, ?_, ?_, by norm_num, by norm_num, by norm_num, ?_, by norm_num,
    by norm_num, ?_, ?_, ?_, by omega, by omega, by rw [hLm] at hLt ⊢; exact hLt, ht, by omega,
    hnum_fam hm100 hσb hx (by omega) ht, hfr⟩
  · unfold P; omega
  · exact ⟨540000 * m, by unfold P; ring⟩
  · simpa using hx
  · unfold P; omega
  · have : 63 * σ ≤ 63 * collatzBarrier 0 (P * m) := Nat.mul_le_mul_left _ hσb
    omega
  · exact Nat.floor_pos.mpr (by linarith)
  · have h0 : (0 : ℝ) ≤ 7 * Real.logb 2 ((P * m : ℕ) : ℝ) := by linarith
    have := Nat.floor_le h0
    unfold Kwin; linarith
  · have hσ2 : σ ≤ 2 * (P * m) := hσb.trans (b_le_two_j m)
    unfold P at hσ2 ⊢; omega
  · have hj : (1080000000 : ℝ) ≤ ((P * m : ℕ) : ℝ) := by
      have : 1080000000 ≤ P * m := by unfold P; omega
      exact_mod_cast this
    push_cast at hj; norm_num; linarith
  · have e : ((P * m / 300 - 4 * m : ℕ) : ℝ) = 3596 * m := by
      have : P * m / 300 - 4 * m = 3596 * m := by unfold P; omega
      rw [this]; push_cast; ring
    rw [e]; push_cast; unfold P
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  · have hl2 := Real.log_two_lt_d9
    have hc := one_sub_cos_ge
    push_cast; unfold P
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hcpos : (0 : ℝ) ≤ 1 - Real.cos (Real.pi * (1 / 108)) := by linarith
    nlinarith

end Family

open Classical in
/-- **Exceptional-set bound from the arithmetic frontier, multi-pair engine** (explicit family,
`m ≥ 1000`). -/
theorem exceptional_bound_of_frontier_family (m : ℕ) (hm : 1000 ≤ m)
    (hfr : ∀ σ t, collatzBarrier 0 (P * m) ≤ σ + 4 * m → σ ≤ collatzBarrier 0 (P * m) → m ≤ t →
      t ≤ collatzBarrier 0 (P * m + m) - σ →
      FrontierRegion.PowerOfTwoDangerousWindowSparsityAt 0 (P * m) σ t (σ + t) (Kwin m) (1 / 108) 2 2) :
    (((range (2 ^ (collatzBarrier 0 (P * m) + 1))).filter fun μ =>
        Odd μ ∧ ∀ M, Confined ((0 : ℕ) : ℝ) (fun i => a (orbit μ i)) M).card : ℝ) ≤
      (1 + 1 + 1) * Real.exp (TaoExternal.lambdaStar * ((0 : ℕ) : ℝ)) / 2 *
        ((2 ^ (collatzBarrier 0 (P * m) + 1) : ℕ) : ℝ) ^
          (1 - TaoExternal.I0 * (((P * m + m : ℕ) : ℝ) / ((collatzBarrier 0 (P * m) + 1 : ℕ) : ℝ))) := by
  have hm100 : 100 ≤ m := by omega
  have hLm : P * m + m - P * m = m := by omega
  have hgap := gap_ge (m := m) (by omega)
  have hbB := bB_le m
  have hKpos : (0 : ℝ) < ((collatzBarrier 0 (P * m) + 1 : ℕ) : ℝ) := by positivity
  refine MultiWhiteChain.exceptional_bound_of_frontier_and_scalar_multi 0 (collatzBarrier 0 (P * m) + 1)
    (P * m) (4 * m) (N := P * m + m) _ 1 1 (by norm_num) (by norm_num) (by unfold P; omega) (by omega)
    (Nat.lt_succ_self _) (by omega) ?_ (by rw [hLm]; omega) ?_ (scalar_main hm100) ?_
  · rw [div_mul_cancel₀ _ hKpos.ne']
  · exact lt_of_le_of_lt (scalar_rho hm100) (by norm_num)
  · intro s σ hKs hσK hx hLt ht
    have hLt' : m ≤ s - σ := by rw [hLm] at hLt; exact hLt
    exact pairData_fam hm hσK hx hLt ht (hfr σ (s - σ) hx (by omega) hLt' ht)

/-- `A = N/K ≥ 1/α + 1/(2·10⁶)` along the family. -/
theorem A_ge (hm : 100 ≤ m) :
    alpha⁻¹ + 1 / 2000000 ≤ ((P * m + m : ℕ) : ℝ) / ((collatzBarrier 0 (P * m) + 1 : ℕ) : ℝ) := by
  have hα1 := alpha_ge
  have hα2 := alpha_le
  have hb := barrier_le (P * m)
  have hαpos : (0 : ℝ) < alpha := by linarith
  have hm0 : (100 : ℝ) ≤ m := by exact_mod_cast hm
  have hK : (0 : ℝ) < ((collatzBarrier 0 (P * m) + 1 : ℕ) : ℝ) := by positivity
  rw [le_div_iff₀ hK]
  push_cast at hb ⊢
  unfold P at hb ⊢
  push_cast at hb ⊢
  have hinv : alpha⁻¹ ≤ 50 / 79 := by
    rw [inv_le_comm₀ hαpos (by norm_num)]; linarith
  have hinv0 : 0 < alpha⁻¹ := inv_pos.mpr hαpos
  have hkey : (alpha⁻¹ + 1 / 2000000) * ((1080000 : ℝ) * m * alpha + 1) ≤ (1080000 + 1) * m := by
    have e : (alpha⁻¹ + 1 / 2000000) * ((1080000 : ℝ) * m * alpha + 1) =
        1080000 * m + alpha⁻¹ + (1080000 : ℝ) * m * alpha / 2000000 + 1 / 2000000 := by
      field_simp; ring
    rw [e]
    have : (1080000 : ℝ) * m * alpha / 2000000 ≤ 1080000 * m * (317 / 200) / 2000000 := by
      have hm' : (0 : ℝ) ≤ 1080000 * m := by positivity
      have := mul_le_mul_of_nonneg_left hα2 hm'
      linarith
    nlinarith
  have hmono : (alpha⁻¹ + 1 / 2000000) * ((collatzBarrier 0 (1080000 * m) : ℝ) + 1) ≤
      (alpha⁻¹ + 1 / 2000000) * ((1080000 : ℝ) * m * alpha + 1) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
  linarith

open Classical in
/-- **Explicit exponent, multi-pair engine.**  For every `m ≥ 1000`, conditionally on the arithmetic
frontier on the good pairs, `#(E₀ ∩ [0, 2^K)) ≤ (3/2) (2^K)^{H₂(1/α) − I₀/(2·10⁶)}`. -/
theorem exceptional_bound_family_exponent (m : ℕ) (hm : 1000 ≤ m)
    (hfr : ∀ σ t, collatzBarrier 0 (P * m) ≤ σ + 4 * m → σ ≤ collatzBarrier 0 (P * m) → m ≤ t →
      t ≤ collatzBarrier 0 (P * m + m) - σ →
      FrontierRegion.PowerOfTwoDangerousWindowSparsityAt 0 (P * m) σ t (σ + t) (Kwin m) (1 / 108) 2 2) :
    (((range (2 ^ (collatzBarrier 0 (P * m) + 1))).filter fun μ =>
        Odd μ ∧ ∀ M, Confined ((0 : ℕ) : ℝ) (fun i => a (orbit μ i)) M).card : ℝ) ≤
      3 / 2 * ((2 ^ (collatzBarrier 0 (P * m) + 1) : ℕ) : ℝ) ^
        (Real.binEntropy alpha⁻¹ / Real.log 2 - TaoExternal.I0 / 2000000) := by
  have h := exceptional_bound_of_frontier_family m hm hfr
  have hI0 := ExceptionalPowerBound.I0_pos'
  have hent := ExceptionalPowerBound.one_sub_I0_div_alpha_eq
  have hA := A_ge (m := m) (by omega)
  have hexp : 1 - TaoExternal.I0 * (((P * m + m : ℕ) : ℝ) / ((collatzBarrier 0 (P * m) + 1 : ℕ) : ℝ)) ≤
      Real.binEntropy alpha⁻¹ / Real.log 2 - TaoExternal.I0 / 2000000 := by
    rw [← hent]
    have := mul_le_mul_of_nonneg_left hA hI0.le
    have e : TaoExternal.I0 * (alpha⁻¹ + 1 / 2000000) = TaoExternal.I0 / alpha + TaoExternal.I0 / 2000000 := by
      rw [div_eq_mul_inv]; ring
    linarith
  have hx : (1 : ℝ) ≤ ((2 ^ (collatzBarrier 0 (P * m) + 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_two_pow
  rw [show TaoExternal.lambdaStar * ((0 : ℕ) : ℝ) = 0 by simp, Real.exp_zero] at h
  calc _ ≤ _ := h
    _ = 3 / 2 * ((2 ^ (collatzBarrier 0 (P * m) + 1) : ℕ) : ℝ) ^
          (1 - TaoExternal.I0 * (((P * m + m : ℕ) : ℝ) / ((collatzBarrier 0 (P * m) + 1 : ℕ) : ℝ))) := by
        norm_num
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx hexp) (by norm_num)

end FrontierFamilyMulti
end EOC
