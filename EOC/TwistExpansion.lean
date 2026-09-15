import EOC.SwapBound
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Twist expansion: additive-character decay ⇒ top-block collision bound

Setting: `r t : ℕ`, `M = 2^(r+t)`, a finite family `y : ι → ℕ` with `y i < M`, and its top blocks
`B i = ⌊y i / 2^r⌋ ∈ [0, 2^t)`.  With `e(x) = exp(2πi x)` (`SwapBound.ee`) define

* `Psi T r t y λ = ∑_{i∈T} e(λ y_i / M)` (additive characters of `y`),
* `coef r t λ = 2^{-r} ∑_{x<2^r} e(−λ x / M)` (twist coefficients).

Results:
* `ee_topBlock`, `sum_ee_topBlock` — **exact twist expansion**: for every `g`,
  `∑_i e(g B_i / 2^t) = ∑_{k<2^r} coef r t (g + 2^t k) · Psi T r t y (g + 2^t k)`.
* `norm_coef` — `‖coef r t λ‖ = ∏_{j<r} |cos(π λ 2^j / M)|` (binary product formula
  `geom_sum_two_pow`: `∑_{x<2^r} z^x = ∏_{j<r} (1 + z^(2^j))`).
* `Sfun_succ`, `Sfun_le` — the fibre ℓ¹ mass `Sfun r θ = ∑_{k<2^r} ∏_{j<r} |cos(π (θ+k) 2^j/2^r)|`
  satisfies the exact recursion `Sfun (r+1) θ = |cos(πθ/2)| Sfun r (θ/2) + |sin(πθ/2)| …` and the
  bound `Sfun r θ ≤ 1 + (r/2) sin(πθ)` on `[0,1]`.
* `sum_norm_coef_le` — **ℓ¹ bound**: `∑_{k<2^r} ‖coef r t (g + 2^t k)‖ ≤ 1 + r/2` for `g ≤ 2^t`.
* `norm_coef_le` — **pointwise twist bound**: for `0 < λ < M`,
  `‖coef r t λ‖ ≤ 2^t / (2 min(λ, M − λ))` (telescoping `sin_two_pow_mul` + Jordan `sin_ge_dist`).
* `sum_sq_norm_ee_eq_card_pairs` — Parseval for collisions of a family `B` with values `< 2^t`.
* `sq_norm_topBlock_le` — weighted Cauchy–Schwarz for one frequency `g ≤ 2^t`:
  `‖∑_i e(g B_i/2^t)‖^2 ≤ (1 + r/2) ∑_k ‖coef(g + 2^t k)‖ ‖Psi(g + 2^t k)‖^2`.
* `collision_le_weighted` — **main result (weighted form)**:
  `2^t · #{(i,j) ∈ T×T : B_i = B_j} ≤ |T|^2 + (1 + r/2) ∑_{1≤g<2^t} ∑_{k<2^r}
  ‖coef(g + 2^t k)‖ ‖Psi(g + 2^t k)‖^2`.
* `collision_le_of_psi` — uniform corollary: if `‖Psi λ‖ ≤ η |T|` for every `λ < M` not divisible by
  `2^t`, then `2^t · #{(i,j) : B_i = B_j} ≤ |T|^2 (1 + (1 + r/2)^2 2^t η^2)`.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace TwistExpansion

open Finset Real SwapBound

/-! ## Basic facts about `e` -/

theorem ee_add (a b : ℝ) : ee (a + b) = ee a * ee b := by
  unfold ee; rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem ee_zero : ee 0 = 1 := by simp [ee]

theorem ee_int (n : ℤ) : ee n = 1 := by
  unfold ee
  rw [show 2 * (π : ℂ) * Complex.I * ((n : ℝ) : ℂ) = n * (2 * π * Complex.I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I n

theorem ee_nat_mul (k : ℕ) (x : ℝ) : ee (k * x) = ee x ^ k := by
  unfold ee; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

theorem ee_eq_one_iff (x : ℝ) : ee x = 1 ↔ ∃ n : ℤ, x = n := by
  unfold ee
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h2 : (2 * (π : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have : ((x : ℝ) : ℂ) = (n : ℂ) := by
      apply mul_left_cancel₀ h2
      linear_combination hn
    exact_mod_cast this
  · rintro ⟨n, rfl⟩
    exact ⟨n, by push_cast; ring⟩

theorem conj_ee (x : ℝ) : (starRingEnd ℂ) (ee x) = ee (-x) := by
  unfold ee
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  push_cast; ring

/-- For `a, b < n`: `n ∣ a − b` (in `ℤ`) iff `a = b`. -/
theorem int_dvd_sub_iff {n a b : ℕ} (ha : a < n) (hb : b < n) :
    (n : ℤ) ∣ (a : ℤ) - b ↔ a = b := by
  constructor
  · intro h
    have hm : (b : ℤ) ≡ a [ZMOD n] := Int.modEq_iff_dvd.mpr h
    unfold Int.ModEq at hm
    rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hb),
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast ha)] at hm
    exact_mod_cast hm.symm
  · rintro rfl; simp

/-- **Orthogonality.** `∑_{k<N} e(k a / N) = N · [N ∣ a]`. -/
theorem sum_ee_orth (N : ℕ) (hN : 0 < N) (a : ℤ) :
    ∑ k ∈ range N, ee (k * a / N) = if (N : ℤ) ∣ a then (N : ℂ) else 0 := by
  have hk : ∀ k : ℕ, ee (k * a / N) = ee (a / N) ^ k := fun k => by
    rw [← ee_nat_mul]; congr 1; ring
  simp_rw [hk]
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  split_ifs with h
  · obtain ⟨q, hq⟩ := h
    have : ee (a / N) = 1 := by
      rw [show ((a : ℤ) : ℝ) / N = (q : ℤ) by rw [hq]; push_cast; field_simp]
      exact ee_int q
    simp [this]
  · have hz : ee (a / N) ≠ 1 := by
      intro hz
      obtain ⟨n, hn⟩ := (ee_eq_one_iff _).mp hz
      apply h
      refine ⟨n, ?_⟩
      have : (a : ℝ) = N * n := by rw [div_eq_iff hN'] at hn; linarith
      exact_mod_cast this
    rw [geom_sum_eq hz, ← ee_nat_mul]
    rw [show ((N : ℕ) : ℝ) * ((a : ℤ) / (N : ℝ)) = ((a : ℤ) : ℝ) by field_simp, ee_int]
    simp

/-! ## The exact twist expansion -/

/-- Twist coefficient `2^{-r} ∑_{x<2^r} e(−λ x / 2^(r+t))`. -/
noncomputable def coef (r t lam : ℕ) : ℂ :=
  ((2 : ℂ) ^ r)⁻¹ * ∑ x ∈ range (2 ^ r), ee (-((lam : ℝ) * x) / 2 ^ (r + t))

/-- Additive characters of the family `y` modulo `2^(r+t)`. -/
noncomputable def Psi {ι : Type*} (T : Finset ι) (r t : ℕ) (y : ι → ℕ) (lam : ℕ) : ℂ :=
  ∑ i ∈ T, ee ((lam : ℝ) * y i / 2 ^ (r + t))

theorem mem_range_dvd_iff {r y x : ℕ} (hx : x < 2 ^ r) :
    ((2 ^ r : ℕ) : ℤ) ∣ (y : ℤ) - x ↔ x = y % 2 ^ r := by
  have hsplit : (y : ℤ) - x = ((y % 2 ^ r : ℕ) : ℤ) - x + ((2 ^ r : ℕ) : ℤ) * (y / 2 ^ r : ℕ) := by
    have := Nat.mod_add_div y (2 ^ r)
    have h' : ((y : ℕ) : ℤ) = ((y % 2 ^ r : ℕ) : ℤ) + ((2 ^ r : ℕ) : ℤ) * (y / 2 ^ r : ℕ) := by
      exact_mod_cast this.symm
    rw [h']; ring
  rw [hsplit, dvd_add_left (dvd_mul_right _ _), int_dvd_sub_iff (Nat.mod_lt _ (by positivity)) hx]
  exact eq_comm

/-- **Twist expansion (one point).** -/
theorem ee_topBlock (r t g y : ℕ) :
    ee ((g : ℝ) * (y / 2 ^ r : ℕ) / 2 ^ t) =
      ∑ k ∈ range (2 ^ r), coef r t (g + 2 ^ t * k) *
        ee (((g + 2 ^ t * k : ℕ) : ℝ) * y / 2 ^ (r + t)) := by
  have h2r : (0 : ℝ) < 2 ^ r := by positivity
  have h2t : (0 : ℝ) < 2 ^ t := by positivity
  -- expand the coefficients and exchange the sums
  have hterm : ∀ k x : ℕ, ee (-(((g + 2 ^ t * k : ℕ) : ℝ) * x) / 2 ^ (r + t)) *
      ee (((g + 2 ^ t * k : ℕ) : ℝ) * y / 2 ^ (r + t)) =
      ee ((g : ℝ) * ((y : ℝ) - x) / 2 ^ (r + t)) *
        ee ((k : ℝ) * (((y : ℤ) - (x : ℤ) : ℤ) : ℝ) / ((2 ^ r : ℕ) : ℝ)) := by
    intro k x
    rw [← ee_add, ← ee_add]
    congr 1
    push_cast
    rw [pow_add]
    field_simp
    ring
  have hexp : ∑ k ∈ range (2 ^ r), coef r t (g + 2 ^ t * k) *
        ee (((g + 2 ^ t * k : ℕ) : ℝ) * y / 2 ^ (r + t)) =
      ((2 : ℂ) ^ r)⁻¹ * ∑ x ∈ range (2 ^ r), ee ((g : ℝ) * ((y : ℝ) - x) / 2 ^ (r + t)) *
        ∑ k ∈ range (2 ^ r), ee ((k : ℝ) * (((y : ℤ) - (x : ℤ) : ℤ) : ℝ) / ((2 ^ r : ℕ) : ℝ)) := by
    unfold coef
    simp_rw [mul_assoc, sum_mul, ← mul_sum]
    congr 1
    rw [sum_comm]
    refine sum_congr rfl fun x _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun k _ => hterm k x
  rw [hexp]
  simp_rw [sum_ee_orth (2 ^ r) (by positivity)]
  have hind : ∀ x ∈ range (2 ^ r), ee ((g : ℝ) * ((y : ℝ) - x) / 2 ^ (r + t)) *
      (if ((2 ^ r : ℕ) : ℤ) ∣ (y : ℤ) - (x : ℤ) then ((2 ^ r : ℕ) : ℂ) else 0) =
      if y % 2 ^ r = x then ((2 : ℂ) ^ r) * ee ((g : ℝ) * ((y : ℝ) - x) / 2 ^ (r + t))
      else 0 := by
    intro x hx
    rw [mem_range] at hx
    by_cases hc : y % 2 ^ r = x
    · have hd : ((2 ^ r : ℕ) : ℤ) ∣ (y : ℤ) - (x : ℤ) := (mem_range_dvd_iff hx).mpr hc.symm
      simp only [hd, hc, ite_true]; push_cast; ring
    · have hd : ¬ ((2 ^ r : ℕ) : ℤ) ∣ (y : ℤ) - (x : ℤ) :=
        fun h => hc ((mem_range_dvd_iff hx).mp h).symm
      simp only [hd, hc, ite_false, mul_zero]
  have hmem : y % 2 ^ r ∈ range (2 ^ r) := mem_range.mpr (Nat.mod_lt _ (by positivity))
  rw [sum_congr rfl hind, sum_ite_eq (range (2 ^ r)) (y % 2 ^ r)]
  simp only [hmem, ite_true]
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero), one_mul]
  congr 1
  have hy : (y : ℝ) - ((y % 2 ^ r : ℕ) : ℝ) = 2 ^ r * ((y / 2 ^ r : ℕ) : ℝ) := by
    have := Nat.mod_add_div y (2 ^ r)
    have h' : (y : ℝ) = ((y % 2 ^ r : ℕ) : ℝ) + 2 ^ r * ((y / 2 ^ r : ℕ) : ℝ) := by
      exact_mod_cast this.symm
    rw [h']; ring
  rw [hy, pow_add]
  field_simp

/-- **Twist expansion (family).** -/
theorem sum_ee_topBlock {ι : Type*} (T : Finset ι) (r t : ℕ) (y : ι → ℕ) (g : ℕ) :
    ∑ i ∈ T, ee ((g : ℝ) * (y i / 2 ^ r : ℕ) / 2 ^ t) =
      ∑ k ∈ range (2 ^ r), coef r t (g + 2 ^ t * k) * Psi T r t y (g + 2 ^ t * k) := by
  simp_rw [ee_topBlock r t g, Psi, mul_sum]
  exact sum_comm

/-! ## Product formula, pointwise and ℓ¹ bounds for the twist coefficients -/

/-- Binary product formula `∑_{x<2^r} z^x = ∏_{j<r} (1 + z^(2^j))`. -/
theorem geom_sum_two_pow (z : ℂ) (r : ℕ) :
    ∑ x ∈ range (2 ^ r), z ^ x = ∏ j ∈ range r, (1 + z ^ (2 ^ j)) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hsh : ∑ x ∈ range (2 ^ r), z ^ (2 ^ r + x) = z ^ (2 ^ r) * ∑ x ∈ range (2 ^ r), z ^ x := by
      rw [mul_sum]; exact sum_congr rfl fun x _ => pow_add _ _ _
    rw [pow_succ, mul_two, sum_range_add, hsh, prod_range_succ, ← ih]
    ring

/-- `∏_{j<r} |cos(π λ 2^j / 2^(r+t))|`. -/
noncomputable def cosProd (r t lam : ℕ) : ℝ :=
  ∏ j ∈ range r, |cos (π * ((lam : ℝ) * 2 ^ j / 2 ^ (r + t)))|

theorem norm_coef (r t lam : ℕ) : ‖coef r t lam‖ = cosProd r t lam := by
  set w := ee (-(lam : ℝ) / 2 ^ (r + t))
  have hx : ∀ x : ℕ, ee (-((lam : ℝ) * x) / 2 ^ (r + t)) = w ^ x := fun x => by
    rw [← ee_nat_mul]; congr 1; ring
  have hj : ∀ j : ℕ, ‖1 + w ^ (2 ^ j)‖ = 2 * |cos (π * ((lam : ℝ) * 2 ^ j / 2 ^ (r + t)))| := by
    intro j
    rw [show w ^ (2 ^ j) = ee (-((lam : ℝ) * 2 ^ j / 2 ^ (r + t))) by
      rw [← ee_nat_mul]; congr 1; push_cast; ring, ← ee_zero, norm_ee_add_ee]
    congr 2; ring_nf
  unfold coef cosProd
  simp_rw [hx]
  rw [geom_sum_two_pow, norm_mul, norm_prod, norm_inv, norm_pow, Complex.norm_ofNat]
  simp_rw [hj]
  rw [prod_mul_distrib, prod_const, card_range]
  field_simp

/-- Telescoping `sin(2^r x) = 2^r sin x ∏_{j<r} cos(2^j x)`. -/
theorem sin_two_pow_mul (r : ℕ) (x : ℝ) :
    sin (2 ^ r * x) = 2 ^ r * sin x * ∏ j ∈ range r, cos (2 ^ j * x) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [prod_range_succ, pow_succ, show 2 ^ r * 2 * x = 2 * (2 ^ r * x) by ring, sin_two_mul, ih]
    ring

/-- Jordan-type lower bound: for `0 < λ < M`, `sin(π λ/M) ≥ 2 min(λ, M−λ)/M`. -/
theorem sin_ge_dist {L M : ℝ} (hM : 0 < M) (hL0 : 0 ≤ L) (hLM : L ≤ M) :
    2 * min L (M - L) / M ≤ sin (π * (L / M)) := by
  rcases le_total L (M - L) with h | h
  · rw [min_eq_left h]
    have hq : 0 ≤ L / M := div_nonneg hL0 hM.le
    have hq2 : L / M ≤ 1 / 2 := by rw [div_le_iff₀ hM]; linarith
    have h1 := mul_le_sin (x := π * (L / M)) (mul_nonneg pi_pos.le hq) (by nlinarith [pi_pos])
    calc 2 * L / M = 2 / π * (π * (L / M)) := by field_simp
      _ ≤ _ := h1
  · rw [min_eq_right h]
    have hs : sin (π * (L / M)) = sin (π * ((M - L) / M)) := by
      rw [← sin_pi_sub]; congr 1; field_simp
    have hq : 0 ≤ (M - L) / M := div_nonneg (by linarith) hM.le
    have hq2 : (M - L) / M ≤ 1 / 2 := by rw [div_le_iff₀ hM]; linarith
    have h1 := mul_le_sin (x := π * ((M - L) / M)) (mul_nonneg pi_pos.le hq)
      (by nlinarith [pi_pos])
    rw [hs]
    calc 2 * (M - L) / M = 2 / π * (π * ((M - L) / M)) := by field_simp
      _ ≤ _ := h1

/-- **Pointwise twist bound.** For `0 < λ < 2^(r+t)`:
`‖coef r t λ‖ ≤ 2^t / (2 min(λ, 2^(r+t) − λ))`. -/
theorem norm_coef_le (r t lam : ℕ) (h0 : 0 < lam) (h1 : lam < 2 ^ (r + t)) :
    ‖coef r t lam‖ ≤ 2 ^ t / (2 * min (lam : ℝ) (2 ^ (r + t) - lam)) := by
  have hM : (0 : ℝ) < 2 ^ (r + t) := by positivity
  have hL1 : (lam : ℝ) < 2 ^ (r + t) := by exact_mod_cast h1
  have hL0 : (0 : ℝ) < lam := by exact_mod_cast h0
  have hmin : 0 < min (lam : ℝ) (2 ^ (r + t) - lam) := lt_min hL0 (by linarith)
  have hs := sin_ge_dist hM hL0.le hL1.le
  have hspos : 0 < sin (π * ((lam : ℝ) / 2 ^ (r + t))) := lt_of_lt_of_le (by positivity) hs
  -- telescoping identity
  have htel := sin_two_pow_mul r (π * ((lam : ℝ) / 2 ^ (r + t)))
  have hprod : cosProd r t lam * (2 ^ r * sin (π * ((lam : ℝ) / 2 ^ (r + t)))) =
      |sin (2 ^ r * (π * ((lam : ℝ) / 2 ^ (r + t))))| := by
    rw [htel, abs_mul, abs_mul, abs_of_pos hspos, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ r),
      abs_prod, cosProd]
    rw [show (∏ j ∈ range r, |cos (2 ^ j * (π * ((lam : ℝ) / 2 ^ (r + t))))|) =
        ∏ j ∈ range r, |cos (π * ((lam : ℝ) * 2 ^ j / 2 ^ (r + t)))| from
      prod_congr rfl fun j _ => by congr 2; ring]
    ring
  have hle : cosProd r t lam * (2 ^ r * sin (π * ((lam : ℝ) / 2 ^ (r + t)))) ≤ 1 := by
    rw [hprod]; exact abs_sin_le_one _
  rw [norm_coef, le_div_iff₀ (by positivity)]
  have hcp : 0 ≤ cosProd r t lam := prod_nonneg fun j _ => abs_nonneg _
  have key : cosProd r t lam *
      (2 ^ r * (2 * min (lam : ℝ) (2 ^ (r + t) - lam) / 2 ^ (r + t))) ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs (by positivity)) hcp) hle
  have h2 : (2 : ℝ) ^ (r + t) = 2 ^ r * 2 ^ t := pow_add _ _ _
  rw [h2] at key
  have h2r : (0 : ℝ) < 2 ^ r := by positivity
  have h2t : (0 : ℝ) < 2 ^ t := by positivity
  have : cosProd r t lam * (2 * min (lam : ℝ) (2 ^ (r + t) - lam)) / 2 ^ t ≤ 1 := by
    rw [h2]
    calc cosProd r t lam * (2 * min (lam : ℝ) (2 ^ r * 2 ^ t - lam)) / 2 ^ t
        = cosProd r t lam *
            (2 ^ r * (2 * min (lam : ℝ) (2 ^ r * 2 ^ t - lam) / (2 ^ r * 2 ^ t))) := by
          field_simp
      _ ≤ 1 := key
  rw [div_le_one h2t] at this
  linarith

/-- The fibre ℓ¹ mass `Sfun r θ = ∑_{k<2^r} ∏_{j<r} |cos(π (θ+k) 2^j / 2^r)|`. -/
noncomputable def Sfun (r : ℕ) (θ : ℝ) : ℝ :=
  ∑ k ∈ range (2 ^ r), ∏ j ∈ range r, |cos (π * ((θ + k) * 2 ^ j / 2 ^ r))|

theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ k ∈ range (2 * n), f k = ∑ k ∈ range n, (f (2 * k) + f (2 * k + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, add_assoc]

theorem Sfun_term (r : ℕ) (θ : ℝ) (b k : ℕ) :
    ∏ j ∈ range (r + 1), |cos (π * ((θ + ((2 * k + b : ℕ) : ℝ)) * 2 ^ j / 2 ^ (r + 1)))| =
      (∏ j ∈ range r, |cos (π * (((θ + b) / 2 + k) * 2 ^ j / 2 ^ r))|) *
        |cos (π * ((θ + b) / 2))| := by
  rw [prod_range_succ]
  congr 1
  · refine prod_congr rfl fun j _ => ?_
    congr 2; push_cast; rw [pow_succ]; field_simp; ring
  · rw [show π * ((θ + ((2 * k + b : ℕ) : ℝ)) * 2 ^ r / 2 ^ (r + 1)) =
        π * ((θ + b) / 2) + (k : ℕ) * π by push_cast; rw [pow_succ]; field_simp; ring,
      cos_add_nat_mul_pi, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

/-- Exact recursion for the fibre mass. -/
theorem Sfun_succ (r : ℕ) (θ : ℝ) :
    Sfun (r + 1) θ = |cos (π * (θ / 2))| * Sfun r (θ / 2) +
      |cos (π * ((θ + 1) / 2))| * Sfun r ((θ + 1) / 2) := by
  unfold Sfun
  rw [pow_succ, mul_comm (2 ^ r) 2, sum_range_two_mul]
  have e0 := fun k => Sfun_term r θ 0 k
  have e1 := fun k => Sfun_term r θ 1 k
  simp only [Nat.cast_zero, add_zero, Nat.cast_one] at e0 e1
  rw [sum_congr rfl fun k _ => by rw [e0 k, e1 k], sum_add_distrib, ← sum_mul, ← sum_mul]
  ring

/-- `Sfun r θ ≤ 1 + (r/2) sin(πθ)` on `[0,1]`. -/
theorem Sfun_le (r : ℕ) : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → Sfun r θ ≤ 1 + r / 2 * sin (π * θ) := by
  induction r with
  | zero => intro θ _ _; simp [Sfun]
  | succ r ih =>
    intro θ h0 h1
    rw [Sfun_succ]
    set a := π * (θ / 2) with ha
    have ha0 : 0 ≤ a := by positivity
    have ha1 : a ≤ π / 2 := by rw [ha]; nlinarith [pi_pos]
    have hc : 0 ≤ cos a := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], ha1⟩
    have hs : 0 ≤ sin a := sin_nonneg_of_nonneg_of_le_pi ha0 (by linarith [pi_pos])
    have e1 : π * ((θ + 1) / 2) = a + π / 2 := by rw [ha]; ring
    have hc1 : |cos (π * ((θ + 1) / 2))| = sin a := by
      rw [e1, cos_add_pi_div_two, abs_neg, abs_of_nonneg hs]
    have hs1 : sin (π * ((θ + 1) / 2)) = cos a := by rw [e1, sin_add_pi_div_two]
    have h2 : sin (π * θ) = 2 * sin a * cos a := by
      rw [show π * θ = 2 * a by rw [ha]; ring, sin_two_mul]
    have i0 := ih (θ / 2) (by positivity) (by linarith)
    have i1 := ih ((θ + 1) / 2) (by positivity) (by linarith)
    rw [hs1] at i1
    rw [abs_of_nonneg hc, hc1, h2]
    have m0 := mul_le_mul_of_nonneg_left i0 hc
    have m1 := mul_le_mul_of_nonneg_left i1 hs
    push_cast
    nlinarith [mul_nonneg (sub_nonneg.2 (sin_le_one a)) (sub_nonneg.2 (cos_le_one a)),
      mul_nonneg hs hc]

theorem sum_cosProd_eq (r t g : ℕ) :
    ∑ k ∈ range (2 ^ r), cosProd r t (g + 2 ^ t * k) = Sfun r ((g : ℝ) / 2 ^ t) := by
  unfold cosProd Sfun
  refine sum_congr rfl fun k _ => prod_congr rfl fun j _ => ?_
  congr 2; push_cast; rw [pow_add]; field_simp

/-- **ℓ¹ bound on a fibre.** For `g ≤ 2^t`: `∑_{k<2^r} ‖coef r t (g + 2^t k)‖ ≤ 1 + r/2`. -/
theorem sum_norm_coef_le (r t g : ℕ) (hg : g ≤ 2 ^ t) :
    ∑ k ∈ range (2 ^ r), ‖coef r t (g + 2 ^ t * k)‖ ≤ 1 + r / 2 := by
  simp_rw [norm_coef]
  rw [sum_cosProd_eq]
  have hθ1 : (g : ℝ) / 2 ^ t ≤ 1 := by
    rw [div_le_one (by positivity)]; exact_mod_cast hg
  have := Sfun_le r ((g : ℝ) / 2 ^ t) (by positivity) hθ1
  have hr : (0 : ℝ) ≤ r / 2 := by positivity
  nlinarith [sin_le_one (π * ((g : ℝ) / 2 ^ t))]

/-! ## Parseval and the collision bound -/

theorem sq_norm_eq_re (z : ℂ) : ‖z‖ ^ 2 = (z * (starRingEnd ℂ) z).re := by
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- **Parseval for collisions** of a family with values `< 2^t`. -/
theorem sum_sq_norm_ee_eq_card_pairs {ι : Type*} (T : Finset ι) (t : ℕ) (B : ι → ℕ)
    (hB : ∀ i ∈ T, B i < 2 ^ t) :
    ∑ g ∈ range (2 ^ t), ‖∑ i ∈ T, ee ((g : ℝ) * B i / 2 ^ t)‖ ^ 2 =
      2 ^ t * ((((T ×ˢ T).filter fun p => B p.1 = B p.2).card : ℕ) : ℝ) := by
  have hterm : ∀ g : ℕ, ‖∑ i ∈ T, ee ((g : ℝ) * B i / 2 ^ t)‖ ^ 2 =
      (∑ p ∈ T ×ˢ T, ee ((g : ℝ) * (((B p.1 : ℤ) - (B p.2 : ℤ) : ℤ) : ℝ) /
        ((2 ^ t : ℕ) : ℝ))).re := by
    intro g
    rw [sq_norm_eq_re, map_sum, sum_mul_sum, ← sum_product']
    congr 1
    refine sum_congr rfl fun p _ => ?_
    rw [conj_ee, ← ee_add]
    congr 1; push_cast; ring
  simp_rw [hterm]
  rw [← Complex.re_sum, sum_comm]
  have horth : ∀ p ∈ T ×ˢ T, ∑ g ∈ range (2 ^ t), ee ((g : ℝ) *
      (((B p.1 : ℤ) - (B p.2 : ℤ) : ℤ) : ℝ) / ((2 ^ t : ℕ) : ℝ)) =
      if B p.1 = B p.2 then ((2 ^ t : ℕ) : ℂ) else 0 := by
    intro p hp
    rw [mem_product] at hp
    rw [sum_ee_orth (2 ^ t) (by positivity)]
    have := int_dvd_sub_iff (n := 2 ^ t) (hB _ hp.1) (hB _ hp.2)
    push_cast at this ⊢
    by_cases h : B p.1 = B p.2
    · simp [h]
    · have h' : ¬ ((2 : ℤ) ^ t ∣ (B p.1 : ℤ) - B p.2) := fun hd => h (this.mp hd)
      simp [h, h']
  rw [sum_congr rfl horth, ← sum_filter, sum_const, nsmul_eq_mul]
  rw [show ((((T ×ˢ T).filter fun p => B p.1 = B p.2).card : ℕ) : ℂ) * ((2 ^ t : ℕ) : ℂ) =
      ((2 ^ t * ((((T ×ˢ T).filter fun p => B p.1 = B p.2).card : ℕ) : ℝ) : ℝ) : ℂ) by
    push_cast; ring, Complex.ofReal_re]

/-- **Weighted twist bound for one frequency** (`g ≤ 2^t`). -/
theorem sq_norm_topBlock_le {ι : Type*} (T : Finset ι) (r t : ℕ) (y : ι → ℕ) (g : ℕ)
    (hg : g ≤ 2 ^ t) :
    ‖∑ i ∈ T, ee ((g : ℝ) * (y i / 2 ^ r : ℕ) / 2 ^ t)‖ ^ 2 ≤
      (1 + r / 2) * ∑ k ∈ range (2 ^ r),
        ‖coef r t (g + 2 ^ t * k)‖ * ‖Psi T r t y (g + 2 ^ t * k)‖ ^ 2 := by
  rw [sum_ee_topBlock]
  have h1 : ‖∑ k ∈ range (2 ^ r), coef r t (g + 2 ^ t * k) * Psi T r t y (g + 2 ^ t * k)‖ ≤
      ∑ k ∈ range (2 ^ r), ‖coef r t (g + 2 ^ t * k)‖ * ‖Psi T r t y (g + 2 ^ t * k)‖ :=
    (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun k _ => norm_mul _ _))
  have hcs : (∑ k ∈ range (2 ^ r), ‖coef r t (g + 2 ^ t * k)‖ * ‖Psi T r t y (g + 2 ^ t * k)‖) ^ 2
      ≤ (∑ k ∈ range (2 ^ r), ‖coef r t (g + 2 ^ t * k)‖) *
        ∑ k ∈ range (2 ^ r), ‖coef r t (g + 2 ^ t * k)‖ * ‖Psi T r t y (g + 2 ^ t * k)‖ ^ 2 :=
    sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun _ _ => norm_nonneg _)
      (fun _ _ => by positivity) (fun _ _ => le_of_eq (by ring))
  have hS := sum_norm_coef_le r t g hg
  have hW : 0 ≤ ∑ k ∈ range (2 ^ r), ‖coef r t (g + 2 ^ t * k)‖ *
      ‖Psi T r t y (g + 2 ^ t * k)‖ ^ 2 := sum_nonneg fun _ _ => by positivity
  calc _ ≤ (∑ k ∈ range (2 ^ r), ‖coef r t (g + 2 ^ t * k)‖ * ‖Psi T r t y (g + 2 ^ t * k)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := hcs
    _ ≤ _ := mul_le_mul_of_nonneg_right hS hW

/-- **Collision bound, weighted form (main result).** With `B i = ⌊y i / 2^r⌋`:
`2^t · #{(i,j) : B_i = B_j} ≤ |T|^2 + (1 + r/2) ∑_{1 ≤ g < 2^t} ∑_{k<2^r}
‖coef(g + 2^t k)‖ ‖Psi(g + 2^t k)‖^2`. -/
theorem collision_le_weighted {ι : Type*} (T : Finset ι) (r t : ℕ) (y : ι → ℕ)
    (hy : ∀ i ∈ T, y i < 2 ^ (r + t)) :
    (2 : ℝ) ^ t * ((((T ×ˢ T).filter fun p => y p.1 / 2 ^ r = y p.2 / 2 ^ r).card : ℕ) : ℝ) ≤
      (T.card : ℝ) ^ 2 + (1 + r / 2) * ∑ g ∈ Ico 1 (2 ^ t), ∑ k ∈ range (2 ^ r),
        ‖coef r t (g + 2 ^ t * k)‖ * ‖Psi T r t y (g + 2 ^ t * k)‖ ^ 2 := by
  have hB : ∀ i ∈ T, y i / 2 ^ r < 2 ^ t := fun i hi => by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, add_comm]; exact hy i hi
  rw [← sum_sq_norm_ee_eq_card_pairs T t (fun i => y i / 2 ^ r) hB, range_eq_Ico,
    sum_eq_sum_Ico_succ_bot (by positivity), mul_sum]
  have h0 : ‖∑ i ∈ T, ee (((0 : ℕ) : ℝ) * ((y i / 2 ^ r : ℕ) : ℝ) / 2 ^ t)‖ ^ 2 =
      (T.card : ℝ) ^ 2 := by
    simp [ee_zero]
  rw [h0]
  gcongr with g hg
  exact sq_norm_topBlock_le T r t y g (by rw [mem_Ico] at hg; omega)

/-- **Uniform corollary.** If `‖Psi λ‖ ≤ η |T|` for every `λ < 2^(r+t)` not divisible by `2^t`,
then `2^t · #{(i,j) : B_i = B_j} ≤ |T|^2 (1 + (1 + r/2)^2 2^t η^2)`. -/
theorem collision_le_of_psi {ι : Type*} (T : Finset ι) (r t : ℕ) (y : ι → ℕ)
    (hy : ∀ i ∈ T, y i < 2 ^ (r + t)) (η : ℝ)
    (hΨ : ∀ lam, lam < 2 ^ (r + t) → ¬ 2 ^ t ∣ lam → ‖Psi T r t y lam‖ ≤ η * T.card) :
    (2 : ℝ) ^ t * ((((T ×ˢ T).filter fun p => y p.1 / 2 ^ r = y p.2 / 2 ^ r).card : ℕ) : ℝ) ≤
      (T.card : ℝ) ^ 2 * (1 + (1 + r / 2) ^ 2 * 2 ^ t * η ^ 2) := by
  have hw := collision_le_weighted T r t y hy
  have hC : (0 : ℝ) ≤ 1 + r / 2 := by positivity
  have hfib : ∀ g ∈ Ico 1 (2 ^ t), ∑ k ∈ range (2 ^ r),
      ‖coef r t (g + 2 ^ t * k)‖ * ‖Psi T r t y (g + 2 ^ t * k)‖ ^ 2 ≤
      (1 + r / 2) * (η * T.card) ^ 2 := by
    intro g hg
    rw [mem_Ico] at hg
    have hk : ∀ k ∈ range (2 ^ r), ‖coef r t (g + 2 ^ t * k)‖ * ‖Psi T r t y (g + 2 ^ t * k)‖ ^ 2
        ≤ ‖coef r t (g + 2 ^ t * k)‖ * (η * T.card) ^ 2 := by
      intro k hk
      rw [mem_range] at hk
      have hlt : g + 2 ^ t * k < 2 ^ (r + t) := by
        have : 2 ^ t * k + 2 ^ t ≤ 2 ^ t * 2 ^ r := by
          rw [← mul_add_one]; exact Nat.mul_le_mul_left _ hk
        rw [pow_add, mul_comm (2 ^ r)]; omega
      have hnd : ¬ 2 ^ t ∣ g + 2 ^ t * k := by
        rw [Nat.dvd_add_left (dvd_mul_right _ _)]
        exact Nat.not_dvd_of_pos_of_lt (by omega) hg.2
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact pow_le_pow_left₀ (norm_nonneg _) (hΨ _ hlt hnd) 2
    calc _ ≤ ∑ k ∈ range (2 ^ r), ‖coef r t (g + 2 ^ t * k)‖ * (η * T.card) ^ 2 := sum_le_sum hk
      _ = (∑ k ∈ range (2 ^ r), ‖coef r t (g + 2 ^ t * k)‖) * (η * T.card) ^ 2 := by rw [sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (sum_norm_coef_le r t g (by omega)) (by positivity)
  have hsum : ∑ g ∈ Ico 1 (2 ^ t), ∑ k ∈ range (2 ^ r),
      ‖coef r t (g + 2 ^ t * k)‖ * ‖Psi T r t y (g + 2 ^ t * k)‖ ^ 2 ≤
      2 ^ t * ((1 + r / 2) * (η * T.card) ^ 2) := by
    calc _ ≤ ∑ _g ∈ Ico 1 (2 ^ t), (1 + r / 2) * (η * T.card) ^ 2 := sum_le_sum hfib
      _ = ((2 ^ t - 1 : ℕ) : ℝ) * ((1 + r / 2) * (η * T.card) ^ 2) := by
          rw [sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have : ((2 ^ t - 1 : ℕ) : ℝ) ≤ ((2 ^ t : ℕ) : ℝ) := by exact_mod_cast Nat.sub_le _ _
          simp
  calc _ ≤ _ := hw
    _ ≤ (T.card : ℝ) ^ 2 + (1 + r / 2) * (2 ^ t * ((1 + r / 2) * (η * T.card) ^ 2)) := by
        gcongr
    _ = _ := by ring

end TwistExpansion
end EOC
