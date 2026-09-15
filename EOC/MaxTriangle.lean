import EOC.TriangleArray
import EOC.GoodAngles

/-!
# Sublinear maximal Tao triangles from the p-adic Subspace Theorem

For a cell `(a,b)` with `a, b ≥ 1` put `X = 2^a · y(a,b)` and `Y = X − 1`; then `3^b ∣ Y`
(`three_pow_dvd`), so `2^a y − 3^b z = 1` with `z = Y / 3^b`.

**External input, kept as a hypothesis.**  `SubspaceInstance δ` is the instance of the p-adic
Subspace Theorem (Schlickewei 1976; Evertse, *Diophantine Approximation*, Ch. 8, Thm 8.7) with
`n = 2`, `K = ℚ`, places `∞, 2, 3`, forms `X − Y, Y` at `∞` and `X, Y` at `2` and `3`, `C = 1`,
`ε = δ`: all nonzero `x = (X,Y) ∈ ℤ²` with
`|X − Y| · |Y| · |X|₂ |Y|₂ · |X|₃ |Y|₃ ≤ max(|X|,|Y|)^{−δ}` lie on finitely many lines through `0`.
Nothing about the Subspace Theorem is proved here.

Proved (no further hypotheses):
* `y_ne_zero`, `three_pow_dvd`, `Y_ne_zero` — the apex relation and nonvanishing;
* `subspaceProd_le` (`P ≤ 2|U|`), `H_bounds` (`1 ≤ H ≤ 2^a 3^b`), `subspace_ineq_of_exc`;
* **`exc_finite`**: `SubspaceInstance δ` ⇒ the set of cells with `|U(a,b)| ≤ ½ (2^a 3^b)^{−δ}`,
  `a, b ≥ 1`, is finite (each line meets `X − Y = 1` once; `2^a ≤ |X|`, `3^b ≤ |Y|`);
* `apexBound_of_exc_finite`, **`sublinearMaxTriangle_of_subspace`**:
  `size(a,b) = log(η 3^b/|y|) ≤ δ(a log 2 + b log 3) + C_δ` for all `a, b ≥ 1`;
* `apex_size_le`, `depth_le`, **`eventually_maxTriangleLE`**, `maxTriangleLE_box`: every triangle
  meeting a region where `a log 2 + b log 3 ≤ K L` has apex size `≤ ε L` once `L ≥ L₀(ε)`
  (`R_max(L) = o(L)`; `L₀` is not computable from the proof: the Subspace Theorem is ineffective).
  The column `a = 0` (`y = 1`, `z = 0`) is a genuine infinite exception, hence `a ≥ 1` throughout.
* Decay side: `card_good_ge` (gap `≤ G` ⇒ `≥ ⌊R/(G+1)⌋` good blocks),
  `positiveDensityGoodAngles_of_gap`, `lowFreqDecay_of_gap`, and
  `lowFreqDecay_of_sublinearMaxTriangle`, which additionally assumes the **unproved**
  `TriangleGapBridge` (max triangle size `≤ R₀` ⇒ good-block gaps `≤ G R₀`).

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace MaxTriangle

open Finset TriangleArray ShellDecomposition

noncomputable section

/-! ## 1. The apex relation -/

theorem u_zero (b : ℕ) : u 0 b = 1 := by simp [u]

/-- `y(a,b) ≠ 0` for `b ≥ 1` (`2^{-a}` is a unit mod `3^b`). -/
theorem y_ne_zero {a b : ℕ} (hb : 1 ≤ b) : y a b ≠ 0 := by
  intro h
  have h1 : ((y a b : ℤ) : ZMod (3 ^ b)) = u a b := ZMod.coe_valMinAbs _
  rw [h, Int.cast_zero] at h1
  have h2 := two_pow_mul_u 0 b a
  rw [zero_add, ← h1, mul_zero, u_zero] at h2
  have h3 : ((1 : ℕ) : ZMod (3 ^ b)) = 0 := by rw [Nat.cast_one]; exact h2.symm
  have h4 := (ZMod.natCast_eq_zero_iff 1 (3 ^ b)).1 h3
  have h5 : 3 ^ b = 1 := Nat.dvd_one.mp h4
  have h6 : 3 ≤ 3 ^ b := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ b := Nat.pow_le_pow_right (by norm_num) hb
  omega

/-- **Apex relation.** `3^b ∣ 2^a y(a,b) − 1`. -/
theorem three_pow_dvd (a b : ℕ) : (3 : ℤ) ^ b ∣ 2 ^ a * y a b - 1 := by
  have h1 := cast_two_pow_mul_y 0 b a 0
  simp only [zero_add, Nat.add_zero] at h1
  rw [u_zero] at h1
  have h2 : ((2 ^ a * y a b - 1 : ℤ) : ZMod (3 ^ b)) = 0 := by
    rw [Int.cast_sub, h1, Int.cast_one, sub_self]
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h2
  exact_mod_cast this

/-- `Y = 2^a y − 1 ≠ 0` for `a ≥ 1` (it is odd). -/
theorem Y_ne_zero {a b : ℕ} (ha : 1 ≤ a) : 2 ^ a * y a b - 1 ≠ 0 := by
  intro h
  have h2 : (2 : ℤ) ∣ 2 ^ a * y a b := Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
  have : (2 : ℤ) ∣ 1 := by
    have e : 2 ^ a * y a b = 1 := by linarith
    rwa [e] at h2
  norm_num at this

theorem one_le_abs_y {a b : ℕ} (hb : 1 ≤ b) : (1 : ℤ) ≤ |y a b| := Int.one_le_abs (y_ne_zero hb)

theorem two_abs_y_le (a b : ℕ) : 2 * |y a b| ≤ 3 ^ b := by
  have h := (u a b).valMinAbs_mem_Ioc
  obtain ⟨h1, h2⟩ := h
  have e : (u a b).valMinAbs = y a b := rfl
  rw [e] at h1 h2
  push_cast at h1 h2
  have : |2 * y a b| ≤ 3 ^ b := abs_le.mpr ⟨by linarith, by linarith⟩
  rwa [abs_mul, abs_two] at this

/-! ## 2. The Subspace instance (external hypothesis) -/

/-- The product in Thm 8.7 for `x = (X, Y)`: forms `X − Y, Y` at `∞`, `X, Y` at `2` and `3`. -/
def subspaceProd (X Y : ℤ) : ℝ :=
  |((X - Y : ℤ) : ℝ)| * |((Y : ℤ) : ℝ)| *
    ((padicNorm 2 (X : ℚ) * padicNorm 2 (Y : ℚ) * padicNorm 3 (X : ℚ) *
      padicNorm 3 (Y : ℚ) : ℚ) : ℝ)

/-- **Instance of the p-adic Subspace Theorem** (Schlickewei; Evertse Ch. 8 Thm 8.7), NOT proved:
`n = 2`, `K = ℚ`, `S = {∞, 2, 3}`, `C = 1`, `ε = δ`.  All nonzero solutions `(X, Y) ∈ ℤ²` of
`subspaceProd X Y ≤ max(|X|,|Y|)^{−δ}` lie on finitely many lines `ℚ·v`, `v ∈ F`. -/
def SubspaceInstance (δ : ℝ) : Prop :=
  ∃ F : Finset (ℤ × ℤ), ∀ X Y : ℤ, (X, Y) ≠ (0, 0) →
    subspaceProd X Y ≤ (max |(X : ℝ)| |(Y : ℝ)|) ^ (-δ) →
      ∃ v ∈ F, v ≠ (0, 0) ∧ X * v.2 = Y * v.1

/-- Exceptional cells at level `δ`: `|U(a,b)| ≤ ½ (2^a 3^b)^{−δ}`, i.e.
`2 |y| (2^a 3^b)^δ ≤ 3^b`, with `a, b ≥ 1`. -/
def Exc (δ : ℝ) : Set (ℕ × ℕ) :=
  {p | 1 ≤ p.1 ∧ 1 ≤ p.2 ∧
    2 * |((y p.1 p.2 : ℤ) : ℝ)| * ((2 : ℝ) ^ p.1 * 3 ^ p.2) ^ δ ≤ 3 ^ p.2}

/-- `P(X, X−1) ≤ 2 |U(a,b)|` for `X = 2^a y(a,b)`. -/
theorem subspaceProd_le {a b : ℕ} (_ha : 1 ≤ a) (hb : 1 ≤ b) :
    subspaceProd (2 ^ a * y a b) (2 ^ a * y a b - 1) ≤ 2 * |((y a b : ℤ) : ℝ)| / 3 ^ b := by
  set X : ℤ := 2 ^ a * y a b with hX
  have h2X : padicNorm 2 (X : ℚ) ≤ (2 : ℚ) ^ (-(a : ℤ)) := by
    have hd : ((2 ^ a : ℕ) : ℤ) ∣ X := by push_cast; exact Dvd.intro _ rfl
    have := (padicNorm.dvd_iff_norm_le (p := 2)).mp hd
    exact_mod_cast this
  have h3Y : padicNorm 3 ((X - 1 : ℤ) : ℚ) ≤ (3 : ℚ) ^ (-(b : ℤ)) := by
    have hd : ((3 ^ b : ℕ) : ℤ) ∣ X - 1 := by push_cast; exact three_pow_dvd a b
    have := (padicNorm.dvd_iff_norm_le (p := 3)).mp hd
    exact_mod_cast this
  have h2Y : padicNorm 2 ((X - 1 : ℤ) : ℚ) ≤ 1 := padicNorm.of_int _
  have h3X : padicNorm 3 (X : ℚ) ≤ 1 := padicNorm.of_int _
  have n2X := padicNorm.nonneg (p := 2) (X : ℚ)
  have n2Y := padicNorm.nonneg (p := 2) ((X - 1 : ℤ) : ℚ)
  have n3X := padicNorm.nonneg (p := 3) (X : ℚ)
  have n3Y := padicNorm.nonneg (p := 3) ((X - 1 : ℤ) : ℚ)
  have hq : padicNorm 2 (X : ℚ) * padicNorm 2 ((X - 1 : ℤ) : ℚ) * padicNorm 3 (X : ℚ) *
      padicNorm 3 ((X - 1 : ℤ) : ℚ) ≤ (2 : ℚ) ^ (-(a : ℤ)) * 1 * 1 * (3 : ℚ) ^ (-(b : ℤ)) := by
    have e2 : (0 : ℚ) ≤ (2 : ℚ) ^ (-(a : ℤ)) := by positivity
    exact mul_le_mul (mul_le_mul (mul_le_mul h2X h2Y n2Y e2) h3X n3X (by positivity)) h3Y n3Y
      (by positivity)
  set q : ℝ := ((padicNorm 2 (X : ℚ) * padicNorm 2 ((X - 1 : ℤ) : ℚ) * padicNorm 3 (X : ℚ) *
      padicNorm 3 ((X - 1 : ℤ) : ℚ) : ℚ) : ℝ) with hqdef
  have hq' : q ≤ ((2 : ℝ) ^ a)⁻¹ * ((3 : ℝ) ^ b)⁻¹ := by
    have := (Rat.cast_le (K := ℝ)).mpr hq
    simp only [zpow_neg, zpow_natCast, mul_one] at this
    push_cast at this
    rw [hqdef]; push_cast; exact this
  have hq0 : 0 ≤ q := by
    rw [hqdef]; exact_mod_cast mul_nonneg (mul_nonneg (mul_nonneg n2X n2Y) n3X) n3Y
  have hy1 : (1 : ℝ) ≤ |((y a b : ℤ) : ℝ)| := by exact_mod_cast one_le_abs_y (a := a) hb
  have hXabs : |((X : ℤ) : ℝ)| = 2 ^ a * |((y a b : ℤ) : ℝ)| := by
    rw [hX]; push_cast; rw [abs_mul, abs_pow, abs_two]
  have h2a : (1 : ℝ) ≤ 2 ^ a := one_le_pow₀ (by norm_num)
  have hYabs : |((X - 1 : ℤ) : ℝ)| ≤ 2 * 2 ^ a * |((y a b : ℤ) : ℝ)| := by
    have h1 : |((X - 1 : ℤ) : ℝ)| ≤ |((X : ℤ) : ℝ)| + 1 := by
      push_cast
      calc |(X : ℝ) - 1| ≤ |(X : ℝ)| + |(1 : ℝ)| := abs_sub _ _
        _ = |(X : ℝ)| + 1 := by rw [abs_one]
    rw [hXabs] at h1
    nlinarith
  have hdiff : |(((X - (X - 1)) : ℤ) : ℝ)| = 1 := by push_cast; ring_nf; simp
  unfold subspaceProd
  rw [hdiff, one_mul, ← hqdef]
  calc |((X - 1 : ℤ) : ℝ)| * q
        ≤ (2 * 2 ^ a * |((y a b : ℤ) : ℝ)|) * (((2 : ℝ) ^ a)⁻¹ * ((3 : ℝ) ^ b)⁻¹) :=
        mul_le_mul hYabs hq' hq0 (by positivity)
    _ = 2 * |((y a b : ℤ) : ℝ)| / 3 ^ b := by field_simp

/-- `1 ≤ H ≤ 2^a 3^b` for `H = max(|X|, |X − 1|)`. -/
theorem H_bounds {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    1 ≤ max |(((2 ^ a * y a b : ℤ)) : ℝ)| |(((2 ^ a * y a b - 1 : ℤ)) : ℝ)| ∧
      max |(((2 ^ a * y a b : ℤ)) : ℝ)| |(((2 ^ a * y a b - 1 : ℤ)) : ℝ)| ≤
        (2 : ℝ) ^ a * 3 ^ b := by
  have hy1 : (1 : ℝ) ≤ |((y a b : ℤ) : ℝ)| := by exact_mod_cast one_le_abs_y (a := a) hb
  have hy2 : 2 * |((y a b : ℤ) : ℝ)| ≤ 3 ^ b := by exact_mod_cast two_abs_y_le a b
  have h2a : (2 : ℝ) ≤ 2 ^ a := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ a := pow_le_pow_right₀ (by norm_num) ha
  have hXabs : |(((2 ^ a * y a b : ℤ)) : ℝ)| = 2 ^ a * |((y a b : ℤ) : ℝ)| := by
    push_cast; rw [abs_mul, abs_pow, abs_two]
  have hY : |(((2 ^ a * y a b - 1 : ℤ)) : ℝ)| ≤ 2 ^ a * |((y a b : ℤ) : ℝ)| + 1 := by
    rw [← hXabs]; push_cast
    calc |(2 : ℝ) ^ a * (y a b : ℝ) - 1| ≤ |(2 : ℝ) ^ a * (y a b : ℝ)| + |(1 : ℝ)| := abs_sub _ _
      _ = _ := by rw [abs_one]
  refine ⟨le_max_of_le_left (by rw [hXabs]; nlinarith), max_le ?_ ?_⟩
  · rw [hXabs]; nlinarith
  · nlinarith

/-- An exceptional cell gives a solution of the Subspace inequality. -/
theorem subspace_ineq_of_exc {δ : ℝ} (hδ : 0 ≤ δ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hexc : 2 * |((y a b : ℤ) : ℝ)| * ((2 : ℝ) ^ a * 3 ^ b) ^ δ ≤ 3 ^ b) :
    subspaceProd (2 ^ a * y a b) (2 ^ a * y a b - 1) ≤
      (max |(((2 ^ a * y a b : ℤ)) : ℝ)| |(((2 ^ a * y a b - 1 : ℤ)) : ℝ)|) ^ (-δ) := by
  obtain ⟨hH1, hHZ⟩ := H_bounds (a := a) ha hb
  set Z : ℝ := (2 : ℝ) ^ a * 3 ^ b with hZ
  have hZ0 : 0 < Z := by positivity
  have hZδ : 0 < Z ^ δ := Real.rpow_pos_of_pos hZ0 δ
  have h1 : 2 * |((y a b : ℤ) : ℝ)| / 3 ^ b ≤ Z ^ (-δ) := by
    rw [Real.rpow_neg hZ0.le, div_le_iff₀ (by positivity)]
    rw [← div_eq_inv_mul, le_div_iff₀ hZδ]
    exact hexc
  have h2 : Z ^ (-δ) ≤
      (max |(((2 ^ a * y a b : ℤ)) : ℝ)| |(((2 ^ a * y a b - 1 : ℤ)) : ℝ)|) ^ (-δ) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hHZ (by linarith)
  exact (subspaceProd_le ha hb).trans (h1.trans h2)

/-- A line through `v ≠ 0` meets `X − Y = 1` in at most one point, and there `|X| ≤ |v₁|`. -/
theorem abs_le_of_line {X : ℤ} {v : ℤ × ℤ} (hv : v ≠ (0, 0)) (h : X * v.2 = (X - 1) * v.1) :
    |X| ≤ |v.1| := by
  have h1 : X * (v.1 - v.2) = v.1 := by linear_combination (-1 : ℤ) * h
  by_cases hd : v.1 - v.2 = 0
  · exfalso
    apply hv
    rw [hd, mul_zero] at h1
    have e1 : v.1 = 0 := h1.symm
    have e2 : v.2 = 0 := by linarith
    exact Prod.ext e1 e2
  · have : 1 ≤ |v.1 - v.2| := Int.one_le_abs hd
    calc |X| = |X| * 1 := (mul_one _).symm
      _ ≤ |X| * |v.1 - v.2| := mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = |v.1| := by rw [← abs_mul, h1]

/-- **Finiteness of exceptional cells** from the Subspace instance. -/
theorem exc_finite {δ : ℝ} (hδ : 0 ≤ δ) (h : SubspaceInstance δ) : (Exc δ).Finite := by
  obtain ⟨F, hF⟩ := h
  set M : ℤ := ∑ v ∈ F, |v.1| with hM
  refine ((Set.finite_Iic M.toNat).prod (Set.finite_Iic (M.toNat + 1))).subset ?_
  rintro ⟨a, b⟩ ⟨ha, hb, hexc⟩
  simp only at ha hb hexc
  set X : ℤ := 2 ^ a * y a b with hX
  have hsol := subspace_ineq_of_exc hδ ha hb hexc
  have hy1 := one_le_abs_y (a := a) hb
  have h2a1 : (1 : ℤ) ≤ 2 ^ a := one_le_pow₀ (by norm_num)
  have hXabs : |X| = 2 ^ a * |y a b| := by rw [hX, abs_mul, abs_pow, abs_two]
  have h2a : (2 : ℤ) ^ a ≤ |X| := by rw [hXabs]; nlinarith
  have hne : (X, X - 1) ≠ (0, 0) := by
    intro h0
    have : X = 0 := congrArg Prod.fst h0
    rw [this, abs_zero] at h2a
    linarith
  obtain ⟨v, hvF, hv0, hline⟩ := hF X (X - 1) hne hsol
  have hXv := abs_le_of_line hv0 hline
  have hvM : |v.1| ≤ M := single_le_sum (f := fun w : ℤ × ℤ => |w.1|) (fun w _ => abs_nonneg _) hvF
  have hY0 : X - 1 ≠ 0 := Y_ne_zero ha
  have h3b : (3 : ℤ) ^ b ≤ |X - 1| :=
    Int.le_of_dvd (abs_pos.mpr hY0) ((dvd_abs _ _).mpr (three_pow_dvd a b))
  have hY1 : |X - 1| ≤ |X| + 1 := by
    calc |X - 1| ≤ |X| + |(1 : ℤ)| := abs_sub _ _
      _ = |X| + 1 := by rw [abs_one]
  have ha' : (a : ℤ) < 2 ^ a := by exact_mod_cast a.lt_two_pow_self
  have hb' : (b : ℤ) < 3 ^ b := by
    have h1 : b < 2 ^ b := b.lt_two_pow_self
    have h2 : 2 ^ b ≤ 3 ^ b := Nat.pow_le_pow_left (by norm_num) b
    exact_mod_cast lt_of_lt_of_le h1 h2
  have hA : (a : ℤ) ≤ M := by linarith
  have hB : (b : ℤ) ≤ M + 1 := by linarith
  simp only [Set.mem_prod, Set.mem_Iic]
  constructor <;> omega

/-! ## 3. Apex bound and sublinear maximal triangles -/

/-- `D(a,b) = a log 2 + b log 3 = log (2^a 3^b)`. -/
def D (a b : ℕ) : ℝ := a * Real.log 2 + b * Real.log 3

/-- Triangle size of a cell: `log (η 3^b / |y(a,b)|) = log (η / |U(a,b)|)`. -/
def size (η : ℝ) (a b : ℕ) : ℝ := Real.log (η * 3 ^ b / |((y a b : ℤ) : ℝ)|)

/-- Apex bound at level `δ` with constant `C`. -/
def ApexBound (η δ C : ℝ) : Prop := ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → size η a b ≤ δ * D a b + C

/-- **`SublinearMaxTriangle`**: for every `δ > 0`, `size ≤ δ (a log 2 + b log 3) + C_δ`
on `a, b ≥ 1`. -/
def SublinearMaxTriangle (η : ℝ) : Prop := ∀ δ > 0, ∃ C, ApexBound η δ C

theorem abs_y_pos {a b : ℕ} (hb : 1 ≤ b) : 0 < |((y a b : ℤ) : ℝ)| :=
  abs_pos.mpr (by exact_mod_cast y_ne_zero hb)

theorem size_eq {η : ℝ} (hη : 0 < η) {a b : ℕ} (hb : 1 ≤ b) :
    size η a b = Real.log η + b * Real.log 3 - Real.log |((y a b : ℤ) : ℝ)| := by
  unfold size
  rw [Real.log_div (by positivity) (abs_y_pos hb).ne', Real.log_mul hη.ne' (by positivity),
    Real.log_pow]

theorem log_Z (a b : ℕ) : Real.log ((2 : ℝ) ^ a * 3 ^ b) = D a b := by
  unfold D
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]

/-- **Finite exceptional set ⇒ apex bound.** -/
theorem apexBound_of_exc_finite {η δ : ℝ} (hη : 0 < η) (hE : (Exc δ).Finite) :
    ∃ C, ApexBound η δ C := by
  set f : ℕ × ℕ → ℝ := fun p => size η p.1 p.2 - δ * D p.1 p.2
  obtain ⟨M, hM⟩ := (hE.image f).bddAbove
  refine ⟨max (Real.log (2 * η)) M, fun a b ha hb => ?_⟩
  by_cases hmem : (a, b) ∈ Exc δ
  · have : f (a, b) ≤ M := hM ⟨(a, b), hmem, rfl⟩
    simp only [f] at this
    linarith [le_max_right (Real.log (2 * η)) M]
  · have hlt : (3 : ℝ) ^ b < 2 * |((y a b : ℤ) : ℝ)| * ((2 : ℝ) ^ a * 3 ^ b) ^ δ := by
      by_contra hc
      exact hmem ⟨ha, hb, not_lt.mp hc⟩
    have hy := abs_y_pos (a := a) hb
    have hZ : (0 : ℝ) < (2 : ℝ) ^ a * 3 ^ b := by positivity
    have hlog := Real.log_lt_log (by positivity) hlt
    rw [Real.log_pow, Real.log_mul (by positivity) (Real.rpow_pos_of_pos hZ δ).ne',
      Real.log_mul (by norm_num) hy.ne', Real.log_rpow hZ, log_Z] at hlog
    rw [size_eq hη hb]
    have h2η : Real.log (2 * η) = Real.log 2 + Real.log η := Real.log_mul (by norm_num) hη.ne'
    linarith [le_max_left (Real.log (2 * η)) M]

/-- **Subspace instance ⇒ `SublinearMaxTriangle`.** -/
theorem sublinearMaxTriangle_of_subspace {η : ℝ} (hη : 0 < η)
    (h : ∀ δ > 0, SubspaceInstance δ) : SublinearMaxTriangle η :=
  fun δ hδ => apexBound_of_exc_finite hη (exc_finite hδ.le (h δ hδ))

/-- `(a,b)` lies in the triangle generated at `(a+k, b+l)`. -/
def InTri (η : ℝ) (a b k l : ℕ) : Prop :=
  (2 : ℝ) ^ k * 3 ^ l * |((y (a + k) (b + l) : ℤ) : ℝ)| ≤ η * 3 ^ (b + l)

theorem D_add (a b k l : ℕ) :
    D (a + k) (b + l) = D a b + (k * Real.log 2 + l * Real.log 3) := by
  unfold D; push_cast; ring

theorem kl_nonneg (k l : ℕ) : 0 ≤ (k : ℝ) * Real.log 2 + l * Real.log 3 := by
  have h2 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  have h3 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)
  positivity

/-- **Apex size of any triangle through `(a,b)`**: `s* ≤ (δ D(a,b) + C)/(1 − δ)`. -/
theorem apex_size_le {η δ C : ℝ} (_hη : 0 < η) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hA : ApexBound η δ C) {a b k l : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (h : InTri η a b k l) :
    size η (a + k) (b + l) ≤ (δ * D a b + C) / (1 - δ) := by
  have hb' : 1 ≤ b + l := le_trans hb (Nat.le_add_right _ _)
  have hy := abs_y_pos (a := a + k) hb'
  have hkl : (k : ℝ) * Real.log 2 + l * Real.log 3 ≤ size η (a + k) (b + l) := by
    unfold size
    have h1 : (2 : ℝ) ^ k * 3 ^ l ≤ η * 3 ^ (b + l) / |((y (a + k) (b + l) : ℤ) : ℝ)| := by
      rw [le_div_iff₀ hy]; exact h
    have h2 := Real.log_le_log (by positivity) h1
    rwa [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at h2
  have hs := hA (a + k) (b + l) (le_trans ha (Nat.le_add_right _ _)) hb'
  rw [D_add] at hs
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-- **Depth bound** for the existing `inLargeTriangle`: `R ≤ δ D(a,b) + C` (`δ ≤ 1`). -/
theorem depth_le {η δ C R : ℝ} (_hη : 0 < η) (_hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hA : ApexBound η δ C)
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (h : inLargeTriangle a b η R) : R ≤ δ * D a b + C := by
  obtain ⟨k, l, hkl⟩ := h
  have hb' : 1 ≤ b + l := le_trans hb (Nat.le_add_right _ _)
  have hy := abs_y_pos (a := a + k) hb'
  have hkR : (k : ℝ) * Real.log 2 + l * Real.log 3 + R ≤ size η (a + k) (b + l) := by
    unfold size
    have h1 : (2 : ℝ) ^ k * 3 ^ l * Real.exp R ≤
        η * 3 ^ (b + l) / |((y (a + k) (b + l) : ℤ) : ℝ)| := by
      rw [le_div_iff₀ hy]
      have e : Real.exp R * Real.exp (-R) = 1 := by rw [← Real.exp_add]; simp
      have hE : 0 < Real.exp R := Real.exp_pos R
      calc (2 : ℝ) ^ k * 3 ^ l * Real.exp R * |((y (a + k) (b + l) : ℤ) : ℝ)|
          = Real.exp R * ((2 : ℝ) ^ k * 3 ^ l * |((y (a + k) (b + l) : ℤ) : ℝ)|) := by ring
        _ ≤ Real.exp R * (η * 3 ^ (b + l) * Real.exp (-R)) := mul_le_mul_of_nonneg_left hkl hE.le
        _ = η * 3 ^ (b + l) * (Real.exp R * Real.exp (-R)) := by ring
        _ = η * 3 ^ (b + l) := by rw [e, mul_one]
    have h2 := Real.log_le_log (by positivity) h1
    rwa [Real.log_mul (by positivity) (Real.exp_pos R).ne', Real.log_mul (by positivity)
      (by positivity), Real.log_pow, Real.log_pow, Real.log_exp] at h2
  have hs := hA (a + k) (b + l) (le_trans ha (Nat.le_add_right _ _)) hb'
  rw [D_add] at hs
  have hnn := kl_nonneg k l
  nlinarith

/-- `R_max(Ω) ≤ R₀`: every triangle meeting `Ω` has apex size `≤ R₀` (the apex is one of the
corners `(a+k, b+l)` with `InTri`). -/
def MaxTriangleLE (η : ℝ) (Ω : Set (ℕ × ℕ)) (R₀ : ℝ) : Prop :=
  ∀ p ∈ Ω, ∀ k l : ℕ, InTri η p.1 p.2 k l → size η (p.1 + k) (p.2 + l) ≤ R₀

/-- **`R_max = o(L)`** on any region with `a, b ≥ 1` and `a log 2 + b log 3 ≤ K L`. -/
theorem eventually_maxTriangleLE {η : ℝ} (hη : 0 < η) (h : SublinearMaxTriangle η) {K ε : ℝ}
    (hK : 0 < K) (hε : 0 < ε) :
    ∃ L₀ : ℝ, ∀ L ≥ L₀, ∀ Ω : Set (ℕ × ℕ),
      (∀ p ∈ Ω, 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ D p.1 p.2 ≤ K * L) → MaxTriangleLE η Ω (ε * L) := by
  set δ : ℝ := min (1 / 2) (ε / (4 * K)) with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
  have hδK : δ * K ≤ ε / 4 := by
    have : δ ≤ ε / (4 * K) := min_le_right _ _
    calc δ * K ≤ ε / (4 * K) * K := mul_le_mul_of_nonneg_right this hK.le
      _ = ε / 4 := by field_simp
  obtain ⟨C, hC⟩ := h δ hδ0
  refine ⟨4 * |C| / ε, fun L hL Ω hΩ p hp k l hkl => ?_⟩
  obtain ⟨ha, hb, hD⟩ := hΩ p hp
  have hL0 : 0 ≤ L := le_trans (by positivity) hL
  have hCL : 4 * |C| ≤ ε * L := by
    have := hL; rw [ge_iff_le, div_le_iff₀ hε] at this; linarith
  have h1 := apex_size_le hη hδ0.le (by linarith) hC ha hb hkl
  have hnum : δ * D p.1 p.2 + C ≤ ε / 4 * L + |C| := by
    have : δ * D p.1 p.2 ≤ δ * (K * L) := mul_le_mul_of_nonneg_left hD hδ0.le
    nlinarith [le_abs_self C]
  have hnum0 : 0 ≤ ε / 4 * L + |C| := by positivity
  calc size η (p.1 + k) (p.2 + l) ≤ (δ * D p.1 p.2 + C) / (1 - δ) := h1
    _ ≤ (ε / 4 * L + |C|) / (1 - δ) := div_le_div_of_nonneg_right hnum (by linarith)
    _ ≤ (ε / 4 * L + |C|) / (1 / 2) := div_le_div_of_nonneg_left hnum0 (by norm_num) (by linarith)
    _ ≤ ε * L := by rw [div_div_eq_mul_div, div_one]; linarith

/-- The corridor/path box `1 ≤ a ≤ m`, `1 ≤ b ≤ L`. -/
def box (m L : ℕ) : Set (ℕ × ℕ) := {p | 1 ≤ p.1 ∧ p.1 ≤ m ∧ 1 ≤ p.2 ∧ p.2 ≤ L}

/-- **Box form.** If `m ≤ c L` then `R_max(box m L) ≤ ε L` for `L ≥ L₀(ε)`. -/
theorem maxTriangleLE_box {η : ℝ} (hη : 0 < η) (h : SublinearMaxTriangle η) {c ε : ℝ}
    (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ L₀ : ℝ, ∀ m L : ℕ, L₀ ≤ L → (m : ℝ) ≤ c * L → MaxTriangleLE η (box m L) (ε * L) := by
  set K : ℝ := c * Real.log 2 + Real.log 3
  have h2 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hK : 0 < K := by positivity
  obtain ⟨L₀, hL₀⟩ := eventually_maxTriangleLE hη h hK hε
  refine ⟨L₀, fun m L hL hm => hL₀ L hL _ fun p hp => ⟨hp.1, hp.2.2.1, ?_⟩⟩
  obtain ⟨_, hpm, _, hpL⟩ := hp
  have e1 : (p.1 : ℝ) ≤ c * L := le_trans (by exact_mod_cast hpm) hm
  have e2 : (p.2 : ℝ) ≤ L := by exact_mod_cast hpL
  unfold D
  nlinarith

/-! ## 4. Good-block gaps ⇒ good-angle density ⇒ `LowFreqDecay` -/

/-- Every window of `G + 1` consecutive blocks (inside `[0,R)`) contains a good block. -/
def GoodGap {ι : Type*} (T : Finset ι) (good : ι → ℕ → Prop) (R G : ℕ) : Prop :=
  ∀ P ∈ T, ∀ r₀, r₀ + (G + 1) ≤ R → ∃ r, r₀ ≤ r ∧ r < r₀ + (G + 1) ∧ good P r

/-- **Gap ⇒ count.**  Gaps `≤ G` force at least `⌊R/(G+1)⌋` good blocks. -/
theorem card_good_ge (good : ℕ → Prop) [DecidablePred good] (R G : ℕ)
    (h : ∀ r₀, r₀ + (G + 1) ≤ R → ∃ r, r₀ ≤ r ∧ r < r₀ + (G + 1) ∧ good r) :
    R / (G + 1) ≤ ((range R).filter good).card := by
  have key : ∀ n, n * (G + 1) ≤ R → n ≤ ((range (n * (G + 1))).filter good).card := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      rw [Nat.succ_mul] at hn
      have hn' : n * (G + 1) ≤ R := by omega
      obtain ⟨r, hr1, hr2, hr⟩ := h (n * (G + 1)) hn
      have hsub : insert r ((range (n * (G + 1))).filter good) ⊆
          (range ((n + 1) * (G + 1))).filter good := by
        intro x hx
        rw [mem_insert] at hx
        rcases hx with rfl | hx
        · exact mem_filter.mpr ⟨mem_range.mpr (by rw [Nat.succ_mul]; omega), hr⟩
        · obtain ⟨hx1, hx2⟩ := mem_filter.mp hx
          have := mem_range.mp hx1
          exact mem_filter.mpr ⟨mem_range.mpr (by rw [Nat.succ_mul]; omega), hx2⟩
      have hnot : r ∉ (range (n * (G + 1))).filter good := by
        intro hx
        have := mem_range.mp (mem_filter.mp hx).1
        omega
      have h1 := card_le_card hsub
      rw [card_insert_of_notMem hnot] at h1
      have h2 := ih hn'
      omega
  have hq : R / (G + 1) * (G + 1) ≤ R := Nat.div_mul_le_self R (G + 1)
  have hmono : ((range (R / (G + 1) * (G + 1))).filter good).card ≤ ((range R).filter good).card :=
    card_le_card (filter_subset_filter _ (range_subset_range.mpr hq))
  exact le_trans (key _ hq) hmono

/-- **Gap ⇒ `PositiveDensityGoodAngles`** with `k = ⌊R/(G+1)⌋`, `ρ = 0`. -/
theorem positiveDensityGoodAngles_of_gap {ι : Type*} (T : Finset ι) (w : ι → ℝ) (W : ι → ℕ → ℝ)
    (good : ι → ℕ → Prop) [∀ P, DecidablePred (good P)] (R G : ℕ) {κ : ℝ}
    (hW : ∀ P ∈ T, ∀ r, 0 ≤ W P r ∧ W P r ≤ 1) (hgood : ∀ P ∈ T, ∀ r, good P r → W P r ≤ κ)
    (hgap : GoodGap T good R G) :
    GoodAngles.PositiveDensityGoodAngles T w W good R (R / (G + 1)) 0 κ := by
  refine ⟨hW, hgood, ?_⟩
  have hempty : T.filter (fun P => ((range R).filter (good P)).card < R / (G + 1)) = ∅ := by
    apply filter_eq_empty_iff.mpr
    intro P hP
    exact not_lt.mpr (card_good_ge (good P) R G (hgap P hP))
  rw [hempty, sum_empty, zero_mul]

variable (b : ℕ → ℕ)

/-- **Gap ⇒ `LowFreqDecay`** at rate `κ^{2⌊R/(G+1)⌋}`. -/
theorem lowFreqDecay_of_gap {κι : Type*} (j0 σ t U : ℕ) (T : Finset κι) (w : κι → ℝ)
    (W : ℕ → κι → ℕ → ℝ) (good : ℕ → κι → ℕ → Prop) [∀ lam c, DecidablePred (good lam c)]
    (R G : ℕ) {κ C γ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hw : ∀ c ∈ T, 0 ≤ w c)
    (hcube : GoodAngles.BlockCubeHyp b j0 σ t U T w W R)
    (hW : ∀ u ≤ U, ∀ lam ∈ cshell (σ + 1) t u, ∀ c ∈ T, ∀ r, 0 ≤ W lam c r ∧ W lam c r ≤ 1)
    (hgood : ∀ u ≤ U, ∀ lam ∈ cshell (σ + 1) t u, ∀ c ∈ T, ∀ r, good lam c r → W lam c r ≤ κ)
    (hgap : ∀ u ≤ U, ∀ lam ∈ cshell (σ + 1) t u, GoodGap T (good lam) R G)
    (hC0 : 0 ≤ C) (hrate : κ ^ (2 * (R / (G + 1))) ≤ C * (2 : ℝ) ^ (-(γ * j0))) :
    DecayInterface.LowFreqDecay b j0 σ t U C γ :=
  GoodAngles.lowFreqDecay_of_goodAngles b j0 σ t U T w W good R (R / (G + 1)) hκ0 hκ1 hw hcube
    (fun u hu lam hlam => positiveDensityGoodAngles_of_gap T w (W lam) (good lam) R G
      (hW u hu lam hlam) (hgood u hu lam hlam) (hgap u hu lam hlam))
    hC0 (by rw [add_zero]; exact hrate)

/-- **Triangle–gap bridge** (analytic/geometric input, NOT proved): if every triangle meeting
`Ω` has apex size `≤ R₀`, then good blocks have gaps `≤ G R₀` along every class.  Its proof would
need Tao's white-point contraction for the block factors and control of direct jumps between
distinct triangles (a step `(a,b) → (a−d, b+1)` between black cells of distinct triangles needs
`2^d η + 3η ≥ 1`, `merge_apex`). -/
def TriangleGapBridge (η : ℝ) (Ω : Set (ℕ × ℕ)) {ι : Type*} (T : Finset ι)
    (good : ι → ℕ → Prop) (R : ℕ) (G : ℝ → ℕ) : Prop :=
  ∀ R₀, MaxTriangleLE η Ω R₀ → GoodGap T good R (G R₀)

/-- **`SublinearMaxTriangle` + bridge ⇒ `LowFreqDecay`** at rate `κ^{2⌊R/(G(εL)+1)⌋}` for
`L ≥ L₀(ε)`.  With `G(R₀) ≈ R₀/log 3` this factor tends to `0` but at no computable rate. -/
theorem lowFreqDecay_of_sublinearMaxTriangle {η : ℝ} (hη : 0 < η) (hsub : SublinearMaxTriangle η)
    {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ L₀ : ℝ, ∀ m L : ℕ, L₀ ≤ L → (m : ℝ) ≤ c * L →
      ∀ {κι : Type*} (j0 σ t U : ℕ) (T : Finset κι) (w : κι → ℝ) (W : ℕ → κι → ℕ → ℝ)
        (good : ℕ → κι → ℕ → Prop) [∀ lam c, DecidablePred (good lam c)] (R : ℕ) (G : ℝ → ℕ)
        {κ C γ : ℝ}, 0 ≤ κ → κ ≤ 1 → (∀ c ∈ T, 0 ≤ w c) →
        GoodAngles.BlockCubeHyp b j0 σ t U T w W R →
        (∀ u ≤ U, ∀ lam ∈ cshell (σ + 1) t u, ∀ c ∈ T, ∀ r, 0 ≤ W lam c r ∧ W lam c r ≤ 1) →
        (∀ u ≤ U, ∀ lam ∈ cshell (σ + 1) t u, ∀ c ∈ T, ∀ r, good lam c r → W lam c r ≤ κ) →
        (∀ u ≤ U, ∀ lam ∈ cshell (σ + 1) t u, TriangleGapBridge η (box m L) T (good lam) R G) →
        0 ≤ C → κ ^ (2 * (R / (G (ε * L) + 1))) ≤ C * (2 : ℝ) ^ (-(γ * j0)) →
        DecayInterface.LowFreqDecay b j0 σ t U C γ := by
  obtain ⟨L₀, hL₀⟩ := maxTriangleLE_box hη hsub hc hε
  refine ⟨L₀, fun m L hL hm => ?_⟩
  intro κι j0 σ t U T w W good _ R G κ C γ hκ0 hκ1 hw hcube hW hgood hbridge hC0 hrate
  exact lowFreqDecay_of_gap b j0 σ t U T w W good R (G (ε * L)) hκ0 hκ1 hw hcube hW hgood
    (fun u hu lam hlam => hbridge u hu lam hlam (ε * L) (hL₀ m L hL hm)) hC0 hrate

end

end MaxTriangle
end EOC
