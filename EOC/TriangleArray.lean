import Mathlib

/-!
# The universal Tao triangle array

For `a b : ℕ` let `u a b = (2⁻¹)^a ∈ ZMod (3^b)` (the residue of `2^{-a}` modulo `3^b`) and let
`y a b : ℤ` be its centered representative (`ZMod.valMinAbs`, so `-3^b < 2 y ≤ 3^b`).
The Tao angle is `U(a,b) = y a b / 3^b`; moving `a ↦ a - 1` doubles it and `b ↦ b - 1` triples
it (modulo `1`).

Main results (exact integer statements):
* `cast_y`, `cast_two_pow_mul_y`: reduction of `y` modulo smaller powers of `3`;
* `y_succ_modEq`, `y_eq_two_mul` (horizontal doubling), `y_modEq_succ`, `y_eq_of_small` (vertical);
* `propagate`: a small apex value determines the whole triangle below/left of it,
  `y a b = 2^k * y (a+k) (b+l)` as soon as `2 · 2^k · |y (a+k) (b+l)| < 3^b`;
* `merge`, `merge_apex`: two black cells `(a+k, b)` and `(a, b+l)` with
  `|y a (b+l)| + 2^k |y (a+k) b| < 3^b` lie in one triangle with apex `(a+k, b+l)`;
* `black`, `inLargeTriangle`, `black_of_inLargeTriangle`.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC.TriangleArray

noncomputable section

instance neZero_three_pow (b : ℕ) : NeZero (3 ^ b) := ⟨pow_ne_zero _ (by norm_num)⟩

/-- `2^{-a}` in `ZMod (3^b)`. -/
def u (a b : ℕ) : ZMod (3 ^ b) := ((2 : ZMod (3 ^ b))⁻¹) ^ a

/-- Centered representative of `2^{-a} mod 3^b`. -/
def y (a b : ℕ) : ℤ := (u a b).valMinAbs

theorem two_mul_inv (b : ℕ) : (2 : ZMod (3 ^ b)) * (2 : ZMod (3 ^ b))⁻¹ = 1 := by
  have h := ZMod.coe_mul_inv_eq_one (n := 3 ^ b) 2 (Nat.Coprime.pow_right b (by norm_num))
  exact_mod_cast h

/-- `2^k · 2^{-(a+k)} = 2^{-a}`. -/
theorem two_pow_mul_u (a b k : ℕ) : (2 : ZMod (3 ^ b)) ^ k * u (a + k) b = u a b := by
  unfold u
  rw [pow_add, mul_left_comm, ← mul_pow, two_mul_inv, one_pow, mul_one]

theorem two_pow_mul_cancel {b k : ℕ} {x x' : ZMod (3 ^ b)}
    (h : (2 : ZMod (3 ^ b)) ^ k * x = 2 ^ k * x') : x = x' := by
  have hk : ((2 : ZMod (3 ^ b))⁻¹) ^ k * (2 : ZMod (3 ^ b)) ^ k = 1 := by
    rw [← mul_pow, mul_comm, two_mul_inv, one_pow]
  calc x = ((2 : ZMod (3 ^ b))⁻¹) ^ k * (2 ^ k * x) := by rw [← mul_assoc, hk, one_mul]
    _ = ((2 : ZMod (3 ^ b))⁻¹) ^ k * (2 ^ k * x') := by rw [h]
    _ = x' := by rw [← mul_assoc, hk, one_mul]

/-- The reduction map `ZMod (3^b') → ZMod (3^b)` sends `2⁻¹` to `2⁻¹`. -/
theorem castHom_inv_two {b b' : ℕ} (h : b ≤ b') :
    ZMod.castHom (pow_dvd_pow 3 h) (ZMod (3 ^ b)) ((2 : ZMod (3 ^ b'))⁻¹) =
      (2 : ZMod (3 ^ b))⁻¹ := by
  set φ := ZMod.castHom (pow_dvd_pow 3 h) (ZMod (3 ^ b))
  have h2 : (2 : ZMod (3 ^ b)) * φ ((2 : ZMod (3 ^ b'))⁻¹) = 1 := by
    have := congrArg φ (two_mul_inv b')
    rwa [map_mul, map_one, map_ofNat] at this
  have hc : (2 : ZMod (3 ^ b))⁻¹ * 2 = 1 := by rw [mul_comm, two_mul_inv]
  calc φ ((2 : ZMod (3 ^ b'))⁻¹) = ((2 : ZMod (3 ^ b))⁻¹ * 2) * φ ((2 : ZMod (3 ^ b'))⁻¹) := by
        rw [hc, one_mul]
    _ = (2 : ZMod (3 ^ b))⁻¹ := by rw [mul_assoc, h2, mul_one]

/-- Reduction: `y a b' ≡ 2^{-a} (mod 3^b)` for `b ≤ b'`. -/
theorem cast_y (a : ℕ) {b b' : ℕ} (h : b ≤ b') : ((y a b' : ℤ) : ZMod (3 ^ b)) = u a b := by
  set φ := ZMod.castHom (pow_dvd_pow 3 h) (ZMod (3 ^ b))
  have h1 : ((y a b' : ℤ) : ZMod (3 ^ b')) = u a b' := ZMod.coe_valMinAbs _
  have h2 := congrArg φ h1
  rw [map_intCast] at h2
  rw [h2]
  unfold u
  rw [map_pow, castHom_inv_two h]

theorem cast_two_pow_mul_y (a b k l : ℕ) :
    ((2 ^ k * y (a + k) (b + l) : ℤ) : ZMod (3 ^ b)) = u a b := by
  push_cast
  rw [cast_y (a + k) (Nat.le_add_right b l), two_pow_mul_u]

/-- **Triangle propagation.**  A small apex value determines every cell below/left of it. -/
theorem propagate (a b k l : ℕ) (h : 2 * (2 ^ k * |y (a + k) (b + l)|) < 3 ^ b) :
    y a b = 2 ^ k * y (a + k) (b + l) := by
  unfold y
  rw [ZMod.valMinAbs_spec]
  refine ⟨(cast_two_pow_mul_y a b k l).symm, ?_⟩
  have habs : |(2 : ℤ) ^ k * (u (a + k) (b + l)).valMinAbs * 2| < 3 ^ b := by
    rw [abs_mul, abs_mul, abs_pow, abs_two]
    unfold y at h
    linarith
  rw [abs_lt] at habs
  constructor
  · push_cast; linarith [habs.1]
  · push_cast; linarith [habs.2]

/-- Horizontal recurrence: `2 y(a+1,b) ≡ y(a,b) (mod 3^b)`. -/
theorem y_succ_modEq (a b : ℕ) : 2 * y (a + 1) b ≡ y a b [ZMOD 3 ^ b] := by
  have h1 := cast_two_pow_mul_y a b 1 0
  have h2 : ((y a b : ℤ) : ZMod (3 ^ b)) = u a b := cast_y a le_rfl
  rw [pow_one, Nat.add_zero] at h1
  have := (ZMod.intCast_eq_intCast_iff _ _ _).1 (h1.trans h2.symm)
  exact_mod_cast this

/-- Doubling inside the black region. -/
theorem y_eq_two_mul (a b : ℕ) (h : 4 * |y (a + 1) b| < 3 ^ b) : y a b = 2 * y (a + 1) b := by
  have h' : 2 * (2 ^ 1 * |y (a + 1) (b + 0)|) < (3 : ℤ) ^ b := by
    simp only [Nat.add_zero, pow_one]; linarith
  have := propagate a b 1 0 h'
  simpa using this

/-- Vertical recurrence: `y(a,b+1) ≡ y(a,b) (mod 3^b)`. -/
theorem y_modEq_succ (a b : ℕ) : y a (b + 1) ≡ y a b [ZMOD 3 ^ b] := by
  have h1 : ((y a (b + 1) : ℤ) : ZMod (3 ^ b)) = u a b := cast_y a (Nat.le_succ b)
  have h2 : ((y a b : ℤ) : ZMod (3 ^ b)) = u a b := cast_y a le_rfl
  have := (ZMod.intCast_eq_intCast_iff _ _ _).1 (h1.trans h2.symm)
  exact_mod_cast this

/-- Vertical tripling inside the black region: `U(a,b) = 3 U(a,b+1)` when small. -/
theorem y_eq_of_small (a b : ℕ) (h : 2 * |y a (b + 1)| < 3 ^ b) : y a b = y a (b + 1) := by
  have := propagate a b 0 1 (by simpa using h)
  simpa using this

/-- **Merge lemma.**  Cells `(a+k, b)` and `(a, b+l)` with small values are linked exactly. -/
theorem merge (a b k l : ℕ) (h : |y a (b + l)| + 2 ^ k * |y (a + k) b| < 3 ^ b) :
    y a (b + l) = 2 ^ k * y (a + k) b := by
  rw [← sub_eq_zero]
  refine Int.eq_zero_of_abs_lt_dvd (m := 3 ^ b) ?_ ?_
  · have e1 : ((y a (b + l) : ℤ) : ZMod (3 ^ b)) = u a b := cast_y a (Nat.le_add_right b l)
    have e2 := cast_two_pow_mul_y a b k 0
    rw [Nat.add_zero] at e2
    have : ((y a (b + l) - 2 ^ k * y (a + k) b : ℤ) : ZMod (3 ^ b)) = 0 := by
      rw [Int.cast_sub, e1, e2, sub_self]
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this
    exact_mod_cast this
  · calc |y a (b + l) - 2 ^ k * y (a + k) b| ≤ |y a (b + l)| + |2 ^ k * y (a + k) b| :=
          abs_sub _ _
      _ = |y a (b + l)| + 2 ^ k * |y (a + k) b| := by rw [abs_mul, abs_pow, abs_two]
      _ < 3 ^ b := h

/-- **Merge ⇒ common apex.**  Under the merge hypothesis the corner `(a+k, b+l)` carries the same
value as `(a+k, b)`, so both cells lie in the triangle with apex `(a+k, b+l)`. -/
theorem merge_apex (a b k l : ℕ) (h : |y a (b + l)| + 2 ^ k * |y (a + k) b| < 3 ^ b) :
    y (a + k) (b + l) = y (a + k) b := by
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · rfl
  have hm := merge a b k l h
  unfold y
  rw [ZMod.valMinAbs_spec]
  constructor
  · -- `2^k · y(a+k,b) = y(a,b+l) = 2^{-a} = 2^k · 2^{-(a+k)}` in `ZMod (3^{b+l})`; cancel `2^k`.
    apply two_pow_mul_cancel (k := k)
    have e1 : ((y a (b + l) : ℤ) : ZMod (3 ^ (b + l))) = u a (b + l) := cast_y a le_rfl
    rw [hm] at e1
    push_cast at e1
    rw [two_pow_mul_u]
    unfold y at e1
    exact e1.symm
  · have hb := (u (a + k) b).valMinAbs_mem_Ioc
    have h3 : (3 : ℤ) ^ b < 3 ^ (b + l) := pow_lt_pow_right₀ (by norm_num) (by omega)
    obtain ⟨hb1, hb2⟩ := hb
    push_cast at hb1 hb2 ⊢
    constructor <;> linarith

/-! ## Black cells and large triangles -/

/-- `(a,b)` is black at threshold `η`: `|U(a,b)| < η`. -/
def black (a b : ℕ) (η : ℝ) : Prop := |((y a b : ℤ) : ℝ)| < η * 3 ^ b

/-- `(a,b)` lies in a triangle of apex `(a+k, b+l)` at depth `≥ R`:
`2^k 3^l |y(a+k,b+l)| ≤ η 3^{b+l} e^{-R}`. -/
def inLargeTriangle (a b : ℕ) (η R : ℝ) : Prop :=
  ∃ k l : ℕ, (2 : ℝ) ^ k * 3 ^ l * |((y (a + k) (b + l) : ℤ) : ℝ)| ≤ η * 3 ^ (b + l) * Real.exp (-R)

/-- A cell deep inside a triangle is black, and its value is dictated by the apex. -/
theorem black_of_inLargeTriangle {a b : ℕ} {η R : ℝ} (hη : 0 < η) (hη4 : η ≤ 1 / 4) (hR : 0 < R)
    (h : inLargeTriangle a b η R) :
    ∃ k l : ℕ, y a b = 2 ^ k * y (a + k) (b + l) ∧ black a b η := by
  obtain ⟨k, l, hkl⟩ := h
  set Y : ℝ := |((y (a + k) (b + l) : ℤ) : ℝ)|
  have hE : Real.exp (-R) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hE0 : 0 < Real.exp (-R) := Real.exp_pos _
  have h3l : (0 : ℝ) < 3 ^ l := by positivity
  have h3b : (0 : ℝ) < 3 ^ b := by positivity
  have hdiv : (2 : ℝ) ^ k * Y ≤ η * 3 ^ b * Real.exp (-R) := by
    have h' : (3 : ℝ) ^ l * ((2 : ℝ) ^ k * Y) ≤ (3 : ℝ) ^ l * (η * 3 ^ b * Real.exp (-R)) := by
      rw [pow_add] at hkl; linarith [hkl]
    exact le_of_mul_le_mul_left h' h3l
  have hsmall : (2 : ℝ) ^ k * Y ≤ 3 ^ b / 4 := by
    have : η * 3 ^ b * Real.exp (-R) ≤ 3 ^ b / 4 := by
      have : η * 3 ^ b * Real.exp (-R) ≤ η * 3 ^ b := by
        have := mul_le_mul_of_nonneg_left hE.le (by positivity : 0 ≤ η * (3 : ℝ) ^ b)
        linarith
      nlinarith
    linarith
  have hprop : 2 * (2 ^ k * |y (a + k) (b + l)|) < (3 : ℤ) ^ b := by
    have hR' : (2 : ℝ) * ((2 : ℝ) ^ k * Y) < 3 ^ b := by linarith
    have : ((2 * (2 ^ k * |y (a + k) (b + l)|) : ℤ) : ℝ) < ((3 ^ b : ℤ) : ℝ) := by
      push_cast; simpa [Y] using hR'
    exact_mod_cast this
  have hy := propagate a b k l hprop
  refine ⟨k, l, hy, ?_⟩
  unfold black
  rw [hy]
  push_cast
  rw [abs_mul, abs_pow, abs_two]
  have : (2 : ℝ) ^ k * Y < η * 3 ^ b := by
    have := mul_lt_mul_of_pos_left hE (by positivity : 0 < η * (3 : ℝ) ^ b)
    linarith
  simpa [Y] using this

end

end EOC.TriangleArray

