import EOC.BlockCube

/-!
# The `L = 3` block: shape set, distinctness, phase factorization, complete-period orthogonality

Exact finite statements for the three-step block of the `WeightedFourier` path product.

* `shape a b = 3·2^a + 2^b`, `shapeSet u` = shapes with `0 ≤ a < b ≤ u − 2`.
* `shape_injective` — shapes are distinct (the bit pattern is `{a, a+1, b}` or `5·2^a`), so
  `card_shapeSet : |Q_u| = C(u−1, 2)`.
* `shape_lt` — `shape a b < 2^u`.
* `block_phase_nat`, `inv_three_step`, `block_phase_factor` — the three step phases
  `3^{-(i+1)}2^S + 3^{-(i+2)}2^{S₁} + 3^{-(i+3)}2^{S₂}` equal
  `3^{-(i+3)}(9·2^S + 2^{S+1}·shape(S₁−S−1, S₂−S−1))`: one angle per block.
* `sum_sq_norm_shapeSet` — **complete-period orthogonality**: for odd `c` and `u ≤ M`,
  `∑_{λ<2^M} ‖∑_{q∈Q_u} e(λ (c q mod 2^M)/2^M)‖^2 = 2^M |Q_u|`.
* `sum_Ico_periodic`, `sum_Ico_sq_norm_shapeSet` — a `p`-periodic function summed over any
  interval of length `k p` gives `k` full periods; hence the complete-period identity holds on
  every interval whose length is a multiple of `2^M` (the exact averaging step for
  complete-period blocks, `M_r ≤ L`).

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace ThreeBlock

open Finset SwapBound

/-! ## Shapes -/

/-- The internal shape of a 3-block: `3·2^a + 2^b`. -/
def shape (a b : ℕ) : ℕ := 3 * 2 ^ a + 2 ^ b

/-- Admissible internal pairs `0 ≤ a < b ≤ u − 2`. -/
def pairSet (u : ℕ) : Finset (ℕ × ℕ) :=
  (range u ×ˢ range u).filter (fun p => p.1 < p.2 ∧ p.2 ≤ u - 2)

/-- The shape set `Q_u`. -/
def shapeSet (u : ℕ) : Finset ℕ := (pairSet u).image (fun p => shape p.1 p.2)

theorem mem_pairSet {u : ℕ} {p : ℕ × ℕ} : p ∈ pairSet u ↔ p.1 < p.2 ∧ p.2 ≤ u - 2 ∧ 2 ≤ u := by
  simp only [pairSet, mem_filter, mem_product, mem_range]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; omega
  · rintro ⟨h1, h2, h3⟩; omega

/-- `shape a (a+k+1) = 2^a · (2(1 + 2^k) + 1)`: the 2-adic valuation is exactly `a`. -/
theorem shape_eq_odd (a k : ℕ) : shape a (a + k + 1) = 2 ^ a * (2 * (1 + 2 ^ k) + 1) := by
  unfold shape; rw [pow_add, pow_add]; ring

theorem two_pow_dvd_shape {a b : ℕ} (h : a < b) : 2 ^ a ∣ shape a b := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h
  rw [shape_eq_odd]; exact dvd_mul_right _ _

theorem not_two_pow_succ_dvd_shape {a b : ℕ} (h : a < b) : ¬ 2 ^ (a + 1) ∣ shape a b := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h
  rw [shape_eq_odd, pow_succ]
  intro hd
  have := Nat.dvd_of_mul_dvd_mul_left (by positivity : 0 < 2 ^ a) hd
  omega

/-- **Distinct shapes.** On pairs `a < b`, `(a, b) ↦ 3·2^a + 2^b` is injective. -/
theorem shape_injective {a b a' b' : ℕ} (h : a < b) (h' : a' < b')
    (he : shape a b = shape a' b') : a = a' ∧ b = b' := by
  have haa : a = a' := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · apply not_two_pow_succ_dvd_shape h
      rw [he]; exact (pow_dvd_pow 2 (by omega)).trans (two_pow_dvd_shape h')
    · apply not_two_pow_succ_dvd_shape h'
      rw [← he]; exact (pow_dvd_pow 2 (by omega)).trans (two_pow_dvd_shape h)
  subst haa
  refine ⟨rfl, ?_⟩
  unfold shape at he
  have hp : 2 ^ b = 2 ^ b' := by omega
  exact Nat.pow_right_injective le_rfl hp

theorem shape_injOn (u : ℕ) :
    Set.InjOn (fun p : ℕ × ℕ => shape p.1 p.2) ↑(pairSet u) := by
  rintro ⟨a, b⟩ hp ⟨a', b'⟩ hp' he
  have h1 := (mem_pairSet.mp hp).1
  have h2 := (mem_pairSet.mp hp').1
  obtain ⟨rfl, rfl⟩ := shape_injective h1 h2 he
  rfl

theorem card_shapeSet_eq_pairSet (u : ℕ) : (shapeSet u).card = (pairSet u).card :=
  card_image_of_injOn (shape_injOn u)

/-- The admissible pairs are the 2-subsets of `{0, …, u−2}`. -/
theorem card_pairSet (u : ℕ) : (pairSet u).card = (u - 1).choose 2 := by
  rw [← card_range (u - 1), ← card_powersetCard]
  refine card_bij (fun p _ => ({p.1, p.2} : Finset ℕ)) ?_ ?_ ?_
  · rintro ⟨a, b⟩ hp
    have := mem_pairSet.mp hp
    simp only [mem_powersetCard]
    refine ⟨?_, card_pair (by omega)⟩
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rw [mem_range]; omega
  · rintro ⟨a, b⟩ hp ⟨a', b'⟩ hp' he
    have h1 := mem_pairSet.mp hp
    have h2 := mem_pairSet.mp hp'
    have ha : a ∈ ({a', b'} : Finset ℕ) := he ▸ mem_insert_self _ _
    have hb : b ∈ ({a', b'} : Finset ℕ) := he ▸ mem_insert_of_mem (mem_singleton_self _)
    have ha' : a' ∈ ({a, b} : Finset ℕ) := he.symm ▸ mem_insert_self _ _
    have hb' : b' ∈ ({a, b} : Finset ℕ) := he.symm ▸ mem_insert_of_mem (mem_singleton_self _)
    simp only [mem_insert, mem_singleton] at ha hb ha' hb'
    simp only [Prod.mk.injEq]
    omega
  · intro s hs
    rw [mem_powersetCard] at hs
    obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hs.2
    have hx : x < u - 1 := mem_range.mp (hs.1 (mem_insert_self _ _))
    have hy : y < u - 1 := mem_range.mp (hs.1 (mem_insert_of_mem (mem_singleton_self _)))
    rcases Nat.lt_or_gt_of_ne hxy with hlt | hlt
    · exact ⟨(x, y), mem_pairSet.mpr ⟨hlt, by omega, by omega⟩, rfl⟩
    · exact ⟨(y, x), mem_pairSet.mpr ⟨hlt, by omega, by omega⟩, pair_comm _ _⟩

/-- **`|Q_u| = C(u−1, 2)`.** -/
theorem card_shapeSet (u : ℕ) : (shapeSet u).card = (u - 1).choose 2 := by
  rw [card_shapeSet_eq_pairSet, card_pairSet]

/-- Shapes fit in `u` bits. -/
theorem shape_lt {a b u : ℕ} (h : a < b) (hb : b ≤ u - 2) (hu : 2 ≤ u) : shape a b < 2 ^ u := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h
  rw [shape_eq_odd]
  have hpk : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  calc 2 ^ a * (2 * (1 + 2 ^ k) + 1) < 2 ^ a * (8 * 2 ^ k) :=
        Nat.mul_lt_mul_of_pos_left (by omega) (by positivity)
    _ = 2 ^ (a + 3 + k) := by rw [pow_add, pow_add]; ring
    _ ≤ 2 ^ u := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem lt_of_mem_shapeSet {u q : ℕ} (hq : q ∈ shapeSet u) : q < 2 ^ u := by
  obtain ⟨⟨a, b⟩, hp, rfl⟩ := mem_image.mp hq
  obtain ⟨h1, h2, h3⟩ := mem_pairSet.mp hp
  exact shape_lt h1 h2 h3

/-! ## Block phase factorization -/

/-- **Integer form.** For `S < S₁ < S₂`,
`9·2^S + 3·2^{S₁} + 2^{S₂} = 9·2^S + 2^{S+1} · shape(S₁−S−1, S₂−S−1)`. -/
theorem block_phase_nat {S S1 S2 : ℕ} (h1 : S < S1) (h2 : S1 < S2) :
    9 * 2 ^ S + 3 * 2 ^ S1 + 2 ^ S2 =
      9 * 2 ^ S + 2 ^ (S + 1) * shape (S1 - S - 1) (S2 - S - 1) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_lt h1
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_lt h2
  have ha : S + a + 1 - S - 1 = a := by omega
  have hb : S + a + 1 + b + 1 - S - 1 = a + 1 + b := by omega
  rw [ha, hb]
  unfold shape
  simp only [pow_add, pow_one]
  ring

/-- `3^{-(n+1)} = 9 · 3^{-(n+3)}` in any commutative ring where `3^{n+3}` is inverted by `v`. -/
theorem inv_three_step {R : Type*} [CommRing R] {v : R} {n : ℕ} (h : v * 3 ^ (n + 3) = 1) :
    (v * 9) * 3 ^ (n + 1) = 1 ∧ (v * 3) * 3 ^ (n + 2) = 1 := by
  constructor
  · rw [← h]; ring
  · rw [← h]; ring

/-- **One angle per block.** With `v = 3^{-(n+3)}`, the three step phases
`(9v)2^S + (3v)2^{S₁} + v 2^{S₂}` equal `v·(9·2^S + 2^{S+1}·shape(S₁−S−1, S₂−S−1))`. -/
theorem block_phase_factor {R : Type*} [CommRing R] (v : R) {S S1 S2 : ℕ} (h1 : S < S1)
    (h2 : S1 < S2) :
    (v * 9) * 2 ^ S + (v * 3) * 2 ^ S1 + v * 2 ^ S2 =
      v * ((9 * 2 ^ S + 2 ^ (S + 1) * shape (S1 - S - 1) (S2 - S - 1) : ℕ) : R) := by
  rw [← block_phase_nat h1 h2]
  push_cast
  ring

/-! ## Complete-period orthogonality -/

theorem mulMod_injOn {u M c : ℕ} (hu : u ≤ M) (hc : Odd c) :
    Set.InjOn (fun q => c * q % 2 ^ M) ↑(shapeSet u) := by
  intro q hq q' hq' he
  have hq1 : q < 2 ^ M := (lt_of_mem_shapeSet hq).trans_le (Nat.pow_le_pow_right (by norm_num) hu)
  have hq2 : q' < 2 ^ M :=
    (lt_of_mem_shapeSet hq').trans_le (Nat.pow_le_pow_right (by norm_num) hu)
  have hcop : Nat.Coprime (2 ^ M) c := Nat.Coprime.pow_left M (Nat.coprime_two_left.mpr hc)
  have hmod : q ≡ q' [MOD 2 ^ M] := Nat.ModEq.cancel_left_of_coprime hcop he
  rwa [Nat.ModEq, Nat.mod_eq_of_lt hq1, Nat.mod_eq_of_lt hq2] at hmod

/-- **Complete-period orthogonality.** For odd `c` (e.g. `c = 3^{-(n+3)} mod 2^M`) and
`u ≤ M`, the block polynomial of `Q_u` at angle `λ c / 2^M` has full-period mean square `|Q_u|`. -/
theorem sum_sq_norm_shapeSet {u M c : ℕ} (hu : u ≤ M) (hc : Odd c) :
    ∑ lam ∈ range (2 ^ M),
        ‖∑ q ∈ shapeSet u, ee ((lam : ℝ) * ((c * q % 2 ^ M : ℕ) : ℝ) / 2 ^ M)‖ ^ 2 =
      2 ^ M * ((shapeSet u).card : ℝ) :=
  BlockCube.sum_sq_norm_eq_of_injOn (shapeSet u) M (fun q => c * q % 2 ^ M)
    (fun _ _ => Nat.mod_lt _ (by positivity)) (mulMod_injOn hu hc)

/-! ## Periodic interval sums -/

theorem sum_range_shift_periodic (f : ℕ → ℝ) {p : ℕ} (hf : ∀ x, f (x + p) = f x) (a : ℕ) :
    ∑ k ∈ range p, f (a + k) = ∑ k ∈ range p, f k := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [← ih]
    have e1 := sum_range_succ (fun k => f (a + k)) p
    have e2 := sum_range_succ' (fun k => f (a + k)) p
    simp only [add_zero] at e2
    have hp : f (a + p) = f a := hf a
    have : ∑ k ∈ range p, f (a + (k + 1)) = ∑ k ∈ range p, f (a + k) := by linarith
    rw [← this]
    refine sum_congr rfl fun k _ => by congr 1; ring

/-- **Periodic interval sums.** A `p`-periodic function summed over any interval of length
`k p` gives `k` full periods. -/
theorem sum_Ico_periodic (f : ℕ → ℝ) {p : ℕ} (hf : ∀ x, f (x + p) = f x) (a k : ℕ) :
    ∑ x ∈ Ico a (a + k * p), f x = k * ∑ x ∈ range p, f x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← sum_Ico_consecutive f (show a ≤ a + k * p by omega)
      (show a + k * p ≤ a + (k + 1) * p by nlinarith), ih, sum_Ico_eq_sum_range,
      show a + (k + 1) * p - (a + k * p) = p by rw [add_mul, one_mul]; omega,
      sum_range_shift_periodic f hf]
    push_cast; ring

/-- The block mean square is `2^M`-periodic in `λ`. -/
theorem blockSq_periodic (T : Finset ℕ) (M : ℕ) (y : ℕ → ℕ) (x : ℕ) :
    ‖∑ q ∈ T, ee (((x + 2 ^ M : ℕ) : ℝ) * (y q : ℝ) / 2 ^ M)‖ ^ 2 =
      ‖∑ q ∈ T, ee ((x : ℝ) * (y q : ℝ) / 2 ^ M)‖ ^ 2 := by
  congr 2
  refine sum_congr rfl fun q _ => ?_
  have h2 : (2 : ℝ) ^ M ≠ 0 := by positivity
  have : ((x + 2 ^ M : ℕ) : ℝ) * (y q : ℝ) / 2 ^ M =
      (x : ℝ) * (y q : ℝ) / 2 ^ M + ((y q : ℤ) : ℝ) := by
    push_cast; field_simp
  rw [this, TwistExpansion.ee_add, TwistExpansion.ee_int, mul_one]

/-- **Exact averaging on complete-period blocks.** On every interval `[a, a + k·2^M)` the
block mean square of `Q_u` (odd multiplier `c`, `u ≤ M`) sums to `k · 2^M · |Q_u|`, i.e. its
average is exactly `|Q_u|` (normalized: `1/|Q_u|`). -/
theorem sum_Ico_sq_norm_shapeSet {u M c : ℕ} (hu : u ≤ M) (hc : Odd c) (a k : ℕ) :
    ∑ lam ∈ Ico a (a + k * 2 ^ M),
        ‖∑ q ∈ shapeSet u, ee ((lam : ℝ) * ((c * q % 2 ^ M : ℕ) : ℝ) / 2 ^ M)‖ ^ 2 =
      k * (2 ^ M * ((shapeSet u).card : ℝ)) := by
  rw [sum_Ico_periodic (fun lam : ℕ =>
      ‖∑ q ∈ shapeSet u, ee ((lam : ℝ) * ((c * q % 2 ^ M : ℕ) : ℝ) / 2 ^ M)‖ ^ 2)
    (fun x => blockSq_periodic (shapeSet u) M (fun q => c * q % 2 ^ M) x) a k,
    sum_sq_norm_shapeSet hu hc]

end ThreeBlock
end EOC
