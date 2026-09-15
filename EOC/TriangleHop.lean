import EOC.MaxTriangle

/-!
# Distinct-triangle hops, black-run decomposition, and what maximum control can give

Path cells are `(a i, b0 + i)` with `a (i+1) + d i = a i` (digit `d i` moves `a` left, `b` up
by one).

* **Jump threshold** (`sameTri_of_small_digit`, `black_distinct_imp_large_digit`,
  `distinct_hop_digit_ge_six`): consecutive black cells `(a'+d, b)`, `(a', b+1)` with
  `y(a', b+1) ≠ 2^d y(a'+d, b)` (distinct triangles, `sameTri_of_common_corner`) force
  `(2^d + 3) η > 1`; at `η = 1/54`, `d ≥ 6`, sharp (`distinct_hop_witness_d6`, kernel-checked).
* **Corner / chain** (`corner_eq`, `chain_value`): a linked chain of `r` steps starting at a black
  cell has a corner generator of the last cell of size `> r log 3`.
* **Run decomposition** (`run_decomposition`, `run_decomposition_54`): for every path of `n` steps,
  `n ≤ W + Occ + H₁ (2 + 2W + J)` where `W` = white cells, `J` = distinct-triangle hops (each with
  digit `≥ 6` at `η = 1/54`), `Occ` = black cells lying in a triangle of size `≥ R₁`,
  `H₁ = ⌊R₁ / log 3⌋ + 1`.
* **Fixed-fraction apexes** (`mem_exc_of_large`, `largeApexes_finite`): from `SubspaceInstance`, the
  set of apexes that are ever of size `≥ ε L` at scale `L` (region `a log 2 + b log 3 ≤ K L`) is
  finite.
* **Same row** (`sameRow_of_small_gap`): distinct black triangles in a row are `≥ 6` columns
  apart at `η = 1/54`.  **Max only** (`occ_eq_zero_of_maxTriangleLE`): `R_max ≤ R₀ < R₁`
  kills `Occ`.
* **Glue** (`positiveDensityGoodAngles_of_runBound`): run bound + large-jump LD + occupation bound
  (both hypotheses) ⇒ `PositiveDensityGoodAngles`.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace TriangleHop

open Finset TriangleArray MaxTriangle

noncomputable section

/-! ## 1. The distinct-triangle jump threshold -/

/-- Consecutive path cells `(a'+d, b)` and `(a', b+1)` carry linked values (same triangle). -/
def SameTri (a' b d : ℕ) : Prop := y a' (b + 1) = 2 ^ d * y (a' + d) b

/-- Both cells black, values not linked: a hop between distinct triangles. -/
def DistinctTriangleHop (η : ℝ) (a' b d : ℕ) : Prop :=
  black (a' + d) b η ∧ black a' (b + 1) η ∧ ¬ SameTri a' b d

/-- **Small digits keep the path in its triangle**: `(2^d + 3) η ≤ 1` and both cells black ⇒
linked. -/
theorem sameTri_of_small_digit {η : ℝ} {a' b d : ℕ} (h : ((2 : ℝ) ^ d + 3) * η ≤ 1)
    (h1 : black (a' + d) b η) (h2 : black a' (b + 1) η) : SameTri a' b d := by
  unfold SameTri
  apply merge a' b d 1
  unfold black at h1 h2
  have hb : (0 : ℝ) < 3 ^ b := by positivity
  have h2d : (0 : ℝ) < 2 ^ d := by positivity
  have key : |((y a' (b + 1) : ℤ) : ℝ)| + 2 ^ d * |((y (a' + d) b : ℤ) : ℝ)| < (3 : ℝ) ^ b := by
    have e : (3 : ℝ) ^ (b + 1) = 3 * 3 ^ b := by ring
    have h1' := mul_lt_mul_of_pos_left h1 h2d
    calc |((y a' (b + 1) : ℤ) : ℝ)| + 2 ^ d * |((y (a' + d) b : ℤ) : ℝ)|
        < η * 3 ^ (b + 1) + 2 ^ d * (η * 3 ^ b) := by linarith
      _ = ((2 : ℝ) ^ d + 3) * η * 3 ^ b := by rw [e]; ring
      _ ≤ 1 * 3 ^ b := mul_le_mul_of_nonneg_right h hb.le
      _ = 3 ^ b := one_mul _
  exact_mod_cast key

/-- **Long-jump lemma.** A hop between distinct black triangles forces `(2^d + 3) η > 1`. -/
theorem black_distinct_imp_large_digit {η : ℝ} {a' b d : ℕ} (h : DistinctTriangleHop η a' b d) :
    1 < ((2 : ℝ) ^ d + 3) * η := by
  obtain ⟨h1, h2, h3⟩ := h
  by_contra hc
  exact h3 (sameTri_of_small_digit (not_lt.mp hc) h1 h2)

/-- General threshold: `2^d > 1/η − 3`. -/
theorem distinct_hop_pow_gt {η : ℝ} (hη : 0 < η) {a' b d : ℕ} (h : DistinctTriangleHop η a' b d) :
    1 / η - 3 < (2 : ℝ) ^ d := by
  have h1 := black_distinct_imp_large_digit h
  have : 1 / η < (2 : ℝ) ^ d + 3 := by
    rw [div_lt_iff₀ hη]; linarith
  linarith

/-- **`η = 1/54`: distinct-triangle hops need `d ≥ 6`.** -/
theorem distinct_hop_digit_ge_six {a' b d : ℕ} (h : DistinctTriangleHop (1 / 54) a' b d) :
    6 ≤ d := by
  have h1 := black_distinct_imp_large_digit h
  by_contra hd
  have h32 : (2 : ℕ) ^ d ≤ 32 :=
    le_trans (Nat.pow_le_pow_right (by norm_num) (by omega : d ≤ 5)) (by norm_num)
  have h32' : (2 : ℝ) ^ d ≤ 32 := by exact_mod_cast h32
  linarith

/-- A common generator `(a'+d+k, b+1+l)` of both cells forces the linked relation. -/
theorem sameTri_of_common_corner {η : ℝ} (hη : 0 < η) (hη4 : η ≤ 1 / 4) {a' b d k l : ℕ}
    (h1 : InTri η (a' + d) b k (l + 1)) (h2 : InTri η a' (b + 1) (d + k) l) : SameTri a' b d := by
  have hsmall : ∀ {A B K : ℕ} (L : ℕ), InTri η A B K L →
      2 * (2 ^ K * |y (A + K) (B + L)|) < (3 : ℤ) ^ B := by
    intro A B K L hin
    unfold InTri at hin
    have h3 : (0 : ℝ) < 3 ^ L := by positivity
    have hle : (2 : ℝ) ^ K * |((y (A + K) (B + L) : ℤ) : ℝ)| ≤ η * 3 ^ B := by
      have : (3 : ℝ) ^ L * ((2 : ℝ) ^ K * |((y (A + K) (B + L) : ℤ) : ℝ)|) ≤
          (3 : ℝ) ^ L * (η * 3 ^ B) := by rw [pow_add] at hin; linarith
      exact le_of_mul_le_mul_left this h3
    have hB : (0 : ℝ) < 3 ^ B := by positivity
    have : (2 : ℝ) * ((2 : ℝ) ^ K * |((y (A + K) (B + L) : ℤ) : ℝ)|) < 3 ^ B := by nlinarith
    exact_mod_cast this
  have e1 := propagate (a' + d) b k (l + 1) (hsmall _ h1)
  have e2 := propagate a' (b + 1) (d + k) l (hsmall _ h2)
  have i1 : a' + (d + k) = a' + d + k := by omega
  have i2 : b + 1 + l = b + (l + 1) := by omega
  unfold SameTri
  rw [e2, e1, i1, i2, pow_add]
  ring

/-- **Same-row separation.** Two black cells `(a+k, b)`, `(a, b)` of one row with
`(2^k + 1) η ≤ 1` are linked (`y a b = 2^k y (a+k) b`); so distinct black triangles in a row at
`η = 1/54` are at least `6` columns apart. -/
theorem sameRow_of_small_gap {η : ℝ} {a b k : ℕ} (h : ((2 : ℝ) ^ k + 1) * η ≤ 1)
    (h1 : black (a + k) b η) (h2 : black a b η) : y a b = 2 ^ k * y (a + k) b := by
  have hm := merge a b k 0
  simp only [Nat.add_zero] at hm
  apply hm
  unfold black at h1 h2
  have hb : (0 : ℝ) < 3 ^ b := by positivity
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have key : |((y a b : ℤ) : ℝ)| + 2 ^ k * |((y (a + k) b : ℤ) : ℝ)| < (3 : ℝ) ^ b := by
    have h1' := mul_lt_mul_of_pos_left h1 h2k
    calc |((y a b : ℤ) : ℝ)| + 2 ^ k * |((y (a + k) b : ℤ) : ℝ)|
        < η * 3 ^ b + 2 ^ k * (η * 3 ^ b) := by linarith
      _ = ((2 : ℝ) ^ k + 1) * η * 3 ^ b := by ring
      _ ≤ 1 * 3 ^ b := mul_le_mul_of_nonneg_right h hb.le
      _ = 3 ^ b := one_mul _
  exact_mod_cast key

/-- `u a b = c` from `2^a c = 1` in `ZMod (3^b)`. -/
theorem u_eq_of {a b : ℕ} {c : ZMod (3 ^ b)} (h : (2 : ZMod (3 ^ b)) ^ a * c = 1) :
    u a b = c := by
  have h2 : ((2 : ZMod (3 ^ b))⁻¹) ^ a * (2 : ZMod (3 ^ b)) ^ a = 1 := by
    rw [← mul_pow, mul_comm, two_mul_inv, one_pow]
  calc u a b = u a b * ((2 : ZMod (3 ^ b)) ^ a * c) := by rw [h, mul_one]
    _ = ((2 : ZMod (3 ^ b))⁻¹ ^ a * (2 : ZMod (3 ^ b)) ^ a) * c := by unfold u; ring
    _ = c := by rw [h2, one_mul]

set_option maxRecDepth 20000 in
theorem y_160_5 : y 160 5 = 4 := by
  unfold y; rw [u_eq_of (c := 4) (by decide)]; decide

set_option maxRecDepth 20000 in
theorem y_154_6 : y 154 6 = 13 := by
  unfold y; rw [u_eq_of (c := 13) (by decide)]; decide

/-- **Sharpness at `η = 1/54`**: cells `(160, 5)` (`y = 4`) and `(154, 6)` (`y = 13`) are black,
lie in distinct triangles (`13 − 64·4 = −3^5`), and are joined by a digit `d = 6`. -/
theorem distinct_hop_witness_d6 : DistinctTriangleHop (1 / 54) 154 5 6 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold black; rw [show 154 + 6 = 160 by rfl, y_160_5]; norm_num
  · unfold black; rw [show 5 + 1 = 6 by rfl, y_154_6]; norm_num
  · unfold SameTri
    rw [show 5 + 1 = 6 by rfl, show 154 + 6 = 160 by rfl, y_160_5, y_154_6]; norm_num

/-! ## 2. Corner and chain lemmas -/

/-- **Corner lemma.** `y a (b+r) = 2^k y (a+k) b` ⇒ the corner `(a+k, b+r)` carries
`y (a+k) b`. -/
theorem corner_eq {a b k r : ℕ} (h : y a (b + r) = 2 ^ k * y (a + k) b) :
    y (a + k) (b + r) = y (a + k) b := by
  have hb := (u (a + k) b).valMinAbs_mem_Ioc
  have e0 : (u (a + k) b).valMinAbs = y (a + k) b := rfl
  have h3 : (3 : ℤ) ^ b ≤ 3 ^ (b + r) := pow_le_pow_right₀ (by norm_num) (by omega)
  unfold y
  rw [ZMod.valMinAbs_spec]
  constructor
  · apply two_pow_mul_cancel (k := k)
    have e1 : ((y a (b + r) : ℤ) : ZMod (3 ^ (b + r))) = u a (b + r) := cast_y a le_rfl
    rw [h] at e1
    push_cast at e1
    rw [two_pow_mul_u]
    unfold y at e1
    exact e1.symm
  · obtain ⟨hb1, hb2⟩ := hb
    push_cast at hb1 hb2 ⊢
    constructor <;> linarith

/-- `Link i`: cells `i` and `i+1` of the path carry linked values. -/
def Link (a d : ℕ → ℕ) (b0 i : ℕ) : Prop := y (a (i + 1)) (b0 + i + 1) = 2 ^ d i * y (a i) (b0 + i)

theorem link_iff_sameTri (a d : ℕ → ℕ) (ha : ∀ i, a (i + 1) + d i = a i) (b0 i : ℕ) :
    Link a d b0 i ↔ SameTri (a (i + 1)) (b0 + i) (d i) := by
  unfold Link SameTri; rw [ha i]

/-- **Chain lemma.** Links on `[s, s+r)` ⇒ `y(cell (s+r)) = 2^{a s − a (s+r)} y(cell s)`. -/
theorem chain_value (a d : ℕ → ℕ) (b0 s : ℕ) (ha : ∀ i, a (i + 1) + d i = a i) :
    ∀ r, (∀ i, s ≤ i → i < s + r → Link a d b0 i) →
      a (s + r) ≤ a s ∧
        y (a (s + r)) (b0 + (s + r)) = 2 ^ (a s - a (s + r)) * y (a s) (b0 + s) := by
  intro r
  induction r with
  | zero => intro _; simp
  | succ r ih =>
    intro hl
    obtain ⟨hle, hv⟩ := ih (fun i h1 h2 => hl i h1 (by omega))
    have hL := hl (s + r) (by omega) (by omega)
    unfold Link at hL
    have har := ha (s + r)
    have e1 : s + (r + 1) = s + r + 1 := by omega
    have e2 : b0 + (s + r) + 1 = b0 + (s + r + 1) := by omega
    rw [e2] at hL
    refine ⟨by rw [e1]; omega, ?_⟩
    rw [e1, hL, hv, ← mul_assoc, ← pow_add]
    congr 2
    omega

theorem size_pos_of_black {η : ℝ} (_hη : 0 < η) {a b : ℕ} (hb : 1 ≤ b) (h : black a b η) :
    0 < size η a b := by
  unfold size
  apply Real.log_pos
  have hy := abs_y_pos (a := a) hb
  rw [one_lt_div hy]
  unfold black at h
  linarith

/-- Size of a vertical translate of a cell with the same value. -/
theorem size_up {η : ℝ} (hη : 0 < η) {a b r : ℕ} (hb : 1 ≤ b) (h : y a (b + r) = y a b) :
    size η a (b + r) = size η a b + r * Real.log 3 := by
  have hy := abs_y_pos (a := a) hb
  unfold size
  rw [h, Real.log_div (by positivity) hy.ne', Real.log_div (by positivity) hy.ne',
    Real.log_mul hη.ne' (by positivity), Real.log_mul hη.ne' (by positivity), Real.log_pow,
    Real.log_pow]
  push_cast; ring

/-! ## 3. Run decomposition -/

section Runs

variable (η : ℝ) (a d : ℕ → ℕ) (b0 : ℕ)

open Classical

/-- Cell `i` is black. -/
def Blk (i : ℕ) : Prop := black (a i) (b0 + i) η

/-- Cell `i` lies in a triangle (some generator) of size `≥ R₁`. -/
def InBig (R₁ : ℝ) (i : ℕ) : Prop :=
  ∃ k l : ℕ, InTri η (a i) (b0 + i) k l ∧ R₁ ≤ size η (a i + k) (b0 + i + l)

/-- A black cell that does not lie in a triangle of size `≥ R₁` is within `H₁ − 1` steps of the
start of its linked run. -/
theorem run_offset_lt {R₁ : ℝ} (hη : 0 < η) (hb0 : 1 ≤ b0) (ha : ∀ i, a (i + 1) + d i = a i)
    {s j : ℕ} (hsj : s ≤ j) (hchain : ∀ i, s ≤ i → i < j → Blk η a b0 i ∧ Link a d b0 i)
    (hs : Blk η a b0 s) (hj : Blk η a b0 j) (hbig : ¬ InBig η a b0 R₁ j) :
    j - s < ⌊R₁ / Real.log 3⌋₊ + 1 := by
  obtain ⟨hle, hv⟩ := chain_value a d b0 s ha (j - s)
    (fun i h1 h2 => (hchain i h1 (by omega)).2)
  have ej : s + (j - s) = j := by omega
  rw [ej] at hle hv
  set k := a s - a j with hk
  have hak : a j + k = a s := by omega
  -- the corner `(a s, b0 + j)` carries `y (a s) (b0 + s)`
  have hc : y (a j + k) ((b0 + s) + (j - s)) = y (a j + k) (b0 + s) := by
    apply corner_eq
    rw [hak]
    have : b0 + s + (j - s) = b0 + j := by omega
    rw [this]; exact hv
  rw [hak] at hc
  have ebj : b0 + s + (j - s) = b0 + j := by omega
  rw [ebj] at hc
  -- the corner generates cell `j`
  have hin : InTri η (a j) (b0 + j) k 0 := by
    unfold InTri
    rw [hak, Nat.add_zero, pow_zero, mul_one, hc]
    have hv' : |((y (a j) (b0 + j) : ℤ) : ℝ)| = 2 ^ k * |((y (a s) (b0 + s) : ℤ) : ℝ)| := by
      rw [hv]; push_cast; rw [abs_mul, abs_pow, abs_two]
    unfold Blk black at hj
    rw [← hv']; exact hj.le
  have hsz : size η (a s) (b0 + j) < R₁ := by
    by_contra hc'
    exact hbig ⟨k, 0, hin, by rw [hak, Nat.add_zero]; exact not_lt.mp hc'⟩
  have hup : size η (a s) (b0 + j) = size η (a s) (b0 + s) + (j - s : ℕ) * Real.log 3 := by
    have := size_up hη (a := a s) (b := b0 + s) (r := j - s) (by omega) (by rw [ebj]; exact hc)
    rwa [ebj] at this
  have hpos := size_pos_of_black hη (a := a s) (b := b0 + s) (by omega) hs
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlt : ((j - s : ℕ) : ℝ) * Real.log 3 < R₁ := by linarith
  have hfl : R₁ / Real.log 3 < (⌊R₁ / Real.log 3⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have : ((j - s : ℕ) : ℝ) < ⌊R₁ / Real.log 3⌋₊ + 1 := by
    have : ((j - s : ℕ) : ℝ) < R₁ / Real.log 3 := by rw [lt_div_iff₀ h3]; exact hlt
    linarith
  exact_mod_cast this

/-- **Run decomposition.** For a path of `n` steps (`b0 ≥ 1`):
`n ≤ W + Occ + H₁ · (1 + W + W' + J)`, where `W = #white`, `W' = #{i : cell i+1 white}`,
`J = #{i : cells i, i+1 black and not linked}`, `Occ = #{black cells in a triangle of size ≥ R₁}`,
`H₁ = ⌊R₁/log 3⌋ + 1`. -/
theorem run_decomposition {R₁ : ℝ} (hη : 0 < η) (hb0 : 1 ≤ b0) (ha : ∀ i, a (i + 1) + d i = a i)
    (n : ℕ) :
    n ≤ ((range n).filter (fun i => ¬ Blk η a b0 i)).card +
      ((range n).filter (fun i => Blk η a b0 i ∧ InBig η a b0 R₁ i)).card +
      (⌊R₁ / Real.log 3⌋₊ + 1) * (1 + ((range n).filter (fun i => ¬ Blk η a b0 i)).card +
        ((range n).filter (fun i => ¬ Blk η a b0 (i + 1))).card +
        ((range n).filter
          (fun i => Blk η a b0 i ∧ Blk η a b0 (i + 1) ∧ ¬ Link a d b0 i)).card) := by
  classical
  set H := ⌊R₁ / Real.log 3⌋₊ + 1 with hH
  set blk : ℕ → Prop := Blk η a b0
  set brk : ℕ → Prop := fun i => ¬ (blk i ∧ Link a d b0 i)
  set starts := (range n).filter (fun i => blk i ∧ (i = 0 ∨ brk (i - 1)))
  -- (A) black cells outside big triangles inject into starts × range H
  have hA : ((range n).filter (fun i => blk i ∧ ¬ InBig η a b0 R₁ i)).card ≤ starts.card * H := by
    have hex : ∀ j, ∃ s, s ≤ j ∧ ∀ i, s ≤ i → i < j → blk i ∧ Link a d b0 i :=
      fun j => ⟨j, le_rfl, fun i h1 h2 => absurd h2 (by omega)⟩
    let st : ℕ → ℕ := fun j => Nat.find (hex j)
    have st_spec : ∀ j, st j ≤ j ∧ ∀ i, st j ≤ i → i < j → blk i ∧ Link a d b0 i :=
      fun j => Nat.find_spec (hex j)
    rw [← card_range H, ← card_product]
    apply card_le_card_of_injOn (fun j => (st j, j - st j))
    · intro j hj
      obtain ⟨hjn, hjb, hjbig⟩ := mem_filter.mp (mem_coe.mp hj)
      obtain ⟨hle, hch⟩ := st_spec j
      have hsb : blk (st j) := by
        rcases Nat.lt_or_ge (st j) j with h | h
        · exact (hch (st j) le_rfl h).1
        · have : st j = j := le_antisymm hle h
          rw [this]; exact hjb
      refine mem_coe.mpr (mem_product.mpr ⟨mem_filter.mpr ⟨mem_range.mpr
        (by have := mem_range.mp hjn; exact (by omega : st j < n)), hsb, ?_⟩,
        mem_range.mpr (run_offset_lt η a d b0 hη hb0 ha hle hch hsb hjb hjbig)⟩)
      by_cases h0 : st j = 0
      · exact Or.inl h0
      · right
        have hmin := Nat.find_min (hex j) (show st j - 1 < st j by omega)
        push Not at hmin
        obtain ⟨i, hi1, hi2, hi3⟩ := hmin (by omega)
        have hi : i = st j - 1 := by
          by_contra hne
          exact hi3 (hch i (by omega) hi2).1 (hch i (by omega) hi2).2
        rw [← hi]; exact fun h => hi3 h.1 h.2
    · intro j1 _ j2 _ heq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨e1, e2⟩ := heq
      have h1 := (st_spec j1).1
      have h2 := (st_spec j2).1
      omega
  -- (B) starts ⊆ {0} ∪ (brk + 1)
  have hB : starts.card ≤ 1 + ((range n).filter brk).card := by
    have hsub : starts ⊆ insert 0 (((range n).filter brk).image (· + 1)) := by
      intro i hi
      rw [mem_filter] at hi
      obtain ⟨hin, _, h0⟩ := hi
      rcases h0 with h0 | h0
      · rw [h0]; exact mem_insert_self _ _
      · by_cases hi0 : i = 0
        · rw [hi0]; exact mem_insert_self _ _
        · apply mem_insert_of_mem
          rw [mem_image]
          exact ⟨i - 1, mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hin; omega), h0⟩,
            by omega⟩
    calc starts.card ≤ (insert 0 (((range n).filter brk).image (· + 1))).card := card_le_card hsub
      _ ≤ (((range n).filter brk).image (· + 1)).card + 1 := card_insert_le _ _
      _ ≤ ((range n).filter brk).card + 1 := Nat.add_le_add_right card_image_le 1
      _ = 1 + ((range n).filter brk).card := by ring
  -- (C) breaks are whites, whites-next, or hops
  have hC : ((range n).filter brk).card ≤ ((range n).filter (fun i => ¬ blk i)).card +
      ((range n).filter (fun i => ¬ blk (i + 1))).card +
      ((range n).filter (fun i => blk i ∧ blk (i + 1) ∧ ¬ Link a d b0 i)).card := by
    have hsub : (range n).filter brk ⊆ ((range n).filter (fun i => ¬ blk i) ∪
        (range n).filter (fun i => ¬ blk (i + 1))) ∪
        (range n).filter (fun i => blk i ∧ blk (i + 1) ∧ ¬ Link a d b0 i) := by
      intro i hi
      rw [mem_filter] at hi
      obtain ⟨hin, hbr⟩ := hi
      simp only [mem_union, mem_filter]
      by_cases h1 : blk i
      · by_cases h2 : blk (i + 1)
        · right; exact ⟨hin, h1, h2, fun hl => hbr ⟨h1, hl⟩⟩
        · left; right; exact ⟨hin, h2⟩
      · left; left; exact ⟨hin, h1⟩
    calc ((range n).filter brk).card ≤ _ := card_le_card hsub
      _ ≤ _ := card_union_le _ _
      _ ≤ _ := Nat.add_le_add_right (card_union_le _ _) _
  -- (D) split `n` into whites, big-black, other black
  have hn : n = ((range n).filter (fun i => ¬ blk i)).card +
      ((range n).filter (fun i => blk i ∧ InBig η a b0 R₁ i)).card +
      ((range n).filter (fun i => blk i ∧ ¬ InBig η a b0 R₁ i)).card := by
    have e1 := card_filter_add_card_filter_not (s := range n) (fun i => blk i)
    have e2 := card_filter_add_card_filter_not (s := (range n).filter (fun i => blk i))
      (fun i => InBig η a b0 R₁ i)
    rw [filter_filter, filter_filter] at e2
    rw [card_range] at e1
    omega
  have hfin : ((range n).filter (fun i => blk i ∧ ¬ InBig η a b0 R₁ i)).card ≤
      H * (1 + ((range n).filter (fun i => ¬ blk i)).card +
        ((range n).filter (fun i => ¬ blk (i + 1))).card +
        ((range n).filter (fun i => blk i ∧ blk (i + 1) ∧ ¬ Link a d b0 i)).card) := by
    calc _ ≤ starts.card * H := hA
      _ ≤ (1 + ((range n).filter brk).card) * H := Nat.mul_le_mul_right H hB
      _ ≤ _ := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left H (by omega)
  omega

/-- `W' ≤ W + 1`. -/
theorem card_white_next_le (n : ℕ) :
    ((range n).filter (fun i => ¬ Blk η a b0 (i + 1))).card ≤
      ((range n).filter (fun i => ¬ Blk η a b0 i)).card + 1 := by
  classical
  have hsub : ((range n).filter (fun i => ¬ Blk η a b0 (i + 1))).image (· + 1) ⊆
      insert n ((range n).filter (fun i => ¬ Blk η a b0 i)) := by
    intro x hx
    rw [mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [mem_filter] at hi
    by_cases h : i + 1 = n
    · rw [h]; exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hi.1; omega),
        hi.2⟩)
  have hinj : (((range n).filter (fun i => ¬ Blk η a b0 (i + 1))).image (· + 1)).card =
      ((range n).filter (fun i => ¬ Blk η a b0 (i + 1))).card :=
    card_image_of_injective _ (fun x y h => by simpa using h)
  calc _ = _ := hinj.symm
    _ ≤ _ := card_le_card hsub
    _ ≤ _ := card_insert_le _ _

/-- **Run decomposition at `η = 1/54`**, with hops counted by digits `≥ 6`:
`n ≤ (2H₁+1) W + Occ + H₁ N₆ + 2H₁`. -/
theorem run_decomposition_54 {R₁ : ℝ} (hb0 : 1 ≤ b0) (ha : ∀ i, a (i + 1) + d i = a i) (n : ℕ) :
    n ≤ (2 * (⌊R₁ / Real.log 3⌋₊ + 1) + 1) *
        ((range n).filter (fun i => ¬ Blk (1 / 54) a b0 i)).card +
      ((range n).filter (fun i => Blk (1 / 54) a b0 i ∧ InBig (1 / 54) a b0 R₁ i)).card +
      (⌊R₁ / Real.log 3⌋₊ + 1) * ((range n).filter (fun i => 6 ≤ d i)).card +
      2 * (⌊R₁ / Real.log 3⌋₊ + 1) := by
  classical
  have h1 := run_decomposition (1 / 54) a d b0 (R₁ := R₁) (by norm_num) hb0 ha n
  have h2 := card_white_next_le (1 / 54) a b0 n
  have h3 : ((range n).filter (fun i => Blk (1 / 54) a b0 i ∧ Blk (1 / 54) a b0 (i + 1) ∧
      ¬ Link a d b0 i)).card ≤ ((range n).filter (fun i => 6 ≤ d i)).card := by
    apply card_le_card
    intro i hi
    rw [mem_filter] at hi ⊢
    obtain ⟨hin, hb1, hb2, hl⟩ := hi
    refine ⟨hin, distinct_hop_digit_ge_six (a' := a (i + 1)) (b := b0 + i) ⟨?_, ?_, ?_⟩⟩
    · unfold Blk at hb1; rw [ha i]; exact hb1
    · unfold Blk at hb2; rw [show b0 + i + 1 = b0 + (i + 1) by omega]; exact hb2
    · rw [← link_iff_sameTri a d ha]; exact hl
  set H := ⌊R₁ / Real.log 3⌋₊ + 1
  have := Nat.mul_le_mul_left H (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left
    (le_refl ((range n).filter (fun i => ¬ Blk (1 / 54) a b0 i)).card) 1) h2) h3)
  nlinarith

/-- Under `R_max(Ω) ≤ R₀ < R₁` (all path cells in `Ω`) no black cell lies in a triangle of size
`≥ R₁`: the occupation term of the run decomposition vanishes. -/
theorem occ_eq_zero_of_maxTriangleLE {Ω : Set (ℕ × ℕ)} {R₀ R₁ : ℝ} (hR : R₀ < R₁)
    (hmax : MaxTriangleLE η Ω R₀) (n : ℕ) (hΩ : ∀ i < n, (a i, b0 + i) ∈ Ω) :
    ((range n).filter (fun i => Blk η a b0 i ∧ InBig η a b0 R₁ i)).card = 0 := by
  rw [card_eq_zero, filter_eq_empty_iff]
  rintro i hi ⟨_, k, l, hin, hbig⟩
  have := hmax (a i, b0 + i) (hΩ i (mem_range.mp hi)) k l hin
  simp only at this
  linarith

end Runs

/-! ## 4. Fixed-fraction large apexes are finitely many (from `SubspaceInstance`) -/

/-- An apex of size `≥ 2δKL` over a cell with `D ≤ K L` is `δ`-exceptional (`δ ≤ 1/2`,
`η ≤ 1/2`). -/
theorem mem_exc_of_large {η δ K L : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1 / 2)
    {a b k l : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hD : D a b ≤ K * L) (hin : InTri η a b k l)
    (hbig : 2 * δ * (K * L) ≤ size η (a + k) (b + l)) : (a + k, b + l) ∈ Exc δ := by
  have hb' : 1 ≤ b + l := le_trans hb (Nat.le_add_right _ _)
  have hy := abs_y_pos (a := a + k) hb'
  set s := size η (a + k) (b + l) with hs
  have hkl : (k : ℝ) * Real.log 2 + l * Real.log 3 ≤ s := by
    unfold InTri at hin
    have h1 : (2 : ℝ) ^ k * 3 ^ l ≤ η * 3 ^ (b + l) / |((y (a + k) (b + l) : ℤ) : ℝ)| := by
      rw [le_div_iff₀ hy]; exact hin
    have h2 := Real.log_le_log (by positivity) h1
    rwa [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at h2
  have hnn := kl_nonneg k l
  have hDs : δ * D (a + k) (b + l) ≤ s := by
    rw [D_add]; nlinarith
  have hlog2η : Real.log (2 * η) ≤ 0 := Real.log_nonpos (by positivity) (by linarith)
  refine ⟨le_trans ha (Nat.le_add_right _ _), hb', ?_⟩
  simp only
  have hZ : (0 : ℝ) < (2 : ℝ) ^ (a + k) * 3 ^ (b + l) := by positivity
  rw [← Real.log_le_log_iff (by positivity) (by positivity)]
  rw [Real.log_mul (by positivity) (Real.rpow_pos_of_pos hZ δ).ne',
    Real.log_mul (by norm_num) hy.ne',
    Real.log_rpow hZ, log_Z, Real.log_pow]
  have hse := size_eq hη (a := a + k) hb'
  rw [← hs] at hse
  have h2η : Real.log (2 * η) = Real.log 2 + Real.log η := Real.log_mul (by norm_num) hη.ne'
  push_cast at hse ⊢
  linarith

/-- Apexes that are ever `ε`-large at their scale `L` (over a cell with `D ≤ K L`). -/
def LargeApexes (η K ε : ℝ) : Set (ℕ × ℕ) :=
  {q | ∃ L : ℝ, ∃ a b k l : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ D a b ≤ K * L ∧ InTri η a b k l ∧
      q = (a + k, b + l) ∧ ε * L ≤ size η (a + k) (b + l)}

/-- **Fixed-fraction large triangles are finitely many, uniformly in `L`** (from the Subspace
instance at `δ = min (1/2) (ε/(2K))`).  (`R_max = o(L)` already forces none for `L ≥ L₀(ε)`; with a
quantitative Subspace Theorem this finite set has an explicit cardinality bound.) -/
theorem largeApexes_finite {η K ε : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2) (hK : 0 < K) (hε : 0 < ε)
    (h : SubspaceInstance (min (1 / 2) (ε / (2 * K)))) : (LargeApexes η K ε).Finite := by
  set δ := min (1 / 2) (ε / (2 * K)) with hδ
  have hδ0 : 0 ≤ δ := le_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
  have hδε : δ ≤ ε / (2 * K) := min_le_right _ _
  refine (exc_finite hδ0 h).subset ?_
  rintro q ⟨L, a, b, k, l, ha, hb, hD, hin, rfl, hbig⟩
  have hD0 : 0 ≤ D a b := kl_nonneg a b
  have hKL : 0 ≤ K * L := le_trans hD0 hD
  have h2 : 2 * δ * (K * L) ≤ ε * L := by
    have : 2 * δ ≤ ε / K := by
      have := mul_le_mul_of_nonneg_left hδε (by norm_num : (0 : ℝ) ≤ 2)
      calc 2 * δ ≤ 2 * (ε / (2 * K)) := this
        _ = ε / K := by field_simp
    calc 2 * δ * (K * L) ≤ ε / K * (K * L) := mul_le_mul_of_nonneg_right this hKL
      _ = ε * L := by field_simp
  exact mem_exc_of_large hη hη2 hδ0 hδ1 ha hb hD hin (h2.trans hbig)

/-! ## 5. Glue: run bound + large-jump LD + occupation ⇒ `PositiveDensityGoodAngles` -/

section Glue

variable {ι : Type*}

/-- **Large-jump LD** (hypothesis about the path law): the weight of paths with more than `Jmax`
distinct-triangle hops is at most `ρ` times the total. -/
def LargeJumpLD (T : Finset ι) (w : ι → ℝ) (Jc : ι → ℕ) (Jmax : ℕ) (ρ : ℝ) : Prop :=
  ∑ P ∈ T.filter (fun P => Jmax < Jc P), w P ≤ ρ * ∑ P ∈ T, w P

/-- **Triangle occupation** (arithmetic hypothesis, NOT proved): the weight of paths with more than
`Omax` steps inside triangles of size `≥ R₁` is at most `ρ` times the total. -/
def TriangleOccupation (T : Finset ι) (w : ι → ℝ) (Occ : ι → ℕ) (Omax : ℕ) (ρ : ℝ) : Prop :=
  ∑ P ∈ T.filter (fun P => Omax < Occ P), w P ≤ ρ * ∑ P ∈ T, w P

/-- **Glue.**  If every path satisfies the run bound `R ≤ (2H₁+1)·#good + Occ + H₁·J`, and
`(2H₁+1) k + Omax + H₁ Jmax ≤ R`, then large-jump LD and occupation give
`PositiveDensityGoodAngles` with `ρ = ρ₁ + ρ₂`. -/
theorem positiveDensityGoodAngles_of_runBound (T : Finset ι) (w : ι → ℝ) (W : ι → ℕ → ℝ)
    (good : ι → ℕ → Prop) [∀ P, DecidablePred (good P)] (R H₁ k Omax Jmax : ℕ) (Occ Jc : ι → ℕ)
    {ρ₁ ρ₂ κ : ℝ} (hw : ∀ P ∈ T, 0 ≤ w P) (hW : ∀ P ∈ T, ∀ r, 0 ≤ W P r ∧ W P r ≤ 1)
    (hgood : ∀ P ∈ T, ∀ r, good P r → W P r ≤ κ)
    (hrun : ∀ P ∈ T, R ≤ (2 * H₁ + 1) * ((range R).filter (good P)).card + Occ P + H₁ * Jc P)
    (hk : (2 * H₁ + 1) * k + Omax + H₁ * Jmax ≤ R)
    (hLD : LargeJumpLD T w Jc Jmax ρ₁) (hOcc : TriangleOccupation T w Occ Omax ρ₂) :
    GoodAngles.PositiveDensityGoodAngles T w W good R k (ρ₁ + ρ₂) κ := by
  classical
  refine ⟨hW, hgood, ?_⟩
  have hsub : T.filter (fun P => ((range R).filter (good P)).card < k) ⊆
      T.filter (fun P => Jmax < Jc P) ∪ T.filter (fun P => Omax < Occ P) := by
    intro P hP
    rw [mem_filter] at hP
    obtain ⟨hPT, hlt⟩ := hP
    rw [mem_union, mem_filter, mem_filter]
    by_contra hc
    push Not at hc
    have h1 := hc.1 hPT
    have h2 := hc.2 hPT
    have h3 := hrun P hPT
    have h4 : (2 * H₁ + 1) * ((range R).filter (good P)).card ≤ (2 * H₁ + 1) * (k - 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have h5 : H₁ * Jc P ≤ H₁ * Jmax := Nat.mul_le_mul_left _ h1
    have h6 : (2 * H₁ + 1) * (k - 1) + (2 * H₁ + 1) = (2 * H₁ + 1) * k := by
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · omega
      · rw [← Nat.mul_succ]; congr 1; omega
    omega
  have hnn : ∀ P ∈ T, 0 ≤ w P := hw
  calc ∑ P ∈ T.filter (fun P => ((range R).filter (good P)).card < k), w P
      ≤ ∑ P ∈ T.filter (fun P => Jmax < Jc P) ∪ T.filter (fun P => Omax < Occ P), w P :=
        sum_le_sum_of_subset_of_nonneg hsub (fun P hP _ => by
          rw [mem_union, mem_filter, mem_filter] at hP
          rcases hP with h | h <;> exact hw P h.1)
    _ ≤ ∑ P ∈ T.filter (fun P => Jmax < Jc P), w P +
          ∑ P ∈ T.filter (fun P => Omax < Occ P), w P := by
        rw [← sum_union_inter]
        have : 0 ≤ ∑ P ∈ T.filter (fun P => Jmax < Jc P) ∩ T.filter (fun P => Omax < Occ P), w P :=
          sum_nonneg fun P hP => hw P (mem_filter.mp (mem_inter.mp hP).1).1
        linarith
    _ ≤ ρ₁ * ∑ P ∈ T, w P + ρ₂ * ∑ P ∈ T, w P := add_le_add hLD hOcc
    _ = (ρ₁ + ρ₂) * ∑ P ∈ T, w P := by ring

end Glue

end

end TriangleHop
end EOC
