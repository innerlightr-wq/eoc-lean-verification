import EOC.OddBlack

/-!
# Reducing `ShapeTail` to a one-sided tight-block count

`OddBlack.ShapeTail` asks that few confined prefix words have fewer than `K` **shape-good** pair
blocks, where (`OddBlack.ShapeGood`) block `r` of class `c` is shape-good when it has at most `N₀`
internal choices and at least one *eligible* choice.  A block therefore fails to be shape-good for
exactly two reasons:

* **tight**: `|B_r| ≤ 1` — the block offers at most one internal choice;
* **big**: `|B_r| > N₀` — the block offers too many.

This file proves that the *big* failure mode is **deterministically rare**: the choice sets of the
`R = j₀/2` blocks of one word satisfy the exact budget

  `∑_{r<R} (|B_r| + 1) ≤ σ`    (`sum_card_pairB_add_le`),

because `|B_r| + 1 ≤ S_{2r+2} − S_{2r}` and the even prefix sums telescope to `S_{2R} ≤ σ`.  Hence a
single word has at most `σ/(N₀+2)` big blocks (`card_big_mul_le`), with **no** counting or
large-deviation input.  Consequently

  `ShapeTail` ⟸ `TightTail` (`shapeTail_of_tightTail`),

where `TightTail` says that few confined words have many tight blocks.  Since (`tight_iff`) a block
is tight exactly when `S_{2r+2} ≤ S_{2r} + 2` (the digit pair is `(1,1)`) or the barrier cuts it
(`b(2r+1) ≤ S_{2r} + 1`), `TightTail` is a statement about *small* digit pairs and barrier contacts
only — the remaining analytic content of the shape large deviation
(`scratch/pressure_2026-09-16`, rate `c(0.1) = 0.073` at `N₀ = 4`).

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace ShapeTailRed

open Finset BlockCubeInstance PrefixCollision OddBlack WhiteContraction

variable (b : ℕ → ℕ)

/-! ## 1. Shape-good means `2 ≤ |B_r| ≤ N₀` -/

/-- The choice set of a pair block is an interval, so it has an eligible element iff it has at
least two elements. -/
theorem elig_nonempty_iff {j0 : ℕ} (c : Fin (j0 + 1) → ℕ) (r : ℕ) :
    (Elig b c r).Nonempty ↔ 2 ≤ (pairB b c r).card := by
  constructor
  · rintro ⟨x, hx⟩
    have hx' := mem_filter.mp hx
    have hne : x ≠ x + 1 := by omega
    exact Finset.one_lt_card.mpr ⟨x, hx'.1, x + 1, hx'.2, hne⟩
  · intro hcard
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hcard
    -- the interval property: a strictly smaller element's successor is still admissible
    have step : ∀ x y : ℕ, x ∈ pairB b c r → y ∈ pairB b c r → x < y → x + 1 ∈ pairB b c r := by
      intro x y hx hy hxy
      simp only [pairB, mem_filter, mem_Ioo] at hx hy ⊢
      exact ⟨⟨by omega, by omega⟩, by omega⟩
    rcases lt_or_gt_of_ne huv with h | h
    · exact ⟨u, mem_filter.mpr ⟨hu, step u v hu hv h⟩⟩
    · exact ⟨v, mem_filter.mpr ⟨hv, step v u hv hu h⟩⟩

/-- **Shape-good is a pure cardinality condition**: `2 ≤ |B_r| ≤ N₀`. -/
theorem shapeGood_iff {N0 j0 : ℕ} (c : Fin (j0 + 1) → ℕ) (r : ℕ) :
    ShapeGood b N0 c r ↔ 2 ≤ (pairB b c r).card ∧ (pairB b c r).card ≤ N0 := by
  unfold ShapeGood
  rw [elig_nonempty_iff]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- A block is **tight** when it offers at most one internal choice. -/
def Tight {j0 : ℕ} (c : Fin (j0 + 1) → ℕ) (r : ℕ) : Prop := (pairB b c r).card ≤ 1

/-- A block is **big** when it offers more than `N₀` internal choices. -/
def Big (N0 : ℕ) {j0 : ℕ} (c : Fin (j0 + 1) → ℕ) (r : ℕ) : Prop := N0 < (pairB b c r).card

instance {j0 : ℕ} (c : Fin (j0 + 1) → ℕ) (r : ℕ) : Decidable (Tight b c r) := by
  unfold Tight; infer_instance

instance {N0 j0 : ℕ} (c : Fin (j0 + 1) → ℕ) (r : ℕ) : Decidable (Big b N0 c r) := by
  unfold Big; infer_instance

/-- Tightness is exactly "the digit pair is `(1,1)`" or "the barrier cuts the block". -/
theorem tight_iff {j0 : ℕ} (c : Fin (j0 + 1) → ℕ) (r : ℕ) :
    Tight b c r ↔ cget c (2 * r + 2) ≤ cget c (2 * r) + 2 ∨ b (2 * r + 1) ≤ cget c (2 * r) + 1 := by
  unfold Tight
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    -- then `S_{2r}+1` and `S_{2r}+2` are both admissible
    have hm1 : cget c (2 * r) + 1 ∈ pairB b c r := by
      simp only [pairB, mem_filter, mem_Ioo]
      exact ⟨⟨by omega, by omega⟩, by omega⟩
    have hm2 : cget c (2 * r) + 2 ∈ pairB b c r := by
      simp only [pairB, mem_filter, mem_Ioo]
      exact ⟨⟨by omega, by omega⟩, by omega⟩
    have : 2 ≤ (pairB b c r).card :=
      Finset.one_lt_card.mpr ⟨_, hm1, _, hm2, by omega⟩
    omega
  · intro h
    rcases h with h | h
    · -- the interval `Ioo` has at most one element
      have hsub : pairB b c r ⊆ Ioo (cget c (2 * r)) (cget c (2 * r + 2)) := filter_subset _ _
      have := card_le_card hsub
      rw [Nat.card_Ioo] at this
      omega
    · -- the barrier cuts everything above `S_{2r}+1`
      have hsub : pairB b c r ⊆ {cget c (2 * r) + 1} := by
        intro x hx
        simp only [pairB, mem_filter, mem_Ioo] at hx
        simp only [mem_singleton]
        omega
      have := card_le_card hsub
      simpa using this

/-! ## 2. The exact block budget -/

/-- One block's choice set costs at least `|B_r| + 1` of the prefix-sum budget. -/
theorem card_pairB_add_le_diff {j0 : ℕ} {P : FiniteValuationWord j0} (hpos : P.Positive) {r : ℕ}
    (h : 2 * r + 2 ≤ j0) :
    (pairB b (pairκ j0 P) r).card + 1 ≤ P.prefixSum (2 * r + 2) - P.prefixSum (2 * r) := by
  have hA : cget (pairκ j0 P) (2 * r) = P.prefixSum (2 * r) :=
    cget_pairκ P (by omega) (by omega)
  have hC : cget (pairκ j0 P) (2 * r + 2) = P.prefixSum (2 * r + 2) :=
    cget_pairκ P (by omega) (by omega)
  -- two positive digits separate the two even prefix sums by at least `2`
  have hstep1 : P.prefixSum (2 * r) < P.prefixSum (2 * r + 1) :=
    prefixSum_lt_succ hpos (by omega)
  have hstep2 : P.prefixSum (2 * r + 1) < P.prefixSum (2 * r + 2) :=
    prefixSum_lt_succ hpos (by omega)
  have hsub : pairB b (pairκ j0 P) r ⊆
      Ioo (cget (pairκ j0 P) (2 * r)) (cget (pairκ j0 P) (2 * r + 2)) := filter_subset _ _
  have hcard := card_le_card hsub
  rw [Nat.card_Ioo, hA, hC] at hcard
  omega

/-- **Block budget.**  The `R = j₀/2` blocks of a confined word of total `σ` satisfy
`∑_r (|B_r| + 1) ≤ σ`. -/
theorem sum_card_pairB_add_le {j0 σ : ℕ} (hj : 1 ≤ j0) {P : FiniteValuationWord j0}
    (hP : P ∈ shellP b j0 σ) :
    ∑ r ∈ range (j0 / 2), ((pairB b (pairκ j0 P) r).card + 1) ≤ σ := by
  obtain ⟨hpos, hconf, htot⟩ := (mem_shellP_iff b hj).mp hP
  -- telescope over the even prefix sums
  have aux : ∀ R : ℕ, 2 * R ≤ j0 →
      ∑ r ∈ range R, ((pairB b (pairκ j0 P) r).card + 1) ≤ P.prefixSum (2 * R) := by
    intro R
    induction R with
    | zero => simp
    | succ R ih =>
      intro hR
      have hprev := ih (by omega)
      have hstep := card_pairB_add_le_diff b hpos (r := R) (by omega)
      have hmono : P.prefixSum (2 * R) ≤ P.prefixSum (2 * R + 2) :=
        prefixSum_le_prefixSum P _ (by omega) (by omega)
      rw [sum_range_succ]
      have : 2 * (R + 1) = 2 * R + 2 := by ring
      rw [this]
      omega
  have h1 := aux (j0 / 2) (by omega)
  have h2 : P.prefixSum (2 * (j0 / 2)) ≤ P.prefixSum j0 :=
    prefixSum_le_prefixSum P _ (by omega) le_rfl
  rw [← htot]
  unfold FiniteValuationWord.total
  omega

/-- **Big blocks are deterministically few.**  A confined word of total `σ` has at most
`σ/(N₀+2)` blocks with more than `N₀` internal choices. -/
theorem card_big_mul_le {j0 σ N0 : ℕ} (hj : 1 ≤ j0) {P : FiniteValuationWord j0}
    (hP : P ∈ shellP b j0 σ) :
    ((range (j0 / 2)).filter (Big b N0 (pairκ j0 P))).card * (N0 + 2) ≤ σ := by
  have hbudget := sum_card_pairB_add_le b hj hP
  calc ((range (j0 / 2)).filter (Big b N0 (pairκ j0 P))).card * (N0 + 2)
      = ∑ _r ∈ (range (j0 / 2)).filter (Big b N0 (pairκ j0 P)), (N0 + 2) := by
        rw [sum_const, smul_eq_mul]
    _ ≤ ∑ r ∈ (range (j0 / 2)).filter (Big b N0 (pairκ j0 P)),
          ((pairB b (pairκ j0 P) r).card + 1) := by
        refine sum_le_sum fun r hr => ?_
        have := (mem_filter.mp hr).2
        unfold Big at this
        omega
    _ ≤ ∑ r ∈ range (j0 / 2), ((pairB b (pairκ j0 P) r).card + 1) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
    _ ≤ σ := hbudget

/-! ## 3. Every block is shape-good, tight, or big -/

open Classical in
/-- The three classes exhaust the blocks. -/
theorem card_le_good_add_tight_add_big {N0 j0 : ℕ} (c : Fin (j0 + 1) → ℕ) (I : Finset ℕ) :
    I.card ≤ (I.filter (ShapeGood b N0 c)).card + (I.filter (Tight b c)).card
      + (I.filter (Big b N0 c)).card := by
  classical
  calc I.card
      ≤ ((I.filter (ShapeGood b N0 c)) ∪ (I.filter (Tight b c)) ∪
          (I.filter (Big b N0 c))).card := by
        refine card_le_card fun r hr => ?_
        by_cases hg : ShapeGood b N0 c r
        · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hr, hg⟩))
        · rw [shapeGood_iff] at hg
          push Not at hg
          by_cases h2 : 2 ≤ (pairB b c r).card
          · have : N0 < (pairB b c r).card := by
              have := hg h2
              omega
            exact mem_union_right _ (mem_filter.mpr ⟨hr, this⟩)
          · exact mem_union_left _ (mem_union_right _
              (mem_filter.mpr ⟨hr, by unfold Tight; omega⟩))
    _ ≤ _ := le_trans (card_union_le _ _) (by
        have := card_union_le (I.filter (ShapeGood b N0 c)) (I.filter (Tight b c))
        omega)

/-! ## 4. `TightTail ⇒ ShapeTail` -/

open Classical in
/-- Number of tight blocks of the class of `P`. -/
noncomputable def tightCount (j0 : ℕ) (P : FiniteValuationWord j0) : ℕ :=
  ((range (j0 / 2)).filter (Tight b (pairκ j0 P))).card

open Classical in
/-- **`TightTail`**: at most a `ρ₁` fraction of the confined prefix shell has `T` or more tight
blocks.  This is the remaining analytic content of the shape large deviation. -/
def TightTail (j0 σ T : ℕ) (ρ₁ : ℝ) : Prop :=
  (((shellP b j0 σ).filter (fun P => T ≤ tightCount b j0 P)).card : ℝ)
    ≤ ρ₁ * ((shellP b j0 σ).card : ℝ)

open Classical in
/-- **`TightTail ⇒ ShapeTail`.**  If few words have `T` or more tight blocks, and
`K + T + σ/(N₀+2) ≤ j₀/2`, then few words have fewer than `K` shape-good blocks: the *big* blocks
are paid for deterministically by the block budget. -/
theorem shapeTail_of_tightTail {j0 σ N0 K T : ℕ} {ρ₁ : ℝ} (hj : 1 ≤ j0)
    (hK : K + T + σ / (N0 + 2) ≤ j0 / 2) (htight : TightTail b j0 σ T ρ₁) :
    ShapeTail b j0 σ N0 K ρ₁ := by
  classical
  unfold ShapeTail
  rw [sum_nCls_filter_eq_card]
  refine le_trans (Nat.cast_le.mpr (card_le_card ?_)) htight
  -- a word with fewer than `K` shape-good blocks has at least `T` tight blocks
  intro P hP
  simp only [mem_filter] at hP ⊢
  obtain ⟨hPs, hfew⟩ := hP
  refine ⟨hPs, ?_⟩
  have hbig := card_big_mul_le b (N0 := N0) hj hPs
  have hbig' : ((range (j0 / 2)).filter (Big b N0 (pairκ j0 P))).card ≤ σ / (N0 + 2) :=
    (Nat.le_div_iff_mul_le (by omega)).mpr hbig
  have hexh := card_le_good_add_tight_add_big b (N0 := N0) (pairκ j0 P) (range (j0 / 2))
  rw [card_range] at hexh
  unfold tightCount
  omega

/-! ## 5. The class-level form of `TightTail` -/

/-- **Class cardinality.**  A coarse class of the prefix shell is the product of its blocks'
choice sets, so its size is `∏_r |B_r|`. -/
theorem card_class_eq_prod {j0 σ t : ℕ} (hj : 1 ≤ j0) {c : Fin (j0 + 1) → ℕ}
    (hc : c ∈ (shellP b j0 σ).image (pairκ j0)) :
    (((shellP b j0 σ).filter (fun P => pairκ j0 P = c)).card : ℝ)
      = ∏ r : Fin (j0 / 2), ((pairB b c (r : ℕ)).card : ℝ) := by
  have h := sum_class_prod (shellP b j0 σ) (pairκ j0) (pairB b) (pairπ j0)
    ((pairDecomposition b j0 σ t hj).inj c hc)
    ((pairDecomposition b j0 σ t hj).image_eq c hc) (fun _ _ => (1 : ℝ))
  simpa using h

open Classical in
/-- **`TightTail` is a class-level statement.**  The tilted word count splits into a sum over
coarse classes weighted by `∏_r |B_r|` — the quantity computed by the block transfer operator
(`EOC.LocalWindow.ker`), since `tightCount` depends on the word only through its class. -/
theorem sum_pow_tight_eq_class_sum {j0 σ t : ℕ} (hj : 1 ≤ j0) (u : ℝ) :
    ∑ P ∈ shellP b j0 σ, u ^ tightCount b j0 P
      = ∑ c ∈ (shellP b j0 σ).image (pairκ j0),
          (∏ r : Fin (j0 / 2), ((pairB b c (r : ℕ)).card : ℝ)) *
            u ^ ((range (j0 / 2)).filter (Tight b c)).card := by
  classical
  rw [← sum_fiberwise_of_maps_to (g := pairκ j0)
    (fun P hP => mem_image_of_mem (pairκ j0) hP) (fun P => u ^ tightCount b j0 P)]
  refine sum_congr rfl fun c hc => ?_
  -- on a class the tight count is constant
  have hconst : ∀ P ∈ (shellP b j0 σ).filter (fun P => pairκ j0 P = c),
      u ^ tightCount b j0 P = u ^ ((range (j0 / 2)).filter (Tight b c)).card := by
    intro P hP
    have : pairκ j0 P = c := (mem_filter.mp hP).2
    unfold tightCount
    rw [this]
  rw [sum_congr rfl hconst, sum_const, nsmul_eq_mul, card_class_eq_prod b (t := t) hj hc]

open Classical in
/-- **Chernoff form of `TightTail`.**  If for some tilt `u ≥ 1` the class-weighted tilted sum
obeys `∑_c (∏_r |B_r|) u^{#tight(c)} ≤ ρ₁ u^T |P_σ|`, then `TightTail b j0 σ T ρ₁`.

The left side is exactly the tilted partition function computed by the block transfer operator
(state = even prefix sum, weight `|B_r|·u^{[|B_r| ≤ 1]}`), so a finite spectral certificate
(`LocalWindow.val_le_of_superEigen` for the numerator, `val_ge_of_subEigen` for `|P_σ|`) suffices. -/
theorem tightTail_of_tilted {j0 σ t T : ℕ} {u ρ₁ : ℝ} (hj : 1 ≤ j0) (hu : 1 ≤ u)
    (htilt : ∑ c ∈ (shellP b j0 σ).image (pairκ j0),
        (∏ r : Fin (j0 / 2), ((pairB b c (r : ℕ)).card : ℝ)) *
          u ^ ((range (j0 / 2)).filter (Tight b c)).card
      ≤ ρ₁ * u ^ T * ((shellP b j0 σ).card : ℝ)) :
    TightTail b j0 σ T ρ₁ := by
  classical
  have hchern := card_filter_ge_mul_pow_le (shellP b j0 σ) (tightCount b j0) hu T
  rw [← sum_pow_tight_eq_class_sum b (t := t) hj u] at htilt
  have hupow : (0 : ℝ) < u ^ T := by positivity
  unfold TightTail
  refine le_of_mul_le_mul_right ?_ hupow
  calc (((shellP b j0 σ).filter (fun P => T ≤ tightCount b j0 P)).card : ℝ) * u ^ T
      ≤ ∑ P ∈ shellP b j0 σ, u ^ tightCount b j0 P := hchern
    _ ≤ ρ₁ * u ^ T * ((shellP b j0 σ).card : ℝ) := htilt
    _ = ρ₁ * ((shellP b j0 σ).card : ℝ) * u ^ T := by ring

/-! ## 6. Explicit denominator: the chord-rotation shell bound -/

/-- **Shell lower bound for the prefix shell.**  Specialization of
`CapacityBounds.shell_choose_le_mul_card` (chord rotation / cycle lemma, already in the repo) to
`shellP`: `C(σ−1, j₀−1) ≤ j₀ · |P_σ|`. -/
theorem choose_le_mul_card_shellP {j0 σ : ℕ} (hj : 1 ≤ j0)
    (hchord : ∀ j ≤ j0, ∀ p : ℕ, j0 * p ≤ j * b j0 → p ≤ b j)
    (hjσ : j0 ≤ σ) (hσ : σ ≤ b j0) :
    Nat.choose (σ - 1) (j0 - 1) ≤ j0 * (shellP b j0 σ).card :=
  CapacityBounds.shell_choose_le_mul_card hj b hchord hjσ hσ

open Classical in
/-- **`TightTail` from an explicit tilted-sum bound.**  The denominator is replaced by the binomial
coefficient supplied by the chord rotation, so the remaining obligation is a comparison of two
explicit finite quantities: the tilted class sum on the left, `C(σ−1, j₀−1)` on the right. -/
theorem tightTail_of_tilted_choose {j0 σ t T : ℕ} {u ρ₁ : ℝ} (hj : 1 ≤ j0) (hu : 1 ≤ u)
    (hρ : 0 ≤ ρ₁)
    (hchord : ∀ j ≤ j0, ∀ p : ℕ, j0 * p ≤ j * b j0 → p ≤ b j)
    (hjσ : j0 ≤ σ) (hσ : σ ≤ b j0)
    (htilt : (j0 : ℝ) * ∑ c ∈ (shellP b j0 σ).image (pairκ j0),
        (∏ r : Fin (j0 / 2), ((pairB b c (r : ℕ)).card : ℝ)) *
          u ^ ((range (j0 / 2)).filter (Tight b c)).card
      ≤ ρ₁ * u ^ T * (Nat.choose (σ - 1) (j0 - 1) : ℝ)) :
    TightTail b j0 σ T ρ₁ := by
  classical
  have hden : (Nat.choose (σ - 1) (j0 - 1) : ℝ) ≤ (j0 : ℝ) * ((shellP b j0 σ).card : ℝ) := by
    exact_mod_cast choose_le_mul_card_shellP b hj hchord hjσ hσ
  have hj0 : (0 : ℝ) < j0 := by exact_mod_cast hj
  refine tightTail_of_tilted b (t := t) hj hu ?_
  have hcoef : (0 : ℝ) ≤ ρ₁ * u ^ T := by positivity
  have hchain := htilt.trans (mul_le_mul_of_nonneg_left hden hcoef)
  refine le_of_mul_le_mul_left ?_ hj0
  calc (j0 : ℝ) * ∑ c ∈ (shellP b j0 σ).image (pairκ j0),
        (∏ r : Fin (j0 / 2), ((pairB b c (r : ℕ)).card : ℝ)) *
          u ^ ((range (j0 / 2)).filter (Tight b c)).card
      ≤ ρ₁ * u ^ T * ((j0 : ℝ) * ((shellP b j0 σ).card : ℝ)) := hchain
    _ = (j0 : ℝ) * (ρ₁ * u ^ T * ((shellP b j0 σ).card : ℝ)) := by ring

open Classical in
/-- **Single-hypothesis wrapper.**  With the shape hypothesis replaced by `TightTail`, the critical
white count follows from `TightTail` and `OddDarkPressure` alone. -/
theorem criticalWhiteCount_of_tight_and_oddPressure {j0 σ t U N0 k n T : ℕ} {d s M ρ₁ ρ₂ : ℝ}
    (hj : 1 ≤ j0) (hs : 1 ≤ s)
    (hK : (k + n) + T + σ / (N0 + 2) ≤ j0 / 2)
    (htight : TightTail b j0 σ T ρ₁)
    (hodd : OddDarkPressure b j0 σ t U d s M) (hM : M ≤ ρ₂ * ((1 + s) / 2) ^ n) :
    CriticalWhiteCount b j0 σ t U N0 d k (ρ₁ + ρ₂) :=
  criticalWhiteCount_of_shape_and_oddPressure b hj hs
    (shapeTail_of_tightTail b (N0 := N0) hj hK htight) hodd hM

end ShapeTailRed
end EOC
