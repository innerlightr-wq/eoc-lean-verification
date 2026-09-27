import EOC.FrontierRegion

/-!
# Multi-pair white contraction

`WhiteContraction.wfac_le_of_pair` credits **one** white consecutive pair in a pair block, which gives
the block factor `W ≤ 1 − 2(1 − cos πd)/|B|` and, for `|B| ≤ N₀`, the constant `κ(d, N₀)`.  This file
credits **all** white pairs of one parity class.

* `norm_sum_le_pairs` — if `S ⊆ B` is a set of left endpoints of pairwise disjoint consecutive pairs
  `(z, z+1) ⊆ B`, each with phase difference at distance `≥ d` from `ℤ`, then
  `‖∑_{z∈B} e(φ z)‖ ≤ |B| − 2|S|(1 − cos πd)`.
* `whiteSet`, `wfac_le_multi` — in a pair block, the white edges of one parity are disjoint; with
  `M` the larger parity class, `W ≤ 1 − 2(1 − cos πd) M / |B|`.  (`M = 1` is the old estimate.)
* `two_mul_M_ge`, `three_M_add_two_D_ge` — `2M ≥ |B| − 1 − D` and, for `|B| ≥ 2`, `3M + 2D ≥ |B|`,
  where `D` is the number of dark edges (the quantity counted by the pressure kernel `oddW`).

No `sorry`, `admit`, `axiom`, `opaque`, or `native_decide`.
-/

namespace EOC
namespace MultiWhite

open Finset Real SwapBound WhiteContraction

/-! ## 1. Disjoint white pairs -/

theorem norm_sum_le_pairs (B S : Finset ℕ) (φ : ℕ → ℝ) {d : ℝ} (hd0 : 0 ≤ d)
    (hS : ∀ z ∈ S, z ∈ B ∧ z + 1 ∈ B ∧ d ≤ distZ (φ z - φ (z + 1)))
    (hsep : ∀ z ∈ S, z + 1 ∉ S) :
    ‖∑ z ∈ B, ee (φ z)‖ ≤ (B.card : ℝ) - 2 * S.card * (1 - Real.cos (π * d)) := by
  set S1 := S.image (· + 1) with hS1
  have hdisj : Disjoint S S1 := by
    rw [disjoint_left]
    intro x hx hx1
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hx1
    exact hsep z hz hx
  have hsub : S ∪ S1 ⊆ B := by
    intro x hx
    rcases mem_union.mp hx with h | h
    · exact (hS x h).1
    · obtain ⟨z, hz, rfl⟩ := mem_image.mp h; exact (hS z hz).2.1
  have hc1 : S1.card = S.card := card_image_of_injective _ (add_left_injective 1)
  have hcU : (S ∪ S1).card = 2 * S.card := by rw [card_union_of_disjoint hdisj, hc1]; ring
  have hsplit : ∑ z ∈ B, ee (φ z) =
      ∑ z ∈ S, (ee (φ z) + ee (φ (z + 1))) + ∑ z ∈ B \ (S ∪ S1), ee (φ z) := by
    rw [← sum_sdiff hsub, sum_union hdisj, hS1, sum_image (fun a _ b _ h => by simpa using h),
      sum_add_distrib]
    ring
  have h1 : ‖∑ z ∈ S, (ee (φ z) + ee (φ (z + 1)))‖ ≤ S.card * (2 * Real.cos (π * d)) := by
    calc ‖∑ z ∈ S, (ee (φ z) + ee (φ (z + 1)))‖ ≤ ∑ z ∈ S, ‖ee (φ z) + ee (φ (z + 1))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _z ∈ S, 2 * Real.cos (π * d) :=
          sum_le_sum fun z hz => norm_ee_add_ee_le hd0 (hS z hz).2.2
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  have h2 : ‖∑ z ∈ B \ (S ∪ S1), ee (φ z)‖ ≤ (B.card : ℝ) - 2 * S.card := by
    calc ‖∑ z ∈ B \ (S ∪ S1), ee (φ z)‖ ≤ ∑ z ∈ B \ (S ∪ S1), ‖ee (φ z)‖ := norm_sum_le _ _
      _ = ((B \ (S ∪ S1)).card : ℝ) := by simp [norm_ee]
      _ = (B.card : ℝ) - 2 * S.card := by
          rw [card_sdiff_of_subset hsub, hcU]
          have : 2 * S.card ≤ B.card := hcU ▸ card_le_card hsub
          push_cast [Nat.cast_sub this]; ring
  rw [hsplit]
  calc _ ≤ ‖∑ z ∈ S, (ee (φ z) + ee (φ (z + 1)))‖ + ‖∑ z ∈ B \ (S ∪ S1), ee (φ z)‖ := norm_add_le _ _
    _ ≤ S.card * (2 * Real.cos (π * d)) + ((B.card : ℝ) - 2 * S.card) := add_le_add h1 h2
    _ = _ := by ring

/-! ## 2. White edges of a pair block -/

section Block

variable (b : ℕ → ℕ)

open Classical in
/-- White edges of parity `p` in pair block `r`: eligible, not dark, `z ≡ p (mod 2)`. -/
noncomputable def whiteSet (m : ℕ) (d : ℝ) (lam : ℕ) {j0 : ℕ} (c : Fin (j0 + 1) → ℕ) (r p : ℕ) :
    Finset ℕ :=
  (OddBlack.Elig b c r).filter (fun z => ¬ OddBlack.Dark m d lam r z ∧ z % 2 = p)

open Classical in
/-- Dark edges of pair block `r` (the edges counted by `oddW`). -/
noncomputable def darkSet (m : ℕ) (d : ℝ) (lam : ℕ) {j0 : ℕ} (c : Fin (j0 + 1) → ℕ) (r : ℕ) :
    Finset ℕ :=
  (OddBlack.Elig b c r).filter (fun z => OddBlack.Dark m d lam r z)

/-- The larger parity class of white edges. -/
noncomputable def Mw (m : ℕ) (d : ℝ) (lam : ℕ) {j0 : ℕ} (c : Fin (j0 + 1) → ℕ) (r : ℕ) : ℕ :=
  max (whiteSet b m d lam c r 0).card (whiteSet b m d lam c r 1).card

theorem wfac_le_parity {m : ℕ} {d : ℝ} (hd0 : 0 ≤ d) {lam j0 : ℕ} (c : Fin (j0 + 1) → ℕ) (r p : ℕ)
    (hB : (BlockCubeInstance.pairB b c r).Nonempty) :
    BlockCubeInstance.Wfac (BlockCubeInstance.pairB b)
        (fun _ r x => SwapCollatz.collatzPhase lam m (WeightedChain.uInv m) (2 * r + 1) x) c r ≤
      1 - 2 * (1 - Real.cos (π * d)) * (whiteSet b m d lam c r p).card /
        (BlockCubeInstance.pairB b c r).card := by
  classical
  unfold BlockCubeInstance.Wfac
  set B := BlockCubeInstance.pairB b c r
  have hpos : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  have h := norm_sum_le_pairs B (whiteSet b m d lam c r p)
    (fun x => SwapCollatz.collatzPhase lam m (WeightedChain.uInv m) (2 * r + 1) x) hd0
    (fun z hz => by
      simp only [whiteSet, OddBlack.Elig, mem_filter] at hz
      obtain ⟨⟨hzB, hz1⟩, hnd, _⟩ := hz
      refine ⟨hzB, hz1, ?_⟩
      unfold OddBlack.Dark at hnd
      exact not_lt.mp hnd)
    (fun z hz hz1 => by
      simp only [whiteSet, mem_filter] at hz hz1 <;> omega)
  rw [div_le_iff₀ hpos]
  have e : (1 - 2 * (1 - Real.cos (π * d)) * ((whiteSet b m d lam c r p).card : ℝ) / B.card) * B.card =
      B.card - 2 * (whiteSet b m d lam c r p).card * (1 - Real.cos (π * d)) := by
    field_simp
  rw [e]; exact h

/-- **Multi-pair block contraction.** `W ≤ 1 − 2(1 − cos πd) M / |B|`. -/
theorem wfac_le_multi {m : ℕ} {d : ℝ} (hd0 : 0 ≤ d) {lam j0 : ℕ} (c : Fin (j0 + 1) → ℕ) (r : ℕ)
    (hB : (BlockCubeInstance.pairB b c r).Nonempty) :
    BlockCubeInstance.Wfac (BlockCubeInstance.pairB b)
        (fun _ r x => SwapCollatz.collatzPhase lam m (WeightedChain.uInv m) (2 * r + 1) x) c r ≤
      1 - 2 * (1 - Real.cos (π * d)) * (Mw b m d lam c r) /
        (BlockCubeInstance.pairB b c r).card := by
  unfold Mw
  rcases le_total (whiteSet b m d lam c r 0).card (whiteSet b m d lam c r 1).card with h | h
  · rw [max_eq_right h]; exact wfac_le_parity b hd0 c r 1 hB
  · rw [max_eq_left h]; exact wfac_le_parity b hd0 c r 0 hB

theorem card_white_add_dark {m : ℕ} {d : ℝ} {lam j0 : ℕ} (c : Fin (j0 + 1) → ℕ) (r : ℕ) :
    (whiteSet b m d lam c r 0).card + (whiteSet b m d lam c r 1).card + (darkSet b m d lam c r).card =
      (OddBlack.Elig b c r).card := by
  classical
  set E := OddBlack.Elig b c r
  have h1 := card_filter_add_card_filter_not (s := E) (fun z => OddBlack.Dark m d lam r z)
  set W := E.filter (fun z => ¬ OddBlack.Dark m d lam r z)
  have h2 := card_filter_add_card_filter_not (s := W) (fun z => z % 2 = 0)
  have e0 : whiteSet b m d lam c r 0 = W.filter (fun z => z % 2 = 0) := by
    ext z; simp [whiteSet, W, E, and_assoc]
  have e1 : whiteSet b m d lam c r 1 = W.filter (fun z => ¬ z % 2 = 0) := by
    ext z; simp only [whiteSet, W, mem_filter]; constructor
    · rintro ⟨hE, hnd, hp⟩; exact ⟨⟨hE, hnd⟩, by omega⟩
    · rintro ⟨⟨hE, hnd⟩, hp⟩; exact ⟨hE, hnd, by omega⟩
  have hd : darkSet b m d lam c r = E.filter (fun z => OddBlack.Dark m d lam r z) := rfl
  rw [e0, e1, h2, hd]
  omega

/-- `2M ≥ |B| − 1 − D`, and `M ≥ 1` if some edge is white. -/
theorem two_mul_M_ge {m : ℕ} {d : ℝ} {lam j0 : ℕ} (c : Fin (j0 + 1) → ℕ) (r : ℕ) :
    (BlockCubeInstance.pairB b c r).card ≤ 2 * Mw b m d lam c r + (darkSet b m d lam c r).card + 1 ∧
      ((darkSet b m d lam c r).card + 2 ≤ (BlockCubeInstance.pairB b c r).card →
        1 ≤ Mw b m d lam c r) := by
  have h1 := card_white_add_dark b (m := m) (d := d) (lam := lam) c r
  have h2 := OddBlack.card_pairB_le_elig_add_one b c r
  unfold Mw
  constructor
  · have := le_max_left (whiteSet b m d lam c r 0).card (whiteSet b m d lam c r 1).card
    have := le_max_right (whiteSet b m d lam c r 0).card (whiteSet b m d lam c r 1).card
    omega
  · intro h
    have := le_max_left (whiteSet b m d lam c r 0).card (whiteSet b m d lam c r 1).card
    have := le_max_right (whiteSet b m d lam c r 0).card (whiteSet b m d lam c r 1).card
    omega

/-- **Integer lemma.** For `|B| ≥ 2`: `3M + 2D ≥ |B|`. -/
theorem three_M_add_two_D_ge {m : ℕ} {d : ℝ} {lam j0 : ℕ} (c : Fin (j0 + 1) → ℕ) (r : ℕ)
    (h2 : 2 ≤ (BlockCubeInstance.pairB b c r).card) :
    (BlockCubeInstance.pairB b c r).card ≤ 3 * Mw b m d lam c r + 2 * (darkSet b m d lam c r).card := by
  obtain ⟨ha, hb⟩ := two_mul_M_ge b (m := m) (d := d) (lam := lam) c r
  by_cases h : (darkSet b m d lam c r).card + 2 ≤ (BlockCubeInstance.pairB b c r).card
  · have := hb h; omega
  · omega

end Block

/-! ## 3. Per-block analytic inequalities -/

section Analytic

variable (b : ℕ → ℕ)

/-- `W² ≤ exp(−4(1 − cos πd) M/|B|)` (Lean division: an empty block gives `W = 0`). -/
theorem wfac_sq_le_exp {m : ℕ} {d : ℝ} (hd0 : 0 ≤ d) {lam j0 : ℕ} (c : Fin (j0 + 1) → ℕ) (r : ℕ) :
    BlockCubeInstance.Wfac (BlockCubeInstance.pairB b)
        (fun _ r x => SwapCollatz.collatzPhase lam m (WeightedChain.uInv m) (2 * r + 1) x) c r ^ 2 ≤
      Real.exp (-(4 * (1 - Real.cos (π * d)) * (Mw b m d lam c r : ℝ) /
        (BlockCubeInstance.pairB b c r).card)) := by
  set W := BlockCubeInstance.Wfac (BlockCubeInstance.pairB b)
    (fun _ r x => SwapCollatz.collatzPhase lam m (WeightedChain.uInv m) (2 * r + 1) x) c r
  have hW := wfac_mem_unit (BlockCubeInstance.pairB b c r)
    (fun x => SwapCollatz.collatzPhase lam m (WeightedChain.uInv m) (2 * r + 1) x)
  have hW0 : 0 ≤ W := hW.1
  rcases (BlockCubeInstance.pairB b c r).eq_empty_or_nonempty with he | hne
  · have : W = 0 := by
      simp only [W, BlockCubeInstance.Wfac, he, sum_empty, norm_zero, card_empty, Nat.cast_zero,
        div_zero]
    rw [this, zero_pow two_ne_zero]; positivity
  · set y := 2 * (1 - Real.cos (π * d)) * (Mw b m d lam c r : ℝ) / (BlockCubeInstance.pairB b c r).card
    have hle : W ≤ 1 - y := wfac_le_multi b hd0 c r hne
    have hy1 : 0 ≤ 1 - y := hW0.trans hle
    have hexp : 1 - y ≤ Real.exp (-y) := by have := Real.add_one_le_exp (-y); linarith
    calc W ^ 2 ≤ (1 - y) ^ 2 := pow_le_pow_left₀ hW0 hle 2
      _ ≤ Real.exp (-y) ^ 2 := pow_le_pow_left₀ hy1 hexp 2
      _ = Real.exp (-(4 * (1 - Real.cos (π * d)) * (Mw b m d lam c r : ℝ) /
            (BlockCubeInstance.pairB b c r).card)) := by
          rw [← Real.exp_nat_mul]; congr 1; simp only [y]; push_cast; ring

/-- **Per-block exchange.** `exp(ln 2 · ([|B| ≥ 2] − 3M/|B|)) ≤ 1 + 2D/|B|`. -/
theorem exp_block_le {m : ℕ} {d : ℝ} {lam j0 : ℕ} (c : Fin (j0 + 1) → ℕ) (r : ℕ) :
    Real.exp (Real.log 2 * ((if 2 ≤ (BlockCubeInstance.pairB b c r).card then (1 : ℝ) else 0) -
        3 * (Mw b m d lam c r : ℝ) / (BlockCubeInstance.pairB b c r).card)) ≤
      1 + 2 * ((darkSet b m d lam c r).card : ℝ) / (BlockCubeInstance.pairB b c r).card := by
  set B := BlockCubeInstance.pairB b c r
  set M := Mw b m d lam c r
  set D := (darkSet b m d lam c r).card
  have hD0 : (0 : ℝ) ≤ 2 * (D : ℝ) / B.card := by positivity
  have hM0 : (0 : ℝ) ≤ 3 * (M : ℝ) / B.card := by positivity
  split_ifs with h2
  · set e : ℝ := 1 - 3 * (M : ℝ) / B.card
    have hpos : (0 : ℝ) < B.card := by exact_mod_cast (show 0 < B.card by omega)
    have hint := three_M_add_two_D_ge b (m := m) (d := d) (lam := lam) c r h2
    have hintR : (B.card : ℝ) ≤ 3 * M + 2 * D := by exact_mod_cast hint
    have heD : e ≤ 2 * (D : ℝ) / B.card := by
      have h1 : (1 : ℝ) ≤ (3 * M + 2 * D) / B.card := by rw [le_div_iff₀ hpos]; linarith
      have h2 : (3 * (M : ℝ) + 2 * D) / B.card = 3 * M / B.card + 2 * D / B.card := by ring
      simp only [e]; linarith
    by_cases he : e ≤ 0
    · calc Real.exp (Real.log 2 * e) ≤ Real.exp 0 := by
            apply Real.exp_le_exp.mpr
            have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
            nlinarith
        _ = 1 := Real.exp_zero
        _ ≤ _ := by linarith
    · push Not at he
      have he1 : e ≤ 1 := by simp only [e]; linarith
      have hb := rpow_one_add_le_one_add_mul_self (s := (1 : ℝ)) (by norm_num) he.le he1
      rw [Real.rpow_def_of_pos (by norm_num)] at hb
      norm_num at hb
      calc Real.exp (Real.log 2 * e) ≤ 1 + e := hb
        _ ≤ _ := by linarith
  · calc Real.exp (Real.log 2 * (0 - 3 * (M : ℝ) / B.card)) ≤ Real.exp 0 := by
          apply Real.exp_le_exp.mpr
          have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
          nlinarith
      _ = 1 := Real.exp_zero
      _ ≤ _ := by linarith

theorem card_pairB_ge_two_of_shapeGood {N0 j0 : ℕ} {c : Fin (j0 + 1) → ℕ} {r : ℕ}
    (h : OddBlack.ShapeGood b N0 c r) : 2 ≤ (BlockCubeInstance.pairB b c r).card := by
  obtain ⟨_, x, hx⟩ := h
  simp only [OddBlack.Elig, mem_filter] at hx
  have : ({x, x + 1} : Finset ℕ) ⊆ BlockCubeInstance.pairB b c r := by
    intro z hz; simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hx.1
    · exact hx.2
  have := card_le_card this
  rwa [card_pair (by omega)] at this

end Analytic

/-! ## 4. Class level -/

section ClassLevel

variable (b : ℕ → ℕ)

open Classical in
theorem block_sum_eq {m : ℕ} {d : ℝ} {lam j0 : ℕ} (c : Fin (j0 + 1) → ℕ) (r : ℕ) :
    ∑ x ∈ BlockCubeInstance.pairB b c r,
        (if x ∈ OddBlack.Elig b c r ∧ OddBlack.Dark m d lam r x then (3 : ℝ) else 1) =
      (BlockCubeInstance.pairB b c r).card + 2 * ((darkSet b m d lam c r).card : ℝ) := by
  set B := BlockCubeInstance.pairB b c r
  have hsub : OddBlack.Elig b c r ⊆ B := OddBlack.elig_subset b c r
  have hfilt : B.filter (fun x => x ∈ OddBlack.Elig b c r ∧ OddBlack.Dark m d lam r x) =
      darkSet b m d lam c r := by
    ext x; simp only [darkSet, mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hsub h.1, h⟩⟩
  rw [sum_ite, hfilt, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one]
  have hc := card_filter_add_card_filter_not (s := B)
    (fun x => x ∈ OddBlack.Elig b c r ∧ OddBlack.Dark m d lam r x)
  rw [hfilt] at hc
  have : ((B.filter (fun x => ¬ (x ∈ OddBlack.Elig b c r ∧ OddBlack.Dark m d lam r x))).card : ℝ) =
      B.card - (darkSet b m d lam c r).card := by
    rw [← hc]; push_cast; ring
  rw [this]; ring

open Classical in
theorem class_moment_eq {j0 σ t : ℕ} (hj : 1 ≤ j0) {m : ℕ} {d : ℝ} {lam : ℕ}
    {c : Fin (j0 + 1) → ℕ} (hc : c ∈ (PrefixCollision.shellP b j0 σ).image (BlockCubeInstance.pairκ j0)) :
    ∑ P ∈ (PrefixCollision.shellP b j0 σ).filter (fun P => BlockCubeInstance.pairκ j0 P = c),
        (3 : ℝ) ^ OddBlack.Nodd b m d lam P =
      ∏ r : Fin (j0 / 2), (((BlockCubeInstance.pairB b c r).card : ℝ) +
        2 * ((darkSet b m d lam c r).card : ℝ)) ∧
    BlockCubeInstance.nCls (PrefixCollision.shellP b j0 σ) (BlockCubeInstance.pairκ j0) c =
      ∏ r : Fin (j0 / 2), ((BlockCubeInstance.pairB b c r).card : ℝ) := by
  set D := BlockCubeInstance.pairDecomposition b j0 σ t hj
  set F := (PrefixCollision.shellP b j0 σ).filter (fun P => BlockCubeInstance.pairκ j0 P = c)
  let g : Fin (j0 / 2) → ℕ → ℝ := fun r x =>
    if x ∈ OddBlack.Elig b c r ∧ OddBlack.Dark m d lam r x then 3 else 1
  have hword : ∀ P ∈ F,
      (3 : ℝ) ^ OddBlack.Nodd b m d lam P = ∏ r : Fin (j0 / 2), g r (BlockCubeInstance.pairπ j0 P r) := by
    intro P hP
    have hκ : BlockCubeInstance.pairκ j0 P = c := (mem_filter.mp hP).2
    unfold OddBlack.Nodd
    rw [OddBlack.pow_card_filter_eq_prod]
    refine prod_congr rfl fun r _ => ?_
    simp only [g, OddBlack.OwnDark, hκ, BlockCubeInstance.pairπ]
  have hprod := OddBlack.sum_class_prod (PrefixCollision.shellP b j0 σ) (BlockCubeInstance.pairκ j0)
    (BlockCubeInstance.pairB b) (BlockCubeInstance.pairπ j0) (D.inj c hc) (D.image_eq c hc) g
  have hcard := OddBlack.sum_class_prod (PrefixCollision.shellP b j0 σ) (BlockCubeInstance.pairκ j0)
    (BlockCubeInstance.pairB b) (BlockCubeInstance.pairπ j0) (D.inj c hc) (D.image_eq c hc)
    (fun _ _ => (1 : ℝ))
  simp only [prod_const_one, sum_const, nsmul_eq_mul, mul_one] at hcard
  refine ⟨?_, by unfold BlockCubeInstance.nCls; exact hcard⟩
  rw [sum_congr rfl hword, hprod]
  exact prod_congr rfl fun r _ => block_sum_eq b c r

open Classical in
/-- **Per-class three-way split.**  With `c₀ = 1 − cos πd`, any real `Λ` (in bits) and any `K`: the
class contribution `w_c ∏ W_r²` is at most its mass if it has fewer than `K` shape-good blocks, plus
`2^{−Λ}` times its pressure moment, plus `w_c · exp(−(4c₀/3)(K − Λ))`. -/
theorem class_split {j0 σ t N0 K : ℕ} (hj : 1 ≤ j0) {d : ℝ} (hd0 : 0 ≤ d) {lam : ℕ} {Λ : ℝ}
    {c : Fin (j0 + 1) → ℕ} (hc : c ∈ (PrefixCollision.shellP b j0 σ).image (BlockCubeInstance.pairκ j0)) :
    BlockCubeInstance.nCls (PrefixCollision.shellP b j0 σ) (BlockCubeInstance.pairκ j0) c *
        ∏ r ∈ range (j0 / 2), BlockCubeInstance.Wfac (BlockCubeInstance.pairB b)
          (fun _ r x => SwapCollatz.collatzPhase lam (σ + 1 + t) (WeightedChain.uInv (σ + 1 + t))
            (2 * r + 1) x) c r ^ 2 ≤
      (if ((range (j0 / 2)).filter (OddBlack.ShapeGood b N0 c)).card < K then
          BlockCubeInstance.nCls (PrefixCollision.shellP b j0 σ) (BlockCubeInstance.pairκ j0) c else 0) +
        (2 : ℝ) ^ (-Λ) * ∑ P ∈ (PrefixCollision.shellP b j0 σ).filter
          (fun P => BlockCubeInstance.pairκ j0 P = c), (3 : ℝ) ^ OddBlack.Nodd b (σ + 1 + t) d lam P +
        BlockCubeInstance.nCls (PrefixCollision.shellP b j0 σ) (BlockCubeInstance.pairκ j0) c *
          Real.exp (-(4 * (1 - Real.cos (π * d)) / 3 * (K - Λ))) := by
  set m := σ + 1 + t
  set R := j0 / 2
  set w := BlockCubeInstance.nCls (PrefixCollision.shellP b j0 σ) (BlockCubeInstance.pairκ j0) c
  set W : ℕ → ℝ := fun r => BlockCubeInstance.Wfac (BlockCubeInstance.pairB b)
    (fun _ r x => SwapCollatz.collatzPhase lam m (WeightedChain.uInv m) (2 * r + 1) x) c r
  set Mc := ∑ P ∈ (PrefixCollision.shellP b j0 σ).filter (fun P => BlockCubeInstance.pairκ j0 P = c),
    (3 : ℝ) ^ OddBlack.Nodd b m d lam P
  set c0 := 1 - Real.cos (π * d)
  obtain ⟨hMc, hw⟩ := class_moment_eq b (t := t) hj (m := m) (d := d) (lam := lam) hc
  have hwpos : 0 < w := BlockCubeInstance.nCls_pos hc
  have hc0 : 0 ≤ c0 := by have := Real.cos_le_one (π * d); simp only [c0]; linarith
  have hW01 : ∀ r, 0 ≤ W r ∧ W r ≤ 1 := fun r => wfac_mem_unit _ _
  have hprodW1 : ∏ r ∈ range R, W r ^ 2 ≤ 1 :=
    prod_le_one (fun r _ => by have := hW01 r; positivity)
      (fun r _ => by have := hW01 r; nlinarith)
  have hprodW0 : 0 ≤ ∏ r ∈ range R, W r ^ 2 := prod_nonneg fun r _ => sq_nonneg _
  have hMc0 : 0 ≤ Mc := sum_nonneg fun _ _ => by positivity
  have hexp0 : 0 ≤ w * Real.exp (-(4 * c0 / 3 * (K - Λ))) := by positivity
  have h2Λ : 0 ≤ (2 : ℝ) ^ (-Λ) * Mc := by positivity
  -- all blocks are nonempty
  have hcardpos : ∀ r : Fin R, (0 : ℝ) < (BlockCubeInstance.pairB b c r).card := by
    intro r
    rcases (Nat.cast_nonneg (BlockCubeInstance.pairB b c r).card : (0 : ℝ) ≤ _).eq_or_lt with h0 | h0
    · exfalso
      have : ∏ r : Fin R, ((BlockCubeInstance.pairB b c r).card : ℝ) = 0 :=
        prod_eq_zero (mem_univ r) h0.symm
      rw [← hw] at this; linarith
    · exact h0
  split_ifs with hK
  · -- few shape-good blocks
    have : w * ∏ r ∈ range R, W r ^ 2 ≤ w := by nlinarith
    linarith
  · push Not at hK
    -- number of blocks of size ≥ 2
    set G : ℕ := ((range R).filter (fun r => 2 ≤ (BlockCubeInstance.pairB b c r).card)).card
    have hGK : K ≤ G := by
      refine hK.trans (card_le_card fun r hr => ?_)
      simp only [mem_filter] at hr ⊢
      exact ⟨hr.1, card_pairB_ge_two_of_shapeGood b hr.2⟩
    set tt : ℝ := ∑ r ∈ range R, (Mw b m d lam c r : ℝ) / (BlockCubeInstance.pairB b c r).card
    -- contraction
    have hcontr : ∏ r ∈ range R, W r ^ 2 ≤ Real.exp (-(4 * c0 * tt)) := by
      calc ∏ r ∈ range R, W r ^ 2
          ≤ ∏ r ∈ range R, Real.exp (-(4 * c0 * (Mw b m d lam c r : ℝ) /
              (BlockCubeInstance.pairB b c r).card)) :=
            prod_le_prod (fun r _ => sq_nonneg _) (fun r _ => wfac_sq_le_exp b hd0 c r)
        _ = Real.exp (-(4 * c0 * tt)) := by
            rw [← Real.exp_sum]; congr 1; simp only [tt, mul_sum]; rw [← sum_neg_distrib]
            refine sum_congr rfl fun r _ => ?_; ring
    -- exchange
    set Y : ℝ := ∏ r ∈ range R, (1 + 2 * ((darkSet b m d lam c r).card : ℝ) /
      (BlockCubeInstance.pairB b c r).card)
    have hwY : w * Y = Mc := by
      rw [show w = _ from hw, show Mc = _ from hMc]
      have hY : Y = ∏ r : Fin R, (1 + 2 * ((darkSet b m d lam c r).card : ℝ) /
          (BlockCubeInstance.pairB b c r).card) :=
        (Fin.prod_univ_eq_prod_range (fun r => (1 + 2 * ((darkSet b m d lam c r).card : ℝ) /
          (BlockCubeInstance.pairB b c r).card)) R).symm
      rw [hY, ← prod_mul_distrib]
      refine prod_congr rfl fun r _ => ?_
      have := (hcardpos r).ne'
      field_simp
    have hexch : Real.exp (Real.log 2 * ((G : ℝ) - 3 * tt)) ≤ Y := by
      have hG : (G : ℝ) = ∑ r ∈ range R,
          (if 2 ≤ (BlockCubeInstance.pairB b c r).card then (1 : ℝ) else 0) := by
        simp only [G]; rw [sum_boole]
      calc Real.exp (Real.log 2 * ((G : ℝ) - 3 * tt))
          = ∏ r ∈ range R, Real.exp (Real.log 2 * ((if 2 ≤ (BlockCubeInstance.pairB b c r).card
              then (1 : ℝ) else 0) - 3 * (Mw b m d lam c r : ℝ) / (BlockCubeInstance.pairB b c r).card)) := by
            rw [← Real.exp_sum]; congr 1
            rw [hG]; simp only [tt, mul_sub, Finset.mul_sum, ← Finset.sum_sub_distrib]
            refine sum_congr rfl fun r _ => ?_; ring
        _ ≤ Y := prod_le_prod (fun r _ => (Real.exp_pos _).le) (fun r _ => exp_block_le b c r)
    by_cases hY : (2 : ℝ) ^ Λ ≤ Y
    · have h1 : w * ∏ r ∈ range R, W r ^ 2 ≤ w := by nlinarith
      have h2 : w ≤ (2 : ℝ) ^ (-Λ) * Mc := by
        rw [← hwY, Real.rpow_neg (by norm_num)]
        have h2pos : (0 : ℝ) < (2 : ℝ) ^ Λ := by positivity
        rw [inv_mul_eq_div, le_div_iff₀ h2pos]; nlinarith
      linarith
    · push Not at hY
      have hlt : (G : ℝ) - 3 * tt < Λ := by
        have h := lt_of_le_of_lt hexch hY
        rw [Real.rpow_def_of_pos (by norm_num), Real.exp_lt_exp] at h
        have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
        nlinarith
      have hGr : (K : ℝ) ≤ G := by exact_mod_cast hGK
      have htt : (K - Λ) / 3 ≤ tt := by linarith
      have hmono : Real.exp (-(4 * c0 * tt)) ≤ Real.exp (-(4 * c0 / 3 * (K - Λ))) := by
        apply Real.exp_le_exp.mpr; nlinarith
      have : w * ∏ r ∈ range R, W r ^ 2 ≤ w * Real.exp (-(4 * c0 / 3 * (K - Λ))) :=
        mul_le_mul_of_nonneg_left (hcontr.trans hmono) hwpos.le
      linarith

end ClassLevel

/-! ## 5. `LowFreqDecay` from ShapeTail and summed pressure, without `N₀` loss -/

section Decay

variable (b : ℕ → ℕ)

open Classical in
/-- **Class average.** `∑_c w_c ∏ W² ≤ ρ₁|P| + 2^{−Λ} ∑_P 3^{N_odd} + |P| exp(−(4c₀/3)(K − Λ))`. -/
theorem avg_prod_sq_le_multi {j0 σ t N0 K : ℕ} (hj : 1 ≤ j0) {d : ℝ} (hd0 : 0 ≤ d) {lam : ℕ}
    {ρ₁ Λ : ℝ} (hshape : OddBlack.ShapeTail b j0 σ N0 K ρ₁) :
    ∑ c ∈ (PrefixCollision.shellP b j0 σ).image (BlockCubeInstance.pairκ j0),
        BlockCubeInstance.nCls (PrefixCollision.shellP b j0 σ) (BlockCubeInstance.pairκ j0) c *
          ∏ r ∈ range (j0 / 2), BlockCubeInstance.Wfac (BlockCubeInstance.pairB b)
            (fun _ r x => SwapCollatz.collatzPhase lam (σ + 1 + t) (WeightedChain.uInv (σ + 1 + t))
              (2 * r + 1) x) c r ^ 2 ≤
      ρ₁ * ((PrefixCollision.shellP b j0 σ).card : ℝ) +
        (2 : ℝ) ^ (-Λ) * ∑ P ∈ PrefixCollision.shellP b j0 σ,
          (3 : ℝ) ^ OddBlack.Nodd b (σ + 1 + t) d lam P +
        ((PrefixCollision.shellP b j0 σ).card : ℝ) *
          Real.exp (-(4 * (1 - Real.cos (π * d)) / 3 * (K - Λ))) := by
  set T := PrefixCollision.shellP b j0 σ
  set κ := BlockCubeInstance.pairκ j0
  set Cl := T.image κ
  set w := BlockCubeInstance.nCls T κ
  refine (sum_le_sum fun c hc => class_split b (t := t) (N0 := N0) (K := K) hj hd0 (lam := lam)
    (Λ := Λ) hc).trans ?_
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← sum_mul]
  have h1 : ∑ c ∈ Cl, (if ((range (j0 / 2)).filter (OddBlack.ShapeGood b N0 c)).card < K
      then w c else 0) ≤ ρ₁ * (T.card : ℝ) := by
    rw [← sum_filter]; exact hshape
  have h2 : ∑ c ∈ Cl, ∑ P ∈ T.filter (fun P => κ P = c), (3 : ℝ) ^ OddBlack.Nodd b (σ + 1 + t) d lam P =
      ∑ P ∈ T, (3 : ℝ) ^ OddBlack.Nodd b (σ + 1 + t) d lam P :=
    sum_fiberwise_of_maps_to (fun P hP => mem_image_of_mem κ hP) _
  have h3 : ∑ c ∈ Cl, w c = (T.card : ℝ) := BlockCubeInstance.sum_nCls T κ
  rw [h2, h3]
  linarith

open Classical in
/-- **`ShapeTail` + frequency-summed pressure ⇒ `LowFreqDecay`, multi-pair version.**  No `N₀` in the
rate: with `c₀ = 1 − cos πd`, it suffices that `ρ₁ + M 2^{−Λ} + exp(−(4c₀/3)(K − Λ)) ≤ C 2^{−γ j}`. -/
theorem lowFreqDecay_multi {j σ t U N0 K : ℕ} {d ρ₁ Λ M C γ : ℝ} (hj : 1 ≤ j)
    (hne : (PrefixCollision.shellP b j σ).Nonempty) (hd0 : 0 ≤ d)
    (hshape : OddBlack.ShapeTail b j σ N0 K ρ₁)
    (hpress : ∀ u ≤ U, ∑ lam ∈ ShellDecomposition.cshell (σ + 1) t u,
        ∑ P ∈ PrefixCollision.shellP b j σ, (3 : ℝ) ^ OddBlack.Nodd b (σ + 1 + t) d lam P ≤
      2 ^ (u + 1) * M * ((PrefixCollision.shellP b j σ).card : ℝ))
    (hrate : ρ₁ + M * (2 : ℝ) ^ (-Λ) + Real.exp (-(4 * (1 - Real.cos (π * d)) / 3 * (K - Λ))) ≤
      C * (2 : ℝ) ^ (-(γ * j))) :
    DecayInterface.LowFreqDecay b j σ t U C γ := by
  intro u hu
  set T := PrefixCollision.shellP b j σ
  set P2 : ℝ := (T.card : ℝ) ^ 2
  set E := Real.exp (-(4 * (1 - Real.cos (π * d)) / 3 * (K - Λ)))
  have hT : (0 : ℝ) < T.card := by exact_mod_cast hne.card_pos
  have hP2 : 0 ≤ P2 := by positivity
  have hwsum : ∑ c ∈ T.image (BlockCubeInstance.pairκ j),
      BlockCubeInstance.nCls T (BlockCubeInstance.pairκ j) c = (T.card : ℝ) := BlockCubeInstance.sum_nCls T _
  obtain ⟨hwpos, hbd⟩ := BlockCubeInstance.blockCubeHyp_pair b j σ t U hj hne
  have hpt : ∀ lam ∈ ShellDecomposition.cshell (σ + 1) t u,
      ‖TwistExpansion.Psi T (σ + 1) t (WeightedChain.yPrime j σ t) lam‖ ^ 2 ≤
        P2 * (ρ₁ + E) + P2 * ((2 : ℝ) ^ (-Λ) *
          (∑ P ∈ T, (3 : ℝ) ^ OddBlack.Nodd b (σ + 1 + t) d lam P) / T.card) := by
    intro lam hlam
    have havg := avg_prod_sq_le_multi b (t := t) (N0 := N0) (K := K) hj hd0 (lam := lam) (Λ := Λ) hshape
    have hdiv : (∑ c ∈ T.image (BlockCubeInstance.pairκ j),
        BlockCubeInstance.nCls T (BlockCubeInstance.pairκ j) c *
          ∏ r ∈ range (j / 2), BlockCubeInstance.Wfac (BlockCubeInstance.pairB b)
            (fun _ r x => SwapCollatz.collatzPhase lam (σ + 1 + t) (WeightedChain.uInv (σ + 1 + t))
              (2 * r + 1) x) c r ^ 2) / ∑ c ∈ T.image (BlockCubeInstance.pairκ j),
          BlockCubeInstance.nCls T (BlockCubeInstance.pairκ j) c ≤
        ρ₁ + E + (2 : ℝ) ^ (-Λ) * (∑ P ∈ T, (3 : ℝ) ^ OddBlack.Nodd b (σ + 1 + t) d lam P) / T.card := by
      rw [hwsum, div_le_iff₀ hT]
      have e : (ρ₁ + E + (2 : ℝ) ^ (-Λ) * (∑ P ∈ T, (3 : ℝ) ^ OddBlack.Nodd b (σ + 1 + t) d lam P) /
          T.card) * T.card = ρ₁ * T.card + (2 : ℝ) ^ (-Λ) *
            (∑ P ∈ T, (3 : ℝ) ^ OddBlack.Nodd b (σ + 1 + t) d lam P) + T.card * E := by
        field_simp; ring
      rw [e]; exact havg
    calc _ ≤ P2 * _ := hbd u hu lam hlam
      _ ≤ P2 * (ρ₁ + E + (2 : ℝ) ^ (-Λ) *
            (∑ P ∈ T, (3 : ℝ) ^ OddBlack.Nodd b (σ + 1 + t) d lam P) / T.card) :=
          mul_le_mul_of_nonneg_left hdiv hP2
      _ = _ := by ring
  have hcard : ((ShellDecomposition.cshell (σ + 1) t u).card : ℝ) ≤ 2 ^ (u + 1) := by
    exact_mod_cast ShellDecomposition.card_cshell_le (σ + 1) t u
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hρ0 : 0 ≤ ρ₁ + E := by
    have := hshape
    by_contra hneg
    push Not at hneg
    have hρneg : ρ₁ < 0 := by linarith
    have h0 : (0 : ℝ) ≤ ρ₁ * T.card := le_trans (sum_nonneg fun c _ => by
      unfold BlockCubeInstance.nCls; positivity) hshape
    nlinarith
  have h2Λ : (0 : ℝ) ≤ (2 : ℝ) ^ (-Λ) := by positivity
  calc ∑ lam ∈ ShellDecomposition.cshell (σ + 1) t u,
        ‖TwistExpansion.Psi T (σ + 1) t (WeightedChain.yPrime j σ t) lam‖ ^ 2
      ≤ ∑ lam ∈ ShellDecomposition.cshell (σ + 1) t u, (P2 * (ρ₁ + E) + P2 * ((2 : ℝ) ^ (-Λ) *
          (∑ P ∈ T, (3 : ℝ) ^ OddBlack.Nodd b (σ + 1 + t) d lam P) / T.card)) := sum_le_sum hpt
    _ = ((ShellDecomposition.cshell (σ + 1) t u).card : ℝ) * (P2 * (ρ₁ + E)) +
          P2 * (2 : ℝ) ^ (-Λ) / T.card * ∑ lam ∈ ShellDecomposition.cshell (σ + 1) t u,
            ∑ P ∈ T, (3 : ℝ) ^ OddBlack.Nodd b (σ + 1 + t) d lam P := by
        rw [sum_add_distrib, sum_const, nsmul_eq_mul, mul_sum]
        congr 1; refine sum_congr rfl fun lam _ => ?_; ring
    _ ≤ 2 ^ (u + 1) * (P2 * (ρ₁ + E)) + P2 * (2 : ℝ) ^ (-Λ) / T.card * (2 ^ (u + 1) * M * T.card) := by
        gcongr
        exact hpress u hu
    _ = 2 ^ (u + 1) * P2 * (ρ₁ + M * (2 : ℝ) ^ (-Λ) + E) := by field_simp; ring
    _ ≤ 2 ^ (u + 1) * P2 * (C * (2 : ℝ) ^ (-(γ * j))) := by gcongr
    _ = _ := by simp only [P2]; ring

end Decay

end MultiWhite
end EOC
