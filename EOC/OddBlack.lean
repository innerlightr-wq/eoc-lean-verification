import EOC.WhiteContraction

/-!
# Odd-cell dark count ⇒ `CriticalWhiteCount`

The white-count round reduced the analytic input to `WhiteContraction.CriticalWhiteCount` (a
class-weighted lower tail for the number of good pair blocks).  This file splits that hypothesis
into a purely combinatorial **shape** tail and an **exponential moment of the word's own dark
odd cells**, and proves the implication.

* `card_filter_ge_mul_pow_le`, `card_filter_le_mul_pow_le` — finite Chernoff (Markov) bounds.
* `card_pairB_le_elig_add_one` — the internal choice set of a pair block is an interval, so all but
  at most one admissible choice `x` has `x + 1` admissible.
* `sum_class_prod` — every coarse class is a product set: the class sum of a block-product equals
  the product of the block sums.
* `goodCount_ge` — `#good ≥ #shape − #bad` (a good block is a shape-good block that is not bad).
* `sum_class_pow_nodd_ge` — for `s ≥ 1`, `∑_{P ∈ class c} s^{N_odd(P)} ≥ |c| · ((1+s)/2)^{#bad(c)}`:
  in a bad block every eligible choice is dark and at least half of the choices are eligible.
* `criticalWhiteCount_of_shape_and_oddPressure` — `ShapeTail + OddDarkPressure ⇒
  CriticalWhiteCount`, hence (via `WhiteContraction.weightedFourier_of_criticalWhiteCount`)
  `WeightedFourier`.
* `nodd_one_le_ntao` — at `λ = 1`, `d = η/2`, the dark count is at most the number of Tao-black odd
  path cells `(m − S_{2r+1}, 2r+2)` (under the smallness side condition), so a Tao-cell exponential
  moment bound gives `OddDarkPressure` at `λ = 1`.

`ShapeTail` is PROVED (LEAN) for the Collatz barrier at every even `j₀ ≥ 300`
(`EOC.ShapeUnconditional.shapeTail_allEven`, via `ShapeTail`/`ShapeBridge`/`ShapeCertificate`);
`OddDarkPressure` is OPEN for the true environment.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace OddBlack

open Finset TriangleArray MaxTriangle PrefixCollision ShellDecomposition WhiteContraction

/-! ## 1. Finite Chernoff bounds -/

theorem card_filter_ge_mul_pow_le {ι : Type*} (T : Finset ι) (f : ι → ℕ) {s : ℝ} (hs : 1 ≤ s)
    (n : ℕ) : ((T.filter (fun i => n ≤ f i)).card : ℝ) * s ^ n ≤ ∑ i ∈ T, s ^ f i := by
  have h0 : ∀ i ∈ T, (0 : ℝ) ≤ s ^ f i := fun i _ => by positivity
  calc ((T.filter (fun i => n ≤ f i)).card : ℝ) * s ^ n
      = ∑ i ∈ T.filter (fun i => n ≤ f i), s ^ n := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ T.filter (fun i => n ≤ f i), s ^ f i :=
        sum_le_sum fun i hi => pow_le_pow_right₀ hs (mem_filter.mp hi).2
    _ ≤ ∑ i ∈ T, s ^ f i := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun i hi _ => h0 i hi)

theorem card_filter_le_mul_pow_le {ι : Type*} (T : Finset ι) (f : ι → ℕ) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t ≤ 1) (n : ℕ) :
    ((T.filter (fun i => f i ≤ n)).card : ℝ) * t ^ n ≤ ∑ i ∈ T, t ^ f i := by
  have h0 : ∀ i ∈ T, (0 : ℝ) ≤ t ^ f i := fun i _ => by positivity
  calc ((T.filter (fun i => f i ≤ n)).card : ℝ) * t ^ n
      = ∑ i ∈ T.filter (fun i => f i ≤ n), t ^ n := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ T.filter (fun i => f i ≤ n), t ^ f i :=
        sum_le_sum fun i hi => pow_le_pow_of_le_one ht0.le ht1 (mem_filter.mp hi).2
    _ ≤ ∑ i ∈ T, t ^ f i := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun i hi _ => h0 i hi)

/-! ## 2. Product classes -/

/-- The class sum of a block product is the product of the block sums. -/
theorem sum_class_prod {ι β : Type*} [DecidableEq β] (T : Finset ι) (κ : ι → β)
    (B : β → ℕ → Finset ℕ) {R : ℕ} (π : ι → Fin R → ℕ) {c : β}
    (hinj : Set.InjOn π ↑(T.filter (fun i => κ i = c)))
    (himg : (T.filter (fun i => κ i = c)).image π = Fintype.piFinset (fun r : Fin R => B c r))
    (g : Fin R → ℕ → ℝ) :
    ∑ i ∈ T.filter (fun i => κ i = c), ∏ r : Fin R, g r (π i r) =
      ∏ r : Fin R, ∑ x ∈ B c r, g r x := by
  rw [prod_univ_sum, ← himg, sum_image (fun x hx y hy h => hinj hx hy h)]

/-! ## 3. Eligible choices -/

section Blocks

variable (b : ℕ → ℕ)

/-- Eligible internal choices of pair block `r`: `x` admissible with `x + 1` admissible. -/
def Elig {j0 : ℕ} (c : Fin (j0 + 1) → ℕ) (r : ℕ) : Finset ℕ :=
  (BlockCubeInstance.pairB b c r).filter (fun x => x + 1 ∈ BlockCubeInstance.pairB b c r)

theorem elig_subset {j0 : ℕ} (c : Fin (j0 + 1) → ℕ) (r : ℕ) :
    Elig b c r ⊆ BlockCubeInstance.pairB b c r := filter_subset _ _

/-- The choice set is an interval: at most one admissible choice is not eligible. -/
theorem card_pairB_le_elig_add_one {j0 : ℕ} (c : Fin (j0 + 1) → ℕ) (r : ℕ) :
    (BlockCubeInstance.pairB b c r).card ≤ (Elig b c r).card + 1 := by
  set B := BlockCubeInstance.pairB b c r
  have hsplit := card_filter_add_card_filter_not (s := B) (fun x => x + 1 ∈ B)
  have hle : (B.filter (fun x => ¬ (x + 1 ∈ B))).card ≤ 1 := by
    refine card_le_one.mpr fun x hx y hy => ?_
    simp only [mem_filter] at hx hy
    have key : ∀ u v, u ∈ B → v ∈ B → u < v → u + 1 ∈ B := by
      intro u v hu hv huv
      simp only [B, BlockCubeInstance.pairB, mem_filter, mem_Ioo] at hu hv ⊢
      exact ⟨⟨by omega, by omega⟩, by omega⟩
    rcases lt_trichotomy x y with h | h | h
    · exact absurd (key x y hx.1 hy.1 h) hx.2
    · exact h
    · exact absurd (key y x hy.1 hx.1 h) hy.2
  change B.card ≤ (B.filter (fun x => x + 1 ∈ B)).card + 1
  omega

/-- If some choice is eligible, at least half of the choices are eligible. -/
theorem card_pairB_le_two_mul_elig {j0 : ℕ} {c : Fin (j0 + 1) → ℕ} {r : ℕ}
    (hne : (Elig b c r).Nonempty) :
    (BlockCubeInstance.pairB b c r).card ≤ 2 * (Elig b c r).card := by
  have h1 := card_pairB_le_elig_add_one b c r
  have h2 := card_pos.mpr hne
  omega

/-! ## 4. Shape-good, dark, bad -/

/-- The phase pair `(x, x+1)` of block `r` is **dark** at frequency `λ`: phase difference within `d`
of an integer. -/
def Dark (m : ℕ) (d : ℝ) (lam r x : ℕ) : Prop :=
  distZ (pairPhase lam m (2 * r + 1) x - pairPhase lam m (2 * r + 1) (x + 1)) < d

/-- Shape-good block: at most `N₀` choices and at least one eligible choice. -/
def ShapeGood (N0 : ℕ) {j0 : ℕ} (c : Fin (j0 + 1) → ℕ) (r : ℕ) : Prop :=
  (BlockCubeInstance.pairB b c r).card ≤ N0 ∧ (Elig b c r).Nonempty

/-- Bad block: shape-good with every eligible choice dark. -/
def BadPair (m N0 : ℕ) (d : ℝ) (lam : ℕ) {j0 : ℕ} (c : Fin (j0 + 1) → ℕ) (r : ℕ) : Prop :=
  ShapeGood b N0 c r ∧ ∀ x ∈ Elig b c r, Dark m d lam r x

theorem goodPair_of_shape_not_bad {m N0 : ℕ} {d : ℝ} {lam j0 : ℕ} {c : Fin (j0 + 1) → ℕ} {r : ℕ}
    (hs : ShapeGood b N0 c r) (hnb : ¬ BadPair b m N0 d lam c r) :
    GoodPair b m N0 d lam c r := by
  unfold BadPair at hnb
  push Not at hnb
  obtain ⟨x, hx, hnd⟩ := hnb hs
  have hx' := mem_filter.mp hx
  refine ⟨hs.1, x, hx'.1, hx'.2, ?_⟩
  unfold Dark at hnd
  exact not_lt.mp hnd

open Classical in
/-- `#good ≥ #shape − #bad`, over any index set. -/
theorem goodCount_ge {m N0 : ℕ} {d : ℝ} {lam j0 : ℕ} (c : Fin (j0 + 1) → ℕ) (I : Finset ℕ) :
    (I.filter (ShapeGood b N0 c)).card ≤
      (I.filter (GoodPair b m N0 d lam c)).card + (I.filter (BadPair b m N0 d lam c)).card := by
  calc (I.filter (ShapeGood b N0 c)).card
      ≤ ((I.filter (GoodPair b m N0 d lam c)) ∪ (I.filter (BadPair b m N0 d lam c))).card := by
        refine card_le_card fun r hr => ?_
        obtain ⟨hrI, hsr⟩ := mem_filter.mp hr
        by_cases hb : BadPair b m N0 d lam c r
        · exact mem_union_right _ (mem_filter.mpr ⟨hrI, hb⟩)
        · exact mem_union_left _ (mem_filter.mpr ⟨hrI, goodPair_of_shape_not_bad b hsr hb⟩)
    _ ≤ _ := card_union_le _ _

/-! ## 5. The word's own dark odd cells -/

/-- Word `P`'s own odd choice `S_{2r+1}` in block `r` is eligible and dark. -/
def OwnDark (m : ℕ) (d : ℝ) (lam : ℕ) {j0 : ℕ} (P : FiniteValuationWord j0) (r : ℕ) : Prop :=
  P.prefixSum (2 * r + 1) ∈ Elig b (BlockCubeInstance.pairκ j0 P) r ∧
    Dark m d lam r (P.prefixSum (2 * r + 1))

open Classical in
/-- **`N_odd`**: number of pair blocks whose own odd choice is eligible and dark. -/
noncomputable def Nodd (m : ℕ) (d : ℝ) (lam : ℕ) {j0 : ℕ} (P : FiniteValuationWord j0) : ℕ :=
  ((range (j0 / 2)).filter (OwnDark b m d lam P)).card

open Classical in
theorem pow_card_filter_eq_prod {s : ℝ} (n : ℕ) (p : ℕ → Prop) :
    s ^ ((range n).filter p).card = ∏ r : Fin n, (if p r then s else 1) := by
  rw [Fin.prod_univ_eq_prod_range (fun r => if p r then s else 1), prod_ite, prod_const_one,
    mul_one, prod_const]

open Classical in
/-- **Class lower bound.**  For `s ≥ 1` and a class `c` of the confined prefix shell,
`∑_{P ∈ c} s^{N_odd(P)} ≥ |c| · ((1+s)/2)^{#bad blocks of c}`. -/
theorem sum_class_pow_nodd_ge {j0 σ t : ℕ} (hj : 1 ≤ j0) {m N0 : ℕ} {d s : ℝ} {lam : ℕ}
    (hs : 1 ≤ s) {c : Fin (j0 + 1) → ℕ}
    (hc : c ∈ (shellP b j0 σ).image (BlockCubeInstance.pairκ j0)) :
    BlockCubeInstance.nCls (shellP b j0 σ) (BlockCubeInstance.pairκ j0) c *
        ((1 + s) / 2) ^ ((range (j0 / 2)).filter (BadPair b m N0 d lam c)).card ≤
      ∑ P ∈ (shellP b j0 σ).filter (fun P => BlockCubeInstance.pairκ j0 P = c),
        s ^ Nodd b m d lam P := by
  set D := BlockCubeInstance.pairDecomposition b j0 σ t hj
  set F := (shellP b j0 σ).filter (fun P => BlockCubeInstance.pairκ j0 P = c)
  -- per-block weight
  let g : Fin (j0 / 2) → ℕ → ℝ := fun r x =>
    if x ∈ Elig b c r ∧ Dark m d lam r x then s else 1
  have hword : ∀ P ∈ F,
      s ^ Nodd b m d lam P = ∏ r : Fin (j0 / 2), g r (BlockCubeInstance.pairπ j0 P r) := by
    intro P hP
    have hκ : BlockCubeInstance.pairκ j0 P = c := (mem_filter.mp hP).2
    unfold Nodd
    rw [pow_card_filter_eq_prod]
    refine prod_congr rfl fun r _ => ?_
    simp only [g, OwnDark, hκ, BlockCubeInstance.pairπ]
  have hprod := sum_class_prod (shellP b j0 σ) (BlockCubeInstance.pairκ j0)
    (BlockCubeInstance.pairB b)
    (BlockCubeInstance.pairπ j0) (D.inj c hc) (D.image_eq c hc) g
  have hcard := sum_class_prod (shellP b j0 σ) (BlockCubeInstance.pairκ j0)
    (BlockCubeInstance.pairB b)
    (BlockCubeInstance.pairπ j0) (D.inj c hc) (D.image_eq c hc) (fun _ _ => (1 : ℝ))
  simp only [prod_const_one, sum_const, nsmul_eq_mul, mul_one] at hcard
  -- nCls = ∏ |B r|
  have hn : BlockCubeInstance.nCls (shellP b j0 σ) (BlockCubeInstance.pairκ j0) c =
      ∏ r : Fin (j0 / 2), ((BlockCubeInstance.pairB b c r).card : ℝ) := by
    unfold BlockCubeInstance.nCls; exact hcard
  rw [sum_congr rfl hword, hprod, hn, pow_card_filter_eq_prod, ← prod_mul_distrib]
  refine prod_le_prod (fun r _ => by
      have : (0 : ℝ) ≤ (if BadPair b m N0 d lam c r then (1 + s) / 2 else 1) := by
        split_ifs <;> linarith
      positivity) fun r _ => ?_
  have hg1 : ∀ x, 1 ≤ g r x := fun x => by simp only [g]; split_ifs <;> linarith
  split_ifs with hbad
  · -- bad block: every eligible choice is dark
    obtain ⟨hshape, hdark⟩ := hbad
    have h2 := card_pairB_le_two_mul_elig b hshape.2
    set B := BlockCubeInstance.pairB b c r
    set E := Elig b c r
    have hEsub : E ⊆ B := elig_subset b c r
    have hsum : ∑ x ∈ B, g r x = (E.card : ℝ) * s + ((B.card : ℝ) - E.card) := by
      rw [← sum_filter_add_sum_filter_not B (fun x => x ∈ E)]
      have hfE : B.filter (fun x => x ∈ E) = E := by
        ext x; simp only [mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hEsub h, h⟩⟩
      have h1 : ∑ x ∈ B.filter (fun x => x ∈ E), g r x = (E.card : ℝ) * s := by
        rw [hfE, ← nsmul_eq_mul, ← sum_const]
        refine sum_congr rfl fun x hx => ?_
        simp only [g]; exact ite_eq_left ⟨hx, hdark x hx⟩
      have h2' : ∑ x ∈ B.filter (fun x => ¬ x ∈ E), g r x = (B.card : ℝ) - E.card := by
        have : ∀ x ∈ B.filter (fun x => ¬ x ∈ E), g r x = 1 := by
          intro x hx
          simp only [g]; exact ite_eq_right (fun h => (mem_filter.mp hx).2 h.1)
        rw [sum_congr rfl this, sum_const, nsmul_eq_mul, mul_one]
        have hc2 := card_filter_add_card_filter_not (s := B) (fun x => x ∈ E)
        rw [hfE] at hc2
        have : ((B.filter (fun x => ¬ x ∈ E)).card : ℝ) = (B.card : ℝ) - E.card := by
          rw [← hc2]; push_cast; ring
        exact this
      rw [h1, h2']
    rw [hsum]
    have h2r : (B.card : ℝ) ≤ 2 * E.card := by exact_mod_cast h2
    nlinarith
  · -- other blocks: every weight is ≥ 1
    calc ((BlockCubeInstance.pairB b c r).card : ℝ) * 1
        = ∑ x ∈ BlockCubeInstance.pairB b c r, (1 : ℝ) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ BlockCubeInstance.pairB b c r, g r x := sum_le_sum fun x _ => hg1 x

/-! ## 6. The interface -/

open Classical in
/-- **Shape tail** (λ-independent; PROVED (MATH) in the pressure round, not formalized): at most a
`ρ₁` fraction of the confined prefix shell (class-weighted) has fewer than `K` shape-good blocks. -/
def ShapeTail (j0 σ N0 K : ℕ) (ρ₁ : ℝ) : Prop :=
  ∑ c ∈ ((shellP b j0 σ).image (BlockCubeInstance.pairκ j0)).filter
      (fun c => ((range (j0 / 2)).filter (ShapeGood b N0 c)).card < K),
    BlockCubeInstance.nCls (shellP b j0 σ) (BlockCubeInstance.pairκ j0) c ≤
  ρ₁ * ((shellP b j0 σ).card : ℝ)

/-- **Odd dark pressure** (OPEN for the true environment): for every low frequency, the exponential
moment of the word's own dark odd cells is at most `M · |P_σ|`. -/
def OddDarkPressure (j0 σ t U : ℕ) (d s M : ℝ) : Prop :=
  ∀ u ≤ U, ∀ lam ∈ cshell (σ + 1) t u,
    ∑ P ∈ shellP b j0 σ, s ^ Nodd b (σ + 1 + t) d lam P ≤ M * ((shellP b j0 σ).card : ℝ)

open Classical in
/-- **`ShapeTail + OddDarkPressure ⇒ CriticalWhiteCount`.**  If fewer than `k + n` shape-good blocks
has class-weighted frequency `≤ ρ₁`, and `∑ s^{N_odd} ≤ M |P_σ|` with `M ≤ ρ₂ ((1+s)/2)^n`, then at
most a `ρ₁ + ρ₂` fraction has fewer than `k` good blocks. -/
theorem criticalWhiteCount_of_shape_and_oddPressure {j0 σ t U N0 k n : ℕ} {d s M ρ₁ ρ₂ : ℝ}
    (hj : 1 ≤ j0) (hs : 1 ≤ s) (hshape : ShapeTail b j0 σ N0 (k + n) ρ₁)
    (hodd : OddDarkPressure b j0 σ t U d s M) (hM : M ≤ ρ₂ * ((1 + s) / 2) ^ n) :
    CriticalWhiteCount b j0 σ t U N0 d k (ρ₁ + ρ₂) := by
  intro u hu lam hlam
  set T := shellP b j0 σ
  set κ := BlockCubeInstance.pairκ j0
  set C := T.image κ
  set w := BlockCubeInstance.nCls T κ
  set good := fun c => ((range (j0 / 2)).filter (GoodPair b (σ + 1 + t) N0 d lam c)).card
  set shp := fun c => ((range (j0 / 2)).filter (ShapeGood b N0 c)).card
  set bad := fun c => ((range (j0 / 2)).filter (BadPair b (σ + 1 + t) N0 d lam c)).card
  have hw0 : ∀ c, 0 ≤ w c := fun c => by unfold w BlockCubeInstance.nCls; positivity
  have htot : ∑ c ∈ C, w c = (T.card : ℝ) := BlockCubeInstance.sum_nCls T κ
  have ha : (0 : ℝ) < (1 + s) / 2 := by linarith
  -- split: few good ⇒ few shape-good or many bad
  have hsplit : ∑ c ∈ C.filter (fun c => good c < k), w c ≤
      ∑ c ∈ C.filter (fun c => shp c < k + n), w c + ∑ c ∈ C.filter (fun c => n ≤ bad c), w c := by
    rw [sum_filter, sum_filter, sum_filter, ← sum_add_distrib]
    refine sum_le_sum fun c _ => ?_
    have hgc := goodCount_ge b (m := σ + 1 + t) (N0 := N0) (d := d) (lam := lam) c (range (j0 / 2))
    split_ifs with h1 h2 h3 h2 h3 <;> linarith [hw0 c]
  -- many bad: Chernoff over the class product
  have hbad : ∑ c ∈ C.filter (fun c => n ≤ bad c), w c * ((1 + s) / 2) ^ n ≤
      ∑ P ∈ T, s ^ Nodd b (σ + 1 + t) d lam P := by
    calc ∑ c ∈ C.filter (fun c => n ≤ bad c), w c * ((1 + s) / 2) ^ n
        ≤ ∑ c ∈ C.filter (fun c => n ≤ bad c), w c * ((1 + s) / 2) ^ bad c :=
          sum_le_sum fun c hc => mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ (by linarith) (mem_filter.mp hc).2) (hw0 c)
      _ ≤ ∑ c ∈ C, w c * ((1 + s) / 2) ^ bad c :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            (fun c _ _ => mul_nonneg (hw0 c) (pow_nonneg ha.le _))
      _ ≤ ∑ c ∈ C, ∑ P ∈ T.filter (fun P => κ P = c), s ^ Nodd b (σ + 1 + t) d lam P :=
          sum_le_sum fun c hc => sum_class_pow_nodd_ge b (t := t) hj hs hc
      _ = ∑ P ∈ T, s ^ Nodd b (σ + 1 + t) d lam P :=
          sum_fiberwise_of_maps_to (fun P hP => mem_image_of_mem κ hP) _
  have hbad2 : ∑ c ∈ C.filter (fun c => n ≤ bad c), w c ≤ ρ₂ * (T.card : ℝ) := by
    have h1 := hodd u hu lam hlam
    rw [← sum_mul] at hbad
    have hpos : (0 : ℝ) < ((1 + s) / 2) ^ n := pow_pos ha n
    have hT : (0 : ℝ) ≤ (T.card : ℝ) := Nat.cast_nonneg _
    have : (∑ c ∈ C.filter (fun c => n ≤ bad c), w c) * ((1 + s) / 2) ^ n ≤
        ρ₂ * (T.card : ℝ) * ((1 + s) / 2) ^ n := by
      calc _ ≤ M * (T.card : ℝ) := hbad.trans h1
        _ ≤ ρ₂ * ((1 + s) / 2) ^ n * (T.card : ℝ) := mul_le_mul_of_nonneg_right hM hT
        _ = ρ₂ * (T.card : ℝ) * ((1 + s) / 2) ^ n := by ring
    exact le_of_mul_le_mul_right this hpos
  have hsh : ∑ c ∈ C.filter (fun c => shp c < k + n), w c ≤ ρ₁ * (T.card : ℝ) := hshape
  change ∑ c ∈ C.filter (fun c => good c < k), w c ≤ (ρ₁ + ρ₂) * ∑ c ∈ C, w c
  rw [htot]
  linarith

/-- **`ShapeTail + OddDarkPressure ⇒ WeightedFourier`** (through `CriticalWhiteCount`). -/
theorem weightedFourier_of_shape_and_oddPressure {N j0 s σ U N0 k n : ℕ} {ε d sv M ρ₁ ρ₂ C γ : ℝ}
    (Nsplit : ℕ → ℕ) (hj : 1 ≤ j0) (hne : (shellP b j0 σ).Nonempty) (hd0 : 0 ≤ d) (hd1 : d ≤ 1 / 2)
    (hN : 2 ≤ N0) (hsv : 1 ≤ sv) (hshape : ShapeTail b j0 σ N0 (k + n) ρ₁)
    (hodd : OddDarkPressure b j0 σ (s - σ) U d sv M) (hM : M ≤ ρ₂ * ((1 + sv) / 2) ^ n)
    (hC0 : 0 ≤ C) (hrate : kappa d N0 ^ (2 * k) + (ρ₁ + ρ₂) ≤ C * (2 : ℝ) ^ (-(γ * j0)))
    (hN1 : ∀ u ∈ range (σ + 1 + (s - σ)), 1 ≤ Nsplit u)
    (hNj : ∀ u ∈ range (σ + 1 + (s - σ)), Nsplit u < j0)
    (hX : ∀ u ∈ range (σ + 1 + (s - σ)), 2 * PsiSieve.Xmax b (Nsplit u) ≤ 2 ^ (σ + 1 + (s - σ)))
    (hfin : (1 + ((σ + 1 : ℕ) : ℝ) / 2) * ∑ u ∈ range (σ + 1 + (s - σ)),
        min 1 (2 ^ (s - σ) / (2 * 2 ^ u)) *
          DecayInterface.mixedBound b j0 σ Nsplit (fun u => u ≤ U)
            (fun u => 2 ^ (u + 1) * C * (2 : ℝ) ^ (-(γ * j0)) * ((shellP b j0 σ).card : ℝ) ^ 2) u ≤
      ε ^ 2 * ((shellP b j0 σ).card : ℝ) ^ 2 * (shellV b N j0 σ (s - σ)).card / 2 ^ (s - σ)) :
    WeightedChain.WeightedFourier b N j0 s σ ε :=
  weightedFourier_of_criticalWhiteCount b Nsplit hj hne hd0 hd1 hN
    (criticalWhiteCount_of_shape_and_oddPressure b hj hsv hshape hodd hM) hC0 hrate hN1 hNj hX hfin

/-! ## 7. `λ = 1`: dark ⇒ Tao-black -/

open Classical in
/-- Number of blocks whose own odd path cell `(m − S_{2r+1}, 2r+2)` is Tao-black. -/
noncomputable def Ntao (m : ℕ) (η : ℝ) {j0 : ℕ} (P : FiniteValuationWord j0) : ℕ :=
  ((range (j0 / 2)).filter (fun r => black (m - P.prefixSum (2 * r + 1)) (2 * r + 2) η)).card

open Classical in
/-- At `λ = 1` and `d = η/2`, under the smallness side condition, a dark own cell is Tao-black:
`N_odd ≤ N_tao`. -/
theorem nodd_one_le_ntao {j0 : ℕ} (P : FiniteValuationWord j0) {m : ℕ} {η : ℝ}
    (hxm : ∀ r < j0 / 2, P.prefixSum (2 * r + 1) ≤ m)
    (hsmall : ∀ r < j0 / 2,
      (2 : ℝ) ^ (P.prefixSum (2 * r + 1)) / (2 ^ m * 3 ^ (2 * r + 2)) ≤ η / 2) :
    Nodd b m (η / 2) 1 P ≤ Ntao m η P := by
  unfold Nodd Ntao
  refine card_le_card fun r hr => ?_
  obtain ⟨hrr, _, hdark⟩ := mem_filter.mp hr
  refine mem_filter.mpr ⟨hrr, ?_⟩
  by_contra hw
  have hrlt := mem_range.mp hrr
  have h := distZ_phase_ge_of_white (m := m) (i := 2 * r + 1) (hxm r hrlt) hw
  rw [show 2 * r + 1 + 1 = 2 * r + 2 by omega] at h
  have hs := hsmall r hrlt
  unfold Dark at hdark
  linarith

end Blocks

end OddBlack
end EOC
