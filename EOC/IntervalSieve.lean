import EOC.TwistExpansion
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The deterministic core of the 3-adic interval sieve

Abstract, exact statements behind the interval-sieve bound (C3) for low-frequency averages of the
characteristic sums `Φ`:

* `dZ x = |x − round x|` — distance to the nearest integer.
* `norm_ee_sub_one_ge` — `4·dZ x ≤ ‖e(x) − 1‖`.
* `norm_sum_ee_le_dirichlet` — **Dirichlet-kernel bound**: if `dZ x > 0` then
  `‖∑_{k<H} e((a+k)x)‖ ≤ 1/(2·dZ x)`; `norm_sum_ee_le_card` — the trivial bound `≤ H`.
* `sum_sq_norm_le_pairs` — **pair expansion**:
  `∑_{k<H} ‖∑_{i∈T} e((a+k)ζ_i)‖^2 ≤ ∑_{i,j∈T} ‖∑_{k<H} e((a+k)(ζ_i − ζ_j))‖`.
* `grid_sieve` — **grid-spacing sieve**: if `ζ_i = A_i/q + δ_i` with `A_i ∈ ℤ`, `0 ≤ δ_i ≤ 1/(2q)`
  and every residue fibre of `A mod q` inside `T` has at most `μ` elements, then
  `∑_{k<H} ‖∑_{i∈T} e((a+k)ζ_i)‖^2 ≤ #T · μ · (H + 2q(1 + log q))`.
* `sqrt_sum_sq_sum_le` (Minkowski for nonnegative families) and `minkowski_step`:
  `√(∑_{λ∈I} ‖∑_{S∈U} F_S(λ) G_S(λ)‖^2) ≤ ∑_{S∈U} g_S √(∑_{λ∈I} ‖F_S(λ)‖^2)` when `‖G_S‖ ≤ g_S`.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace IntervalSieve

open Finset Real SwapBound TwistExpansion

/-! ## Distance to the nearest integer and the Dirichlet kernel -/

/-- Distance from `x` to the nearest integer. -/
noncomputable def dZ (x : ℝ) : ℝ := |x - round x|

theorem dZ_nonneg (x : ℝ) : 0 ≤ dZ x := abs_nonneg _

theorem dZ_le_half (x : ℝ) : dZ x ≤ 1 / 2 := abs_sub_round x

theorem dZ_le (x : ℝ) (z : ℤ) : dZ x ≤ |x - z| := round_le x z

theorem ee_half : ee (1 / 2) = -1 := by
  unfold ee
  rw [show 2 * (π : ℂ) * Complex.I * ((1 / 2 : ℝ) : ℂ) = π * Complex.I by push_cast; ring]
  exact Complex.exp_pi_mul_I

theorem norm_ee_sub_one (x : ℝ) : ‖ee x - 1‖ = 2 * |Real.sin (π * x)| := by
  have h := norm_ee_add_ee x (1 / 2)
  rw [ee_half, ← sub_eq_add_neg] at h
  rw [h, show π * (x - 1 / 2) = π * x - π / 2 by ring, Real.cos_sub_pi_div_two]

/-- `|sin(π r)| ≥ 2|r|` for `|r| ≤ 1/2`. -/
theorem two_abs_le_abs_sin {r : ℝ} (hr : |r| ≤ 1 / 2) : 2 * |r| ≤ |Real.sin (π * r)| := by
  have hpi := Real.pi_pos
  have key : ∀ y : ℝ, 0 ≤ y → y ≤ 1 / 2 → 2 * y ≤ Real.sin (π * y) := by
    intro y hy0 hy1
    have h := Real.mul_le_sin (x := π * y) (by positivity) (by nlinarith)
    calc 2 * y = 2 / π * (π * y) := by field_simp
      _ ≤ _ := h
  rcases le_total 0 r with h0 | h0
  · rw [abs_of_nonneg h0] at hr ⊢
    exact (key r h0 hr).trans (le_abs_self _)
  · rw [abs_of_nonpos h0] at hr ⊢
    have := key (-r) (by linarith) hr
    rw [show π * -r = -(π * r) by ring, Real.sin_neg] at this
    exact this.trans (neg_le_abs _)

theorem ee_sub_round (x : ℝ) : ee (x - round x) = ee x := by
  rw [sub_eq_add_neg, ee_add, show -((round x : ℤ) : ℝ) = ((-round x : ℤ) : ℝ) by push_cast; ring,
    ee_int, mul_one]

theorem norm_ee_sub_one_ge (x : ℝ) : 4 * dZ x ≤ ‖ee x - 1‖ := by
  rw [← ee_sub_round, norm_ee_sub_one]
  have := two_abs_le_abs_sin (dZ_le_half x)
  unfold dZ at this ⊢
  linarith

theorem ee_mul_add (a x : ℝ) (k : ℕ) : ee ((a + k) * x) = ee (a * x) * ee x ^ k := by
  rw [add_mul, ee_add, ← ee_nat_mul]

/-- The trivial bound. -/
theorem norm_sum_ee_le_card (H : ℕ) (a x : ℝ) : ‖∑ k ∈ range H, ee ((a + k) * x)‖ ≤ H := by
  calc ‖∑ k ∈ range H, ee ((a + k) * x)‖ ≤ ∑ k ∈ range H, ‖ee ((a + k) * x)‖ := norm_sum_le _ _
    _ = H := by simp [norm_ee]

/-- **Dirichlet-kernel bound.** -/
theorem norm_sum_ee_le_dirichlet (H : ℕ) (a x : ℝ) (hd : 0 < dZ x) :
    ‖∑ k ∈ range H, ee ((a + k) * x)‖ ≤ 1 / (2 * dZ x) := by
  set w := ee x
  have hw1 : 0 < ‖w - 1‖ := lt_of_lt_of_le (by linarith) (norm_ee_sub_one_ge x)
  have hne : w - 1 ≠ 0 := norm_pos_iff.mp hw1
  have hgeom : (∑ k ∈ range H, w ^ k) * (w - 1) = w ^ H - 1 := geom_sum_mul w H
  have hsum : ∑ k ∈ range H, ee ((a + k) * x) = ee (a * x) * ((w ^ H - 1) / (w - 1)) := by
    simp_rw [ee_mul_add, ← mul_sum]
    rw [← hgeom, mul_div_cancel_right₀ _ hne]
  rw [hsum, norm_mul, norm_ee, one_mul, norm_div]
  have hnum : ‖w ^ H - 1‖ ≤ 2 := by
    calc ‖w ^ H - 1‖ ≤ ‖w ^ H‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, norm_ee, one_pow, norm_one]; norm_num
  have h4 := norm_ee_sub_one_ge x
  rw [div_le_div_iff₀ hw1 (by positivity)]
  nlinarith [dZ_nonneg x]

/-! ## Pair expansion -/

theorem conj_ee (y : ℝ) : (starRingEnd ℂ) (ee y) = ee (-y) := by
  unfold ee
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  push_cast; ring

theorem sq_norm_sum_eq {ι : Type*} (T : Finset ι) (z : ι → ℂ) :
    ‖∑ i ∈ T, z i‖ ^ 2 = (∑ i ∈ T, ∑ j ∈ T, z i * (starRingEnd ℂ) (z j)).re := by
  rw [Complex.sq_norm, ← Complex.ofReal_re (Complex.normSq _), ← Complex.mul_conj, map_sum,
    sum_mul]
  simp_rw [mul_sum]

/-- **Pair expansion** of an interval-averaged energy. -/
theorem sum_sq_norm_le_pairs {ι : Type*} (T : Finset ι) (ζ : ι → ℝ) (H : ℕ) (a : ℝ) :
    ∑ k ∈ range H, ‖∑ i ∈ T, ee ((a + k) * ζ i)‖ ^ 2 ≤
      ∑ i ∈ T, ∑ j ∈ T, ‖∑ k ∈ range H, ee ((a + k) * (ζ i - ζ j))‖ := by
  have hpair : ∀ k : ℕ, ∀ i j : ι, ee ((a + k) * ζ i) * (starRingEnd ℂ) (ee ((a + k) * ζ j)) =
      ee ((a + k) * (ζ i - ζ j)) := by
    intro k i j; rw [conj_ee, ← ee_add]; congr 1; ring
  simp_rw [sq_norm_sum_eq, hpair]
  rw [← Complex.re_sum]
  calc (∑ k ∈ range H, ∑ i ∈ T, ∑ j ∈ T, ee ((a + k) * (ζ i - ζ j))).re
      = (∑ i ∈ T, ∑ j ∈ T, ∑ k ∈ range H, ee ((a + k) * (ζ i - ζ j))).re := by
        rw [sum_comm]; congr 1; refine sum_congr rfl fun i _ => ?_; rw [sum_comm]
    _ ≤ ‖∑ i ∈ T, ∑ j ∈ T, ∑ k ∈ range H, ee ((a + k) * (ζ i - ζ j))‖ := Complex.re_le_norm _
    _ ≤ ∑ i ∈ T, ‖∑ j ∈ T, ∑ k ∈ range H, ee ((a + k) * (ζ i - ζ j))‖ := norm_sum_le _ _
    _ ≤ _ := sum_le_sum fun i _ => norm_sum_le _ _

/-! ## Grid-spacing sieve -/

/-- An integer in the residue class `c = n mod q` has absolute value `≥ min c (q − c)`. -/
theorem min_le_abs_sub {n q : ℤ} (z : ℤ) (hq : 0 < q) :
    min (n % q) (q - n % q) ≤ |n - q * z| := by
  have h0 : 0 ≤ n % q := Int.emod_nonneg n hq.ne'
  have h1 : n % q < q := Int.emod_lt_of_pos n hq
  have hdiv : n % q + q * (n / q) = n := Int.emod_add_mul_ediv n q
  set c := n % q
  set k := n / q - z
  have hm : n - q * z = c + q * k := by simp only [k, mul_sub]; linarith
  rw [hm]
  rcases le_or_gt 0 k with hk | hk
  · have : 0 ≤ q * k := mul_nonneg hq.le hk
    rw [abs_of_nonneg (by linarith)]; exact (min_le_left _ _).trans (by linarith)
  · have : q * k ≤ -q := by nlinarith
    rw [abs_of_neg (by omega)]; exact (min_le_right _ _).trans (by linarith)

/-- Kernel bound for a pair on the grid `(1/q)ℤ` perturbed by at most `1/(2q)`. -/
theorem kernel_le_of_grid (H : ℕ) (a : ℝ) {q : ℕ} (hq : 1 ≤ q) (n : ℤ) {d : ℝ}
    (hd : |d| ≤ 1 / (2 * q)) {c : ℕ} (hc : (c : ℤ) = n % q) (hc0 : c ≠ 0) :
    ‖∑ k ∈ range H, ee ((a + k) * ((n : ℝ) / q + d))‖ ≤ q / c + q / (q - c) := by
  have hq0 : (0 : ℤ) < q := by exact_mod_cast hq
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hcq : c < q := by have := Int.emod_lt_of_pos n hq0; omega
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hc0
  have hcqR : (c : ℝ) + 1 ≤ q := by exact_mod_cast hcq
  set m : ℝ := min (c : ℝ) ((q : ℝ) - c) with hm_def
  have hm1 : 1 ≤ m := le_min hc1 (by linarith)
  have hclaim : ∀ z : ℤ, m / (2 * q) ≤ |(n : ℝ) / q + d - z| := by
    intro z
    have hint := min_le_abs_sub (n := n) z hq0
    rw [← hc] at hint
    have hintR : m ≤ |(n : ℝ) - q * z| := by
      have := (Int.cast_le (R := ℝ)).mpr hint
      push_cast at this; simpa [hm_def] using this
    have hsplit : (n : ℝ) / q + d - z = ((n : ℝ) - q * z) / q + d := by field_simp; ring
    rw [hsplit]
    have h1 : |((n : ℝ) - q * z) / q| = |(n : ℝ) - q * z| / q := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < q)]
    have h2 : |((n : ℝ) - q * z) / q| - |d| ≤ |((n : ℝ) - q * z) / q + d| := by
      have := abs_sub_abs_le_abs_sub (((n : ℝ) - q * z) / q) (-d)
      rwa [abs_neg, sub_neg_eq_add] at this
    have h3 : m / q ≤ |(n : ℝ) - q * z| / q := div_le_div_of_nonneg_right hintR (by positivity)
    have h4 : m / (2 * q) = m / q - m / (2 * q) := by field_simp; ring
    have h5 : 1 / (2 * q) ≤ m / (2 * q) := div_le_div_of_nonneg_right hm1 (by positivity)
    linarith
  have hdZ : m / (2 * q) ≤ dZ ((n : ℝ) / q + d) := hclaim _
  have hpos : 0 < m / (2 * q) := by positivity
  calc ‖∑ k ∈ range H, ee ((a + k) * ((n : ℝ) / q + d))‖
      ≤ 1 / (2 * dZ ((n : ℝ) / q + d)) := norm_sum_ee_le_dirichlet H a _ (hpos.trans_le hdZ)
    _ ≤ 1 / (2 * (m / (2 * q))) := by gcongr
    _ = q / m := by field_simp
    _ ≤ q / c + q / (q - c) := by
      have hA : 0 ≤ (q : ℝ) / c := by positivity
      have hB : 0 ≤ (q : ℝ) / (q - c) := div_nonneg (by linarith) (by linarith)
      rcases min_choice (c : ℝ) ((q : ℝ) - c) with h | h
      · rw [hm_def, h]; linarith
      · rw [hm_def, h]; linarith

theorem sum_Ico_one_div_le (q : ℕ) : ∑ c ∈ Ico 1 q, (1 : ℝ) / c ≤ 1 + Real.log q := by
  have h1 : ∑ c ∈ Ico 1 q, (1 : ℝ) / c = ∑ k ∈ range (q - 1), (1 : ℝ) / ((1 + k : ℕ) : ℝ) := by
    rw [sum_Ico_eq_sum_range]
  have h2 : ∑ k ∈ range (q - 1), (1 : ℝ) / ((1 + k : ℕ) : ℝ) ≤
      ∑ k ∈ range q, (1 : ℝ) / ((1 + k : ℕ) : ℝ) :=
    sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (Nat.sub_le _ _))
      fun _ _ _ => by positivity
  have h3 : ((harmonic q : ℚ) : ℝ) = ∑ k ∈ range q, (1 : ℝ) / ((1 + k : ℕ) : ℝ) := by
    rw [harmonic]; push_cast
    exact sum_congr rfl fun k _ => by rw [one_div, add_comm]
  linarith [harmonic_le_one_add_log q]

theorem sum_Ico_one_div_reflect (q : ℕ) :
    ∑ c ∈ Ico 1 q, (1 : ℝ) / ((q : ℝ) - c) = ∑ c ∈ Ico 1 q, (1 : ℝ) / c := by
  refine sum_nbij' (fun c => q - c) (fun c => q - c) ?_ ?_ ?_ ?_ ?_
  · intro c hc; simp only [mem_Ico] at hc ⊢; omega
  · intro c hc; simp only [mem_Ico] at hc ⊢; omega
  · intro c hc; simp only [mem_Ico] at hc; omega
  · intro c hc; simp only [mem_Ico] at hc; omega
  · intro c hc
    simp only [mem_Ico] at hc
    rw [Nat.cast_sub hc.2.le]

/-- The per-residue kernel majorant. -/
noncomputable def kb (H q c : ℕ) : ℝ := if c = 0 then (H : ℝ) else q / c + q / (q - c)

theorem kb_nonneg (H q c : ℕ) (hc : c < q) : 0 ≤ kb H q c := by
  unfold kb
  have : (c : ℝ) < q := by exact_mod_cast hc
  split_ifs
  · positivity
  · exact add_nonneg (by positivity) (div_nonneg (by positivity) (by linarith))

theorem sum_kb_le (H q : ℕ) (hq : 1 ≤ q) :
    ∑ c ∈ range q, kb H q c ≤ H + 2 * q * (1 + Real.log q) := by
  rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega : 0 < q)]
  have hrest : ∑ c ∈ Ico (0 + 1) q, kb H q c =
      q * ∑ c ∈ Ico 1 q, (1 : ℝ) / c + q * ∑ c ∈ Ico 1 q, (1 : ℝ) / ((q : ℝ) - c) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun c hc => ?_
    have : c ≠ 0 := by simp only [mem_Ico] at hc; omega
    simp only [kb, this, ite_false]; ring
  have hk0 : kb H q 0 = H := by simp [kb]
  rw [hrest, sum_Ico_one_div_reflect, hk0]
  have := sum_Ico_one_div_le q
  have hq0 : (0 : ℝ) ≤ q := by positivity
  nlinarith

/-- **Grid-spacing sieve.**  Points `ζ_i = A_i/q + δ_i` with `0 ≤ δ_i ≤ 1/(2q)` whose residues
`A_i mod q` have fibres of size `≤ μ` inside `T`. -/
theorem grid_sieve {ι : Type*} (T : Finset ι) {q : ℕ} (hq : 1 ≤ q) (A : ι → ℤ) (δ : ι → ℝ)
    (hδ0 : ∀ i ∈ T, 0 ≤ δ i) (hδ1 : ∀ i ∈ T, δ i ≤ 1 / (2 * q)) (μ : ℕ)
    (hμ : ∀ c : ℤ, (T.filter fun j => A j % q = c).card ≤ μ) (H : ℕ) (a : ℝ) :
    ∑ k ∈ range H, ‖∑ i ∈ T, ee ((a + k) * ((A i : ℝ) / q + δ i))‖ ^ 2 ≤
      T.card * μ * (H + 2 * q * (1 + Real.log q)) := by
  classical
  have hq0 : (0 : ℤ) < q := by exact_mod_cast hq
  set r : ι → ι → ℕ := fun i j => ((A i - A j) % (q : ℤ)).toNat
  have hr : ∀ i j, ((r i j : ℕ) : ℤ) = (A i - A j) % q := fun i j =>
    Int.toNat_of_nonneg (Int.emod_nonneg _ hq0.ne')
  have hrlt : ∀ i j, r i j < q := fun i j => by
    have := Int.emod_lt_of_pos (A i - A j) hq0; have := hr i j; omega
  -- pair kernel bound
  have hpair : ∀ i ∈ T, ∀ j ∈ T,
      ‖∑ k ∈ range H, ee ((a + k) * (((A i : ℝ) / q + δ i) - ((A j : ℝ) / q + δ j)))‖ ≤
        kb H q (r i j) := by
    intro i hi j hj
    have hre : ((A i : ℝ) / q + δ i) - ((A j : ℝ) / q + δ j) =
        (((A i - A j : ℤ) : ℝ)) / q + (δ i - δ j) := by push_cast; ring
    rw [hre]
    by_cases h0 : r i j = 0
    · simp only [kb, h0, ite_true]; exact norm_sum_ee_le_card H a _
    · simp only [kb, h0, ite_false]
      refine kernel_le_of_grid H a hq (A i - A j) ?_ (hr i j) h0
      rw [abs_le]; have := hδ0 i hi; have := hδ0 j hj; have := hδ1 i hi; have := hδ1 j hj
      constructor <;> linarith
  -- fibre count
  have hrow : ∀ i ∈ T, ∑ j ∈ T, kb H q (r i j) ≤ μ * (H + 2 * q * (1 + Real.log q)) := by
    intro i _
    rw [← sum_fiberwise_of_maps_to (s := T) (t := range q) (g := r i)
      (fun j _ => mem_range.mpr (hrlt i j))]
    calc ∑ c ∈ range q, ∑ j ∈ T with r i j = c, kb H q (r i j)
        = ∑ c ∈ range q, ((T.filter fun j => r i j = c).card : ℝ) * kb H q c := by
          refine sum_congr rfl fun c _ => ?_
          rw [sum_congr rfl fun j hj => by rw [(mem_filter.mp hj).2], sum_const, nsmul_eq_mul]
      _ ≤ ∑ c ∈ range q, (μ : ℝ) * kb H q c := by
          refine sum_le_sum fun c hc => mul_le_mul_of_nonneg_right ?_
            (kb_nonneg H q c (mem_range.mp hc))
          have hsub : (T.filter fun j => r i j = c) ⊆
              (T.filter fun j => A j % q = (A i - c) % q) := by
            intro j hj
            rw [mem_filter] at hj ⊢
            refine ⟨hj.1, ?_⟩
            have h1 : (A i - A j) % (q : ℤ) = (c : ℤ) := by rw [← hr i j, hj.2]
            have h2 : Int.ModEq q (A i - A j) c := by
              unfold Int.ModEq; rw [h1]
              exact (Int.emod_eq_of_lt (by positivity) (by
                have := hrlt i j; rw [hj.2] at this; exact_mod_cast this)).symm
            have h3 := (Int.ModEq.refl (A i)).sub h2
            rw [sub_sub_cancel] at h3
            exact h3
          exact_mod_cast (card_le_card hsub).trans (hμ _)
      _ = μ * ∑ c ∈ range q, kb H q c := by rw [mul_sum]
      _ ≤ μ * (H + 2 * q * (1 + Real.log q)) :=
          mul_le_mul_of_nonneg_left (sum_kb_le H q hq) (by positivity)
  calc ∑ k ∈ range H, ‖∑ i ∈ T, ee ((a + k) * ((A i : ℝ) / q + δ i))‖ ^ 2
      ≤ ∑ i ∈ T, ∑ j ∈ T, ‖∑ k ∈ range H,
          ee ((a + k) * (((A i : ℝ) / q + δ i) - ((A j : ℝ) / q + δ j)))‖ :=
        sum_sq_norm_le_pairs T (fun i => (A i : ℝ) / q + δ i) H a
    _ ≤ ∑ i ∈ T, ∑ j ∈ T, kb H q (r i j) :=
        sum_le_sum fun i hi => sum_le_sum fun j hj => hpair i hi j hj
    _ ≤ ∑ i ∈ T, (μ : ℝ) * (H + 2 * q * (1 + Real.log q)) := sum_le_sum hrow
    _ = T.card * μ * (H + 2 * q * (1 + Real.log q)) := by rw [sum_const, nsmul_eq_mul]; ring

/-! ## Minkowski step -/

theorem sqrt_sum_sq_add_le {α : Type*} (I : Finset α) (x y : α → ℝ) :
    √(∑ l ∈ I, (x l + y l) ^ 2) ≤ √(∑ l ∈ I, x l ^ 2) + √(∑ l ∈ I, y l ^ 2) := by
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt I x y
  have hX := Real.sq_sqrt (sum_nonneg fun l (_ : l ∈ I) => sq_nonneg (x l))
  have hY := Real.sq_sqrt (sum_nonneg fun l (_ : l ∈ I) => sq_nonneg (y l))
  have hexp : ∑ l ∈ I, (x l + y l) ^ 2 =
      ∑ l ∈ I, x l ^ 2 + 2 * ∑ l ∈ I, x l * y l + ∑ l ∈ I, y l ^ 2 := by
    simp only [add_sq, sum_add_distrib, mul_assoc, ← mul_sum]
  calc √(∑ l ∈ I, (x l + y l) ^ 2)
      ≤ √((√(∑ l ∈ I, x l ^ 2) + √(∑ l ∈ I, y l ^ 2)) ^ 2) := by
        apply Real.sqrt_le_sqrt; rw [hexp]; nlinarith
    _ = √(∑ l ∈ I, x l ^ 2) + √(∑ l ∈ I, y l ^ 2) := Real.sqrt_sq (by positivity)

/-- **Minkowski** for finite families. -/
theorem sqrt_sum_sq_sum_le {α β : Type*} (I : Finset α) (U : Finset β) (b : β → α → ℝ) :
    √(∑ l ∈ I, (∑ S ∈ U, b S l) ^ 2) ≤ ∑ S ∈ U, √(∑ l ∈ I, b S l ^ 2) := by
  classical
  induction U using Finset.induction_on with
  | empty => simp
  | insert s U hs ih =>
    simp only [sum_insert hs]
    exact (sqrt_sum_sq_add_le I (b s) (fun l => ∑ S ∈ U, b S l)).trans (by linarith)

/-- **Minkowski step** of the interval sieve: trivially bounded continuation sums `G_S`. -/
theorem minkowski_step {α β : Type*} (I : Finset α) (U : Finset β) (F G : β → α → ℂ) (g : β → ℝ)
    (hg : ∀ S ∈ U, 0 ≤ g S) (hG : ∀ S ∈ U, ∀ l ∈ I, ‖G S l‖ ≤ g S) :
    √(∑ l ∈ I, ‖∑ S ∈ U, F S l * G S l‖ ^ 2) ≤ ∑ S ∈ U, g S * √(∑ l ∈ I, ‖F S l‖ ^ 2) := by
  have hpt : ∀ l ∈ I, ‖∑ S ∈ U, F S l * G S l‖ ≤ ∑ S ∈ U, g S * ‖F S l‖ := by
    intro l hl
    refine (norm_sum_le _ _).trans (sum_le_sum fun S hS => ?_)
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hG S hS l hl) (norm_nonneg _)
  calc √(∑ l ∈ I, ‖∑ S ∈ U, F S l * G S l‖ ^ 2)
      ≤ √(∑ l ∈ I, (∑ S ∈ U, g S * ‖F S l‖) ^ 2) := by
        apply Real.sqrt_le_sqrt
        exact sum_le_sum fun l hl => by gcongr; exact hpt l hl
    _ ≤ ∑ S ∈ U, √(∑ l ∈ I, (g S * ‖F S l‖) ^ 2) := sqrt_sum_sq_sum_le I U _
    _ = ∑ S ∈ U, g S * √(∑ l ∈ I, ‖F S l‖ ^ 2) := by
        refine sum_congr rfl fun S hS => ?_
        simp_rw [mul_pow]
        rw [← mul_sum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (hg S hS)]

end IntervalSieve
end EOC
