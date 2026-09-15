import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The digit-swap inequality for barrier-confined path products

Abstract setting: a barrier `b : ℕ → ℕ`, a phase field `φ : ℕ → ℕ → ℝ` (step `i`, state `S`), a
target state `σ`.  The path product with `n` remaining steps from `(i, S)` is

  `T i 0 S = [S = σ]`,
  `T i (n+1) S = e(φ i S) · ∑_{d ∈ [1, b(i+1) − S]} T (i+1) n (S + d)`,

with `e x = exp(2πi x)`; i.e. `T 0 J 0 = ∑_{paths} ∏_i e(φ i S_i)` over digit paths
`0 = S_0 < S_1 < … < S_J = σ` with `S_{i+1} ≤ b(i+1)`.  (The confined prefix characteristic sum
`Φ(h)` of the Syracuse offset is the instance `b = collatzBarrier U`,
`φ i S = −(h·3^{−(i+1)}·2^S mod 2^m)/2^m`, `J = j0`; that instantiation is not made here.)

* `ee_add_ee`, `norm_ee_add_ee` — `‖e a + e b‖ = 2 |cos (π (a − b))|`.
* `regroup` — two consecutive steps regrouped by their total `u = d + e`.
* `norm_T_two_le` — **two-step block inequality**:
  `‖T i (n+2) S‖ ≤ ∑_u ‖T (i+2) n (S+u)‖ · ‖∑_{d ∈ A_u} e(φ (i+1) (S+d))‖`,
  `A_u = blockSet b i S u` = admissible first digits of a block with total `u`.
* `norm_sum_ee_le_swapWeight` — **swap bound**: pairing `d ↔ u − d` inside `A_u`,
  `‖∑_{d ∈ A_u} e(ψ d)‖ ≤ ∑_{d ∈ lo} 2 |cos (π (ψ d − ψ (u − d)))| + #single`.
* `swapWeight_le_card` — the swap weight never exceeds `#A_u`.
* `G`, `norm_T_le_G` — the dominating nonnegative pair-step DP: `‖T i n S‖ ≤ G i n S`.
* `G_le_pow_mul_N`, `norm_T_le_pow_mul_N` — **good-block decay**: if `swapWeight ≤ κ·#A_u` on a set
  of "good" blocks (`0 ≤ κ ≤ 1`) and a potential `r` lower-bounds the number of good blocks still
  to come along every admissible continuation, then `‖T i n S‖ ≤ κ^(r i n S) · N i n S`, where
  `N` counts admissible paths.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace SwapBound

open Finset Real

/-- `e(x) = exp(2πi x)`. -/
noncomputable def ee (x : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * x)

theorem norm_ee (x : ℝ) : ‖ee x‖ = 1 := by
  unfold ee
  rw [show 2 * (π : ℂ) * Complex.I * x = ((2 * π * x : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem ee_add_ee (a b : ℝ) :
    ee a + ee b = ee ((a + b) / 2) * (2 * Complex.cos ((π * (a - b) : ℝ) : ℂ)) := by
  rw [Complex.two_cos, mul_add]
  unfold ee
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1 <;> congr 1 <;> push_cast <;> ring

theorem norm_ee_add_ee (a b : ℝ) : ‖ee a + ee b‖ = 2 * |Real.cos (π * (a - b))| := by
  rw [ee_add_ee, norm_mul, norm_ee, one_mul, norm_mul, ← Complex.ofReal_cos, Complex.norm_real,
    Real.norm_eq_abs]
  norm_num

/-! ## Pairing inside one block -/

section Pairing

variable (A : Finset ℕ) (u : ℕ)

/-- Smaller members of the swap pairs `{d, u − d} ⊆ A`. -/
def lo : Finset ℕ := A.filter fun d => 2 * d < u ∧ u - d ∈ A
/-- Larger members of the swap pairs. -/
def hi : Finset ℕ := A.filter fun d => ¬ (2 * d < u ∧ u - d ∈ A) ∧ (u < 2 * d ∧ u - d ∈ A)
/-- Unpaired members (partner outside `A`, or the fixed point `2d = u`). -/
def single : Finset ℕ :=
  A.filter fun d => ¬ (2 * d < u ∧ u - d ∈ A) ∧ ¬ (u < 2 * d ∧ u - d ∈ A)

theorem sum_split {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ d ∈ A, f d = ∑ d ∈ lo A u, f d + ∑ d ∈ hi A u, f d + ∑ d ∈ single A u, f d := by
  rw [← sum_filter_add_sum_filter_not A (fun d => 2 * d < u ∧ u - d ∈ A) f,
    ← sum_filter_add_sum_filter_not (A.filter fun d => ¬ (2 * d < u ∧ u - d ∈ A))
      (fun d => u < 2 * d ∧ u - d ∈ A) f, filter_filter, filter_filter, add_assoc]
  rfl

variable {A u}

theorem sum_hi_eq {M : Type*} [AddCommMonoid M] (hA : ∀ d ∈ A, d < u) (f : ℕ → M) :
    ∑ d ∈ hi A u, f d = ∑ d ∈ lo A u, f (u - d) := by
  symm
  refine sum_nbij' (fun d => u - d) (fun d => u - d) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · intro d hd
    simp only [lo, mem_filter] at hd
    have hdu := hA d hd.1
    simp only [hi, mem_filter]
    refine ⟨hd.2.2, ?_, by omega, ?_⟩
    · omega
    · rw [show u - (u - d) = d by omega]; exact hd.1
  · intro d hd
    simp only [hi, mem_filter] at hd
    have hdu := hA d hd.1
    simp only [lo, mem_filter]
    refine ⟨hd.2.2.2, by omega, ?_⟩
    rw [show u - (u - d) = d by omega]; exact hd.1
  · intro d hd
    simp only [lo, mem_filter] at hd
    have := hA d hd.1
    omega
  · intro d hd
    simp only [hi, mem_filter] at hd
    have := hA d hd.1
    omega

/-- `#A = 2·#lo + #single`. -/
theorem card_eq (hA : ∀ d ∈ A, d < u) :
    (A.card : ℝ) = 2 * (lo A u).card + (single A u).card := by
  have h := sum_split A u (fun _ => (1 : ℝ))
  rw [sum_hi_eq hA] at h
  simp only [sum_const, nsmul_eq_mul, mul_one] at h
  rw [h]; ring

variable (A u)

/-- The swap weight of a block. -/
noncomputable def swapWeight (ψ : ℕ → ℝ) : ℝ :=
  ∑ d ∈ lo A u, 2 * |Real.cos (π * (ψ d - ψ (u - d)))| + (single A u).card

theorem swapWeight_nonneg (ψ : ℕ → ℝ) : 0 ≤ swapWeight A u ψ := by
  unfold swapWeight
  have : 0 ≤ ∑ d ∈ lo A u, 2 * |Real.cos (π * (ψ d - ψ (u - d)))| :=
    sum_nonneg fun _ _ => by positivity
  positivity

variable {A u}

/-- **Swap bound.** -/
theorem norm_sum_ee_le_swapWeight (hA : ∀ d ∈ A, d < u) (ψ : ℕ → ℝ) :
    ‖∑ d ∈ A, ee (ψ d)‖ ≤ swapWeight A u ψ := by
  rw [sum_split A u, sum_hi_eq hA, ← sum_add_distrib]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_sum_le _ _).trans (le_of_eq ?_)
    exact sum_congr rfl fun d _ => norm_ee_add_ee _ _
  · refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp [norm_ee]

theorem swapWeight_le_card (hA : ∀ d ∈ A, d < u) (ψ : ℕ → ℝ) :
    swapWeight A u ψ ≤ A.card := by
  rw [card_eq hA]
  unfold swapWeight
  have : ∑ d ∈ lo A u, 2 * |Real.cos (π * (ψ d - ψ (u - d)))| ≤ ∑ _d ∈ lo A u, (2 : ℝ) :=
    sum_le_sum fun d _ => by
      have := Real.abs_cos_le_one (π * (ψ d - ψ (u - d)))
      linarith
  rw [sum_const, nsmul_eq_mul] at this
  linarith

/-- If every pair of the block has `|cos| ≤ c`, the swap weight is at most
`2c·#lo + #single`. -/
theorem swapWeight_le_of_cos_le (ψ : ℕ → ℝ) {c : ℝ}
    (hc : ∀ d ∈ lo A u, |Real.cos (π * (ψ d - ψ (u - d)))| ≤ c) :
    swapWeight A u ψ ≤ 2 * c * (lo A u).card + (single A u).card := by
  unfold swapWeight
  have : ∑ d ∈ lo A u, 2 * |Real.cos (π * (ψ d - ψ (u - d)))| ≤ ∑ _d ∈ lo A u, 2 * c :=
    sum_le_sum fun d hd => by linarith [hc d hd]
  rw [sum_const, nsmul_eq_mul] at this
  linarith

end Pairing

/-! ## Path products, regrouping, and the two-step block inequality -/

section Paths

variable (b : ℕ → ℕ) (φ : ℕ → ℕ → ℝ) (σ : ℕ)

/-- The path product with `n` remaining steps from step `i`, state `S`. -/
noncomputable def T : ℕ → ℕ → ℕ → ℂ
  | _, 0, S => if S = σ then 1 else 0
  | i, n + 1, S => ee (φ i S) * ∑ d ∈ Icc 1 (b (i + 1) - S), T (i + 1) n (S + d)

/-- The number of admissible paths with `n` remaining steps from `(i, S)` to `σ`. -/
noncomputable def N : ℕ → ℕ → ℕ → ℝ
  | _, 0, S => if S = σ then 1 else 0
  | i, n + 1, S => ∑ d ∈ Icc 1 (b (i + 1) - S), N (i + 1) n (S + d)

/-- Admissible first digits `d` of a two-step block from `(i, S)` with total `u = d + e`. -/
def blockSet (i S u : ℕ) : Finset ℕ :=
  (Icc 1 (b (i + 1) - S)).filter fun d => d < u ∧ u - d ≤ b (i + 2) - (S + d)

theorem lt_of_mem_blockSet {i S u d : ℕ} (hd : d ∈ blockSet b i S u) : d < u :=
  (mem_filter.mp hd).2.1

theorem N_nonneg : ∀ n i S, 0 ≤ N b σ i n S
  | 0, i, S => by simp only [N]; split_ifs <;> norm_num
  | n + 1, i, S => by
      simp only [N]
      exact sum_nonneg fun d _ => N_nonneg n (i + 1) (S + d)

/-- **Regrouping two steps by their total.** -/
theorem regroup {R : Type*} [CommSemiring R] (B1 B2 S : ℕ) (g F : ℕ → R) :
    ∑ d ∈ Icc 1 (B1 - S), g d * ∑ e ∈ Icc 1 (B2 - (S + d)), F (S + d + e) =
      ∑ u ∈ range (B2 + 1), F (S + u) *
        ∑ d ∈ (Icc 1 (B1 - S)).filter (fun d => d < u ∧ u - d ≤ B2 - (S + d)), g d := by
  have hin : ∀ d ∈ Icc 1 (B1 - S), ∑ e ∈ Icc 1 (B2 - (S + d)), F (S + d + e) =
      ∑ u ∈ (range (B2 + 1)).filter (fun u => d < u ∧ u - d ≤ B2 - (S + d)), F (S + u) := by
    intro d _
    refine sum_nbij' (fun e => d + e) (fun u => u - d) ?_ ?_ ?_ ?_ ?_
    · intro e he
      simp only [mem_Icc] at he
      simp only [mem_filter, mem_range]
      omega
    · intro u hu
      simp only [mem_filter, mem_range] at hu
      simp only [mem_Icc]
      omega
    · intro e _; simp
    · intro u hu
      simp only [mem_filter, mem_range] at hu
      omega
    · intro e _; rw [add_assoc]
  rw [sum_congr rfl fun d hd => by rw [hin d hd]]
  simp_rw [mul_sum, sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun u _ => sum_congr rfl fun d _ => ?_
  split_ifs <;> simp [mul_comm]

/-- Two steps of `T`, regrouped by the block total. -/
theorem T_two (i n S : ℕ) :
    T b φ σ i (n + 2) S = ee (φ i S) *
      ∑ u ∈ range (b (i + 2) + 1), T b φ σ (i + 2) n (S + u) *
        ∑ d ∈ blockSet b i S u, ee (φ (i + 1) (S + d)) := by
  rw [T]
  simp only [T]
  congr 1
  exact regroup (b (i + 1)) (b (i + 2)) S (fun d => ee (φ (i + 1) (S + d)))
    (fun x => T b φ σ (i + 2) n x)

/-- Two steps of `N`, regrouped by the block total. -/
theorem N_two (i n S : ℕ) :
    N b σ i (n + 2) S =
      ∑ u ∈ range (b (i + 2) + 1), N b σ (i + 2) n (S + u) * (blockSet b i S u).card := by
  simp only [N]
  have h := regroup (b (i + 1)) (b (i + 2)) S (fun _ => (1 : ℝ)) (fun x => N b σ (i + 2) n x)
  simp only [one_mul, sum_const, nsmul_eq_mul, mul_one] at h
  rw [h]
  rfl

/-- **Two-step block inequality.** -/
theorem norm_T_two_le (i n S : ℕ) :
    ‖T b φ σ i (n + 2) S‖ ≤ ∑ u ∈ range (b (i + 2) + 1),
      ‖T b φ σ (i + 2) n (S + u)‖ * ‖∑ d ∈ blockSet b i S u, ee (φ (i + 1) (S + d))‖ := by
  rw [T_two, norm_mul, norm_ee, one_mul]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  exact sum_congr rfl fun u _ => norm_mul _ _

/-- The swap weight of the block `(i, S, u)`. -/
noncomputable def blockWeight (i S u : ℕ) : ℝ :=
  swapWeight (blockSet b i S u) u (fun d => φ (i + 1) (S + d))

theorem blockWeight_nonneg (i S u : ℕ) : 0 ≤ blockWeight b φ i S u :=
  swapWeight_nonneg _ _ _

theorem norm_block_le (i S u : ℕ) :
    ‖∑ d ∈ blockSet b i S u, ee (φ (i + 1) (S + d))‖ ≤ blockWeight b φ i S u :=
  norm_sum_ee_le_swapWeight (fun _ hd => lt_of_mem_blockSet b hd) (fun d => φ (i + 1) (S + d))

theorem blockWeight_le_card (i S u : ℕ) :
    blockWeight b φ i S u ≤ (blockSet b i S u).card :=
  swapWeight_le_card (fun _ hd => lt_of_mem_blockSet b hd) _

/-- The dominating pair-step DP (a single leftover step is weighted by its count). -/
noncomputable def G : ℕ → ℕ → ℕ → ℝ
  | _, 0, S => if S = σ then 1 else 0
  | i, 1, S => ∑ d ∈ Icc 1 (b (i + 1) - S), (if S + d = σ then 1 else 0)
  | i, n + 2, S => ∑ u ∈ range (b (i + 2) + 1), blockWeight b φ i S u * G (i + 2) n (S + u)

/-- **Swap domination:** `‖T i n S‖ ≤ G i n S`. -/
theorem norm_T_le_G : ∀ n i S, ‖T b φ σ i n S‖ ≤ G b φ σ i n S
  | 0, i, S => by
      simp only [T, G]; split_ifs <;> simp
  | 1, i, S => by
      simp only [T, G]
      rw [norm_mul, norm_ee, one_mul]
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      refine sum_congr rfl fun d _ => ?_
      split_ifs <;> simp
  | n + 2, i, S => by
      refine (norm_T_two_le b φ σ i n S).trans ?_
      simp only [G]
      refine sum_le_sum fun u _ => ?_
      rw [mul_comm (blockWeight b φ i S u)]
      exact mul_le_mul (norm_T_le_G n (i + 2) (S + u)) (norm_block_le b φ i S u)
        (norm_nonneg _) ((norm_nonneg _).trans (norm_T_le_G n (i + 2) (S + u)))

end Paths

/-! ## Good blocks ⇒ exponential decay -/

section Decay

variable (b : ℕ → ℕ) (φ : ℕ → ℕ → ℝ) (σ : ℕ)

/-- **Good-block decay.** Let `0 ≤ κ ≤ 1` and let `good i S u` be a set of blocks on which
`blockWeight ≤ κ · #A_u`.  Let `r i n S` be a potential with `r i 0 S = r i 1 S = 0` and, for
every nonempty block `(i, S, u)` whose continuation can still reach `σ`,
`r i (n+2) S ≤ r (i+2) n (S+u) + [good i S u]` (so `r` lower-bounds the number of good blocks
on every admissible continuation).  Then `G i n S ≤ κ^(r i n S) · N i n S`. -/
theorem G_le_pow_mul_N (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (good : ℕ → ℕ → ℕ → Prop)
    [∀ i S u, Decidable (good i S u)]
    (hgood : ∀ i S u, good i S u → blockWeight b φ i S u ≤ κ * (blockSet b i S u).card)
    (r : ℕ → ℕ → ℕ → ℕ) (hr0 : ∀ i S, r i 0 S = 0) (hr1 : ∀ i S, r i 1 S = 0)
    (hstep : ∀ i n S u, u ∈ range (b (i + 2) + 1) → (blockSet b i S u).Nonempty →
      N b σ (i + 2) n (S + u) ≠ 0 →
      r i (n + 2) S ≤ r (i + 2) n (S + u) + if good i S u then 1 else 0) :
    ∀ n i S, G b φ σ i n S ≤ κ ^ r i n S * N b σ i n S
  | 0, i, S => by simp only [G, N, hr0, pow_zero, one_mul]; exact le_rfl
  | 1, i, S => by
      simp only [G, N, hr1, pow_zero, one_mul]
      exact le_rfl
  | n + 2, i, S => by
      simp only [G]
      rw [N_two, mul_sum]
      refine sum_le_sum fun u hu => ?_
      have ih := G_le_pow_mul_N κ hκ0 hκ1 good hgood r hr0 hr1 hstep n (i + 2) (S + u)
      have hw0 := blockWeight_nonneg b φ i S u
      have hN0 := N_nonneg b σ n (i + 2) (S + u)
      calc blockWeight b φ i S u * G b φ σ (i + 2) n (S + u)
          ≤ blockWeight b φ i S u * (κ ^ r (i + 2) n (S + u) * N b σ (i + 2) n (S + u)) :=
            mul_le_mul_of_nonneg_left ih hw0
        _ ≤ κ ^ r i (n + 2) S * (N b σ (i + 2) n (S + u) * (blockSet b i S u).card) := by
            rcases (blockSet b i S u).eq_empty_or_nonempty with hE | hne
            · have hw : blockWeight b φ i S u = 0 := by
                unfold blockWeight swapWeight lo single
                simp [hE]
              rw [hw, zero_mul]; positivity
            by_cases hNz : N b σ (i + 2) n (S + u) = 0
            · rw [hNz]; simp
            have hs := hstep i n S u hu hne hNz
            have hpow : ∀ k : ℕ, r i (n + 2) S ≤ k → κ ^ k ≤ κ ^ r i (n + 2) S :=
              fun k hk => pow_le_pow_of_le_one hκ0 hκ1 hk
            have hc0 : (0 : ℝ) ≤ (blockSet b i S u).card := Nat.cast_nonneg _
            by_cases hg : good i S u
            · simp only [hg, ↓reduceIte] at hs
              have hw := hgood i S u hg
              have h1 : κ ^ (r (i + 2) n (S + u) + 1) ≤ κ ^ r i (n + 2) S := hpow _ hs
              calc blockWeight b φ i S u * (κ ^ r (i + 2) n (S + u) * N b σ (i + 2) n (S + u))
                  ≤ κ * (blockSet b i S u).card *
                      (κ ^ r (i + 2) n (S + u) * N b σ (i + 2) n (S + u)) :=
                    mul_le_mul_of_nonneg_right hw (by positivity)
                _ = κ ^ (r (i + 2) n (S + u) + 1) *
                      (N b σ (i + 2) n (S + u) * (blockSet b i S u).card) := by ring
                _ ≤ κ ^ r i (n + 2) S * (N b σ (i + 2) n (S + u) * (blockSet b i S u).card) :=
                    mul_le_mul_of_nonneg_right h1 (by positivity)
            · simp only [hg, ↓reduceIte, add_zero] at hs
              have hw := blockWeight_le_card b φ i S u
              have h1 : κ ^ r (i + 2) n (S + u) ≤ κ ^ r i (n + 2) S := hpow _ hs
              calc blockWeight b φ i S u * (κ ^ r (i + 2) n (S + u) * N b σ (i + 2) n (S + u))
                  ≤ (blockSet b i S u).card *
                      (κ ^ r (i + 2) n (S + u) * N b σ (i + 2) n (S + u)) :=
                    mul_le_mul_of_nonneg_right hw (by positivity)
                _ ≤ (blockSet b i S u).card *
                      (κ ^ r i (n + 2) S * N b σ (i + 2) n (S + u)) :=
                    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 hN0) hc0
                _ = κ ^ r i (n + 2) S * (N b σ (i + 2) n (S + u) * (blockSet b i S u).card) := by
                    ring

/-- **Characteristic decay from good blocks:** `‖T i n S‖ ≤ κ^(r i n S) · N i n S`. -/
theorem norm_T_le_pow_mul_N (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (good : ℕ → ℕ → ℕ → Prop)
    [∀ i S u, Decidable (good i S u)]
    (hgood : ∀ i S u, good i S u → blockWeight b φ i S u ≤ κ * (blockSet b i S u).card)
    (r : ℕ → ℕ → ℕ → ℕ) (hr0 : ∀ i S, r i 0 S = 0) (hr1 : ∀ i S, r i 1 S = 0)
    (hstep : ∀ i n S u, u ∈ range (b (i + 2) + 1) → (blockSet b i S u).Nonempty →
      N b σ (i + 2) n (S + u) ≠ 0 →
      r i (n + 2) S ≤ r (i + 2) n (S + u) + if good i S u then 1 else 0)
    (n i S : ℕ) : ‖T b φ σ i n S‖ ≤ κ ^ r i n S * N b σ i n S :=
  (norm_T_le_G b φ σ n i S).trans
    (G_le_pow_mul_N b φ σ κ hκ0 hκ1 good hgood r hr0 hr1 hstep n i S)

/-- A sufficient criterion for a good block: every swap pair has `|cos(π Δ)| ≤ cos(π η)` and the
unpaired digits are at most a fraction `f` of the block, giving
`blockWeight ≤ (f + (1 − f) cos(π η)) · #A_u`. -/
theorem blockWeight_le_of_pairs (i S u : ℕ) {c f : ℝ} (hc1 : c ≤ 1)
    (hc : ∀ d ∈ lo (blockSet b i S u) u,
      |Real.cos (π * (φ (i + 1) (S + d) - φ (i + 1) (S + (u - d))))| ≤ c)
    (hf : ((single (blockSet b i S u) u).card : ℝ) ≤ f * (blockSet b i S u).card) :
    blockWeight b φ i S u ≤ (f + (1 - f) * c) * (blockSet b i S u).card := by
  have hA : ∀ d ∈ blockSet b i S u, d < u := fun _ hd => lt_of_mem_blockSet b hd
  have h1 := swapWeight_le_of_cos_le (A := blockSet b i S u) (u := u)
    (fun d => φ (i + 1) (S + d)) hc
  have hcard := card_eq hA
  unfold blockWeight
  -- 2c·#lo + #single = c·(#A − #single) + #single ≤ (f + (1−f)c)·#A
  have : 2 * c * ((lo (blockSet b i S u) u).card : ℝ) + (single (blockSet b i S u) u).card =
      c * (blockSet b i S u).card + (1 - c) * (single (blockSet b i S u) u).card := by
    rw [hcard]; ring
  rw [this] at h1
  nlinarith

end Decay

end SwapBound
end EOC
