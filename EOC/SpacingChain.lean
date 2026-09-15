import EOC.FirstDivergence
import EOC.ShellRefined
import EOC.IntervalSieve

/-!
# Pair spacing, the first-divergence odd quotient, and the spacing ⇒ `WeightedFourier` transfer

* `odd_quotient` — **first-divergence odd quotient**: under the hypotheses of
  `FirstDivergence.q_sub_valuation`, `q d j − q e j = 2^(s d i + min (d i) (e i)) · Δ` with `Δ` odd.
* `centDistZ M n = min (n mod M) (M − n mod M)` — centered distance of `n` from `0` in `ℤ/M`;
  `pairSpacing T y M D` — ordered pairs `(i, j) ∈ T × T` with `centDistZ M (y i − y j) < D`.
* `centDistZ_div_le_dZ` — `centDistZ M n / M ≤ dZ (n / M)`.
* `pair_kernel_le` — per-pair kernel: `‖∑_{k<H} e((a+k)(y_i − y_j)/M)‖ ≤ kerZ H M (y_i − y_j)` with
  `kerZ = H` at centered distance `0`, `min H (M / (2·centDist))` otherwise.
* `sum_sq_le_kernel` — **spacing ⇒ interval energy** (exact pair-kernel form).
* `sum_sq_le_pairSpacing` — threshold form:
  `∑_{k<H} ‖∑_{i∈T} e((a+k) y_i / M)‖^2 ≤ H · pairSpacing T y M D + (#T)^2 · M / (2D)`.
* `weightedFourier_of_shell_bound` / **`spacingExponent_implies_weightedFourier`** — if every
  centered shell satisfies the `ShellRefined` hypothesis with `a_u = C · 2^(−θu)`, then
  `WeightedFourier` holds with
  `ε^2 = (1 + (σ+1)/2) · (∑_u min(2^(u+1), 2^t) · C · 2^(−θu)) · 2^t / |V_{σ,s}|`.
  All analytic spacing input stays a hypothesis.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace SpacingChain

open Finset SwapBound TwistExpansion PrefixCollision WeightedChain ShellDecomposition IntervalSieve

/-! ## The first-divergence odd quotient -/

/-- **First-divergence odd quotient.** -/
theorem odd_quotient {d e : ℕ → ℕ} {i j : ℕ} (hagree : ∀ l < i, d l = e l) (hne : d i ≠ e i)
    (hij : i + 1 < j) (hd : ∀ l < j, 1 ≤ d l) (he : ∀ l < j, 1 ≤ e l) :
    ∃ Δ : ℤ, Odd Δ ∧ (q d j : ℤ) - q e j = 2 ^ (s d i + min (d i) (e i)) * Δ := by
  obtain ⟨hdvd, hndvd⟩ := FirstDivergence.q_sub_valuation hagree hne hij hd he
  obtain ⟨Δ, hΔ⟩ := hdvd
  refine ⟨Δ, ?_, hΔ⟩
  rcases Int.even_or_odd Δ with ⟨k, hk⟩ | hodd
  · exfalso; apply hndvd
    exact ⟨k, by rw [hΔ, hk, pow_succ]; ring⟩
  · exact hodd

/-! ## Centered distance and the pair-spacing count -/

/-- Centered distance of `n` from `0` in `ℤ/M`. -/
def centDistZ (M n : ℤ) : ℤ := min (n % M) (M - n % M)

/-- Ordered pairs of `T` whose points `y` are within centered distance `< D` modulo `M`. -/
def pairSpacing {ι : Type*} (T : Finset ι) (y : ι → ℤ) (M D : ℤ) : ℕ :=
  ((T ×ˢ T).filter fun p => centDistZ M (y p.1 - y p.2) < D).card

theorem centDistZ_nonneg {M : ℤ} (hM : 0 < M) (n : ℤ) : 0 ≤ centDistZ M n := by
  unfold centDistZ
  have h0 : 0 ≤ n % M := Int.emod_nonneg n hM.ne'
  have h1 : n % M < M := Int.emod_lt_of_pos n hM
  exact le_min h0 (by linarith)

/-- The centered distance controls the distance to the nearest integer. -/
theorem centDistZ_div_le_dZ {M : ℤ} (hM : 0 < M) (n : ℤ) :
    (centDistZ M n : ℝ) / M ≤ dZ ((n : ℝ) / M) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  set z := round ((n : ℝ) / M)
  have hkey := min_le_abs_sub (n := n) z hM
  have hcast : ((|n - M * z| : ℤ) : ℝ) = |(n : ℝ) - M * z| := by push_cast; ring_nf
  unfold dZ
  rw [div_le_iff₀ hMr]
  calc (centDistZ M n : ℝ) ≤ |(n : ℝ) - M * z| := by
        rw [← hcast]; exact_mod_cast hkey
    _ = |(n : ℝ) / M - z| * M := by
        rw [← abs_of_pos hMr, ← abs_mul, abs_of_pos hMr]
        congr 1; field_simp
    _ = |(n : ℝ) / M - z| * M := rfl

/-! ## Pair kernel and the spacing ⇒ energy transfer -/

/-- Pair kernel: `H` at centered distance `0`, `min H (M/(2c))` at centered distance `c > 0`. -/
noncomputable def kerZ (H : ℕ) (M n : ℤ) : ℝ :=
  if centDistZ M n = 0 then (H : ℝ) else min (H : ℝ) ((M : ℝ) / (2 * centDistZ M n))

theorem kerZ_le_H (H : ℕ) (M n : ℤ) : kerZ H M n ≤ H := by
  unfold kerZ; split_ifs
  · exact le_rfl
  · exact min_le_left _ _

theorem pair_kernel_le (H : ℕ) (a : ℝ) {M : ℤ} (hM : 0 < M) (n : ℤ) :
    ‖∑ k ∈ range H, ee ((a + k) * ((n : ℝ) / M))‖ ≤ kerZ H M n := by
  unfold kerZ
  split_ifs with h0
  · exact norm_sum_ee_le_card H a _
  · refine le_min (norm_sum_ee_le_card H a _) ?_
    have hc : 0 < centDistZ M n := lt_of_le_of_ne (centDistZ_nonneg hM n) (Ne.symm h0)
    have hcr : (0 : ℝ) < centDistZ M n := by exact_mod_cast hc
    have hMr : (0 : ℝ) < M := by exact_mod_cast hM
    have hle := centDistZ_div_le_dZ hM n
    have hd : 0 < dZ ((n : ℝ) / M) := lt_of_lt_of_le (by positivity) hle
    calc ‖∑ k ∈ range H, ee ((a + k) * ((n : ℝ) / M))‖ ≤ 1 / (2 * dZ ((n : ℝ) / M)) :=
          norm_sum_ee_le_dirichlet H a _ hd
      _ ≤ 1 / (2 * ((centDistZ M n : ℝ) / M)) := by
          apply one_div_le_one_div_of_le (by positivity); linarith
      _ = (M : ℝ) / (2 * centDistZ M n) := by field_simp

/-- **Spacing ⇒ interval energy**, exact pair-kernel form. -/
theorem sum_sq_le_kernel {ι : Type*} (T : Finset ι) (y : ι → ℤ) (H : ℕ) (a : ℝ) {M : ℤ}
    (hM : 0 < M) :
    ∑ k ∈ range H, ‖∑ i ∈ T, ee ((a + k) * ((y i : ℝ) / M))‖ ^ 2 ≤
      ∑ i ∈ T, ∑ j ∈ T, kerZ H M (y i - y j) := by
  refine (sum_sq_norm_le_pairs T (fun i => (y i : ℝ) / M) H a).trans ?_
  refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
  have hsub : (y i : ℝ) / M - (y j : ℝ) / M = (((y i - y j : ℤ)) : ℝ) / M := by
    push_cast; ring
  simp only [hsub]
  exact pair_kernel_le H a hM _

/-- **Spacing ⇒ interval energy**, threshold form: pairs at centered distance `< D` cost `H`,
all others cost at most `M/(2D)`. -/
theorem sum_sq_le_pairSpacing {ι : Type*} (T : Finset ι) (y : ι → ℤ) (H : ℕ) (a : ℝ) {M D : ℤ}
    (hM : 0 < M) (hD : 0 < D) :
    ∑ k ∈ range H, ‖∑ i ∈ T, ee ((a + k) * ((y i : ℝ) / M))‖ ^ 2 ≤
      H * pairSpacing T y M D + (T.card : ℝ) ^ 2 * ((M : ℝ) / (2 * D)) := by
  refine (sum_sq_le_kernel T y H a hM).trans ?_
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  set f : ι × ι → ℝ := fun p => kerZ H M (y p.1 - y p.2)
  set cl : ι × ι → Prop := fun p => centDistZ M (y p.1 - y p.2) < D
  have hsplit : ∑ i ∈ T, ∑ j ∈ T, kerZ H M (y i - y j) = ∑ p ∈ T ×ˢ T, f p := by
    rw [sum_product]
  rw [hsplit, ← sum_filter_add_sum_filter_not (T ×ˢ T) cl]
  have hclose : ∑ p ∈ (T ×ˢ T).filter cl, f p ≤ H * pairSpacing T y M D := by
    calc ∑ p ∈ (T ×ˢ T).filter cl, f p ≤ ∑ p ∈ (T ×ˢ T).filter cl, (H : ℝ) :=
          sum_le_sum fun p _ => kerZ_le_H H M _
      _ = H * pairSpacing T y M D := by
          rw [sum_const, nsmul_eq_mul, mul_comm]; rfl
  have hfar : ∑ p ∈ (T ×ˢ T).filter (fun p => ¬ cl p), f p ≤
      (T.card : ℝ) ^ 2 * ((M : ℝ) / (2 * D)) := by
    have hpt : ∀ p ∈ (T ×ˢ T).filter (fun p => ¬ cl p), f p ≤ (M : ℝ) / (2 * D) := by
      intro p hp
      have hp' : D ≤ centDistZ M (y p.1 - y p.2) := not_lt.mp (mem_filter.mp hp).2
      have h0 : centDistZ M (y p.1 - y p.2) ≠ 0 := by omega
      have hcr : (D : ℝ) ≤ centDistZ M (y p.1 - y p.2) := by exact_mod_cast hp'
      simp only [f, kerZ, h0, ↓reduceIte]
      refine (min_le_right _ _).trans ?_
      exact div_le_div_of_nonneg_left hMr.le (by positivity) (by linarith)
    calc ∑ p ∈ (T ×ˢ T).filter (fun p => ¬ cl p), f p
        ≤ ∑ p ∈ (T ×ˢ T).filter (fun p => ¬ cl p), (M : ℝ) / (2 * D) := sum_le_sum hpt
      _ = ((T ×ˢ T).filter (fun p => ¬ cl p)).card * ((M : ℝ) / (2 * D)) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ((T ×ˢ T).card : ℝ) * ((M : ℝ) / (2 * D)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast card_filter_le _ _
      _ = (T.card : ℝ) ^ 2 * ((M : ℝ) / (2 * D)) := by
          rw [card_product]; push_cast; ring
  linarith

/-! ## Spacing exponent ⇒ `WeightedFourier` -/

/-- `WeightedFourier` from shell averages `a_u = C · 2^(−θu)` for any `ε` above the explicit
budget. -/
theorem weightedFourier_of_shell_bound (b : ℕ → ℕ) (N j0 s σ : ℕ) (ε C θ : ℝ) (hC : 0 ≤ C)
    (hV : 0 < (shellV b N j0 σ (s - σ)).card)
    (hshell : ∀ u ∈ range (σ + 1 + (s - σ)),
      ∑ lam ∈ cshell (σ + 1) (s - σ) u,
        ‖Psi (shellP b j0 σ) (σ + 1) (s - σ) (yPrime j0 σ (s - σ)) lam‖ ^ 2 ≤
      (cshell (σ + 1) (s - σ) u).card *
        ((C * (2 : ℝ) ^ (-θ * u)) * ((shellP b j0 σ).card : ℝ) ^ 2))
    (hε : (1 + ((σ + 1 : ℕ) : ℝ) / 2) *
        (∑ u ∈ range (σ + 1 + (s - σ)),
          min (2 ^ (u + 1)) (2 ^ (s - σ)) * (C * (2 : ℝ) ^ (-θ * u))) *
          2 ^ (s - σ) / (shellV b N j0 σ (s - σ)).card ≤ ε ^ 2) :
    WeightedFourier b N j0 s σ ε := by
  refine ShellRefined.weightedFourier_of_shell_averages_refined b N j0 s σ ε
    (fun u => C * (2 : ℝ) ^ (-θ * u)) (fun u => by positivity) hshell ?_
  have hVr : (0 : ℝ) < (shellV b N j0 σ (s - σ)).card := by exact_mod_cast hV
  have h2 : (0 : ℝ) < 2 ^ (s - σ) := by positivity
  rw [div_le_iff₀ hVr] at hε
  rw [le_div_iff₀ h2]
  calc (1 + ((σ + 1 : ℕ) : ℝ) / 2) *
        (∑ u ∈ range (σ + 1 + (s - σ)),
          min (2 ^ (u + 1)) (2 ^ (s - σ)) * (C * (2 : ℝ) ^ (-θ * u))) *
          2 ^ (s - σ)
      ≤ ε ^ 2 * (shellV b N j0 σ (s - σ)).card := hε
    _ = ε ^ 2 * (shellV b N j0 σ (s - σ)).card := rfl

/-- **Spacing exponent ⇒ `WeightedFourier`** with the explicit
`ε = √((1 + (σ+1)/2) · (∑_u min(2^(u+1), 2^t) · C · 2^(−θu)) · 2^t / |V_{σ,s}|)`. -/
theorem spacingExponent_implies_weightedFourier (b : ℕ → ℕ) (N j0 s σ : ℕ) (C θ : ℝ) (hC : 0 ≤ C)
    (hV : 0 < (shellV b N j0 σ (s - σ)).card)
    (hshell : ∀ u ∈ range (σ + 1 + (s - σ)),
      ∑ lam ∈ cshell (σ + 1) (s - σ) u,
        ‖Psi (shellP b j0 σ) (σ + 1) (s - σ) (yPrime j0 σ (s - σ)) lam‖ ^ 2 ≤
      (cshell (σ + 1) (s - σ) u).card *
        ((C * (2 : ℝ) ^ (-θ * u)) * ((shellP b j0 σ).card : ℝ) ^ 2)) :
    WeightedFourier b N j0 s σ
      (Real.sqrt ((1 + ((σ + 1 : ℕ) : ℝ) / 2) *
        (∑ u ∈ range (σ + 1 + (s - σ)),
          min (2 ^ (u + 1)) (2 ^ (s - σ)) * (C * (2 : ℝ) ^ (-θ * u))) *
          2 ^ (s - σ) / (shellV b N j0 σ (s - σ)).card)) := by
  refine weightedFourier_of_shell_bound b N j0 s σ _ C θ hC hV hshell ?_
  rw [Real.sq_sqrt (by positivity)]

end SpacingChain
end EOC
