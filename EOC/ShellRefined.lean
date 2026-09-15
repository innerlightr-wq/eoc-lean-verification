import EOC.ShellDecomposition

/-!
# Refined shell weights for the `WeightedFourier` sum

`ShellDecomposition.weightedFourier_of_shell_averages` charges every centered shell `u` the
weight `2^t`.  Since `‖coef‖ ≤ 1`, the low shells (`u < t`) really carry only `2^(u+1)`.

* `norm_coef_le_one` — `‖coef r t λ‖ ≤ 1`.
* `norm_coef_le_cshell_refined` — on `cshell r t u`: `‖coef r t λ‖ ≤ min 1 (2^t / (2 · 2^u))`.
* `card_mul_weight_le` — `#shell_u · min 1 (2^t/(2·2^u)) ≤ min (2^(u+1)) (2^t)`.
* `weighted_sum_le_of_shell_averages_refined` — refined shell-average bound.
* **`weightedFourier_of_shell_averages_refined`** — `WeightedFourier` from per-shell averages with
  budget `(1 + (σ+1)/2) · ∑_u min (2^(u+1)) (2^t) · a_u ≤ ε^2 |V_{σ,s}| / 2^t`.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace ShellRefined

open Finset TwistExpansion PrefixCollision WeightedChain ShellDecomposition

theorem norm_coef_le_one (r t lam : ℕ) : ‖coef r t lam‖ ≤ 1 := by
  rw [norm_coef]
  unfold cosProd
  exact prod_le_one (fun _ _ => abs_nonneg _) (fun _ _ => Real.abs_cos_le_one _)

theorem norm_coef_le_cshell_refined {r t u lam : ℕ} (h : lam ∈ cshell r t u) :
    ‖coef r t lam‖ ≤ min 1 (2 ^ t / (2 * 2 ^ u)) :=
  le_min (norm_coef_le_one r t lam) (norm_coef_le_cshell h)

theorem card_mul_weight_le (r t u : ℕ) :
    ((cshell r t u).card : ℝ) * min 1 (2 ^ t / (2 * 2 ^ u)) ≤ min (2 ^ (u + 1)) (2 ^ t) := by
  have hcard : ((cshell r t u).card : ℝ) ≤ 2 ^ (u + 1) := by exact_mod_cast card_cshell_le r t u
  have hc0 : (0 : ℝ) ≤ (cshell r t u).card := by positivity
  refine le_min ?_ ?_
  · calc ((cshell r t u).card : ℝ) * min 1 (2 ^ t / (2 * 2 ^ u))
        ≤ (cshell r t u).card * 1 := mul_le_mul_of_nonneg_left (min_le_left _ _) hc0
      _ ≤ 2 ^ (u + 1) := by rw [mul_one]; exact hcard
  · calc ((cshell r t u).card : ℝ) * min 1 (2 ^ t / (2 * 2 ^ u))
        ≤ (cshell r t u).card * (2 ^ t / (2 * 2 ^ u)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hc0
      _ ≤ 2 ^ (u + 1) * (2 ^ t / (2 * 2 ^ u)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 2 ^ t := by rw [pow_succ]; field_simp

/-- **Refined shell-average bound.** If `F ≥ 0` and every centered shell satisfies
`∑_{λ ∈ shell_u} F λ ≤ #shell_u · a_u` (with `a_u ≥ 0`), then
`∑_g ∑_k ‖coef(g + 2^t k)‖ F(g + 2^t k) ≤ ∑_{u < r+t} min (2^(u+1)) (2^t) · a_u`. -/
theorem weighted_sum_le_of_shell_averages_refined (r t : ℕ) (F : ℕ → ℝ) (a : ℕ → ℝ)
    (hF : ∀ lam, 0 ≤ F lam) (ha : ∀ u, 0 ≤ a u)
    (hshell : ∀ u ∈ range (r + t), ∑ lam ∈ cshell r t u, F lam ≤ (cshell r t u).card * a u) :
    ∑ g ∈ Ico 1 (2 ^ t), ∑ k ∈ range (2 ^ r), ‖coef r t (g + 2 ^ t * k)‖ * F (g + 2 ^ t * k) ≤
      ∑ u ∈ range (r + t), min (2 ^ (u + 1)) (2 ^ t) * a u := by
  rw [sum_fibre_eq_sum_nondvd r t (fun lam => ‖coef r t lam‖ * F lam)]
  change ∑ lam ∈ nondvd r t, ‖coef r t lam‖ * F lam ≤ _
  rw [sum_nondvd_eq_sum_cshell]
  refine sum_le_sum fun u hu => ?_
  set w : ℝ := min 1 (2 ^ t / (2 * 2 ^ u))
  have hw0 : 0 ≤ w := le_min zero_le_one (by positivity)
  have hw : ∀ lam ∈ cshell r t u, ‖coef r t lam‖ * F lam ≤ w * F lam :=
    fun lam hl => mul_le_mul_of_nonneg_right (norm_coef_le_cshell_refined hl) (hF lam)
  calc ∑ lam ∈ cshell r t u, ‖coef r t lam‖ * F lam
      ≤ ∑ lam ∈ cshell r t u, w * F lam := sum_le_sum hw
    _ = w * ∑ lam ∈ cshell r t u, F lam := by rw [mul_sum]
    _ ≤ w * ((cshell r t u).card * a u) := mul_le_mul_of_nonneg_left (hshell u hu) hw0
    _ = ((cshell r t u).card * w) * a u := by ring
    _ ≤ min (2 ^ (u + 1)) (2 ^ t) * a u :=
        mul_le_mul_of_nonneg_right (card_mul_weight_le r t u) (ha u)

/-- **`WeightedFourier` from per-shell averages, refined weights.** With `t = s − σ`,
`r = σ + 1`: if every centered shell satisfies
`∑_{λ ∈ shell_u} ‖Ψ λ‖^2 ≤ #shell_u · a_u · |P_σ|^2` (with `a_u ≥ 0`) and
`(1 + (σ+1)/2) · ∑_u min (2^(u+1)) (2^t) · a_u ≤ ε^2 |V_{σ,s}| / 2^t`, then
`WeightedFourier b N j0 s σ ε`. -/
theorem weightedFourier_of_shell_averages_refined (b : ℕ → ℕ) (N j0 s σ : ℕ) (ε : ℝ)
    (a : ℕ → ℝ) (ha : ∀ u, 0 ≤ a u)
    (hshell : ∀ u ∈ range (σ + 1 + (s - σ)),
      ∑ lam ∈ cshell (σ + 1) (s - σ) u,
        ‖Psi (shellP b j0 σ) (σ + 1) (s - σ) (yPrime j0 σ (s - σ)) lam‖ ^ 2 ≤
      (cshell (σ + 1) (s - σ) u).card * (a u * ((shellP b j0 σ).card : ℝ) ^ 2))
    (hfin : (1 + ((σ + 1 : ℕ) : ℝ) / 2) *
        ∑ u ∈ range (σ + 1 + (s - σ)), min (2 ^ (u + 1)) (2 ^ (s - σ)) * a u ≤
      ε ^ 2 * (shellV b N j0 σ (s - σ)).card / 2 ^ (s - σ)) :
    WeightedFourier b N j0 s σ ε := by
  unfold WeightedFourier
  set P2 : ℝ := ((shellP b j0 σ).card : ℝ) ^ 2
  have hP2 : 0 ≤ P2 := by positivity
  have hbase := weighted_sum_le_of_shell_averages_refined (σ + 1) (s - σ)
    (fun lam => ‖Psi (shellP b j0 σ) (σ + 1) (s - σ) (yPrime j0 σ (s - σ)) lam‖ ^ 2)
    (fun u => a u * P2) (fun _ => by positivity) (fun u => mul_nonneg (ha u) hP2) hshell
  have hpre : (0 : ℝ) ≤ 1 + ((σ + 1 : ℕ) : ℝ) / 2 := by positivity
  calc (1 + ((σ + 1 : ℕ) : ℝ) / 2) * ∑ g ∈ Ico 1 (2 ^ (s - σ)), ∑ k ∈ range (2 ^ (σ + 1)),
        ‖coef (σ + 1) (s - σ) (g + 2 ^ (s - σ) * k)‖ *
          ‖Psi (shellP b j0 σ) (σ + 1) (s - σ) (yPrime j0 σ (s - σ))
            (g + 2 ^ (s - σ) * k)‖ ^ 2
      ≤ (1 + ((σ + 1 : ℕ) : ℝ) / 2) *
          ∑ u ∈ range (σ + 1 + (s - σ)), min (2 ^ (u + 1)) (2 ^ (s - σ)) * (a u * P2) :=
        mul_le_mul_of_nonneg_left hbase hpre
    _ = ((1 + ((σ + 1 : ℕ) : ℝ) / 2) *
          ∑ u ∈ range (σ + 1 + (s - σ)), min (2 ^ (u + 1)) (2 ^ (s - σ)) * a u) * P2 := by
        rw [mul_assoc, sum_mul]
        congr 1
        exact sum_congr rfl fun _ _ => by ring
    _ ≤ (ε ^ 2 * (shellV b N j0 σ (s - σ)).card / 2 ^ (s - σ)) * P2 :=
        mul_le_mul_of_nonneg_right hfin hP2
    _ = ε ^ 2 * P2 * (shellV b N j0 σ (s - σ)).card / 2 ^ (s - σ) := by ring

end ShellRefined
end EOC
