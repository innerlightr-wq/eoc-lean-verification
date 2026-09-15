import EOC.PsiSieve
import EOC.ShellRefined
import EOC.SpacingChain

/-!
# The (C3) sieve for `Ψ` in centered-shell form

`PsiSieve.psi_shell_sieve` bounds `∑_{k<H} ‖Ψ(a+k)‖²` on any `H` consecutive frequencies.
A centered shell `cshell (σ+1) t u` lies in two such intervals of length `2^u`
(`[2^u, 2^{u+1})` and `[M+1−2^{u+1}, M+1−2^u)`, `M = 2^{σ+1+t}`), so

* `cshell_subset_two_intervals` — the covering;
* `sum_cshell_le_two_intervals` — for `F ≥ 0`, the shell sum is at most the two interval sums;
* `sieveBound` — the right-hand side of `psi_shell_sieve`;
* `psi_cshell_sieve` — `∑_{λ ∈ shell_u} ‖Ψ λ‖² ≤ 2 · sieveBound(N, 2^u)^2`;
* `weighted_sum_le_of_shell_sums_refined` — refined weighted sum from per-shell SUM bounds,
  weight `min 1 (2^t/(2·2^u))` per shell (no normalization by `#shell`);
* **`weightedFourier_of_psiSieve`** — `WeightedFourier` from a choice of split `N_u` per shell and
  the budget `(1 + (σ+1)/2) · ∑_u min 1 (2^t/(2·2^u)) · 2·sieveBound(N_u, 2^u)^2
  ≤ ε² |P_σ|² |V_{σ,s}| / 2^t`.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace PsiShellBound

open Finset TwistExpansion PrefixCollision WeightedChain ShellDecomposition

/-- Sum over a union is at most the sum of the sums (nonnegative terms). -/
theorem sum_union_le_of_nonneg {ι : Type*} [DecidableEq ι] {A B : Finset ι}
    {F : ι → ℝ} (hF : ∀ x ∈ A ∪ B, 0 ≤ F x) :
    ∑ x ∈ A ∪ B, F x ≤ ∑ x ∈ A, F x + ∑ x ∈ B, F x := by
  rw [← sum_union_inter]
  have : 0 ≤ ∑ x ∈ A ∩ B, F x :=
    sum_nonneg fun x hx => hF x (mem_union_left _ (mem_inter.mp hx).1)
  linarith

/-- Centered shells lie in two intervals of length `2^u`. -/
theorem cshell_subset_two_intervals (r t u : ℕ) :
    cshell r t u ⊆ Ico (2 ^ u) (2 ^ u + 2 ^ u) ∪
      Ico (2 ^ (r + t) + 1 - 2 ^ (u + 1)) (2 ^ (r + t) + 1 - 2 ^ (u + 1) + 2 ^ u) := by
  intro lam h
  have hb := mem_cshell_bounds h
  have hlt : lam < 2 ^ (r + t) := by
    simp only [cshell, nondvd, mem_filter, mem_Ico] at h; exact h.1.1.2
  have hpu : 2 ^ (u + 1) = 2 ^ u + 2 ^ u := by rw [pow_succ]; ring
  simp only [mem_union, mem_Ico]
  unfold cdist at hb
  by_cases hc : lam ≤ 2 ^ (r + t) - lam
  · left; rw [min_eq_left hc] at hb; omega
  · right; rw [min_eq_right (by omega)] at hb; omega

/-- For `F ≥ 0`, a centered-shell sum is at most the sums over the two covering intervals. -/
theorem sum_cshell_le_two_intervals (r t u : ℕ) (F : ℕ → ℝ) (hF : ∀ lam, 0 ≤ F lam) :
    ∑ lam ∈ cshell r t u, F lam ≤
      ∑ k ∈ range (2 ^ u), F (2 ^ u + k) +
        ∑ k ∈ range (2 ^ u), F (2 ^ (r + t) + 1 - 2 ^ (u + 1) + k) := by
  classical
  calc ∑ lam ∈ cshell r t u, F lam
      ≤ ∑ lam ∈ Ico (2 ^ u) (2 ^ u + 2 ^ u) ∪
          Ico (2 ^ (r + t) + 1 - 2 ^ (u + 1)) (2 ^ (r + t) + 1 - 2 ^ (u + 1) + 2 ^ u), F lam :=
        sum_le_sum_of_subset_of_nonneg (cshell_subset_two_intervals r t u)
          (fun lam _ _ => hF lam)
    _ ≤ ∑ lam ∈ Ico (2 ^ u) (2 ^ u + 2 ^ u), F lam +
          ∑ lam ∈ Ico (2 ^ (r + t) + 1 - 2 ^ (u + 1)) (2 ^ (r + t) + 1 - 2 ^ (u + 1) + 2 ^ u),
            F lam := sum_union_le_of_nonneg (fun lam _ => hF lam)
    _ = _ := by rw [sum_Ico_eq_sum_range, sum_Ico_eq_sum_range]; simp


/-- The right-hand side of `PsiSieve.psi_shell_sieve` for split `N` and interval length `H`. -/
noncomputable def sieveBound (b : ℕ → ℕ) (j0 σ N H : ℕ) : ℝ :=
  ∑ S ∈ range (σ + 1), ((shellV b j0 N S (σ - S)).card : ℝ) *
    min (√(H : ℝ) * (shellP b N S).card)
      √((shellP b N S).card * (PsiSieve.Xmax b N / 3 ^ N + 1 : ℕ) *
        (H + 2 * (3 ^ N : ℕ) * (1 + Real.log (3 ^ N : ℕ))))

/-- An interval sum of `‖Ψ‖²` is at most `sieveBound²`. -/
theorem sum_interval_le_sieveBound_sq (b : ℕ → ℕ) (j0 σ t N : ℕ) (hN1 : 1 ≤ N) (hNj : N < j0)
    (hX : 2 * PsiSieve.Xmax b N ≤ 2 ^ (σ + 1 + t)) (a H : ℕ) :
    ∑ k ∈ range H, ‖Psi (shellP b j0 σ) (σ + 1) t (yPrime j0 σ t) (a + k)‖ ^ 2 ≤
      sieveBound b j0 σ N H ^ 2 := by
  have h := PsiSieve.psi_shell_sieve b j0 σ t N hN1 hNj hX a H
  have h0 : 0 ≤ ∑ k ∈ range H, ‖Psi (shellP b j0 σ) (σ + 1) t (yPrime j0 σ t) (a + k)‖ ^ 2 :=
    sum_nonneg fun _ _ => by positivity
  have hs := Real.sq_sqrt h0
  rw [← hs]
  exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2

/-- **(C3) on a centered shell.** `∑_{λ ∈ shell_u} ‖Ψ λ‖² ≤ 2 · sieveBound(N, 2^u)²`. -/
theorem psi_cshell_sieve (b : ℕ → ℕ) (j0 σ t N u : ℕ) (hN1 : 1 ≤ N) (hNj : N < j0)
    (hX : 2 * PsiSieve.Xmax b N ≤ 2 ^ (σ + 1 + t)) :
    ∑ lam ∈ cshell (σ + 1) t u, ‖Psi (shellP b j0 σ) (σ + 1) t (yPrime j0 σ t) lam‖ ^ 2 ≤
      2 * sieveBound b j0 σ N (2 ^ u) ^ 2 := by
  refine (sum_cshell_le_two_intervals (σ + 1) t u _ (fun _ => by positivity)).trans ?_
  have h1 := sum_interval_le_sieveBound_sq b j0 σ t N hN1 hNj hX (2 ^ u) (2 ^ u)
  have h2 := sum_interval_le_sieveBound_sq b j0 σ t N hN1 hNj hX
    (2 ^ (σ + 1 + t) + 1 - 2 ^ (u + 1)) (2 ^ u)
  linarith

/-- **Refined weighted sum from per-shell sums.** If `F ≥ 0` and `∑_{λ ∈ shell_u} F λ ≤ s_u`
(with `s_u ≥ 0`), then `∑_g ∑_k ‖coef(g + 2^t k)‖ F(g + 2^t k) ≤ ∑_u min 1 (2^t/(2·2^u)) · s_u`. -/
theorem weighted_sum_le_of_shell_sums_refined (r t : ℕ) (F : ℕ → ℝ) (sb : ℕ → ℝ)
    (hF : ∀ lam, 0 ≤ F lam)
    (hshell : ∀ u ∈ range (r + t), ∑ lam ∈ cshell r t u, F lam ≤ sb u) :
    ∑ g ∈ Ico 1 (2 ^ t), ∑ k ∈ range (2 ^ r), ‖coef r t (g + 2 ^ t * k)‖ * F (g + 2 ^ t * k) ≤
      ∑ u ∈ range (r + t), min 1 (2 ^ t / (2 * 2 ^ u)) * sb u := by
  rw [sum_fibre_eq_sum_nondvd r t (fun lam => ‖coef r t lam‖ * F lam)]
  change ∑ lam ∈ nondvd r t, ‖coef r t lam‖ * F lam ≤ _
  rw [sum_nondvd_eq_sum_cshell]
  refine sum_le_sum fun u hu => ?_
  set w : ℝ := min 1 (2 ^ t / (2 * 2 ^ u))
  have hw0 : 0 ≤ w := le_min zero_le_one (by positivity)
  have hw : ∀ lam ∈ cshell r t u, ‖coef r t lam‖ * F lam ≤ w * F lam :=
    fun lam hl => mul_le_mul_of_nonneg_right
      (ShellRefined.norm_coef_le_cshell_refined hl) (hF lam)
  calc ∑ lam ∈ cshell r t u, ‖coef r t lam‖ * F lam
      ≤ ∑ lam ∈ cshell r t u, w * F lam := sum_le_sum hw
    _ = w * ∑ lam ∈ cshell r t u, F lam := by rw [mul_sum]
    _ ≤ w * sb u := mul_le_mul_of_nonneg_left (hshell u hu) hw0

/-- **`WeightedFourier` from the (C3) sieve for `Ψ`.** With `t = s − σ`: choose a split `N_u`
for every centered shell `u < σ + 1 + t` with `1 ≤ N_u < j0` and `2·Xmax(N_u) ≤ 2^{σ+1+t}`.
If `(1 + (σ+1)/2) · ∑_u min 1 (2^t/(2·2^u)) · 2·sieveBound(N_u, 2^u)² ≤ ε² |P_σ|² |V_{σ,s}| / 2^t`,
then `WeightedFourier b N j0 s σ ε`. -/
theorem weightedFourier_of_psiSieve (b : ℕ → ℕ) (N j0 s σ : ℕ) (ε : ℝ) (Nsplit : ℕ → ℕ)
    (hN1 : ∀ u ∈ range (σ + 1 + (s - σ)), 1 ≤ Nsplit u)
    (hNj : ∀ u ∈ range (σ + 1 + (s - σ)), Nsplit u < j0)
    (hX : ∀ u ∈ range (σ + 1 + (s - σ)), 2 * PsiSieve.Xmax b (Nsplit u) ≤ 2 ^ (σ + 1 + (s - σ)))
    (hfin : (1 + ((σ + 1 : ℕ) : ℝ) / 2) * ∑ u ∈ range (σ + 1 + (s - σ)),
        min 1 (2 ^ (s - σ) / (2 * 2 ^ u)) * (2 * sieveBound b j0 σ (Nsplit u) (2 ^ u) ^ 2) ≤
      ε ^ 2 * ((shellP b j0 σ).card : ℝ) ^ 2 * (shellV b N j0 σ (s - σ)).card / 2 ^ (s - σ)) :
    WeightedFourier b N j0 s σ ε := by
  unfold WeightedFourier
  have hbase := weighted_sum_le_of_shell_sums_refined (σ + 1) (s - σ)
    (fun lam => ‖Psi (shellP b j0 σ) (σ + 1) (s - σ) (yPrime j0 σ (s - σ)) lam‖ ^ 2)
    (fun u => 2 * sieveBound b j0 σ (Nsplit u) (2 ^ u) ^ 2) (fun _ => by positivity)
    (fun u hu => psi_cshell_sieve b j0 σ (s - σ) (Nsplit u) u (hN1 u hu) (hNj u hu) (hX u hu))
  have hpre : (0 : ℝ) ≤ 1 + ((σ + 1 : ℕ) : ℝ) / 2 := by positivity
  exact (mul_le_mul_of_nonneg_left hbase hpre).trans hfin

end PsiShellBound
end EOC
