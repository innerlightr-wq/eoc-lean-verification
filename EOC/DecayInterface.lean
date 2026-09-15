import EOC.SpacingChain
import EOC.PsiShellBound
import EOC.PowerOrbit
import EOC.ShellRefined

/-!
# Dyadic kernel summation and the mixed shell interface

* `kern_le_dyadic` / `kerZ_pow_le` — per-pair dyadic majorant of the interval kernel with `H = 2^u`,
  `M = 2^V`: `kerZ ≤ 2^u·[c < 2^{V−u}] + ∑_{v<u} 2^v·[c < 2^{V−v}]` (`c` = centered distance).
* `sum_kerZ_le_dyadic` — summed over pairs:
  `∑_{i,j} kerZ ≤ 2^u · pairSpacing(2^{V−u}) + ∑_{v<u} 2^v · pairSpacing(2^{V−v})`.
* **`sum_sq_le_of_spacingExponent`** — **spacing exponent ⇒ interval energy**: if every dyadic pair
  count satisfies `pairSpacing(2^{V−v}) ≤ C·(#T)²·2^{−θv} + #T` for `v ≤ u` (`0 ≤ C`, `θ ≤ 1`), then
  `∑_{k<2^u} ‖∑_i e((a+k) y_i / 2^V)‖² ≤ C·(u+1)·2^u·2^{−θu}·(#T)² + 2·2^u·#T`.
* `weightedFourier_of_shell_sums` — generic per-shell-sum form of the refined interface.
* **`weightedFourier_of_mixed`** — per shell, the minimum of the (C3) sieve bound and any available
  hypothesis bound `D u`.
* `LowFreqDecay` and **`weightedFourier_of_lowFreqDecay_and_sieve`** — a low-frequency decay
  hypothesis on shells `u ≤ U`, the sieve elsewhere.
* **`weightedFourier_of_spreading_and_sieve`** — `PowerOrbit.ContinuationSpreading` feeds the same
  mixed interface.

All analytic input stays a hypothesis. No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace DecayInterface

open Finset SwapBound TwistExpansion PrefixCollision WeightedChain ShellDecomposition
  SpacingChain PsiShellBound

/-! ## 1. Dyadic kernel summation -/

/-- Per-distance dyadic majorant of the interval kernel (`c` a centered distance in `[0, 2^V)`). -/
theorem kern_le_dyadic (V : ℕ) (c : ℤ) (_hc0 : 0 ≤ c) (hcV : c < 2 ^ V) :
    ∀ u, u ≤ V →
      (if c = 0 then (2 : ℝ) ^ u else min ((2 : ℝ) ^ u) ((2 : ℝ) ^ V / (2 * (c : ℝ)))) ≤
        (2 : ℝ) ^ u * (if c < 2 ^ (V - u) then 1 else 0) +
          ∑ v ∈ range u, (2 : ℝ) ^ v * (if c < 2 ^ (V - v) then 1 else 0) := by
  intro u
  induction u with
  | zero =>
    intro _
    have h1 : c < 2 ^ (V - 0) := by simpa using hcV
    simp only [pow_zero, h1, ite_true, mul_one, range_zero, sum_empty, add_zero]
    split_ifs
    · exact le_rfl
    · exact min_le_left _ _
  | succ u ih =>
    intro hu
    have hsum_nonneg : 0 ≤ ∑ v ∈ range u, (2 : ℝ) ^ v * (if c < 2 ^ (V - v) then 1 else 0) :=
      sum_nonneg fun v _ => mul_nonneg (by positivity) (by split_ifs <;> norm_num)
    rw [sum_range_succ]
    by_cases hA : c < 2 ^ (V - (u + 1))
    · -- close pair: kernel ≤ H = 2^{u+1}
      have hL : (if c = 0 then (2 : ℝ) ^ (u + 1) else
          min ((2 : ℝ) ^ (u + 1)) ((2 : ℝ) ^ V / (2 * (c : ℝ)))) ≤ (2 : ℝ) ^ (u + 1) := by
        split_ifs
        · exact le_rfl
        · exact min_le_left _ _
      have hlast : 0 ≤ (2 : ℝ) ^ u * (if c < 2 ^ (V - u) then 1 else 0) :=
        mul_nonneg (by positivity) (by split_ifs <;> norm_num)
      simp only [hA, ite_true, mul_one]
      linarith
    · have hA' : (2 : ℤ) ^ (V - (u + 1)) ≤ c := not_lt.mp hA
      have hcpos : (0 : ℤ) < c := lt_of_lt_of_le (by positivity) hA'
      have hc0' : c ≠ 0 := hcpos.ne'
      have hAr : (2 : ℝ) ^ (V - (u + 1)) ≤ (c : ℝ) := by exact_mod_cast hA'
      have hcr : (0 : ℝ) < c := by exact_mod_cast hcpos
      have hVsplit : (2 : ℝ) ^ V = 2 ^ (u + 1) * 2 ^ (V - (u + 1)) := by
        rw [← pow_add, Nat.add_sub_cancel' hu]
      -- x := 2^V / (2c) ≤ 2^u
      have hx : (2 : ℝ) ^ V / (2 * (c : ℝ)) ≤ 2 ^ u := by
        rw [div_le_iff₀ (by positivity), hVsplit]
        have : (2 : ℝ) ^ (u + 1) = 2 * 2 ^ u := by rw [pow_succ]; ring
        rw [this]
        have h2u : (0 : ℝ) ≤ 2 ^ u := by positivity
        nlinarith
      have hL : (if c = 0 then (2 : ℝ) ^ (u + 1) else
          min ((2 : ℝ) ^ (u + 1)) ((2 : ℝ) ^ V / (2 * (c : ℝ)))) ≤ (2 : ℝ) ^ V / (2 * (c : ℝ)) := by
        simp only [hc0', ↓reduceIte]; exact min_le_right _ _
      simp only [hA, ite_false, mul_zero, zero_add]
      by_cases hB : c < 2 ^ (V - u)
      · simp only [hB, ite_true, mul_one]
        linarith
      · simp only [hB, ite_false, mul_zero, add_zero]
        have hih := ih (by omega)
        simp only [hc0', ↓reduceIte, min_eq_right hx] at hih
        simp only [hB, ite_false, mul_zero, zero_add] at hih
        linarith

theorem centDistZ_lt {M : ℤ} (hM : 0 < M) (n : ℤ) : centDistZ M n < M := by
  unfold centDistZ
  have h1 : n % M < M := Int.emod_lt_of_pos n hM
  exact lt_of_le_of_lt (min_le_left _ _) h1

/-- The dyadic majorant for `kerZ` with `H = 2^u`, `M = 2^V`. -/
theorem kerZ_pow_le (V u : ℕ) (hu : u ≤ V) (n : ℤ) :
    kerZ (2 ^ u) (2 ^ V) n ≤
      (2 : ℝ) ^ u * (if centDistZ (2 ^ V) n < 2 ^ (V - u) then 1 else 0) +
        ∑ v ∈ range u, (2 : ℝ) ^ v * (if centDistZ (2 ^ V) n < 2 ^ (V - v) then 1 else 0) := by
  have hM : (0 : ℤ) < 2 ^ V := by positivity
  have h := kern_le_dyadic V (centDistZ (2 ^ V) n) (centDistZ_nonneg hM n) (centDistZ_lt hM n) u hu
  unfold kerZ
  push_cast
  exact h

/-- **Dyadic kernel summation** over pairs. -/
theorem sum_kerZ_le_dyadic {ι : Type*} (T : Finset ι) (y : ι → ℤ) (V u : ℕ) (hu : u ≤ V) :
    ∑ i ∈ T, ∑ j ∈ T, kerZ (2 ^ u) (2 ^ V) (y i - y j) ≤
      (2 : ℝ) ^ u * pairSpacing T y (2 ^ V) (2 ^ (V - u)) +
        ∑ v ∈ range u, (2 : ℝ) ^ v * pairSpacing T y (2 ^ V) (2 ^ (V - v)) := by
  set ind : ℕ → ι × ι → ℝ := fun v p =>
    if centDistZ (2 ^ V) (y p.1 - y p.2) < 2 ^ (V - v) then 1 else 0
  have hcount : ∀ v, (pairSpacing T y (2 ^ V) (2 ^ (V - v)) : ℝ) = ∑ p ∈ T ×ˢ T, ind v p := by
    intro v
    simp only [ind, pairSpacing]
    rw [sum_boole]
  rw [← sum_product' (f := fun i j => kerZ (2 ^ u) (2 ^ V) (y i - y j))]
  calc ∑ p ∈ T ×ˢ T, kerZ (2 ^ u) (2 ^ V) (y p.1 - y p.2)
      ≤ ∑ p ∈ T ×ˢ T, ((2 : ℝ) ^ u * ind u p + ∑ v ∈ range u, (2 : ℝ) ^ v * ind v p) :=
        sum_le_sum fun p _ => kerZ_pow_le V u hu _
    _ = (2 : ℝ) ^ u * ∑ p ∈ T ×ˢ T, ind u p +
          ∑ v ∈ range u, (2 : ℝ) ^ v * ∑ p ∈ T ×ˢ T, ind v p := by
        rw [sum_add_distrib, ← mul_sum, sum_comm]
        congr 1
        exact sum_congr rfl fun v _ => by rw [mul_sum]
    _ = _ := by
        rw [hcount u]
        congr 1
        exact sum_congr rfl fun v _ => by rw [hcount v]

/-- `2^v · 2^{−θv} ≤ 2^u · 2^{−θu}` for `v ≤ u`, `θ ≤ 1`. -/
theorem two_pow_mul_rpow_le {θ : ℝ} (hθ : θ ≤ 1) {v u : ℕ} (hvu : v ≤ u) :
    (2 : ℝ) ^ v * (2 : ℝ) ^ (-(θ * v)) ≤ (2 : ℝ) ^ u * (2 : ℝ) ^ (-(θ * u)) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have e : ∀ w : ℕ, (2 : ℝ) ^ w * (2 : ℝ) ^ (-(θ * w)) = (2 : ℝ) ^ ((1 - θ) * w) := by
    intro w
    rw [← Real.rpow_natCast, ← Real.rpow_add h2]
    congr 1; ring
  rw [e v, e u]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hvu' : (v : ℝ) ≤ u := by exact_mod_cast hvu
  nlinarith

theorem sum_range_two_pow_le (u : ℕ) : ∑ v ∈ range u, (2 : ℝ) ^ v ≤ 2 ^ u := by
  induction u with
  | zero => simp
  | succ u ih =>
    rw [sum_range_succ, pow_succ]
    linarith [pow_pos (show (0 : ℝ) < 2 by norm_num) u]

/-- **Spacing exponent ⇒ interval energy** (dyadic kernel summation). With `M = 2^V`, `H = 2^u`,
`u ≤ V`, `0 ≤ C`, `θ ≤ 1`: if `pairSpacing T y M (2^{V−v}) ≤ C·(#T)²·2^{−θv} + #T` for all `v ≤ u`,
then `∑_{k<2^u} ‖∑_{i∈T} e((a+k) y_i / M)‖² ≤ C·(u+1)·2^u·2^{−θu}·(#T)² + 2·2^u·#T`. -/
theorem sum_sq_le_of_spacingExponent {ι : Type*} (T : Finset ι) (y : ι → ℤ) (a : ℝ) (V u : ℕ)
    (hu : u ≤ V) (C θ : ℝ) (hC : 0 ≤ C) (hθ : θ ≤ 1)
    (hE : ∀ v ≤ u, (pairSpacing T y (2 ^ V) (2 ^ (V - v)) : ℝ) ≤
      C * (T.card : ℝ) ^ 2 * (2 : ℝ) ^ (-(θ * v)) + T.card) :
    ∑ k ∈ range (2 ^ u), ‖∑ i ∈ T, ee ((a + k) * ((y i : ℝ) / ((2 ^ V : ℤ) : ℝ)))‖ ^ 2 ≤
      C * (u + 1) * 2 ^ u * (2 : ℝ) ^ (-(θ * u)) * (T.card : ℝ) ^ 2 + 2 * 2 ^ u * T.card := by
  have hM : (0 : ℤ) < 2 ^ V := by positivity
  have h1 := sum_sq_le_kernel T y (2 ^ u) a hM
  have h2 := sum_kerZ_le_dyadic T y V u hu
  set n : ℝ := (T.card : ℝ)
  set R : ℝ := (2 : ℝ) ^ u * (2 : ℝ) ^ (-(θ * u))
  have hn : 0 ≤ n := by positivity
  have hR : 0 ≤ R := by positivity
  -- first term
  have hA : (2 : ℝ) ^ u * pairSpacing T y (2 ^ V) (2 ^ (V - u)) ≤ C * n ^ 2 * R + 2 ^ u * n := by
    have := hE u le_rfl
    calc (2 : ℝ) ^ u * pairSpacing T y (2 ^ V) (2 ^ (V - u))
        ≤ (2 : ℝ) ^ u * (C * n ^ 2 * (2 : ℝ) ^ (-(θ * u)) + n) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = C * n ^ 2 * R + 2 ^ u * n := by simp only [R]; ring
  -- dyadic tail
  have hB : ∑ v ∈ range u, (2 : ℝ) ^ v * pairSpacing T y (2 ^ V) (2 ^ (V - v)) ≤
      C * n ^ 2 * (u * R) + 2 ^ u * n := by
    calc ∑ v ∈ range u, (2 : ℝ) ^ v * pairSpacing T y (2 ^ V) (2 ^ (V - v))
        ≤ ∑ v ∈ range u, (C * n ^ 2 * ((2 : ℝ) ^ v * (2 : ℝ) ^ (-(θ * v))) + (2 : ℝ) ^ v * n) := by
          refine sum_le_sum fun v hv => ?_
          have hv' : v ≤ u := (mem_range.mp hv).le
          have := hE v hv'
          calc (2 : ℝ) ^ v * pairSpacing T y (2 ^ V) (2 ^ (V - v))
              ≤ (2 : ℝ) ^ v * (C * n ^ 2 * (2 : ℝ) ^ (-(θ * v)) + n) :=
                mul_le_mul_of_nonneg_left this (by positivity)
            _ = _ := by ring
      _ ≤ ∑ v ∈ range u, (C * n ^ 2 * R + (2 : ℝ) ^ v * n) := by
          refine sum_le_sum fun v hv => ?_
          have := two_pow_mul_rpow_le hθ (mem_range.mp hv).le
          have hCn : 0 ≤ C * n ^ 2 := by positivity
          nlinarith
      _ = C * n ^ 2 * (u * R) + (∑ v ∈ range u, (2 : ℝ) ^ v) * n := by
          rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, sum_mul]; ring
      _ ≤ C * n ^ 2 * (u * R) + 2 ^ u * n :=
          by linarith [mul_le_mul_of_nonneg_right (sum_range_two_pow_le u) hn]
  have hcast : ((2 ^ u : ℕ) : ℝ) = (2 : ℝ) ^ u := by push_cast; ring
  calc ∑ k ∈ range (2 ^ u), ‖∑ i ∈ T, ee ((a + k) * ((y i : ℝ) / ((2 ^ V : ℤ) : ℝ)))‖ ^ 2
      ≤ ∑ i ∈ T, ∑ j ∈ T, kerZ (2 ^ u) (2 ^ V) (y i - y j) := h1
    _ ≤ _ := h2
    _ ≤ C * n ^ 2 * R + 2 ^ u * n + (C * n ^ 2 * (u * R) + 2 ^ u * n) := add_le_add hA hB
    _ = C * (u + 1) * 2 ^ u * (2 : ℝ) ^ (-(θ * u)) * n ^ 2 + 2 * 2 ^ u * n := by
        simp only [R]; ring

/-! ## 2. Mixed shell interface -/

section Mixed

variable (b : ℕ → ℕ)

/-- **`WeightedFourier` from arbitrary per-shell sum bounds** (refined weights). -/
theorem weightedFourier_of_shell_sums (N j0 s σ : ℕ) (ε : ℝ) (sb : ℕ → ℝ)
    (hshell : ∀ u ∈ range (σ + 1 + (s - σ)),
      ∑ lam ∈ cshell (σ + 1) (s - σ) u,
        ‖Psi (shellP b j0 σ) (σ + 1) (s - σ) (yPrime j0 σ (s - σ)) lam‖ ^ 2 ≤ sb u)
    (hfin : (1 + ((σ + 1 : ℕ) : ℝ) / 2) * ∑ u ∈ range (σ + 1 + (s - σ)),
        min 1 (2 ^ (s - σ) / (2 * 2 ^ u)) * sb u ≤
      ε ^ 2 * ((shellP b j0 σ).card : ℝ) ^ 2 * (shellV b N j0 σ (s - σ)).card / 2 ^ (s - σ)) :
    WeightedFourier b N j0 s σ ε := by
  unfold WeightedFourier
  have hbase := weighted_sum_le_of_shell_sums_refined (σ + 1) (s - σ)
    (fun lam => ‖Psi (shellP b j0 σ) (σ + 1) (s - σ) (yPrime j0 σ (s - σ)) lam‖ ^ 2)
    sb (fun _ => by positivity) hshell
  have hpre : (0 : ℝ) ≤ 1 + ((σ + 1 : ℕ) : ℝ) / 2 := by positivity
  exact (mul_le_mul_of_nonneg_left hbase hpre).trans hfin

/-- The mixed per-shell bound: on shells where a hypothesis bound `D u` is available (`hasD u`),
the minimum of `D u` and the (C3) sieve bound; elsewhere the sieve bound. -/
noncomputable def mixedBound (j0 σ : ℕ) (Nsplit : ℕ → ℕ) (hasD : ℕ → Prop) [DecidablePred hasD]
    (D : ℕ → ℝ) (u : ℕ) : ℝ :=
  if hasD u then min (D u) (2 * sieveBound b j0 σ (Nsplit u) (2 ^ u) ^ 2)
  else 2 * sieveBound b j0 σ (Nsplit u) (2 ^ u) ^ 2

/-- **Mixed interface.** Every shell uses the (C3) sieve; shells with an extra hypothesis bound
`D u` use the better of the two. -/
theorem weightedFourier_of_mixed (N j0 s σ : ℕ) (ε : ℝ) (Nsplit : ℕ → ℕ)
    (hasD : ℕ → Prop) [DecidablePred hasD] (D : ℕ → ℝ)
    (hN1 : ∀ u ∈ range (σ + 1 + (s - σ)), 1 ≤ Nsplit u)
    (hNj : ∀ u ∈ range (σ + 1 + (s - σ)), Nsplit u < j0)
    (hX : ∀ u ∈ range (σ + 1 + (s - σ)), 2 * PsiSieve.Xmax b (Nsplit u) ≤ 2 ^ (σ + 1 + (s - σ)))
    (hD : ∀ u ∈ range (σ + 1 + (s - σ)), hasD u →
      ∑ lam ∈ cshell (σ + 1) (s - σ) u,
        ‖Psi (shellP b j0 σ) (σ + 1) (s - σ) (yPrime j0 σ (s - σ)) lam‖ ^ 2 ≤ D u)
    (hfin : (1 + ((σ + 1 : ℕ) : ℝ) / 2) * ∑ u ∈ range (σ + 1 + (s - σ)),
        min 1 (2 ^ (s - σ) / (2 * 2 ^ u)) * mixedBound b j0 σ Nsplit hasD D u ≤
      ε ^ 2 * ((shellP b j0 σ).card : ℝ) ^ 2 * (shellV b N j0 σ (s - σ)).card / 2 ^ (s - σ)) :
    WeightedFourier b N j0 s σ ε := by
  refine weightedFourier_of_shell_sums b N j0 s σ ε _ (fun u hu => ?_) hfin
  have hsieve := psi_cshell_sieve b j0 σ (s - σ) (Nsplit u) u (hN1 u hu) (hNj u hu) (hX u hu)
  unfold mixedBound
  split_ifs with h
  · exact le_min (hD u hu h) hsieve
  · exact hsieve

/-- **Low-frequency decay hypothesis** (analytic input, NOT proved): on every centered shell
`u ≤ U`, `∑_{λ ∈ shell_u} ‖Ψ λ‖² ≤ 2^{u+1} · C · 2^{−γ j0} · |P_σ|²` (i.e. mean square
`≤ C·2^{−γ j0}` per frequency). -/
def LowFreqDecay (j0 σ t U : ℕ) (C γ : ℝ) : Prop :=
  ∀ u ≤ U, ∑ lam ∈ cshell (σ + 1) t u, ‖Psi (shellP b j0 σ) (σ + 1) t (yPrime j0 σ t) lam‖ ^ 2 ≤
    2 ^ (u + 1) * C * (2 : ℝ) ^ (-(γ * j0)) * ((shellP b j0 σ).card : ℝ) ^ 2

/-- **Low-frequency decay on shells `u ≤ U` + (C3) sieve elsewhere ⇒ `WeightedFourier`.** -/
theorem weightedFourier_of_lowFreqDecay_and_sieve (N j0 s σ U : ℕ) (ε C γ : ℝ)
    (Nsplit : ℕ → ℕ)
    (hN1 : ∀ u ∈ range (σ + 1 + (s - σ)), 1 ≤ Nsplit u)
    (hNj : ∀ u ∈ range (σ + 1 + (s - σ)), Nsplit u < j0)
    (hX : ∀ u ∈ range (σ + 1 + (s - σ)), 2 * PsiSieve.Xmax b (Nsplit u) ≤ 2 ^ (σ + 1 + (s - σ)))
    (hdecay : LowFreqDecay b j0 σ (s - σ) U C γ)
    (hfin : (1 + ((σ + 1 : ℕ) : ℝ) / 2) * ∑ u ∈ range (σ + 1 + (s - σ)),
        min 1 (2 ^ (s - σ) / (2 * 2 ^ u)) *
          mixedBound b j0 σ Nsplit (fun u => u ≤ U)
            (fun u => 2 ^ (u + 1) * C * (2 : ℝ) ^ (-(γ * j0)) * ((shellP b j0 σ).card : ℝ) ^ 2) u ≤
      ε ^ 2 * ((shellP b j0 σ).card : ℝ) ^ 2 * (shellV b N j0 σ (s - σ)).card / 2 ^ (s - σ)) :
    WeightedFourier b N j0 s σ ε :=
  weightedFourier_of_mixed b N j0 s σ ε Nsplit (fun u => u ≤ U) _ hN1 hNj hX
    (fun u _ hu => hdecay u hu) hfin

/-! ## 3. `ContinuationSpreading` feeds the mixed interface -/

/-- Per-shell bounds from `PowerOrbit.ContinuationSpreading`, in the form used by
`weightedFourier_of_mixed`. -/
theorem shellBounds_of_continuationSpreading {j0 σ t : ℕ} {Nsplit : ℕ → ℕ} {C θ : ℝ}
    (hN1 : ∀ u ∈ range (σ + 1 + t), 1 ≤ Nsplit u)
    (hNj : ∀ u ∈ range (σ + 1 + t), Nsplit u < j0)
    (h : PowerOrbit.ContinuationSpreading b j0 σ t Nsplit C θ) :
    ∀ u ∈ range (σ + 1 + t), True →
      ∑ lam ∈ cshell (σ + 1) t u, ‖Psi (shellP b j0 σ) (σ + 1) t (yPrime j0 σ t) lam‖ ^ 2 ≤
        2 * (C * 2 ^ u * (2 : ℝ) ^ (-(θ * u)) * ((shellP b j0 σ).card : ℝ) ^ 2) :=
  fun u hu _ => PowerOrbit.shell_sum_le_of_continuationSpreading b hN1 hNj h u hu

/-- **`ContinuationSpreading` + (C3) sieve ⇒ `WeightedFourier`**, shellwise minimum of the two
bounds. -/
theorem weightedFourier_of_spreading_and_sieve (N j0 s σ : ℕ) (ε C θ : ℝ) (Nsplit : ℕ → ℕ)
    (hN1 : ∀ u ∈ range (σ + 1 + (s - σ)), 1 ≤ Nsplit u)
    (hNj : ∀ u ∈ range (σ + 1 + (s - σ)), Nsplit u < j0)
    (hX : ∀ u ∈ range (σ + 1 + (s - σ)), 2 * PsiSieve.Xmax b (Nsplit u) ≤ 2 ^ (σ + 1 + (s - σ)))
    (h : PowerOrbit.ContinuationSpreading b j0 σ (s - σ) Nsplit C θ)
    (hfin : (1 + ((σ + 1 : ℕ) : ℝ) / 2) * ∑ u ∈ range (σ + 1 + (s - σ)),
        min 1 (2 ^ (s - σ) / (2 * 2 ^ u)) *
          mixedBound b j0 σ Nsplit (fun _ => True)
            (fun u => 2 * (C * 2 ^ u * (2 : ℝ) ^ (-(θ * u)) * ((shellP b j0 σ).card : ℝ) ^ 2)) u ≤
      ε ^ 2 * ((shellP b j0 σ).card : ℝ) ^ 2 * (shellV b N j0 σ (s - σ)).card / 2 ^ (s - σ)) :
    WeightedFourier b N j0 s σ ε :=
  weightedFourier_of_mixed b N j0 s σ ε Nsplit (fun _ => True) _ hN1 hNj hX
    (shellBounds_of_continuationSpreading b hN1 hNj h) hfin

end Mixed

end DecayInterface
end EOC
