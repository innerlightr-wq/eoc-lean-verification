import EOC.CapacityBounds
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Elementary binomial entropy bounds and the confined-language entropy

With `T n k j = C(n,j) · k^j · (n-k)^(n-j)`, the binomial theorem gives
`∑_{j ≤ n} T n k j = n^n`, and the terms are unimodal with maximum at `j = k`. Hence the two
natural-number inequalities (valid for every `k ≤ n`, with `0^0 = 1`):

* `choose_mul_pow_le` — `C(n,k) · k^k · (n-k)^(n-k) ≤ n^n`;
* `pow_le_succ_mul_choose_mul_pow` — `n^n ≤ (n+1) · C(n,k) · k^k · (n-k)^(n-k)`.

In logarithmic form, with `ent n k = n log n − k log k − (n−k) log (n−k)` (`= n·H(k/n)` in nats):
`log C(n,k) ≤ ent n k ≤ log (n+1) + log C(n,k)`.

Combined with the capacity sandwich (`CapacityBounds.collatz_capacity_sandwich`) this gives
explicit two-sided finite bounds for `W_c(N) = #confinedWords N (collatzBarrier c)`
(`log_card_confined_le`, `log_card_confined_ge`), and the entropy limit (paper Thm 6.2):

* `tendsto_log_card_confined` — `log W_c(N) / N → α log α − (α−1) log (α−1) = α · H(1/α)`
  (natural logarithms; `alpha_entropy_eq` identifies the constant with `α · binEntropy (1/α)`).

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace EntropyBounds

open Finset Real Filter Topology CapacityBounds

/-! ## 1. Natural-number binomial bounds -/

/-- Binomial term `C(n,j) · k^j · (n-k)^(n-j)`. -/
def T (n k j : ℕ) : ℕ := n.choose j * k ^ j * (n - k) ^ (n - j)

theorem sum_T (n k : ℕ) (hk : k ≤ n) : ∑ j ∈ range (n + 1), T n k j = n ^ n := by
  have h := add_pow k (n - k) n
  rw [Nat.add_sub_cancel' hk] at h
  rw [h]
  exact sum_congr rfl fun j _ => by unfold T; rw [Nat.cast_id]; ring

/-- `C(n,k) · k^k · (n-k)^(n-k) ≤ n^n`. -/
theorem choose_mul_pow_le (n k : ℕ) (hk : k ≤ n) :
    n.choose k * k ^ k * (n - k) ^ (n - k) ≤ n ^ n := by
  rw [← sum_T n k hk]
  exact single_le_sum (f := T n k) (fun _ _ => Nat.zero_le _) (mem_range.mpr (Nat.lt_succ_of_le hk))

theorem T_succ (n k j : ℕ) (hj : j < n) :
    T n k (j + 1) * ((j + 1) * (n - k)) = T n k j * ((n - j) * k) := by
  unfold T
  obtain ⟨m, hm⟩ : ∃ m, n - j = m + 1 := ⟨n - j - 1, by omega⟩
  have hm' : n - (j + 1) = m := by omega
  have hc := Nat.choose_succ_right_eq n j
  rw [hm] at hc
  rw [hm', hm]
  calc n.choose (j + 1) * k ^ (j + 1) * (n - k) ^ m * ((j + 1) * (n - k))
      = (n.choose (j + 1) * (j + 1)) * (k ^ j * k) * ((n - k) ^ m * (n - k)) := by ring
    _ = (n.choose j * (m + 1)) * (k ^ j * k) * ((n - k) ^ m * (n - k)) := by rw [hc]
    _ = n.choose j * k ^ j * (n - k) ^ (m + 1) * ((m + 1) * k) := by ring

theorem T_succ_le (n k j : ℕ) (hkj : k ≤ j) (hkn : k < n) : T n k (j + 1) ≤ T n k j := by
  by_cases hj : j < n
  · have h := T_succ n k j hj
    have hpos : 0 < (j + 1) * (n - k) := Nat.mul_pos (Nat.succ_pos j) (by omega)
    have hle : (n - j) * k ≤ (j + 1) * (n - k) :=
      calc (n - j) * k ≤ (n - k) * k := Nat.mul_le_mul_right _ (by omega)
        _ ≤ (n - k) * (j + 1) := Nat.mul_le_mul_left _ (by omega)
        _ = (j + 1) * (n - k) := by ring
    have hmul : T n k (j + 1) * ((j + 1) * (n - k)) ≤ T n k j * ((j + 1) * (n - k)) := by
      rw [h]
      exact Nat.mul_le_mul_left _ hle
    exact Nat.le_of_mul_le_mul_right hmul hpos
  · have h0 : n.choose (j + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [T, h0]

theorem T_le_succ (n k j : ℕ) (hjk : j < k) (hkn : k ≤ n) : T n k j ≤ T n k (j + 1) := by
  have hj : j < n := by omega
  by_cases hnk : n - k = 0
  · have hne : n - j ≠ 0 := by omega
    simp [T, hnk, zero_pow hne]
  · have h := T_succ n k j hj
    have hpos : 0 < (j + 1) * (n - k) := Nat.mul_pos (Nat.succ_pos j) (Nat.pos_of_ne_zero hnk)
    have hle : (j + 1) * (n - k) ≤ (n - j) * k :=
      calc (j + 1) * (n - k) ≤ k * (n - k) := Nat.mul_le_mul_right _ (by omega)
        _ ≤ k * (n - j) := Nat.mul_le_mul_left _ (by omega)
        _ = (n - j) * k := by ring
    have hmul : T n k j * ((j + 1) * (n - k)) ≤ T n k (j + 1) * ((j + 1) * (n - k)) := by
      rw [h]
      exact Nat.mul_le_mul_left _ hle
    exact Nat.le_of_mul_le_mul_right hmul hpos

/-- The binomial terms are maximal at `j = k`. -/
theorem T_le_T_self (n k j : ℕ) (hk : k ≤ n) : T n k j ≤ T n k k := by
  rcases le_or_gt j k with hjk | hkj
  · have key : ∀ d, d ≤ k → T n k (k - d) ≤ T n k k := by
      intro d
      induction d with
      | zero => intro _; simp
      | succ d ih =>
          intro hd
          calc T n k (k - (d + 1)) ≤ T n k (k - (d + 1) + 1) := T_le_succ n k _ (by omega) hk
            _ = T n k (k - d) := by congr 1; omega
            _ ≤ T n k k := ih (by omega)
    simpa [Nat.sub_sub_self hjk] using key (k - j) (by omega)
  · have key : ∀ d, T n k (k + d) ≤ T n k k := by
      intro d
      induction d with
      | zero => simp
      | succ d ih =>
          rcases lt_or_eq_of_le hk with hkn | hkn
          · exact (T_succ_le n k (k + d) (by omega) hkn).trans ih
          · have h0 : n.choose (k + (d + 1)) = 0 := Nat.choose_eq_zero_of_lt (by omega)
            simp [T, h0]
    simpa [Nat.add_sub_cancel' hkj.le] using key (j - k)

/-- `n^n ≤ (n+1) · C(n,k) · k^k · (n-k)^(n-k)`. -/
theorem pow_le_succ_mul_choose_mul_pow (n k : ℕ) (hk : k ≤ n) :
    n ^ n ≤ (n + 1) * (n.choose k * k ^ k * (n - k) ^ (n - k)) := by
  rw [← sum_T n k hk]
  calc ∑ j ∈ range (n + 1), T n k j ≤ ∑ _j ∈ range (n + 1), T n k k :=
        sum_le_sum fun j _ => T_le_T_self n k j hk
    _ = (n + 1) * T n k k := by simp
    _ = (n + 1) * (n.choose k * k ^ k * (n - k) ^ (n - k)) := by unfold T; rfl

/-! ## 2. Logarithmic form -/

/-- `ent n k = n log n − k log k − (n−k) log (n−k)`, i.e. `n · H(k/n)` in nats. -/
noncomputable def ent (n k : ℕ) : ℝ :=
  n * log n - k * log k - ((n - k : ℕ) : ℝ) * log ((n - k : ℕ) : ℝ)

theorem self_pow_pos (k : ℕ) : 0 < k ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · exact pow_pos hk k

theorem cast_prod_pos (n k : ℕ) (hk : k ≤ n) :
    (0 : ℝ) < ((n.choose k * k ^ k * (n - k) ^ (n - k) : ℕ) : ℝ) := by
  exact_mod_cast Nat.mul_pos (Nat.mul_pos (Nat.choose_pos hk) (self_pow_pos k))
    (self_pow_pos (n - k))

theorem log_prod (n k : ℕ) (hk : k ≤ n) :
    log ((n.choose k * k ^ k * (n - k) ^ (n - k) : ℕ) : ℝ) =
      log (n.choose k) + k * log k + ((n - k : ℕ) : ℝ) * log ((n - k : ℕ) : ℝ) := by
  have h1 : ((n.choose k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  have h2 : ((k ^ k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (self_pow_pos k).ne'
  have h3 : (((n - k) ^ (n - k) : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (self_pow_pos (n - k)).ne'
  rw [Nat.cast_mul, Nat.cast_mul, Real.log_mul (mul_ne_zero h1 h2) h3, Real.log_mul h1 h2,
    Nat.cast_pow, Nat.cast_pow, Real.log_pow, Real.log_pow]

/-- `log C(n,k) ≤ n · H(k/n)`. -/
theorem log_choose_le_ent (n k : ℕ) (hk : k ≤ n) : log (n.choose k) ≤ ent n k := by
  have hle : ((n.choose k * k ^ k * (n - k) ^ (n - k) : ℕ) : ℝ) ≤ ((n ^ n : ℕ) : ℝ) := by
    exact_mod_cast choose_mul_pow_le n k hk
  have h := Real.log_le_log (cast_prod_pos n k hk) hle
  rw [log_prod n k hk, Nat.cast_pow, Real.log_pow] at h
  unfold ent
  linarith

/-- `n · H(k/n) ≤ log (n+1) + log C(n,k)`. -/
theorem ent_le_log_succ_add_log_choose (n k : ℕ) (hk : k ≤ n) :
    ent n k ≤ log ((n : ℝ) + 1) + log (n.choose k) := by
  have hle : ((n ^ n : ℕ) : ℝ) ≤
      (((n + 1) * (n.choose k * k ^ k * (n - k) ^ (n - k)) : ℕ) : ℝ) := by
    exact_mod_cast pow_le_succ_mul_choose_mul_pow n k hk
  have hpos : (0 : ℝ) < ((n ^ n : ℕ) : ℝ) := by exact_mod_cast self_pow_pos n
  have h := Real.log_le_log hpos hle
  rw [Nat.cast_mul, Real.log_mul (by positivity) (cast_prod_pos n k hk).ne', log_prod n k hk,
    Nat.cast_pow, Real.log_pow] at h
  push_cast at h
  unfold ent
  linarith

/-! ## 3. Two-sided finite bounds for `W_c(N)` -/

/-- `W_c(N) = #confinedWords N (collatzBarrier c)`. -/
noncomputable abbrev W (c N : ℕ) : ℕ := (confinedWords N (collatzBarrier c)).card

theorem one_le_W (c : ℕ) {N : ℕ} (hN : 1 ≤ N) : 1 ≤ W c N := by
  have h := (collatz_capacity_sandwich c hN).2.1
  have hc : 0 < Nat.choose (collatzBarrier c N) N := Nat.choose_pos (le_collatzBarrier c N)
  change 1 ≤ (confinedWords N (collatzBarrier c)).card
  rcases Nat.eq_zero_or_pos (confinedWords N (collatzBarrier c)).card with h0 | h0
  · rw [h0] at h
    omega
  · exact h0

/-- **Upper entropy bound.** `log W_c(N) ≤ s_N · H(N/s_N)` (as `ent s_N N`). -/
theorem log_W_le (c : ℕ) {N : ℕ} (hN : 1 ≤ N) :
    log (W c N) ≤ ent (collatzBarrier c N) N := by
  have hW : (0 : ℝ) < W c N := by exact_mod_cast one_le_W c hN
  calc log (W c N) ≤ log (Nat.choose (collatzBarrier c N) N) :=
        Real.log_le_log hW (by exact_mod_cast card_confinedWords_le_choose hN _)
    _ ≤ ent (collatzBarrier c N) N := log_choose_le_ent _ _ (le_collatzBarrier c N)

/-- **Lower entropy bound.** `s_N · H(N/s_N) − log (s_N+1) − log N ≤ log W_c(N)`. -/
theorem log_W_ge (c : ℕ) {N : ℕ} (hN : 1 ≤ N) :
    ent (collatzBarrier c N) N - log ((collatzBarrier c N : ℝ) + 1) - log N ≤ log (W c N) := by
  have hW : (0 : ℝ) < W c N := by exact_mod_cast one_le_W c hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hC : (0 : ℝ) < Nat.choose (collatzBarrier c N) N := by
    exact_mod_cast Nat.choose_pos (le_collatzBarrier c N)
  have h1 := ent_le_log_succ_add_log_choose _ _ (le_collatzBarrier c N)
  have h2 : log (Nat.choose (collatzBarrier c N) N) ≤ log N + log (W c N) := by
    rw [← Real.log_mul hNr.ne' hW.ne']
    exact Real.log_le_log hC (by exact_mod_cast (collatz_capacity_sandwich c hN).2.1)
  linarith

/-! ## 4. The entropy limit -/

/-- `f t = t log t − (t−1) log (t−1)`, so that `ent s N = N · f (s/N)`. -/
noncomputable def f (t : ℝ) : ℝ := t * log t - (t - 1) * log (t - 1)

theorem f_continuous : Continuous f :=
  continuous_mul_log.sub (continuous_mul_log.comp (continuous_sub_right 1))

theorem ent_eq_mul_f {s N : ℕ} (hN : 1 ≤ N) (hNs : N ≤ s) :
    ent s N = N * f ((s : ℝ) / N) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  unfold ent f
  have hsub : ((s - N : ℕ) : ℝ) = (s : ℝ) - N := by push_cast [Nat.cast_sub hNs]; ring
  rw [hsub]
  have hq : (s : ℝ) / N - 1 = ((s : ℝ) - N) / N := by field_simp
  rw [hq]
  rcases eq_or_lt_of_le hNs with heq | hlt
  · subst heq
    simp
  · have hsN : (0 : ℝ) < (s : ℝ) - N := by
      have : (N : ℝ) < s := by exact_mod_cast hlt
      linarith
    have hs : (0 : ℝ) < s := by linarith
    rw [Real.log_div hs.ne' hNr.ne', Real.log_div hsN.ne' hNr.ne']
    field_simp
    ring

theorem tendsto_barrier_div (c : ℕ) :
    Tendsto (fun N : ℕ => (collatzBarrier c N : ℝ) / N) atTop (𝓝 alpha) := by
  have hlo : Tendsto (fun N : ℕ => alpha + ((c : ℝ) - 1) / N) atTop (𝓝 alpha) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat ((c : ℝ) - 1))
  have hhi : Tendsto (fun N : ℕ => alpha + (c : ℝ) / N) atTop (𝓝 alpha) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (c : ℝ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hfl := Nat.sub_one_lt_floor ((N : ℝ) * alpha + c)
    unfold collatzBarrier
    rw [le_div_iff₀ hNr]
    rw [add_mul, div_mul_cancel₀ _ hNr.ne']
    linarith
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hfl := Nat.floor_le (barrier_arg_nonneg c N)
    unfold collatzBarrier
    rw [div_le_iff₀ hNr, add_mul, div_mul_cancel₀ _ hNr.ne']
    linarith

theorem tendsto_log_nat_div : Tendsto (fun N : ℕ => log (N : ℝ) / N) atTop (𝓝 0) := by
  have h := (tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
    tendsto_natCast_atTop_atTop
  refine h.congr fun N => ?_
  simp

/-- **Confined-language entropy** (paper Thm 6.2), natural logarithms:
`log W_c(N) / N → α log α − (α−1) log (α−1)`. -/
theorem tendsto_log_card_confined (c : ℕ) :
    Tendsto (fun N : ℕ => log (W c N) / N) atTop (𝓝 (f alpha)) := by
  have hf : Tendsto (fun N : ℕ => f ((collatzBarrier c N : ℝ) / N)) atTop (𝓝 (f alpha)) :=
    (f_continuous.tendsto alpha).comp (tendsto_barrier_div c)
  -- error term `(log (s_N + 1) + log N) / N`, dominated by `(log (α + c + 1) + 2 log N) / N`
  have herr : Tendsto (fun N : ℕ => (log ((collatzBarrier c N : ℝ) + 1) + log N) / N) atTop
      (𝓝 0) := by
    have hdom : Tendsto (fun N : ℕ => log (alpha + c + 1) / N + 2 * (log (N : ℝ) / N)) atTop
        (𝓝 0) := by
      simpa using (tendsto_const_div_atTop_nhds_zero_nat (log (alpha + c + 1))).add
        (tendsto_log_nat_div.const_mul 2)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdom ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have h1 : 0 ≤ log ((collatzBarrier c N : ℝ) + 1) :=
        Real.log_nonneg (by have := (Nat.cast_nonneg (collatzBarrier c N) : (0 : ℝ) ≤ _); linarith)
      have h2 : 0 ≤ log (N : ℝ) := Real.log_nonneg hNr
      positivity
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have hN0 : (0 : ℝ) < N := by linarith
      have hsN : (collatzBarrier c N : ℝ) + 1 ≤ (alpha + c + 1) * N := by
        have hfl := Nat.floor_le (barrier_arg_nonneg c N)
        unfold collatzBarrier
        have hc : (c : ℝ) ≤ c * N := by nlinarith [(Nat.cast_nonneg c : (0 : ℝ) ≤ c)]
        nlinarith
      have hpos : (0 : ℝ) < (collatzBarrier c N : ℝ) + 1 := by positivity
      have hlog : log ((collatzBarrier c N : ℝ) + 1) ≤ log (alpha + c + 1) + log N := by
        rw [← Real.log_mul (by have := alpha_pos; positivity) hN0.ne']
        exact Real.log_le_log hpos hsN
      have hr : log (alpha + c + 1) / N + 2 * (log (N : ℝ) / N) =
          (log (alpha + c + 1) + 2 * log N) / N := by ring
      rw [hr]
      exact div_le_div_of_nonneg_right (by linarith) hN0.le
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using hf.sub herr) hf ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have h := log_W_ge c hN
    rw [ent_eq_mul_f hN (le_collatzBarrier c N)] at h
    rw [le_div_iff₀ hNr]
    have hexp : (f ((collatzBarrier c N : ℝ) / N) -
        (log ((collatzBarrier c N : ℝ) + 1) + log N) / N) * N =
        N * f ((collatzBarrier c N : ℝ) / N) - log ((collatzBarrier c N : ℝ) + 1) - log N := by
      field_simp
      ring
    rw [hexp]
    linarith
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have h := log_W_le c hN
    rw [ent_eq_mul_f hN (le_collatzBarrier c N)] at h
    rw [div_le_iff₀ hNr]
    linarith

/-- The limit constant is `α · H(1/α)`. -/
theorem alpha_entropy_eq : f alpha = alpha * Real.binEntropy alpha⁻¹ := by
  have ha : 1 < alpha := one_lt_alpha
  have ha0 : alpha ≠ 0 := by linarith
  have ha1 : alpha - 1 ≠ 0 := by linarith
  unfold f Real.binEntropy
  rw [inv_inv, show 1 - alpha⁻¹ = (alpha - 1) / alpha by field_simp, inv_div,
    Real.log_div ha0 ha1]
  field_simp
  ring

end EntropyBounds
end EOC
