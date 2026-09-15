import EOC.PsiShellBound
import EOC.WhiteRun

/-!
# The power-of-2 orbit modulo `3^n`, the shell shift, and continuation spreading

* `padicValNat_three_two_pow_sub_one` — LTE for `p = 3`:
  `v₃(2^d − 1) = if Even d then 1 + v₃(d) else 0` (`d ≥ 1`).
* `three_pow_dvd_two_pow_sub_one_iff` — `3^n ∣ 2^d − 1 ↔ 2·3^{n−1} ∣ d` (`n ≥ 1`).
* `orderOf_two_zmod_three_pow` — `orderOf (2 : ZMod (3^n)) = 2·3^{n−1}` (`n ≥ 1`).
* `card_orbit_collisions_eq`, `card_orbit_collisions_le` — the orbit collision hierarchy on a window
  `range W`: `2^a = 2^{a'}` in `ZMod (3^r)` iff `2·3^{r−1} ∣ a − a'`, and the count of such pairs is
  at most `W·(W/(2·3^{r−1}) + 1)`.
* `yPrime_succ_mod`, `Psi_shell_shift` — lowering `m = σ+1+t` by one is doubling the frequency:
  `Ψ_t(λ) = Ψ_{t+1}(2λ)`.
* `ContinuationSpreading` (hypothesis) and **`weightedFourier_of_continuationSpreading`**.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace PowerOrbit

open Finset

/-! ## 1. LTE for `3 ∣ 2^d − 1` -/

theorem padicValNat_three_two_pow_sub_one {d : ℕ} (hd : 1 ≤ d) :
    padicValNat 3 (2 ^ d - 1) = if Even d then 1 + padicValNat 3 d else 0 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  split_ifs with he
  · obtain ⟨e, rfl⟩ := he
    have he0 : e ≠ 0 := by omega
    have h4 : 2 ^ (e + e) = 4 ^ e := by rw [← two_mul, pow_mul]; norm_num
    have hlte := padicValNat.pow_sub_pow (p := 3) (x := 4) (y := 1) (by decide) (by norm_num)
      (by norm_num) (by norm_num) he0
    rw [one_pow] at hlte
    rw [h4, hlte, show (4 - 1 : ℕ) = 3 by norm_num, padicValNat_self,
      show e + e = 2 * e by ring, padicValNat.mul (by norm_num) he0,
      padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2), zero_add]
  · apply padicValNat.eq_zero_of_not_dvd
    obtain ⟨e, rfl⟩ := Nat.not_even_iff_odd.mp he
    intro h
    have h1 : (2 ^ (2 * e + 1) - 1 : ℕ) = 2 * 4 ^ e - 1 := by
      rw [pow_succ, pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num, mul_comm]
    rw [h1] at h
    have h4 : 4 ^ e % 3 = 1 := by rw [Nat.pow_mod]; norm_num
    have hpos : 1 ≤ 4 ^ e := Nat.one_le_pow _ _ (by norm_num)
    omega

theorem three_pow_dvd_two_pow_sub_one_iff {n d : ℕ} (hn : 1 ≤ n) :
    3 ^ n ∣ 2 ^ d - 1 ↔ 2 * 3 ^ (n - 1) ∣ d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  have hne : 2 ^ d - 1 ≠ 0 := by
    have : 2 ≤ 2 ^ d := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
    omega
  rw [padicValNat_dvd_iff_le hne, padicValNat_three_two_pow_sub_one hd]
  have hcop : Nat.Coprime 2 (3 ^ (n - 1)) := Nat.Coprime.pow_right _ (by norm_num)
  constructor
  · intro h
    split_ifs at h with he
    · have h3 : 3 ^ (n - 1) ∣ d := (padicValNat_dvd_iff_le hd.ne').mpr (by omega)
      exact hcop.mul_dvd_of_dvd_of_dvd (even_iff_two_dvd.mp he) h3
    · omega
  · intro h
    have he : Even d := even_iff_two_dvd.mpr (dvd_trans (dvd_mul_right 2 _) h)
    have h3 : 3 ^ (n - 1) ∣ d := dvd_trans (dvd_mul_left _ 2) h
    rw [ite_eq_left_iff.mpr (fun h => absurd he h)]
    have := (padicValNat_dvd_iff_le hd.ne').mp h3
    omega

theorem two_pow_eq_one_iff {n d : ℕ} (hn : 1 ≤ n) :
    (2 : ZMod (3 ^ n)) ^ d = 1 ↔ 2 * 3 ^ (n - 1) ∣ d := by
  rw [← three_pow_dvd_two_pow_sub_one_iff hn]
  have h1 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  rw [← Nat.modEq_iff_dvd' h1, ← ZMod.natCast_eq_natCast_iff]
  push_cast
  exact eq_comm

/-- **Exact order**: `2` has order `2·3^{n−1}` modulo `3^n`. -/
theorem orderOf_two_zmod_three_pow {n : ℕ} (hn : 1 ≤ n) :
    orderOf (2 : ZMod (3 ^ n)) = 2 * 3 ^ (n - 1) := by
  apply Nat.dvd_antisymm
  · exact orderOf_dvd_iff_pow_eq_one.mpr ((two_pow_eq_one_iff hn).mpr dvd_rfl)
  · exact (two_pow_eq_one_iff hn).mp (pow_orderOf_eq_one _)

/-! ## 2. Orbit collision hierarchy -/

theorem isUnit_two_pow {r a : ℕ} : IsUnit ((2 : ZMod (3 ^ r)) ^ a) := by
  have h2 : IsUnit (2 : ZMod (3 ^ r)) := by
    have := (ZMod.unitOfCoprime 2 (Nat.Coprime.pow_right r (by norm_num : Nat.Coprime 2 3))).isUnit
    simpa using this
  exact h2.pow a

theorem two_pow_eq_two_pow_iff_of_le {r a a' : ℕ} (hr : 1 ≤ r) (h : a ≤ a') :
    (2 : ZMod (3 ^ r)) ^ a = 2 ^ a' ↔ 2 * 3 ^ (r - 1) ∣ a' - a := by
  rw [← two_pow_eq_one_iff hr, show a' = a + (a' - a) by omega, pow_add, eq_comm,
    Nat.add_sub_cancel_left]
  exact isUnit_two_pow.mul_eq_left

theorem two_pow_eq_two_pow_iff {r a a' : ℕ} (hr : 1 ≤ r) :
    (2 : ZMod (3 ^ r)) ^ a = 2 ^ a' ↔ ((2 * 3 ^ (r - 1) : ℕ) : ℤ) ∣ (a' : ℤ) - a := by
  rcases le_total a a' with h | h
  · rw [two_pow_eq_two_pow_iff_of_le hr h, ← Int.natCast_dvd_natCast, Nat.cast_sub h]
  · rw [eq_comm, two_pow_eq_two_pow_iff_of_le hr h, ← Int.natCast_dvd_natCast, Nat.cast_sub h,
      ← dvd_neg, neg_sub]

/-- The pairs of a window `range W` colliding modulo `3^r` are exactly the pairs whose exponent
difference is divisible by `2·3^{r−1}`. -/
theorem card_orbit_collisions_eq {r : ℕ} (hr : 1 ≤ r) (W : ℕ) :
    ((range W ×ˢ range W).filter fun p : ℕ × ℕ => (2 : ZMod (3 ^ r)) ^ p.1 = 2 ^ p.2).card =
      ((range W ×ˢ range W).filter fun p : ℕ × ℕ =>
        ((2 * 3 ^ (r - 1) : ℕ) : ℤ) ∣ (p.2 : ℤ) - p.1).card := by
  congr 1
  exact filter_congr fun p _ => two_pow_eq_two_pow_iff hr

theorem card_orbit_collisions_le {r : ℕ} (hr : 1 ≤ r) (W : ℕ) :
    ((range W ×ˢ range W).filter fun p : ℕ × ℕ => (2 : ZMod (3 ^ r)) ^ p.1 = 2 ^ p.2).card ≤
      W * (W / (2 * 3 ^ (r - 1)) + 1) := by
  set L := 2 * 3 ^ (r - 1) with hL
  have hL0 : 0 < L := by positivity
  rw [card_orbit_collisions_eq hr, card_filter, sum_product]
  have hinner : ∀ a ∈ range W, (∑ a' ∈ range W,
      if ((L : ℕ) : ℤ) ∣ ((a, a').2 : ℤ) - (a, a').1 then 1 else 0) ≤ W / L + 1 := by
    intro a _
    rw [← card_filter]
    calc ((range W).filter fun a' : ℕ => ((L : ℕ) : ℤ) ∣ (a' : ℤ) - a).card
        ≤ ((Ico 0 (0 + W)).filter fun x => x % L = a % L).card := by
          apply card_le_card
          intro a' ha'
          simp only [mem_filter, mem_range, mem_Ico] at ha' ⊢
          refine ⟨⟨Nat.zero_le _, by omega⟩, ?_⟩
          exact ((Nat.modEq_iff_dvd).mpr ha'.2).symm
      _ ≤ W / L + 1 := WhiteRun.card_Ico_filter_mod_le 0 W L (a % L)
  calc ∑ a ∈ range W, ∑ a' ∈ range W,
        (if ((L : ℕ) : ℤ) ∣ ((a, a').2 : ℤ) - (a, a').1 then 1 else 0)
      ≤ ∑ a ∈ range W, (W / L + 1) := sum_le_sum hinner
    _ = W * (W / L + 1) := by rw [sum_const, card_range, smul_eq_mul]

/-! ## 3. Shell shift: lowering `m` by one doubles the frequency -/

section Shift

open WeightedChain TwistExpansion PrefixCollision

variable {j0 : ℕ}

/-- Consistency of the phase points under reduction: `y'_{t+1} mod 2^{σ+1+t} = y'_t`. -/
theorem yPrime_succ_mod (σ t : ℕ) (P : FiniteValuationWord j0) :
    yPrime j0 σ (t + 1) P % 2 ^ (σ + 1 + t) = yPrime j0 σ t P := by
  set M : ℕ := 2 ^ (σ + 1 + t) with hM
  have h1 := yPrime_spec j0 σ (t + 1) P
  have h0 := yPrime_spec j0 σ t P
  have hdvd : ((M : ℕ) : ℤ) ∣ ((2 ^ (σ + 1 + (t + 1)) : ℕ) : ℤ) := by
    rw [hM]; exact Int.natCast_dvd_natCast.mpr (pow_dvd_pow 2 (by omega))
  have h1' := h1.of_dvd hdvd
  have hcong : (3 : ℤ) ^ j0 * (yPrime j0 σ (t + 1) P : ℤ) ≡ 3 ^ j0 * (yPrime j0 σ t P : ℤ)
      [ZMOD ((M : ℕ) : ℤ)] := h1'.trans h0.symm
  have hcop : IsCoprime ((M : ℕ) : ℤ) ((3 : ℤ) ^ j0) := by
    have : Nat.Coprime M (3 ^ j0) :=
      Nat.Coprime.pow _ _ (by norm_num : Nat.Coprime 2 3)
    exact_mod_cast Nat.isCoprime_iff_coprime.mpr this
  have hd : ((M : ℕ) : ℤ) ∣ (yPrime j0 σ t P : ℤ) - yPrime j0 σ (t + 1) P := by
    have := (Int.ModEq.dvd hcong)
    rw [← mul_sub] at this
    exact hcop.dvd_of_dvd_mul_left this
  have hmod : (yPrime j0 σ (t + 1) P : ℤ) ≡ yPrime j0 σ t P [ZMOD ((M : ℕ) : ℤ)] :=
    Int.modEq_of_dvd hd
  have hlt : yPrime j0 σ t P < M := yPrime_lt j0 σ t P
  have hnat : yPrime j0 σ (t + 1) P % M = yPrime j0 σ t P % M := by
    have := hmod
    unfold Int.ModEq at this
    exact_mod_cast this
  rw [hnat, Nat.mod_eq_of_lt hlt]

/-- **Shell shift**: `Ψ_t(λ) = Ψ_{t+1}(2λ)` for the phase points of `P_σ`. -/
theorem Psi_shell_shift (T : Finset (FiniteValuationWord j0)) (σ t lam : ℕ) :
    Psi T (σ + 1) t (yPrime j0 σ t) lam =
      Psi T (σ + 1) (t + 1) (yPrime j0 σ (t + 1)) (2 * lam) := by
  unfold Psi
  refine sum_congr rfl fun P _ => ?_
  set M : ℕ := 2 ^ (σ + 1 + t) with hM
  set kq : ℕ := yPrime j0 σ (t + 1) P / M with hkq
  have hsplit : yPrime j0 σ (t + 1) P = yPrime j0 σ t P + M * kq := by
    have := Nat.mod_add_div (yPrime j0 σ (t + 1) P) M
    rw [yPrime_succ_mod] at this
    exact this.symm
  have hpow : (2 : ℝ) ^ (σ + 1 + (t + 1)) = 2 * (M : ℝ) := by
    rw [hM]; push_cast; rw [show σ + 1 + (t + 1) = σ + 1 + t + 1 by omega, pow_succ]; ring
  have hM0 : (0 : ℝ) < M := by rw [hM]; positivity
  rw [hsplit]
  push_cast
  rw [hpow, show (2 : ℝ) ^ (σ + 1 + t) = (M : ℝ) by rw [hM]; push_cast; ring]
  have : (2 * (lam : ℝ) * ((yPrime j0 σ t P : ℝ) + (M : ℝ) * (kq : ℝ))) /
      (2 * (M : ℝ)) = (lam : ℝ) * yPrime j0 σ t P / M + (((lam * kq : ℕ) : ℤ) : ℝ) := by
    push_cast; field_simp
  rw [this, ee_add, ee_int, mul_one]

end Shift

/-! ## 4. Continuation spreading ⇒ `WeightedFourier` -/

section Spreading

open WeightedChain TwistExpansion PrefixCollision PsiSieve PsiShellBound ShellDecomposition

variable (b : ℕ → ℕ)

/-- **Continuation-spreading hypothesis** (analytic input, NOT proved): for every centered shell
`u < m = σ+1+t` and both covering intervals `a + range 2^u` of the shell, the split path sum
`∑_S F_S G_S` (prefix of length `Nsplit u`, continuation to `(j0, σ)`) has mean square at most
`C · 2^{−θu} · |P_σ|²`. -/
def ContinuationSpreading (j0 σ t : ℕ) (Nsplit : ℕ → ℕ) (C θ : ℝ) : Prop :=
  ∀ u ∈ range (σ + 1 + t), ∀ a ∈ ({2 ^ u, 2 ^ (σ + 1 + t) + 1 - 2 ^ (u + 1)} : Finset ℕ),
    ∑ k ∈ range (2 ^ u),
        ‖∑ S ∈ range (σ + 1), Fpre b (σ + 1 + t) (Nsplit u) S (a + k) *
          Gsuf b (σ + 1 + t) j0 (Nsplit u) σ S (a + k)‖ ^ 2 ≤
      C * 2 ^ u * (2 : ℝ) ^ (-(θ * u)) * ((shellP b j0 σ).card : ℝ) ^ 2

/-- Under `ContinuationSpreading`, every centered shell sum of `‖Ψ‖²` is at most
`2·C·2^u·2^{−θu}·|P_σ|²`. -/
theorem shell_sum_le_of_continuationSpreading {j0 σ t : ℕ} {Nsplit : ℕ → ℕ} {C θ : ℝ}
    (hN1 : ∀ u ∈ range (σ + 1 + t), 1 ≤ Nsplit u)
    (hNj : ∀ u ∈ range (σ + 1 + t), Nsplit u < j0)
    (h : ContinuationSpreading b j0 σ t Nsplit C θ) (u : ℕ) (hu : u ∈ range (σ + 1 + t)) :
    ∑ lam ∈ cshell (σ + 1) t u, ‖Psi (shellP b j0 σ) (σ + 1) t (yPrime j0 σ t) lam‖ ^ 2 ≤
      2 * (C * 2 ^ u * (2 : ℝ) ^ (-(θ * u)) * ((shellP b j0 σ).card : ℝ) ^ 2) := by
  have hint : ∀ a ∈ ({2 ^ u, 2 ^ (σ + 1 + t) + 1 - 2 ^ (u + 1)} : Finset ℕ),
      ∑ k ∈ range (2 ^ u), ‖Psi (shellP b j0 σ) (σ + 1) t (yPrime j0 σ t) (a + k)‖ ^ 2 ≤
        C * 2 ^ u * (2 : ℝ) ^ (-(θ * u)) * ((shellP b j0 σ).card : ℝ) ^ 2 := by
    intro a ha
    have heq : ∀ k, ‖Psi (shellP b j0 σ) (σ + 1) t (yPrime j0 σ t) (a + k)‖ =
        ‖∑ S ∈ range (σ + 1), Fpre b (σ + 1 + t) (Nsplit u) S (a + k) *
          Gsuf b (σ + 1 + t) j0 (Nsplit u) σ S (a + k)‖ := fun k => by
      rw [norm_Psi_eq, ← psi_split b (σ + 1 + t) j0 (Nsplit u) σ (a + k) (hN1 u hu) (hNj u hu)]
    simp_rw [heq]
    exact h u hu a ha
  calc ∑ lam ∈ cshell (σ + 1) t u, ‖Psi (shellP b j0 σ) (σ + 1) t (yPrime j0 σ t) lam‖ ^ 2
      ≤ ∑ k ∈ range (2 ^ u), ‖Psi (shellP b j0 σ) (σ + 1) t (yPrime j0 σ t) (2 ^ u + k)‖ ^ 2 +
        ∑ k ∈ range (2 ^ u), ‖Psi (shellP b j0 σ) (σ + 1) t (yPrime j0 σ t)
          (2 ^ (σ + 1 + t) + 1 - 2 ^ (u + 1) + k)‖ ^ 2 :=
        sum_cshell_le_two_intervals (σ + 1) t u _ (fun _ => by positivity)
    _ ≤ _ := by
        rw [two_mul]
        exact add_le_add (hint _ (by simp)) (hint _ (by simp))

/-- **`ContinuationSpreading ⇒ WeightedFourier`** (with `t = s − σ`), with the explicit budget
`(1 + (σ+1)/2) · ∑_u min 1 (2^t/(2·2^u)) · 2·C·2^u·2^{−θu}·|P_σ|² ≤ ε² |P_σ|² |V_{σ,s}| / 2^t`. -/
theorem weightedFourier_of_continuationSpreading (N j0 s σ : ℕ) (ε : ℝ) (Nsplit : ℕ → ℕ) (C θ : ℝ)
    (hN1 : ∀ u ∈ range (σ + 1 + (s - σ)), 1 ≤ Nsplit u)
    (hNj : ∀ u ∈ range (σ + 1 + (s - σ)), Nsplit u < j0)
    (h : ContinuationSpreading b j0 σ (s - σ) Nsplit C θ)
    (hfin : (1 + ((σ + 1 : ℕ) : ℝ) / 2) * ∑ u ∈ range (σ + 1 + (s - σ)),
        min 1 (2 ^ (s - σ) / (2 * 2 ^ u)) *
          (2 * (C * 2 ^ u * (2 : ℝ) ^ (-(θ * u)) * ((shellP b j0 σ).card : ℝ) ^ 2)) ≤
      ε ^ 2 * ((shellP b j0 σ).card : ℝ) ^ 2 * (shellV b N j0 σ (s - σ)).card / 2 ^ (s - σ)) :
    WeightedFourier b N j0 s σ ε := by
  unfold WeightedFourier
  have hbase := weighted_sum_le_of_shell_sums_refined (σ + 1) (s - σ)
    (fun lam => ‖Psi (shellP b j0 σ) (σ + 1) (s - σ) (yPrime j0 σ (s - σ)) lam‖ ^ 2)
    (fun u => 2 * (C * 2 ^ u * (2 : ℝ) ^ (-(θ * u)) * ((shellP b j0 σ).card : ℝ) ^ 2))
    (fun _ => by positivity)
    (fun u hu => shell_sum_le_of_continuationSpreading b hN1 hNj h u hu)
  have hpre : (0 : ℝ) ≤ 1 + ((σ + 1 : ℕ) : ℝ) / 2 := by positivity
  exact (mul_le_mul_of_nonneg_left hbase hpre).trans hfin

end Spreading

end PowerOrbit
end EOC
