import EOC.IntervalSieve
import EOC.WeightedChain
import EOC.FirstDivergence
import EOC.WhiteRun
import EOC.PrefixCollision

/-!
# The 3-adic interval sieve (C3) instantiated for `Ψ`

* `reciprocity` — for `u·3^k ≡ 1 (mod 2^m)`, `v·2^m ≡ 1 (mod 3^k)`:
  `u/2^m + v/3^k − 1/(3^k 2^m) ∈ ℤ`.
* `X_injOn`, `X_le_Xmax` — the prefix map `X(P) = C P N = ∑_{i<N} 3^{N−1−i} 2^{S_i}` is injective
  on each prefix shell `P_{N,S}` and bounded by `Xmax b N = ∑_{i<N} 3^{N−1−i} 2^{b i}`.
* `prefix_phase_grid` — grid form of the prefix phase:
  `Z/2^m = z + (−W X)/3^N + X/(3^N 2^m)` with `z ∈ ℤ`, `Z = ∑_{i<N} u_i 2^{S_i}`, `W·2^m ≡ 1 (3^N)`.
* `psi_split` — path splitting of the `Ψ` path product at step `N` over the state `S = S_N`.
* `psi_shell_sieve` — **(C3) for `Ψ`**: on any `H` consecutive frequencies,
  `√(∑_{k<H} ‖Ψ(a+k)‖²) ≤ ∑_S g_S · min(√H · p_S, √(p_S μ (H + 2·3^N(1+log 3^N))))`,
  `p_S = |P_{N,S}|`, `g_S = |V|` (continuations), `μ = Xmax/3^N + 1`, provided `2·Xmax ≤ 2^m`.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace PsiSieve

open Finset CapacityBounds FiniteValuationWord PrefixCollision

/-! ## 1. Reciprocity -/

theorem reciprocity {k m : ℕ} {u v : ℤ} (hu : u * 3 ^ k ≡ 1 [ZMOD 2 ^ m])
    (hv : v * 2 ^ m ≡ 1 [ZMOD 3 ^ k]) :
    ∃ z : ℤ, (u : ℝ) / 2 ^ m + v / 3 ^ k - 1 / (3 ^ k * 2 ^ m) = z := by
  have h1 : (2 : ℤ) ^ m ∣ u * 3 ^ k + v * 2 ^ m - 1 := by
    have := hu.symm.dvd
    have h2 : u * 3 ^ k + v * 2 ^ m - 1 = (u * 3 ^ k - 1) + 2 ^ m * v := by ring
    rw [h2]; exact dvd_add this (dvd_mul_right _ _)
  have h3 : (3 : ℤ) ^ k ∣ u * 3 ^ k + v * 2 ^ m - 1 := by
    have := hv.symm.dvd
    have h2 : u * 3 ^ k + v * 2 ^ m - 1 = (v * 2 ^ m - 1) + 3 ^ k * u := by ring
    rw [h2]; exact dvd_add this (dvd_mul_right _ _)
  obtain ⟨z, hz⟩ := (WhiteRun.isCoprime_two_pow_three_pow m k).mul_dvd h1 h3
  refine ⟨z, ?_⟩
  have hzR : (u : ℝ) * 3 ^ k + v * 2 ^ m - 1 = 2 ^ m * 3 ^ k * z := by exact_mod_cast hz
  have h2m : (2 : ℝ) ^ m ≠ 0 := by positivity
  have h3k : (3 : ℝ) ^ k ≠ 0 := by positivity
  field_simp
  linear_combination hzR

/-- A sum of terms each an integer plus `g i` is an integer plus `∑ g`. -/
theorem sum_int_add {ι : Type*} (T : Finset ι) (f g : ι → ℝ)
    (h : ∀ i ∈ T, ∃ z : ℤ, f i = z + g i) : ∃ z : ℤ, ∑ i ∈ T, f i = z + ∑ i ∈ T, g i := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a T ha ih =>
    obtain ⟨z1, hz1⟩ := h a (mem_insert_self a T)
    obtain ⟨z2, hz2⟩ := ih fun i hi => h i (mem_insert_of_mem hi)
    refine ⟨z1 + z2, ?_⟩
    rw [sum_insert ha, sum_insert ha, hz1, hz2]; push_cast; ring

/-! ## 2. The prefix map -/

/-- Upper bound for the prefix map under the barrier `b`. -/
def Xmax (b : ℕ → ℕ) (N : ℕ) : ℕ := ∑ i ∈ range N, 3 ^ (N - 1 - i) * 2 ^ b i

theorem X_le_Xmax {b : ℕ → ℕ} {N S : ℕ} (hN : 1 ≤ N) {P : FiniteValuationWord N}
    (hP : P ∈ shellP b N S) : C P.toInfinite N ≤ Xmax b N := by
  rw [shellP, mem_filter, mem_confinedWords hN] at hP
  obtain ⟨⟨_, hbar⟩, _⟩ := hP
  unfold C Xmax
  refine sum_le_sum fun i hi => ?_
  have hi' := mem_range.mp hi
  refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) ?_)
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0; simp
  · rw [← prefixSum_eq_s P hi'.le]
    exact hbar i (mem_Icc.mpr ⟨hpos, hi'.le⟩)

theorem X_injOn (b : ℕ → ℕ) {N : ℕ} (hN : 1 ≤ N) (S : ℕ) :
    Set.InjOn (fun P : FiniteValuationWord N => C P.toInfinite N) ↑(shellP b N S) := by
  intro P hP P' hP' hX
  simp only at hX
  simp only [coe_filter, shellP, Set.mem_ofPred_eq, mem_confinedWords hN] at hP hP'
  obtain ⟨⟨hpos, _⟩, htot⟩ := hP
  obtain ⟨⟨hpos', _⟩, htot'⟩ := hP'
  have hd : ∀ l < N, 1 ≤ P.toInfinite l := fun l hl => by
    rw [toInfinite_apply_of_lt _ hl]; exact hpos _
  have he : ∀ l < N, 1 ≤ P'.toInfinite l := fun l hl => by
    rw [toInfinite_apply_of_lt _ hl]; exact hpos' _
  by_contra hne
  have hex : ∃ i, i < N ∧ P.toInfinite i ≠ P'.toInfinite i := by
    by_contra hall
    push_neg at hall
    apply hne; funext i
    have := hall i i.isLt
    rwa [toInfinite_apply_of_lt _ i.isLt, toInfinite_apply_of_lt _ i.isLt] at this
  classical
  set i := Nat.find hex with hi
  have hiN : i < N := (Nat.find_spec hex).1
  have hdiff : P.toInfinite i ≠ P'.toInfinite i := (Nat.find_spec hex).2
  have hagree : ∀ l < i, P.toInfinite l = P'.toInfinite l := by
    intro l hl
    by_contra h
    exact Nat.find_min hex hl ⟨lt_trans hl hiN, h⟩
  by_cases hlast : i + 1 < N
  · have hv := (FirstDivergence.q_sub_valuation hagree hdiff hlast hd he).2
    apply hv
    rw [q_eq_C, q_eq_C, hX, sub_self]
    exact dvd_zero _
  · have hiN1 : i + 1 = N := by omega
    have hs : s P.toInfinite i = s P'.toInfinite i := FirstDivergence.s_eq_of_agree hagree le_rfl
    have hT : s P.toInfinite N = s P'.toInfinite N := by
      rw [← prefixSum_eq_s P le_rfl, ← prefixSum_eq_s P' le_rfl]
      change P.total = P'.total
      rw [htot, htot']
    have hT' : s P.toInfinite (i + 1) = s P'.toInfinite (i + 1) := by rw [hiN1]; exact hT
    rw [s_succ, s_succ, hs] at hT'
    exact hdiff (by omega)

/-! ## 3. Grid form of the prefix phase -/

theorem uInv_modEq (m i : ℕ) :
    ((WeightedChain.uInv m i : ℕ) : ℤ) * 3 ^ (i + 1) ≡ 1 [ZMOD 2 ^ m] := by
  have h : ((WeightedChain.uInv m i * 3 ^ (i + 1) : ℕ) : ZMod (2 ^ m)) = ((1 : ℕ) : ZMod (2 ^ m)) := by
    push_cast
    unfold WeightedChain.uInv
    rw [ZMod.natCast_zmod_val, mul_comm]
    push_cast
    exact WeightedChain.three_pow_mul_inv m (i + 1)
  have := (ZMod.natCast_eq_natCast_iff _ _ _).mp h
  have h2 := (Int.natCast_modEq_iff (n := 2 ^ m)).mpr this
  push_cast at h2
  exact h2

/-- An integer inverse of `2^m` modulo `3^N`. -/
noncomputable def W (m N : ℕ) : ℕ := (((2 ^ m : ℕ) : ZMod (3 ^ N))⁻¹).val

theorem W_modEq (m N : ℕ) : ((W m N : ℕ) : ℤ) * 2 ^ m ≡ 1 [ZMOD 3 ^ N] := by
  have hc : Nat.Coprime (2 ^ m) (3 ^ N) :=
    Nat.Coprime.pow m N (by norm_num : Nat.Coprime 2 3)
  have h : ((W m N * 2 ^ m : ℕ) : ZMod (3 ^ N)) = ((1 : ℕ) : ZMod (3 ^ N)) := by
    push_cast
    unfold W
    rw [ZMod.natCast_zmod_val, mul_comm]
    have := ZMod.coe_mul_inv_eq_one (n := 3 ^ N) (2 ^ m) hc
    push_cast at this ⊢
    exact this
  have := (ZMod.natCast_eq_natCast_iff _ _ _).mp h
  have h2 := (Int.natCast_modEq_iff (n := 3 ^ N)).mpr this
  push_cast at h2
  exact h2

/-- The prefix phase numerator `Z = ∑_{i<N} u_i 2^{S_i}`. -/
noncomputable def Zpre (m N : ℕ) (P : FiniteValuationWord N) : ℕ :=
  ∑ i ∈ range N, WeightedChain.uInv m i * 2 ^ P.prefixSum i

theorem prefix_phase_grid (m N : ℕ) (P : FiniteValuationWord N) :
    ∃ z : ℤ, (Zpre m N P : ℝ) / 2 ^ m =
      z + ((-(W m N : ℤ) * C P.toInfinite N : ℤ) : ℝ) / 3 ^ N +
        (C P.toInfinite N : ℝ) / (3 ^ N * 2 ^ m) := by
  have hterm : ∀ i ∈ range N, ∃ z : ℤ,
      (WeightedChain.uInv m i : ℝ) * 2 ^ P.prefixSum i / 2 ^ m =
        z + ((-(W m N : ℝ)) * (3 ^ (N - 1 - i) * 2 ^ P.prefixSum i) / 3 ^ N +
          (3 ^ (N - 1 - i) * 2 ^ P.prefixSum i) / (3 ^ N * 2 ^ m)) := by
    intro i hi
    have hiN := mem_range.mp hi
    have hv : ((W m N : ℕ) : ℤ) * 2 ^ m ≡ 1 [ZMOD 3 ^ (i + 1)] :=
      (W_modEq m N).of_dvd (pow_dvd_pow 3 (by omega))
    obtain ⟨z, hz⟩ := reciprocity (uInv_modEq m i) hv
    refine ⟨z * 2 ^ P.prefixSum i, ?_⟩
    have h3 : (3 : ℝ) ^ N = 3 ^ (N - 1 - i) * 3 ^ (i + 1) := by
      rw [← pow_add]; congr 1; omega
    have h2m : (2 : ℝ) ^ m ≠ 0 := by positivity
    have h3k : (3 : ℝ) ^ (i + 1) ≠ 0 := by positivity
    have h3j : (3 : ℝ) ^ (N - 1 - i) ≠ 0 := by positivity
    have hz' : (WeightedChain.uInv m i : ℝ) / 2 ^ m =
        z - (W m N : ℝ) / 3 ^ (i + 1) + 1 / (3 ^ (i + 1) * 2 ^ m) := by
      push_cast at hz; linarith
    have e1 : (-(W m N : ℝ)) * (3 ^ (N - 1 - i) * 2 ^ P.prefixSum i) /
        (3 ^ (N - 1 - i) * 3 ^ (i + 1)) = -(W m N : ℝ) * 2 ^ P.prefixSum i / 3 ^ (i + 1) := by
      field_simp
    have e2 : (3 ^ (N - 1 - i) * 2 ^ P.prefixSum i : ℝ) / (3 ^ (N - 1 - i) * 3 ^ (i + 1) * 2 ^ m) =
        2 ^ P.prefixSum i / (3 ^ (i + 1) * 2 ^ m) := by
      field_simp
    rw [h3, e1, e2, mul_div_right_comm, hz']
    push_cast
    ring
  obtain ⟨z, hz⟩ := sum_int_add (range N) _ _ hterm
  refine ⟨z, ?_⟩
  have hL : (Zpre m N P : ℝ) / 2 ^ m =
      ∑ i ∈ range N, (WeightedChain.uInv m i : ℝ) * 2 ^ P.prefixSum i / 2 ^ m := by
    unfold Zpre; push_cast; rw [sum_div]
  have hC : (C P.toInfinite N : ℝ) = ∑ i ∈ range N, (3 : ℝ) ^ (N - 1 - i) * 2 ^ P.prefixSum i := by
    unfold C; push_cast
    refine sum_congr rfl fun i hi => ?_
    rw [prefixSum_eq_s P (mem_range.mp hi).le]
  rw [hL, hz, sum_add_distrib, ← sum_div, ← sum_div, ← mul_sum]
  push_cast
  rw [hC]
  ring

/-! ## 4. Path splitting and the sieve for `Ψ` -/

section Sieve

variable (b : ℕ → ℕ)

open SwapBound

/-- Step phase of the `Ψ` path product. -/
noncomputable abbrev cp (lam m i S : ℕ) : ℝ :=
  SwapCollatz.collatzPhase lam m (WeightedChain.uInv m) i S

/-- Prefix sum over `N`-step prefixes ending at state `S`. -/
noncomputable def Fpre (m N S lam : ℕ) : ℂ :=
  ∑ P ∈ shellP b N S, ∏ i ∈ range N, ee (cp lam m i (P.prefixSum i))

/-- Continuation sum from state `S` at step `N` to total `σ` at step `j0`. -/
noncomputable def Gsuf (m j0 N σ S lam : ℕ) : ℂ :=
  ∑ v ∈ shellV b j0 N S (σ - S), ∏ k ∈ range (j0 - N), ee (cp lam m (N + k) (S + v.prefixSum k))

theorem prefixSum_concat_lt {N j0 : ℕ} (P : FiniteValuationWord N) (v : FiniteValuationWord (j0 - N))
    (hj : N ≤ j0) {i : ℕ} (hi : i ≤ N) : (concat j0 P v).prefixSum i = P.prefixSum i := by
  rw [← prefixSum_pre (concat j0 P v) hj hi, pre_concat P v hj]

theorem prefixSum_concat_ge {N j0 : ℕ} (P : FiniteValuationWord N) (v : FiniteValuationWord (j0 - N))
    (hj : N ≤ j0) {k : ℕ} (hk : k ≤ j0 - N) :
    (concat j0 P v).prefixSum (N + k) = P.total + v.prefixSum k := by
  have h := prefixSum_suf (concat j0 P v) hj hk
  rw [suf_concat P v hj, prefixSum_concat_lt P v hj le_rfl] at h
  change _ = P.prefixSum N + _
  omega

/-- **Path splitting** of the `Ψ` path product at step `N`. -/
theorem psi_split (m j0 N σ lam : ℕ) (hN1 : 1 ≤ N) (hNj : N < j0) :
    ∑ P ∈ shellP b j0 σ, ∏ i ∈ range j0, ee (cp lam m i (P.prefixSum i)) =
      ∑ S ∈ range (σ + 1), Fpre b m N S lam * Gsuf b m j0 N σ S lam := by
  rw [show shellP b j0 σ = (confinedWords j0 b).filter (fun w => w.total = σ) from rfl,
    sum_shell_eq_sum_split b hN1 hNj σ]
  refine sum_congr rfl fun S _ => ?_
  rw [Fpre, Gsuf, sum_mul_sum]
  refine sum_congr rfl fun P hP => sum_congr rfl fun v _ => ?_
  have hPS : P.total = S := (mem_filter.mp hP).2
  have hr : range j0 = range (N + (j0 - N)) := by congr 1; omega
  rw [hr, prod_range_add]
  congr 1
  · exact prod_congr rfl fun i hi => by
      rw [prefixSum_concat_lt P v hNj.le (mem_range.mp hi).le]
  · exact prod_congr rfl fun k hk => by
      rw [prefixSum_concat_ge P v hNj.le (mem_range.mp hk).le, hPS]

theorem ee_prod {ι : Type*} (T : Finset ι) (x : ι → ℝ) : ∏ i ∈ T, ee (x i) = ee (∑ i ∈ T, x i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [TwistExpansion.ee_zero]
  | insert a T ha ih => rw [prod_insert ha, sum_insert ha, ih, TwistExpansion.ee_add]

theorem norm_Gsuf_le (m j0 N σ S lam : ℕ) :
    ‖Gsuf b m j0 N σ S lam‖ ≤ (shellV b j0 N S (σ - S)).card := by
  unfold Gsuf
  refine (norm_sum_le _ _).trans ?_
  rw [← nsmul_one (shellV b j0 N S (σ - S)).card, ← sum_const]
  refine sum_le_sum fun v _ => ?_
  rw [norm_prod]
  simp [norm_ee]

theorem norm_Fpre_le (m N S lam : ℕ) : ‖Fpre b m N S lam‖ ≤ (shellP b N S).card := by
  unfold Fpre
  refine (norm_sum_le _ _).trans ?_
  rw [← nsmul_one (shellP b N S).card, ← sum_const]
  refine sum_le_sum fun v _ => ?_
  rw [norm_prod]
  simp [norm_ee]

/-- The prefix product is a single character of the prefix numerator. -/
theorem prod_cp_eq (lam m N : ℕ) (P : FiniteValuationWord N) :
    ∏ i ∈ range N, ee (cp lam m i (P.prefixSum i)) = ee (-((lam : ℝ) * ((Zpre m N P : ℝ) / 2 ^ m))) := by
  simp only [cp, SwapCollatz.collatzPhase, WeightedChain.ee_neg_fract]
  rw [ee_prod, sum_neg_distrib]
  congr 1; congr 1
  unfold Zpre
  push_cast
  rw [sum_div, mul_sum]
  exact sum_congr rfl fun i _ => by ring

/-- `‖Fpre‖` in grid form. -/
theorem norm_Fpre_eq_grid (m N S lam : ℕ) :
    ‖Fpre b m N S lam‖ = ‖∑ P ∈ shellP b N S, ee ((lam : ℝ) *
      (((-(W m N : ℤ) * C P.toInfinite N : ℤ) : ℝ) / ((3 ^ N : ℕ) : ℝ) +
        (C P.toInfinite N : ℝ) / (3 ^ N * 2 ^ m)))‖ := by
  unfold Fpre
  simp_rw [prod_cp_eq]
  rw [← norm_star (∑ P ∈ shellP b N S, ee (-((lam : ℝ) * ((Zpre m N P : ℝ) / 2 ^ m))))]
  congr 1
  rw [star_sum]
  refine sum_congr rfl fun P _ => ?_
  have h := IntervalSieve.conj_ee (-((lam : ℝ) * ((Zpre m N P : ℝ) / 2 ^ m)))
  rw [neg_neg] at h
  change (starRingEnd ℂ) _ = _
  rw [h]
  obtain ⟨z, hz⟩ := prefix_phase_grid m N P
  rw [hz, mul_add, mul_add, TwistExpansion.ee_add, TwistExpansion.ee_add,
    show (lam : ℝ) * z = ((lam * z : ℤ) : ℝ) by push_cast; ring, TwistExpansion.ee_int, one_mul]
  push_cast
  rw [mul_add, TwistExpansion.ee_add]

/-- **Sieve bound for the prefix sums.** -/
theorem sum_sq_norm_Fpre_le (m N S : ℕ) (hN : 1 ≤ N) (hX : 2 * Xmax b N ≤ 2 ^ m) (a H : ℕ) :
    ∑ k ∈ range H, ‖Fpre b m N S (a + k)‖ ^ 2 ≤
      (shellP b N S).card * (Xmax b N / 3 ^ N + 1 : ℕ) *
        (H + 2 * (3 ^ N : ℕ) * (1 + Real.log (3 ^ N : ℕ))) := by
  classical
  set T := shellP b N S
  set q : ℕ := 3 ^ N with hqdef
  have hq : 1 ≤ q := Nat.one_le_pow _ _ (by norm_num)
  set A : FiniteValuationWord N → ℤ := fun P => -(W m N : ℤ) * C P.toInfinite N
  set δ : FiniteValuationWord N → ℝ := fun P => (C P.toInfinite N : ℝ) / (3 ^ N * 2 ^ m)
  have hδ0 : ∀ P ∈ T, 0 ≤ δ P := fun P _ => by positivity
  have hδ1 : ∀ P ∈ T, δ P ≤ 1 / (2 * q) := by
    intro P hP
    have hC := X_le_Xmax hN hP
    have h2 : (2 : ℝ) * C P.toInfinite N ≤ 2 ^ m := by exact_mod_cast (by omega : 2 * C P.toInfinite N ≤ 2 ^ m)
    simp only [δ, hqdef]
    push_cast
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 3) N]
  have hμ : ∀ c : ℤ, (T.filter fun j => A j % q = c).card ≤ Xmax b N / 3 ^ N + 1 := by
    intro c
    by_cases hne : (T.filter fun j => A j % q = c).Nonempty
    · obtain ⟨P0, hP0⟩ := hne
      have hsub : (T.filter fun j => A j % q = c) ⊆
          T.filter fun P => C P.toInfinite N % q = C P0.toInfinite N % q := by
        intro P hP
        rw [mem_filter] at hP hP0 ⊢
        refine ⟨hP.1, ?_⟩
        have h1 : A P ≡ A P0 [ZMOD q] := by
          unfold Int.ModEq; rw [hP.2, hP0.2]
        have hWq : ((W m N : ℕ) : ℤ) * 2 ^ m ≡ 1 [ZMOD q] := by
          rw [hqdef]; push_cast; exact W_modEq m N
        have h2 := h1.mul_left (-(2 : ℤ) ^ m)
        have e1 : -(2 : ℤ) ^ m * A P = ((W m N : ℕ) : ℤ) * 2 ^ m * C P.toInfinite N := by
          simp only [A]; ring
        have e2 : -(2 : ℤ) ^ m * A P0 = ((W m N : ℕ) : ℤ) * 2 ^ m * C P0.toInfinite N := by
          simp only [A]; ring
        rw [e1, e2] at h2
        have h3 := (hWq.mul_right (C P.toInfinite N : ℤ)).symm.trans
          (h2.trans (hWq.mul_right (C P0.toInfinite N : ℤ)))
        rw [one_mul, one_mul] at h3
        exact (Int.natCast_modEq_iff (n := q)).mp h3
      refine (card_le_card hsub).trans ?_
      exact WhiteRun.card_fibre_mod_le T (fun P => C P.toInfinite N) (Xmax b N) q _
        (X_injOn b hN S) (fun P hP => X_le_Xmax hN hP)
    · rw [not_nonempty_iff_eq_empty.mp hne, card_empty]; exact Nat.zero_le _
  have hsieve := IntervalSieve.grid_sieve T hq A δ hδ0 hδ1 _ hμ H (a : ℝ)
  calc ∑ k ∈ range H, ‖Fpre b m N S (a + k)‖ ^ 2
      = ∑ k ∈ range H, ‖∑ i ∈ T, ee (((a : ℝ) + k) * ((A i : ℝ) / q + δ i))‖ ^ 2 := by
        refine sum_congr rfl fun k _ => ?_
        rw [norm_Fpre_eq_grid]
        congr 2
        refine sum_congr rfl fun P _ => ?_
        congr 1
        simp only [A, δ, hqdef]
        push_cast
        ring
    _ ≤ _ := hsieve

/-- **(C3) for `Ψ`.**  On any `H` consecutive frequencies `a, …, a+H−1`, splitting the prefix
paths at step `N` (`1 ≤ N < j0`) with `2·Xmax(N) ≤ 2^m`, `m = σ + 1 + t`:
`√(∑ ‖Ψ‖²) ≤ ∑_S g_S · min(√H·p_S, √(p_S μ (H + 2·3^N (1 + log 3^N))))`. -/
theorem psi_shell_sieve (j0 σ t N : ℕ) (hN1 : 1 ≤ N) (hNj : N < j0)
    (hX : 2 * Xmax b N ≤ 2 ^ (σ + 1 + t)) (a H : ℕ) :
    √(∑ k ∈ range H, ‖TwistExpansion.Psi (shellP b j0 σ) (σ + 1) t (WeightedChain.yPrime j0 σ t) (a + k)‖ ^ 2) ≤
      ∑ S ∈ range (σ + 1), ((shellV b j0 N S (σ - S)).card : ℝ) *
        min (√(H : ℝ) * (shellP b N S).card)
          √((shellP b N S).card * (Xmax b N / 3 ^ N + 1 : ℕ) *
            (H + 2 * (3 ^ N : ℕ) * (1 + Real.log (3 ^ N : ℕ)))) := by
  set m := σ + 1 + t with hm
  have hsum : ∑ k ∈ range H,
      ‖TwistExpansion.Psi (shellP b j0 σ) (σ + 1) t (WeightedChain.yPrime j0 σ t) (a + k)‖ ^ 2 =
      ∑ k ∈ range H, ‖∑ S ∈ range (σ + 1), Fpre b m N S (a + k) * Gsuf b m j0 N σ S (a + k)‖ ^ 2 := by
    refine sum_congr rfl fun k _ => ?_
    rw [WeightedChain.norm_Psi_eq, ← psi_split b m j0 N σ (a + k) hN1 hNj]
  rw [hsum]
  refine (IntervalSieve.minkowski_step (range H) (range (σ + 1))
    (fun S k => Fpre b m N S (a + k)) (fun S k => Gsuf b m j0 N σ S (a + k))
    (fun S => ((shellV b j0 N S (σ - S)).card : ℝ)) (fun S _ => by positivity)
    (fun S _ k _ => norm_Gsuf_le b m j0 N σ S (a + k))).trans ?_
  refine sum_le_sum fun S _ => mul_le_mul_of_nonneg_left (le_min ?_ ?_) (by positivity)
  · calc √(∑ k ∈ range H, ‖Fpre b m N S (a + k)‖ ^ 2)
        ≤ √(∑ k ∈ range H, ((shellP b N S).card : ℝ) ^ 2) := by
          apply Real.sqrt_le_sqrt
          exact sum_le_sum fun k _ => by
            gcongr
            exact norm_Fpre_le b m N S _
      _ = √(H : ℝ) * (shellP b N S).card := by
          rw [sum_const, card_range, nsmul_eq_mul, Real.sqrt_mul (by positivity),
            Real.sqrt_sq (by positivity)]
  · exact Real.sqrt_le_sqrt (sum_sq_norm_Fpre_le b m N S hN1 hX a H)

end Sieve

end PsiSieve
end EOC
