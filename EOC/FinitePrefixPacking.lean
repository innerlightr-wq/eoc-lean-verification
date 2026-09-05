import EOC.BoundedDrift

/-!
# Finite-prefix injective packing

This file gives the finite-horizon form of the injective packing argument.
Unlike `EOC.BoundedDrift`, the drift floor is required only through the
specified prefix.  The final count uses the fact that every post-initial
accelerated orbit state is odd and is not divisible by `3`.
-/

namespace EOC

open PeriodicCore BoundedDriftCore

/-! ## Finite-horizon drift and state bounds -/

/-- A lower drift bound through `N` gives the corresponding integer power
inequality through `N`. -/
theorem three_pow_le_of_drift_upto (d : ℕ → ℕ) (G : ℝ) (N : ℕ)
    (hlow : ∀ j ≤ N, -G ≤ R d j) :
    ∀ j ≤ N, 3 ^ j ≤ 2 ^ (Nat.ceil G) * 2 ^ s d j := by
  intro j hj
  have hR := hlow j hj
  unfold R at hR
  have hG : G ≤ (Nat.ceil G : ℝ) := Nat.le_ceil G
  have hexp : (j : ℝ) * alpha ≤ (s d j : ℝ) + (Nat.ceil G : ℝ) := by
    linarith
  have h3 : ((3 : ℝ)) ^ j = (2 : ℝ) ^ ((j : ℝ) * alpha) := by
    unfold alpha
    rw [mul_comm, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_logb (by norm_num) (by norm_num) (by norm_num), Real.rpow_natCast]
  have hmono : (2 : ℝ) ^ ((j : ℝ) * alpha)
      ≤ (2 : ℝ) ^ ((s d j : ℝ) + (Nat.ceil G : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hrhs : (2 : ℝ) ^ ((s d j : ℝ) + (Nat.ceil G : ℝ))
      = (2 : ℝ) ^ (Nat.ceil G) * (2 : ℝ) ^ (s d j) := by
    rw [Real.rpow_add (by norm_num), Real.rpow_natCast, Real.rpow_natCast, mul_comm]
  have hreal : ((3 : ℝ)) ^ j
      ≤ (2 : ℝ) ^ (Nat.ceil G) * (2 : ℝ) ^ (s d j) := by
    rw [h3, ← hrhs]
    exact hmono
  exact_mod_cast hreal

/-- Natural-valued specialization of `three_pow_le_of_drift_upto`, avoiding
the ceiling in the main integer theorem. -/
theorem three_pow_le_of_nat_drift_upto (d : ℕ → ℕ) (g N : ℕ)
    (hlow : ∀ j ≤ N, -((g : ℝ)) ≤ R d j) :
    ∀ j ≤ N, 3 ^ j ≤ 2 ^ g * 2 ^ s d j := by
  simpa using three_pow_le_of_drift_upto d (g : ℝ) N hlow

private def prefixExtension (m : ℕ → ℕ) (N : ℕ) (i : ℕ) : ℕ :=
  if i < N then m i else (∑ k ∈ Finset.range N, m k) + i + 1

private theorem prefixExtension_eq (m : ℕ → ℕ) {N i : ℕ} (hi : i < N) :
    prefixExtension m N i = m i := by
  simp [prefixExtension, hi]

private theorem prefixExtension_pos (m : ℕ → ℕ) (N : ℕ)
    (hm : ∀ i < N, 1 ≤ m i) : ∀ i, 1 ≤ prefixExtension m N i := by
  intro i
  by_cases hi : i < N
  · simpa [prefixExtension, hi] using hm i hi
  · simp [prefixExtension, hi]

private theorem prefixExtension_injective (m : ℕ → ℕ) (N : ℕ)
    (hinj : ∀ i < N, ∀ j < N, m i = m j → i = j) :
    ∀ i j, prefixExtension m N i = prefixExtension m N j → i = j := by
  intro i j hij
  have hsum : ∀ k < N, m k ≤ ∑ x ∈ Finset.range N, m x := by
    intro k hk
    exact Finset.single_le_sum (fun x _ ↦ Nat.zero_le (m x))
      (Finset.mem_range.mpr hk)
  by_cases hi : i < N
  · by_cases hj : j < N
    · apply hinj i hi j hj
      simpa [prefixExtension, hi, hj] using hij
    · have hi' := hsum i hi
      simp [prefixExtension, hi, hj] at hij
      omega
  · by_cases hj : j < N
    · have hj' := hsum j hj
      simp [prefixExtension, hi, hj] at hij
      omega
    · simp [prefixExtension, hi, hj] at hij
      omega

private theorem pr_congr_upto (f g : ℕ → ℕ) (N : ℕ)
    (hfg : ∀ i < N, f i = g i) : pr f N = pr g N := by
  induction N with
  | zero => rfl
  | succ N ih =>
      rw [pr_succ, pr_succ, ih (fun i hi ↦ hfg i (by omega)), hfg N (by omega)]

/-- Finite-prefix form of `BoundedDriftCore.packing_bound`: only the values
with indices below `N` need be positive and pairwise distinct. -/
theorem packing_bound_upto (m : ℕ → ℕ)
    (N L : ℕ)
    (hm : ∀ i < N, 1 ≤ m i)
    (hinj : ∀ i < N, ∀ j < N, m i = m j → i = j)
    (hNL : N ≤ 2 ^ L) :
    2 ^ (L + 1) * pr (fun i ↦ 3 * m i + 1) N
      ≤ 3 ^ (L + 1) * pr (fun i ↦ 3 * m i) N := by
  let m' := prefixExtension m N
  have hpack := packing_bound m' (prefixExtension_pos m N hm)
    (prefixExtension_injective m N hinj) N L hNL
  have hplus : pr (fun i ↦ 3 * m' i + 1) N = pr (fun i ↦ 3 * m i + 1) N := by
    apply pr_congr_upto
    intro i hi
    rw [show m' i = m i by exact prefixExtension_eq m hi]
  have hplain : pr (fun i ↦ 3 * m' i) N = pr (fun i ↦ 3 * m i) N := by
    apply pr_congr_upto
    intro i hi
    rw [show m' i = m i by exact prefixExtension_eq m hi]
  simpa only [hplus, hplain] using hpack

/-- Finite-horizon form of `BoundedDriftCore.state_bound`.  Its lower-power
hypothesis is needed only at indices `j ≤ N`. -/
theorem state_bound_upto (m d : ℕ → ℕ) (G : ℕ)
    (N L : ℕ)
    (hm : ∀ i, 1 ≤ m i)
    (hinj : ∀ i < N, ∀ j < N, m i = m j → i = j)
    (hstep : ∀ i, 2 ^ d i * m (i + 1) = 3 * m i + 1)
    (hlow : ∀ j ≤ N, 3 ^ j ≤ 2 ^ G * 2 ^ sr d j)
    (hNL : N ≤ 2 ^ L) :
    ∀ j ≤ N, m j * 2 ^ (L + 1) ≤ 2 ^ G * m 0 * 3 ^ (L + 1) := by
  intro j hj
  have hid := orbit_product_identity m d hstep j
  have hQj : 1 ≤ pr (fun i ↦ 3 * m i) j :=
    pr_pos _ (fun i ↦ by have := hm i; omega) j
  have hQN : 1 ≤ pr (fun i ↦ 3 * m i) N :=
    pr_pos _ (fun i ↦ by have := hm i; omega) N
  have h2S : 1 ≤ 2 ^ sr d j := Nat.pow_pos (by decide)
  have h1 : m j * pr (fun i ↦ 3 * m i) j
      ≤ 2 ^ G * m 0 * pr (fun i ↦ 3 * m i + 1) j := by
    apply Nat.le_of_mul_le_mul_left _ h2S
    calc
      2 ^ sr d j * (m j * pr (fun i ↦ 3 * m i) j)
          = 3 ^ j * m 0 * pr (fun i ↦ 3 * m i + 1) j := by rw [← hid]; ac_rfl
      _ ≤ (2 ^ G * 2 ^ sr d j) * m 0 * pr (fun i ↦ 3 * m i + 1) j :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (hlow j hj))
      _ = 2 ^ sr d j * (2 ^ G * m 0 * pr (fun i ↦ 3 * m i + 1) j) := by ac_rfl
  obtain ⟨t, rfl⟩ : ∃ t, N = j + t := ⟨N - j, by omega⟩
  have h2 : pr (fun i ↦ 3 * m i + 1) j * pr (fun i ↦ 3 * m i) (j + t)
      ≤ pr (fun i ↦ 3 * m i) j * pr (fun i ↦ 3 * m i + 1) (j + t) := by
    rw [pr_add, pr_add]
    have hle : pr (fun i ↦ 3 * m (j + i)) t
        ≤ pr (fun i ↦ 3 * m (j + i) + 1) t :=
      pr_le_pr _ _ t (fun _ _ ↦ Nat.le_succ _)
    calc
      pr (fun i ↦ 3 * m i + 1) j *
          (pr (fun i ↦ 3 * m i) j * pr (fun i ↦ 3 * m (j + i)) t)
          = (pr (fun i ↦ 3 * m i) j * pr (fun i ↦ 3 * m i + 1) j) *
              pr (fun i ↦ 3 * m (j + i)) t := by ac_rfl
      _ ≤ (pr (fun i ↦ 3 * m i) j * pr (fun i ↦ 3 * m i + 1) j) *
              pr (fun i ↦ 3 * m (j + i) + 1) t := Nat.mul_le_mul_left _ hle
      _ = pr (fun i ↦ 3 * m i) j *
          (pr (fun i ↦ 3 * m i + 1) j * pr (fun i ↦ 3 * m (j + i) + 1) t) := by ac_rfl
  have h3 : m j * pr (fun i ↦ 3 * m i) (j + t)
      ≤ 2 ^ G * m 0 * pr (fun i ↦ 3 * m i + 1) (j + t) := by
    apply Nat.le_of_mul_le_mul_left _ hQj
    calc
      pr (fun i ↦ 3 * m i) j * (m j * pr (fun i ↦ 3 * m i) (j + t))
          = (m j * pr (fun i ↦ 3 * m i) j) * pr (fun i ↦ 3 * m i) (j + t) := by ac_rfl
      _ ≤ (2 ^ G * m 0 * pr (fun i ↦ 3 * m i + 1) j) *
              pr (fun i ↦ 3 * m i) (j + t) := Nat.mul_le_mul_right _ h1
      _ = 2 ^ G * m 0 *
          (pr (fun i ↦ 3 * m i + 1) j * pr (fun i ↦ 3 * m i) (j + t)) := by ac_rfl
      _ ≤ 2 ^ G * m 0 *
          (pr (fun i ↦ 3 * m i) j * pr (fun i ↦ 3 * m i + 1) (j + t)) :=
        Nat.mul_le_mul_left _ h2
      _ = pr (fun i ↦ 3 * m i) j *
          (2 ^ G * m 0 * pr (fun i ↦ 3 * m i + 1) (j + t)) := by ac_rfl
  have hpack := packing_bound_upto m (j + t) L (fun i _ ↦ hm i)
    (fun i hi j hj ↦ hinj i (by omega) j (by omega)) (by omega)
  apply Nat.le_of_mul_le_mul_left _ hQN
  calc
    pr (fun i ↦ 3 * m i) (j + t) * (m j * 2 ^ (L + 1))
        = (m j * pr (fun i ↦ 3 * m i) (j + t)) * 2 ^ (L + 1) := by ac_rfl
    _ ≤ (2 ^ G * m 0 * pr (fun i ↦ 3 * m i + 1) (j + t)) * 2 ^ (L + 1) :=
      Nat.mul_le_mul_right _ h3
    _ = 2 ^ G * m 0 *
        (2 ^ (L + 1) * pr (fun i ↦ 3 * m i + 1) (j + t)) := by ac_rfl
    _ ≤ 2 ^ G * m 0 *
        (3 ^ (L + 1) * pr (fun i ↦ 3 * m i) (j + t)) :=
      Nat.mul_le_mul_left _ hpack
    _ = pr (fun i ↦ 3 * m i) (j + t) * (2 ^ G * m 0 * 3 ^ (L + 1)) := by ac_rfl

/-! ## Post-initial residue restriction -/

/-- No accelerated Collatz successor is divisible by `3`. -/
theorem three_not_dvd_orbit_succ (M j : ℕ) : ¬ 3 ∣ orbit M (j + 1) := by
  intro hdiv
  have hleft : 3 ∣ 2 ^ a (orbit M j) * orbit M (j + 1) := dvd_mul_of_dvd_right hdiv _
  rw [orbit_step M j] at hleft
  omega

/-- Every post-initial state of an odd accelerated orbit is coprime to `6`. -/
theorem orbit_succ_coprime_six (M j : ℕ) (hM : Odd M) :
    Nat.Coprime (orbit M (j + 1)) 6 := by
  rw [show 6 = 2 * 3 by norm_num, Nat.coprime_mul_iff_right]
  exact ⟨(odd_orbit hM (j + 1)).coprime_two_right,
    ((by decide : Nat.Prime 3).coprime_iff_not_dvd.mpr
      (three_not_dvd_orbit_succ M j)).symm⟩

/-! ## A compressed count of the residues coprime to `6` -/

/-- Rank the admissible residues `6q+1, 6q+5` consecutively as `2q+1, 2q+2`. -/
def coprimeSixRank (x : ℕ) : ℕ :=
  2 * (x / 6) + if x % 6 = 1 then 1 else 2

theorem mod_six_eq_one_or_five {x : ℕ} (hodd : Odd x) (hthree : ¬ 3 ∣ x) :
    x % 6 = 1 ∨ x % 6 = 5 := by
  rw [Nat.odd_iff] at hodd
  rw [Nat.dvd_iff_mod_eq_zero] at hthree
  have h2 := Nat.mod_mod_of_dvd x (by decide : 2 ∣ 6)
  have h3 := Nat.mod_mod_of_dvd x (by decide : 3 ∣ 6)
  have hlt := Nat.mod_lt x (by decide : 0 < 6)
  omega

theorem coprimeSixRank_pos (x : ℕ) : 1 ≤ coprimeSixRank x := by
  unfold coprimeSixRank
  split_ifs <;> omega

theorem three_mul_coprimeSixRank_le_add_two {x : ℕ}
    (hodd : Odd x) (hthree : ¬ 3 ∣ x) :
    3 * coprimeSixRank x ≤ x + 2 := by
  rcases mod_six_eq_one_or_five hodd hthree with hmod | hmod
  · unfold coprimeSixRank
    rw [ite_eq_left hmod]
    have hdecomp := Nat.mod_add_div x 6
    omega
  · unfold coprimeSixRank
    rw [ite_eq_right (by omega)]
    have hdecomp := Nat.mod_add_div x 6
    omega

theorem coprimeSixRank_injective_on {x y : ℕ}
    (hxodd : Odd x) (hxthree : ¬ 3 ∣ x)
    (hyodd : Odd y) (hythree : ¬ 3 ∣ y)
    (hrank : coprimeSixRank x = coprimeSixRank y) : x = y := by
  rcases mod_six_eq_one_or_five hxodd hxthree with hx | hx <;>
    rcases mod_six_eq_one_or_five hyodd hythree with hy | hy
  · unfold coprimeSixRank at hrank
    rw [ite_eq_left hx, ite_eq_left hy] at hrank
    have hxd := Nat.mod_add_div x 6
    have hyd := Nat.mod_add_div y 6
    omega
  · unfold coprimeSixRank at hrank
    rw [ite_eq_left hx, ite_eq_right (by omega)] at hrank
    omega
  · unfold coprimeSixRank at hrank
    rw [ite_eq_right (by omega), ite_eq_left hy] at hrank
    omega
  · unfold coprimeSixRank at hrank
    rw [ite_eq_right (by omega), ite_eq_right (by omega)] at hrank
    have hxd := Nat.mod_add_div x 6
    have hyd := Nat.mod_add_div y 6
    omega

/-- `N` distinct positive integers bounded by `B`, all odd and not divisible
by `3`, force the sharp uniform bound `3*N ≤ B+2`. -/
theorem coprime_six_packing (m : ℕ → ℕ) (N B : ℕ)
    (hinj : ∀ i < N, ∀ j < N, m i = m j → i = j)
    (hodd : ∀ i < N, Odd (m i))
    (hthree : ∀ i < N, ¬ 3 ∣ m i)
    (hbound : ∀ i < N, m i ≤ B) :
    3 * N ≤ B + 2 := by
  let X := (B + 2) / 3
  let r : ℕ → ℕ := fun i ↦
    if i < N then coprimeSixRank (m i) else X + i + 1
  have hrange : ∀ i < N, 1 ≤ r i ∧ r i ≤ X := by
    intro i hi
    rw [show r i = coprimeSixRank (m i) by simp [r, hi]]
    refine ⟨coprimeSixRank_pos _, ?_⟩
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 3)).2
    exact le_trans (by simpa [mul_comm] using
      three_mul_coprimeSixRank_le_add_two (hodd i hi) (hthree i hi))
      (Nat.add_le_add_right (hbound i hi) 2)
  have hrinj : ∀ i j, r i = r j → i = j := by
    intro i j hij
    by_cases hi : i < N
    · by_cases hj : j < N
      · apply hinj i hi j hj
        apply coprimeSixRank_injective_on (hodd i hi) (hthree i hi)
          (hodd j hj) (hthree j hj)
        simpa only [r, ite_eq_left hi, ite_eq_left hj] using hij
      · have hir := (hrange i hi).2
        have hjr : X < r j := by simp [r, hj]
        exfalso
        omega
    · by_cases hj : j < N
      · have hjr := (hrange j hj).2
        have hir : X < r i := by simp [r, hi]
        exfalso
        omega
      · simpa [r, hi, hj] using hij
  have hpig := pigeonhole r hrinj N X hrange
  have hmul : 3 * N ≤ 3 * X := Nat.mul_le_mul_left 3 hpig
  have hdiv : 3 * X ≤ B + 2 := by
    have := Nat.div_mul_le_self (B + 2) 3
    simpa [X, mul_comm] using this
  exact le_trans hmul hdiv

/-! ## Main finite-prefix theorem -/

/-- Finite-prefix injective drift-depth bound with the strongest uniform
mod-`6` counting constant. -/
theorem finite_prefix_injective_drift_depth_bound
    (M L g : ℕ) (hM : Odd M)
    (hinj : ∀ i ≤ 2 ^ L, ∀ j ≤ 2 ^ L, orbit M i = orbit M j → i = j)
    (hlow : ∀ j ≤ 2 ^ L, -((g : ℝ)) ≤ R (fun n ↦ a (orbit M n)) j) :
    (3 * 2 ^ L - 2) * 2 ^ (L + 1) ≤ 2 ^ g * M * 3 ^ (L + 1) := by
  let d : ℕ → ℕ := fun n ↦ a (orbit M n)
  let C := 2 ^ g * M * 3 ^ (L + 1)
  let D := 2 ^ (L + 1)
  let B := C / D
  have hpow : ∀ j ≤ 2 ^ L, 3 ^ j ≤ 2 ^ g * 2 ^ sr d j := by
    intro j hj
    rw [← s_eq_sr]
    exact three_pow_le_of_nat_drift_upto d g (2 ^ L) (by simpa [d] using hlow) j hj
  have hstates : ∀ j ≤ 2 ^ L, orbit M j * D ≤ C := by
    intro j hj
    simpa [d, C, D] using
      state_bound_upto (orbit M) d g (2 ^ L) L (fun i ↦ (odd_orbit hM i).pos)
        (fun i hi j hj ↦ hinj i (Nat.le_of_lt hi) j (Nat.le_of_lt hj))
        (orbit_step M) hpow (le_refl _) j hj
  have hcount : 3 * 2 ^ L ≤ B + 2 := by
    apply coprime_six_packing (fun i ↦ orbit M (i + 1)) (2 ^ L) B
    · intro i hi j hj heq
      have := hinj (i + 1) (by omega) (j + 1) (by omega) heq
      omega
    · intro i _
      exact odd_orbit hM (i + 1)
    · intro i _
      exact three_not_dvd_orbit_succ M i
    · intro i hi
      apply (Nat.le_div_iff_mul_le (by positivity : 0 < D)).2
      exact hstates (i + 1) (by omega)
  have hB : 0 ≤ B := Nat.zero_le _
  have hsub : 3 * 2 ^ L - 2 ≤ B := by omega
  calc
    (3 * 2 ^ L - 2) * 2 ^ (L + 1) = (3 * 2 ^ L - 2) * D := by rfl
    _ ≤ B * D := Nat.mul_le_mul_right D hsub
    _ ≤ C := Nat.div_mul_le_self C D
    _ = 2 ^ g * M * 3 ^ (L + 1) := by rfl

/-- A power-only corollary exposing the two powers of `2` contributed by
the horizon and the state denominator when `L ≥ 1`. -/
theorem finite_prefix_injective_drift_depth_power_bound
    (M L g : ℕ) (hL : 1 ≤ L) (hM : Odd M)
    (hinj : ∀ i ≤ 2 ^ L, ∀ j ≤ 2 ^ L, orbit M i = orbit M j → i = j)
    (hlow : ∀ j ≤ 2 ^ L, -((g : ℝ)) ≤ R (fun n ↦ a (orbit M n)) j) :
    2 ^ (2 * (L + 1)) ≤ 2 ^ g * M * 3 ^ (L + 1) := by
  have htwo : 2 ≤ 2 ^ L := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by decide) hL
  have hfront : 2 ^ (L + 1) ≤ 3 * 2 ^ L - 2 := by
    rw [pow_succ]
    omega
  have hmain := finite_prefix_injective_drift_depth_bound M L g hM hinj hlow
  calc
    2 ^ (2 * (L + 1)) = 2 ^ (L + 1) * 2 ^ (L + 1) := by
      rw [← pow_add]
      congr 1
      omega
    _ ≤ (3 * 2 ^ L - 2) * 2 ^ (L + 1) := Nat.mul_le_mul_right _ hfront
    _ ≤ 2 ^ g * M * 3 ^ (L + 1) := hmain

/-- Real drift-floor version of `finite_prefix_injective_drift_depth_bound`.
The integer loss is exactly the natural ceiling of `G`. -/
theorem finite_prefix_injective_real_drift_depth_bound
    (M L : ℕ) (G : ℝ) (hM : Odd M)
    (hinj : ∀ i ≤ 2 ^ L, ∀ j ≤ 2 ^ L, orbit M i = orbit M j → i = j)
    (hlow : ∀ j ≤ 2 ^ L, -G ≤ R (fun n ↦ a (orbit M n)) j) :
    (3 * 2 ^ L - 2) * 2 ^ (L + 1)
      ≤ 2 ^ (Nat.ceil G) * M * 3 ^ (L + 1) := by
  apply finite_prefix_injective_drift_depth_bound M L (Nat.ceil G) hM hinj
  intro j hj
  exact le_trans (neg_le_neg (Nat.le_ceil G)) (hlow j hj)

end EOC
