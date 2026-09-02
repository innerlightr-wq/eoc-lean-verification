import EOC.Periodic
import EOC.BoundedDriftCore
/-!
# EOC/BoundedDrift.lean — bounded-drift realizer escape (bridge to the repository API)

STATUS: NOT COMPILED IN THE AUDIT ENVIRONMENT (Mathlib cache unreachable there).
`EOC/BoundedDriftCore.lean` IS kernel-checked (Lean 4.34.0-rc1, no Mathlib, standard axioms).
This file is written against the exact signatures in the repository's compiled
`Periodic.lean` / `Confinement.lean` / `Realizer.lean`. Lines marked `-- CHECK` are the only
Mathlib names not already used elsewhere in the repository.

Curry-independent: the injective branch uses only `BoundedDriftCore.no_injective_orbit_of_lower_drift`.
-/

namespace EOC
open PeriodicCore BoundedDriftCore

/-! ### Step law along an actual orbit -/

theorem orbit_step (m0 : ℕ) : ∀ i, 2 ^ a (orbit m0 i) * orbit m0 (i + 1) = 3 * orbit m0 i + 1 := by
  intro i
  rw [orbit_succ]
  unfold T
  exact Nat.mul_div_cancel' (two_pow_a_dvd _)

/-! ### Non-injective orbits are eventually periodic words -/

theorem evPeriodic_of_noninj (m0 i j : ℕ) (hij : i < j) (heq : orbit m0 i = orbit m0 j) :
    EvPeriodic (fun n => a (orbit m0 n)) i (j - i) := by
  intro n hn
  have key : ∀ t, orbit m0 (i + t + (j - i)) = orbit m0 (i + t) := by
    intro t
    rw [show i + t + (j - i) = j + t from by omega, orbit_add m0 j t, ← heq, ← orbit_add]
  obtain ⟨t, ht⟩ : ∃ t, n = i + t := ⟨n - i, by omega⟩
  subst ht
  show a (orbit m0 (i + t + (j - i))) = a (orbit m0 (i + t))
  rw [key t]

/-- **Case A.** A non-injective orbit is not permanently upper-confined. -/
theorem noninjective_orbit_not_upper_confined (c : ℝ) (m0 : ℕ) (hm0 : Odd m0)
    (hnoninj : ∃ i j, i ≠ j ∧ orbit m0 i = orbit m0 j) :
    ∃ N, ¬ Confined c (fun n => a (orbit m0 n)) N := by
  obtain ⟨i, j, hne, heq⟩ := hnoninj
  rcases Nat.lt_or_gt_of_ne hne with hij | hij
  · exact not_confined_forever_of_evPeriodic_orbit c m0 i (j - i) hm0 (by omega)
      (evPeriodic_of_noninj m0 i j hij heq)
  · exact not_confined_forever_of_evPeriodic_orbit c m0 j (i - j) hm0 (by omega)
      (evPeriodic_of_noninj m0 j i hij heq.symm)

/-- **Case B (integer form).** An injective orbit has no integer lower drift bound. -/
theorem injective_orbit_no_lower_drift (m0 : ℕ) (hm0 : Odd m0) (Gn : ℕ)
    (hinj : ∀ i j, orbit m0 i = orbit m0 j → i = j)
    (hlow : ∀ j, 3 ^ j ≤ 2 ^ Gn * 2 ^ s (fun n => a (orbit m0 n)) j) : False :=
  no_injective_orbit_of_lower_drift (orbit m0) (fun n => a (orbit m0 n)) Gn
    (fun i => (odd_orbit hm0 i).pos)      -- CHECK: `Odd.pos`
    hinj (orbit_step m0)
    (fun j => by rw [← s_eq_sr]; exact hlow j)

/-! ### Real drift bound ⇒ integer drift bound -/

theorem three_pow_le_of_drift (d : ℕ → ℕ) (G : ℝ) (hlow : ∀ N, -G ≤ R d N) :
    ∀ j, 3 ^ j ≤ 2 ^ (Nat.ceil G) * 2 ^ s d j := by
  intro j
  have hR := hlow j
  unfold R at hR
  have hG : G ≤ (Nat.ceil G : ℝ) := Nat.le_ceil G
  have hexp : (j : ℝ) * alpha ≤ (s d j : ℝ) + (Nat.ceil G : ℝ) := by linarith
  have h3 : ((3 : ℝ)) ^ j = (2 : ℝ) ^ ((j : ℝ) * alpha) := by
    unfold alpha
    rw [mul_comm, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_logb (by norm_num) (by norm_num) (by norm_num), Real.rpow_natCast]
    -- CHECK: `Real.rpow_logb (b_pos) (b_ne_one) (hx : 0 < x) : b ^ logb b x = x`
  have hmono : (2 : ℝ) ^ ((j : ℝ) * alpha) ≤ (2 : ℝ) ^ ((s d j : ℝ) + (Nat.ceil G : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hrhs : (2 : ℝ) ^ ((s d j : ℝ) + (Nat.ceil G : ℝ)) = (2 : ℝ) ^ (Nat.ceil G) * (2 : ℝ) ^ (s d j) := by
    rw [Real.rpow_add (by norm_num), Real.rpow_natCast, Real.rpow_natCast, mul_comm]
  have hreal : ((3 : ℝ)) ^ j ≤ (2 : ℝ) ^ (Nat.ceil G) * (2 : ℝ) ^ (s d j) := by
    rw [h3, ← hrhs]; exact hmono
  exact_mod_cast hreal

/-! ### Main theorem -/

/-- **Bounded-drift realizer escape (integer lower bound).** -/
theorem leastRealizer_unbounded_of_int_drift (c : ℝ) (Gn : ℕ) (d : ℕ → ℕ) (hd : ∀ i, 1 ≤ d i)
    (hup : ∀ N, R d N ≤ c) (hlow : ∀ j, 3 ^ j ≤ 2 ^ Gn * 2 ^ s d j) :
    ∀ M, ∃ N, M < leastRealizer d N := by
  intro M
  by_contra hno
  push_neg at hno
  have hmono : ∀ N, leastRealizer d N ≤ leastRealizer d (N + 1) :=
    fun N => leastRealizer_mono d N (fun i _ => hd i)
  obtain ⟨N0, hN0⟩ := eventually_const_of_mono_bounded (leastRealizer d) hmono M hno
  set N1 := max N0 1 with hN1
  have hconst : ∀ N, N1 ≤ N → leastRealizer d N = leastRealizer d N1 := by
    intro N hN
    rw [hN0 N (le_trans (le_max_left _ _) hN), hN0 N1 (le_max_left _ _)]
  have hword := realizes_all_of_leastRealizer_const d hd N1 (le_max_right _ _) _ hconst
  set m := leastRealizer d N1 with hm
  have hodd : Odd m := leastRealizer_odd d N1 (le_max_right _ _) (fun i _ => hd i)
  have hwordeq : (fun i => a (orbit m i)) = d := funext hword
  by_cases hinj : ∀ i j, orbit m i = orbit m j → i = j
  · exact injective_orbit_no_lower_drift m hodd Gn hinj (by rw [hwordeq]; exact hlow)
  · push_neg at hinj
    obtain ⟨i, j, heq, hne⟩ := hinj
    obtain ⟨N, hN⟩ := noninjective_orbit_not_upper_confined c m hodd ⟨i, j, hne, heq⟩
    apply hN
    intro k _
    rw [hwordeq]
    exact hup k

/-- **Bounded-drift realizer escape (real form).** -/
theorem leastRealizer_unbounded_of_two_sided_drift (c G : ℝ) (d : ℕ → ℕ) (hd : ∀ i, 1 ≤ d i)
    (hup : ∀ N, R d N ≤ c) (hlow : ∀ N, -G ≤ R d N) :
    ∀ M, ∃ N, M < leastRealizer d N :=
  leastRealizer_unbounded_of_int_drift c (Nat.ceil G) d hd hup (three_pow_le_of_drift d G hlow)

end EOC
