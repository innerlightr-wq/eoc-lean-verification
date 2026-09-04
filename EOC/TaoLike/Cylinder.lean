import EOC.Realizer

/-!
# Cylinder restart (Tao-like EOC program, Milestone 1)

Exact arithmetic of restarting the accelerated map inside a realizer cylinder.

Main results:

* `restart_step` — one-step restart: if `a m ≤ s`, then perturbing `m` by `2^(s+1) * k`
  leaves the valuation unchanged and shifts `T m` by `2^(s - a m + 1) * (3 * k)`.
* `orbit_cylinder_restart` — the `t`-step version along the orbit's own valuation word.
* `cylinder_restart` — translation-covariant form: if `m` realizes `d` to depth `t`, so does
  `m + 2^(S d t + 1) * k`, and `orbit (m + 2^(S d t + 1) * k) t = orbit m t + 2 * 3^t * k`.
* `cylinder_restart_leastRealizer` — the canonical-class corollary.

No parity hypothesis is needed for `restart_step`/`orbit_cylinder_restart`: the valuation
`a m = v₂(3m+1)` is exact by definition, and the perturbation `2^(s+1) k` stays even after
dividing by `2^(a m)` precisely because the exponent is `s + 1` (not `s`).
-/

namespace EOC

open Finset

/-! ### Exact division facts about `T` -/

/-- Exact factorisation `3m + 1 = 2^(a m) * T m`. -/
theorem three_mul_add_one_eq (m : ℕ) : 3 * m + 1 = 2 ^ a m * T m := by
  obtain ⟨c, hc0⟩ := (pow_padicValNat_dvd : 2 ^ padicValNat 2 (3 * m + 1) ∣ 3 * m + 1)
  have hc : 3 * m + 1 = 2 ^ a m * c := hc0
  have hT : T m = c := by
    unfold T
    rw [hc, Nat.mul_div_cancel_left c (by positivity)]
  rw [hT]
  exact hc

/-- If `3m + 1 = 2^(a m) * c` then `T m = c`. -/
theorem T_eq_of_eq (m c : ℕ) (h : 3 * m + 1 = 2 ^ a m * c) : T m = c := by
  unfold T
  rw [h, Nat.mul_div_cancel_left c (by positivity)]

/-- `T m` is always odd (the cofactor of the exact 2-power is odd). -/
theorem T_odd (m : ℕ) : Odd (T m) := by
  have hne : 3 * m + 1 ≠ 0 := by omega
  have hnot0 : ¬ 2 ^ (padicValNat 2 (3 * m + 1) + 1) ∣ 3 * m + 1 :=
    pow_succ_padicValNat_not_dvd hne
  have hnot : ¬ 2 ^ (a m + 1) ∣ 3 * m + 1 := hnot0
  rcases Nat.even_or_odd (T m) with heven | hodd
  · exfalso
    obtain ⟨c, hc⟩ := heven
    apply hnot
    refine ⟨c, ?_⟩
    rw [three_mul_add_one_eq m, hc, pow_succ]
    ring
  · exact hodd

/-! ### One-step restart -/

/-- **One-step restart lemma.** Let `d = a m` and `d ≤ s`. Then for every `k`,
`a (m + 2^(s+1) k) = d` and `T (m + 2^(s+1) k) = T m + 2^(s-d+1) * (3k)`.

The modulus must be `2^(s+1)`, not `2^s`: after dividing by `2^d` the perturbation is
`3 * 2^(s+1-d) * k`, which is even because `s + 1 - d ≥ 1`. -/
theorem restart_step (m k s : ℕ) (hs : a m ≤ s) :
    a (m + 2 ^ (s + 1) * k) = a m ∧
    T (m + 2 ^ (s + 1) * k) = T m + 2 ^ (s - a m + 1) * (3 * k) := by
  -- the key factorisation of `3 m' + 1`
  have hkey : 3 * (m + 2 ^ (s + 1) * k) + 1
      = 2 ^ a m * (T m + 2 ^ (s - a m + 1) * (3 * k)) := by
    have h1 : 3 * m + 1 = 2 ^ a m * T m := three_mul_add_one_eq m
    have h2 : 2 ^ (s + 1) = 2 ^ a m * 2 ^ (s - a m + 1) := by
      rw [← pow_add]
      congr 1
      omega
    calc 3 * (m + 2 ^ (s + 1) * k) + 1
        = (3 * m + 1) + 2 ^ (s + 1) * (3 * k) := by ring
      _ = 2 ^ a m * T m + 2 ^ a m * 2 ^ (s - a m + 1) * (3 * k) := by rw [h1, h2]
      _ = 2 ^ a m * (T m + 2 ^ (s - a m + 1) * (3 * k)) := by ring
  -- the cofactor is odd: odd + even
  have hodd : Odd (T m + 2 ^ (s - a m + 1) * (3 * k)) := by
    have heven : Even (2 ^ (s - a m + 1) * (3 * k)) := by
      rw [pow_succ]
      exact ⟨2 ^ (s - a m) * (3 * k), by ring⟩
    exact (T_odd m).add_even heven
  have hcof_ne : T m + 2 ^ (s - a m + 1) * (3 * k) ≠ 0 := hodd.pos.ne'
  have hnot2 : ¬ 2 ∣ T m + 2 ^ (s - a m + 1) * (3 * k) :=
    Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hodd)
  -- valuation is preserved
  have hval : a (m + 2 ^ (s + 1) * k) = a m := by
    unfold a
    rw [hkey, padicValNat.mul (by positivity) hcof_ne, padicValNat_base_pow (by norm_num),
      padicValNat.eq_zero_of_not_dvd hnot2, add_zero]
    rfl
  -- the image is translated
  have hT : T (m + 2 ^ (s + 1) * k) = T m + 2 ^ (s - a m + 1) * (3 * k) := by
    apply T_eq_of_eq
    rw [hval]
    exact hkey
  exact ⟨hval, hT⟩

/-! ### Orbit bookkeeping -/

/-- Shifting the orbit by one step equals iterating from `T m`. -/
theorem orbit_succ_left (m : ℕ) : ∀ j, orbit m (j + 1) = orbit (T m) j := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih => rw [orbit_succ, ih, orbit_succ]

/-- Prefix sum of the orbit's own valuation word, peeled at the first step. -/
theorem S_orbWord_succ (m t : ℕ) :
    S (fun j => a (orbit m j)) (t + 1) = a m + S (fun j => a (orbit (T m) j)) t := by
  unfold S s
  rw [Finset.sum_range_succ']
  simp only [orbit_zero, orbit_succ_left]
  ring

/-! ### Cylinder restart along the orbit's own valuation word -/

/-- **Cylinder restart (orbit-word form).** With `S_t := ∑_{j<t} a(orbit m j)`, every
`m' = m + 2^(S_t+1) k` has the same first `t` valuations as `m`, and
`orbit m' t = orbit m t + 2 * 3^t * k`. No parity hypothesis is required. -/
theorem orbit_cylinder_restart : ∀ (t m k : ℕ),
    (∀ j < t, a (orbit (m + 2 ^ (S (fun i => a (orbit m i)) t + 1) * k) j) = a (orbit m j)) ∧
    orbit (m + 2 ^ (S (fun i => a (orbit m i)) t + 1) * k) t = orbit m t + 2 * 3 ^ t * k := by
  intro t
  induction t with
  | zero =>
    intro m k
    refine ⟨fun j hj => absurd hj (Nat.not_lt_zero _), ?_⟩
    show m + 2 ^ (S (fun i => a (orbit m i)) 0 + 1) * k = m + 2 * 3 ^ 0 * k
    rw [S, s_zero]
    ring
  | succ t ih =>
    intro m k
    have hsum : S (fun i => a (orbit m i)) (t + 1)
        = a m + S (fun i => a (orbit (T m) i)) t := S_orbWord_succ m t
    rw [hsum]
    have hle : a m ≤ a m + S (fun i => a (orbit (T m) i)) t := Nat.le_add_right _ _
    obtain ⟨hval, hT⟩ := restart_step m k (a m + S (fun i => a (orbit (T m) i)) t) hle
    have hTm' : T (m + 2 ^ (a m + S (fun i => a (orbit (T m) i)) t + 1) * k)
        = T m + 2 ^ (S (fun i => a (orbit (T m) i)) t + 1) * (3 * k) := by
      rw [hT, Nat.add_sub_cancel_left]
    obtain ⟨ihval, ihorb⟩ := ih (T m) (3 * k)
    refine ⟨?_, ?_⟩
    · intro j hj
      cases j with
      | zero =>
        rw [orbit_zero, orbit_zero]
        exact hval
      | succ j =>
        rw [orbit_succ_left, orbit_succ_left, hTm']
        exact ihval j (by omega)
    · rw [orbit_succ_left, orbit_succ_left, hTm', ihorb]
      ring

/-! ### Cylinder restart for realized words (translation-covariant form) -/

/-- **Cylinder restart.** If `m` realizes the length-`t` word `d`, then for every `k : ℕ`
the seed `m + 2^(S d t + 1) * k` also realizes `d`, and its `t`-th iterate is translated
by exactly `2 * 3^t * k`. `k` is arbitrary; there is no upper bound. -/
theorem cylinder_restart (d : ℕ → ℕ) (t m k : ℕ) (h : Realizes d t m) :
    Realizes d t (m + 2 ^ (S d t + 1) * k) ∧
    orbit (m + 2 ^ (S d t + 1) * k) t = orbit m t + 2 * 3 ^ t * k := by
  obtain ⟨hodd, hval⟩ := h
  have hS : S d t = S (fun i => a (orbit m i)) t := by
    unfold S s
    exact Finset.sum_congr rfl (fun i hi => (hval i (Finset.mem_range.mp hi)).symm)
  rw [hS]
  obtain ⟨hv, ho⟩ := orbit_cylinder_restart t m k
  refine ⟨⟨?_, fun j hj => ?_⟩, ho⟩
  · have heven : Even (2 ^ (S (fun i => a (orbit m i)) t + 1) * k) := by
      rw [pow_succ]
      exact ⟨2 ^ (S (fun i => a (orbit m i)) t) * k, by ring⟩
    exact hodd.add_even heven
  · rw [hv j hj]
    exact hval j hj

/-! ### Canonical-class corollary -/

/-- The least realizer realizes its word (for positive words of positive length). -/
theorem leastRealizer_realizes (d : ℕ → ℕ) (t : ℕ) (ht : 1 ≤ t)
    (hd_pos : ∀ i < t, 1 ≤ d i) :
    Realizes d t (leastRealizer d t) :=
  (realizerCongruence d t (leastRealizer d t) (leastRealizer_odd d t ht hd_pos) hd_pos).mpr
    (leastRealizer_modEq d t)

/-- **Cylinder parameterisation.** Every element `leastRealizer d t + 2^(S d t + 1) k` of the
realizer class realizes `d`, with `t`-th iterate translated by `2 * 3^t * k`. -/
theorem cylinder_restart_leastRealizer (d : ℕ → ℕ) (t k : ℕ) (ht : 1 ≤ t)
    (hd_pos : ∀ i < t, 1 ≤ d i) :
    Realizes d t (leastRealizer d t + 2 ^ (S d t + 1) * k) ∧
    orbit (leastRealizer d t + 2 ^ (S d t + 1) * k) t
      = orbit (leastRealizer d t) t + 2 * 3 ^ t * k :=
  cylinder_restart d t (leastRealizer d t) k (leastRealizer_realizes d t ht hd_pos)

end EOC
