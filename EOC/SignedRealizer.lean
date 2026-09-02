import EOC.Confinement
import EOC.SignedBlock

/-!
# EOC/SignedRealizer.lean

Plus/minus realizer complement and the joint valuation theorem.

This file uses the public `leastRealizer` API from `EOC.Realizer` and
re-proves the small residue-class existence/uniqueness infrastructure
needed for the minus realizer.
-/

namespace EOC

/-! ### Solutions of `2^M ∣ 3^N x + A` below the modulus -/

/-- `3^N` is odd for every `N`. -/
private theorem odd_three_pow_signed (N : ℕ) : Odd (3 ^ N) := by
  induction N with
  | zero =>
      exact ⟨0, by norm_num⟩
  | succ N ih =>
      obtain ⟨w, hw⟩ := ih
      exact ⟨3 * w + 1, by rw [pow_succ, hw]; ring⟩

/--
Existence of a representative below `2^M` solving
`2^M ∣ 3^N x + A`.

This is the same Hensel-style induction used in `EOC.Realizer`.
-/
theorem exists_lt_dvd' (N M A : ℕ) :
    ∃ x, x < 2 ^ M ∧ 2 ^ M ∣ 3 ^ N * x + A := by
  induction M with
  | zero =>
      exact ⟨0, by norm_num, by simp⟩
  | succ M ih =>
      obtain ⟨x, hxlt, hdvd⟩ := ih
      obtain ⟨c, hc⟩ := hdvd
      have hpow : (2 : ℕ) ^ (M + 1) = 2 ^ M + 2 ^ M := by
        rw [pow_succ]
        ring
      rcases Nat.even_or_odd c with ⟨c', hc'⟩ | hcodd
      · have hc2 : c = 2 * c' := by
          rw [hc']
          ring
        refine ⟨x, by omega, ?_⟩
        refine ⟨c', ?_⟩
        rw [hc, hc2, pow_succ]
        ring
      · obtain ⟨w, hw⟩ := hcodd
        obtain ⟨w3, hw3⟩ := odd_three_pow_signed N
        refine ⟨x + 2 ^ M, by omega, ?_⟩
        refine ⟨w + w3 + 1, ?_⟩
        have step1 :
            3 ^ N * (x + 2 ^ M) + A =
              (3 ^ N * x + A) + 3 ^ N * 2 ^ M := by
          ring
        rw [step1, hc, hw, hw3, pow_succ]
        ring

/-- Uniqueness of a solution below the modulus. -/
theorem unique_lt_dvd
    (N M A x y : ℕ)
    (hx : x < 2 ^ M)
    (hy : y < 2 ^ M)
    (hxd : 2 ^ M ∣ 3 ^ N * x + A)
    (hyd : 2 ^ M ∣ 3 ^ N * y + A) :
    x = y := by
  have hcop : Nat.Coprime (2 ^ M) (3 ^ N) :=
    Nat.Coprime.pow M N (by decide)
  have hmod : 3 ^ N * x ≡ 3 ^ N * y [MOD 2 ^ M] :=
    Nat.ModEq.add_right_cancel' A
      ((Nat.modEq_zero_iff_dvd.2 hxd).trans
        (Nat.modEq_zero_iff_dvd.2 hyd).symm)
  have hxy : x ≡ y [MOD 2 ^ M] :=
    Nat.ModEq.cancel_left_of_coprime hcop hmod
  exact Nat.ModEq.eq_of_lt_of_lt hxy hx hy

/-! ### The minus realizer -/

/--
The minus congruence

`3^N x - q ≡ 2^S (mod 2^{S+1})`

written additively as

`2^{S+1} ∣ 3^N x + (2^{S+1}-1)(q+2^S)`.
-/
def minusTarget (d : ℕ → ℕ) (N : ℕ) : ℕ :=
  (2 ^ (S d N + 1) - 1) * (q d N + 2 ^ S d N)

/-- Least representative of the minus congruence. -/
noncomputable def leastRealizerMinus (d : ℕ → ℕ) (N : ℕ) : ℕ :=
  Nat.find (exists_lt_dvd' N (S d N + 1) (minusTarget d N))

theorem leastRealizerMinus_lt (d : ℕ → ℕ) (N : ℕ) :
    leastRealizerMinus d N < 2 ^ (S d N + 1) :=
  (Nat.find_spec
    (exists_lt_dvd' N (S d N + 1) (minusTarget d N))).1

theorem leastRealizerMinus_dvd (d : ℕ → ℕ) (N : ℕ) :
    2 ^ (S d N + 1) ∣
      3 ^ N * leastRealizerMinus d N + minusTarget d N :=
  (Nat.find_spec
    (exists_lt_dvd' N (S d N + 1) (minusTarget d N))).2

/--
**Complement identity.**

For a nonempty positive valuation word,

`r₊(D) + r₋(D) = 2^{S_N+1}`.

Equivalently, the two representatives are negatives of one another
modulo `2^{S_N+1}`.
-/
theorem realizer_complement
    (d : ℕ → ℕ)
    (N : ℕ)
    (hN : 1 ≤ N)
    (hd : ∀ i < N, 1 ≤ d i) :
    leastRealizer d N + leastRealizerMinus d N =
      2 ^ (S d N + 1) := by
  set M := 2 ^ (S d N + 1) with hM

  have hr_lt := leastRealizer_lt d N
  have hr_pos : 1 ≤ leastRealizer d N :=
    (leastRealizer_odd d N hN hd).pos
  have hr_dvd := leastRealizer_dvd d N

  have hx0_lt : M - leastRealizer d N < M := by
    omega

  have hx0_dvd :
      M ∣
        3 ^ N * (M - leastRealizer d N) +
          minusTarget d N := by

    have hsum :
        3 ^ N * (M - leastRealizer d N) +
            minusTarget d N +
            (3 ^ N * leastRealizer d N +
              (q d N + 2 ^ S d N))
          =
        M * (3 ^ N + (q d N + 2 ^ S d N)) := by

      unfold minusTarget
      rw [← hM, Nat.mul_sub, Nat.sub_mul, one_mul]

      have h1 :
          3 ^ N * leastRealizer d N ≤ 3 ^ N * M :=
        Nat.mul_le_mul_left _ (le_of_lt hr_lt)

      have h2 :
          q d N + 2 ^ S d N ≤
            M * (q d N + 2 ^ S d N) :=
        Nat.le_mul_of_pos_left _ (by positivity)

      zify [h1, h2]
      ring

    have htotal :
        M ∣
          3 ^ N * (M - leastRealizer d N) +
              minusTarget d N +
              (3 ^ N * leastRealizer d N +
                (q d N + 2 ^ S d N)) := by
      rw [hsum]
      exact dvd_mul_right _ _

    exact (Nat.dvd_add_left hr_dvd).1 htotal

  have huniq :=
    unique_lt_dvd
      N
      (S d N + 1)
      (minusTarget d N)
      (leastRealizerMinus d N)
      (M - leastRealizer d N)
      (leastRealizerMinus_lt d N)
      hx0_lt
      (leastRealizerMinus_dvd d N)
      hx0_dvd

  omega

/--
No nonempty positive valuation word has the same representative in
both signs.
-/
theorem realizer_plus_ne_minus
    (d : ℕ → ℕ)
    (N : ℕ)
    (hN : 1 ≤ N)
    (hd : ∀ i < N, 1 ≤ d i) :
    leastRealizer d N ≠ leastRealizerMinus d N := by

  intro heq

  have hsum := realizer_complement d N hN hd
  have hodd := leastRealizer_odd d N hN hd

  have hdouble :
      2 * leastRealizer d N = 2 * 2 ^ S d N := by
    rw [heq] at hsum
    rw [pow_succ] at hsum
    omega

  have h2 :
      leastRealizer d N = 2 ^ S d N := by
    omega

  have hlast : 1 ≤ d (N - 1) := by
    apply hd
    omega

  have hS : 1 ≤ S d N := by
    unfold S
    rw [show N = (N - 1) + 1 from by omega, s_succ]
    omega

  have heven : Even (leastRealizer d N) := by
    rw [h2]
    exact Nat.even_pow.2 ⟨even_two, by omega⟩

  exact (Nat.not_even_iff_odd.2 hodd) heven

/-! ### Joint valuation theorem -/

/-- `v₂(3m - 1)`, the valuation driving `T₋`. -/
noncomputable def am (m : ℕ) : ℕ :=
  padicValNat 2 (3 * m - 1)

/--
If `m ≡ 3 (mod 4)`, then `v₂(3m+1)=1`.
-/
theorem plus_val_eq_one_of_mod_four_eq_three
    (m : ℕ)
    (hm : m % 4 = 3) :
    a m = 1 := by

  have hodd : Odd m := by
    rw [Nat.odd_iff]
    omega

  have h1 : 1 ≤ a m :=
    a_pos_of_odd hodd

  have hne : 3 * m + 1 ≠ 0 := by
    omega

  apply le_antisymm _ h1

  by_contra h

  have h2 : 2 ≤ a m := by
    omega

  have hdvd :
      2 ^ 2 ∣ 3 * m + 1 :=
    (padicValNat_dvd_iff_le hne).2 h2

  omega

/--
If `m ≡ 3 (mod 4)`, then `v₂(3m-1) ≥ 2`.
-/
theorem minus_val_ge_two_of_mod_four_eq_three
    (m : ℕ)
    (hm : m % 4 = 3) :
    2 ≤ am m := by

  have hne : 3 * m - 1 ≠ 0 := by
    omega

  have hmdecomp := Nat.mod_add_div m 4

  have hdvd4 : 4 ∣ 3 * m - 1 := by
    refine ⟨3 * (m / 4) + 2, ?_⟩
    omega

  have hdvd22 : 2 ^ 2 ∣ 3 * m - 1 := by
    simpa using hdvd4

  unfold am
  exact (padicValNat_dvd_iff_le hne).1 hdvd22

/--
If `m ≡ 1 (mod 4)`, then `v₂(3m-1)=1`.
-/
theorem minus_val_eq_one_of_mod_four_eq_one
    (m : ℕ)
    (hm : m % 4 = 1) :
    am m = 1 := by

  have hne : 3 * m - 1 ≠ 0 := by
    omega

  have hmdecomp := Nat.mod_add_div m 4

  have hdvd2 : 2 ∣ 3 * m - 1 := by
    refine ⟨6 * (m / 4) + 1, ?_⟩
    omega

  have hdvd21 : 2 ^ 1 ∣ 3 * m - 1 := by
    simpa using hdvd2

  have h1 : 1 ≤ am m := by
    unfold am
    exact (padicValNat_dvd_iff_le hne).1 hdvd21

  apply le_antisymm _ h1

  by_contra h

  have h2 : 2 ≤ am m := by
    omega

  have hdvd4 :
      2 ^ 2 ∣ 3 * m - 1 :=
    (padicValNat_dvd_iff_le hne).2 h2

  obtain ⟨k, hk⟩ := hdvd4

  norm_num at hk

  omega

/--
If `m ≡ 1 (mod 4)`, then `v₂(3m+1) ≥ 2`.
-/
theorem plus_val_ge_two_of_mod_four_eq_one
    (m : ℕ)
    (hm : m % 4 = 1) :
    2 ≤ a m := by

  have hne : 3 * m + 1 ≠ 0 := by
    omega

  have hmdecomp := Nat.mod_add_div m 4

  have hdvd4 : 4 ∣ 3 * m + 1 := by
    refine ⟨3 * (m / 4) + 1, ?_⟩
    omega

  have hdvd22 : 2 ^ 2 ∣ 3 * m + 1 := by
    simpa using hdvd4

  unfold a
  exact (padicValNat_dvd_iff_le hne).1 hdvd22

/--
**Joint valuation theorem.**

For every odd `m`,

`min (v₂(3m+1)) (v₂(3m-1)) = 1`.
-/
theorem joint_val_two_min
    (m : ℕ)
    (hm : Odd m) :
    min (a m) (am m) = 1 := by

  have h4 :
      m % 4 = 1 ∨ m % 4 = 3 := by
    rw [Nat.odd_iff] at hm
    omega

  rcases h4 with h | h

  · rw [minus_val_eq_one_of_mod_four_eq_one m h]
    have hplus :=
      plus_val_ge_two_of_mod_four_eq_one m h
    omega

  · rw [plus_val_eq_one_of_mod_four_eq_three m h]
    have hminus :=
      minus_val_ge_two_of_mod_four_eq_three m h
    omega

end EOC
