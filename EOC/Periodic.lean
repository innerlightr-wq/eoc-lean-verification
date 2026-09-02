import EOC.Confinement
import EOC.PeriodicCore
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# EOC/Periodic.lean — Bridge: periodic-sector realizer escape

`PeriodicCore.lean` contains the kernel-checked arithmetic core.
This file bridges that core to the EOC repository definitions.
-/

namespace EOC
open PeriodicCore

/-! ### Transport: repository `s`/`q` agree with the core `sr`/`qr` -/

theorem s_eq_sr (d : ℕ → ℕ) : ∀ j, s d j = sr d j := by
  intro j
  induction j with
  | zero => simp
  | succ n ih => rw [s_succ, sr_succ, ih]

theorem q_eq_qr (d : ℕ → ℕ) : ∀ j, q d j = qr d j := by
  intro j
  induction j with
  | zero => rfl
  | succ n ih => rw [q_succ, qr_succ, ih, s_eq_sr]

/-! ### Orbit shift and the exact block identity along an actual orbit -/

theorem orbit_add (m0 j : ℕ) :
    ∀ i, orbit m0 (j + i) = orbit (orbit m0 j) i := by
  intro i
  induction i with
  | zero => rfl
  | succ n ih =>
      rw [
        show j + (n + 1) = (j + n) + 1 from by omega,
        orbit_succ,
        ih,
        orbit_succ
      ]

theorem two_pow_a_dvd (m : ℕ) : 2 ^ a m ∣ 3 * m + 1 :=
  pow_padicValNat_dvd

/--
Exact block identity: for the actual orbit of `m0` and the window word
starting at `j`,

`2^{S_B} * m_{j+L} = 3^L * m_j + C_B`.

This is `iter_carry_eq` applied to the shifted orbit.
-/
theorem orbit_block_identity (m0 j L : ℕ) :
    2 ^ s (fun i => a (orbit m0 (j + i))) L * orbit m0 (j + L)
      =
    3 ^ L * orbit m0 j
      + q (fun i => a (orbit m0 (j + i))) L := by
  set w : ℕ → ℕ := fun i => a (orbit m0 (j + i)) with hw

  have hval :
      ∀ i < L, a (orbit (orbit m0 j) i) = w i := by
    intro i _
    simp [hw, orbit_add]

  have hiter :
      ∀ i, i ≤ L →
        orbit (orbit m0 j) i = iter w (orbit m0 j) i :=
    orbit_eq_iter_of_orbit_valuation w L (orbit m0 j) hval

  have hdvd :
      ∀ i < L,
        2 ^ w i ∣ (3 * iter w (orbit m0 j) i + 1) := by
    intro i hi
    rw [← hiter i (le_of_lt hi), hw]
    simpa [orbit_add] using two_pow_a_dvd (orbit m0 (j + i))

  have h :=
    iter_carry_eq w (orbit m0 j) L hdvd L (le_refl L)

  rw [← hiter L (le_refl L), ← orbit_add] at h
  exact h

/-!
### Theorem A, arithmetic part

For a positive integer orbit with an eventually periodic valuation block,
the repeated block satisfies `3^L < 2^{S_B}`.
-/

theorem three_pow_lt_two_pow_of_evPeriodic_orbit
    (m0 j0 L : ℕ)
    (hm0 : Odd m0)
    (hL : 1 ≤ L)
    (hper : EvPeriodic (fun i => a (orbit m0 i)) j0 L) :
    3 ^ L <
      2 ^ blockSum (fun i => a (orbit m0 i)) j0 L := by

  set d : ℕ → ℕ := fun i => a (orbit m0 i) with hd

  have hdpos : ∀ i, 1 ≤ d i :=
    hd_pos_of_orbit hm0

  refine
    three_pow_lt_two_pow_of_block_return
      L
      (blockSum d j0 L)
      (blockCarry d j0 L)
      (fun r => orbit m0 (j0 + r * L))
      ?hS
      ?hC
      ?hrec

  · exact le_trans hL (sr_ge_of_pos _ L (fun i _ => hdpos _))

  · exact qr_pos _ L hL

  · intro r

    have hid :=
      orbit_block_identity m0 (j0 + r * L) L

    have hshift :=
      block_shift_invariant d j0 L hper r L (le_refl L)

    rw [s_eq_sr, q_eq_qr] at hid

    have hs' :
        sr (fun i => a (orbit m0 (j0 + r * L + i))) L
          =
        blockSum d j0 L :=
      hshift.2

    have hq' :
        qr (fun i => a (orbit m0 (j0 + r * L + i))) L
          =
        blockCarry d j0 L :=
      hshift.1

    rw [hs', hq'] at hid

    rw [
      show
        j0 + (r + 1) * L =
          j0 + r * L + L
      from by ring
    ]

    exact hid

/-! ### Real drift: `3^L < 2^S` gives `alpha * L < S` -/

theorem alpha_mul_lt_of_pow_lt
    (L S : ℕ)
    (h : 3 ^ L < 2 ^ S) :
    alpha * L < S := by

  unfold alpha

  have h3 : (0 : ℝ) < 3 ^ L := by
    positivity

  have hcast :
      ((3 : ℝ) ^ L) < (2 : ℝ) ^ S := by
    exact_mod_cast h

  have hlt :=
    Real.logb_lt_logb
      (by norm_num : (1 : ℝ) < 2)
      h3
      hcast

  rw [
    Real.logb_pow,
    Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)
  ] at hlt

  simpa [mul_comm] using hlt

theorem R_periodic
    (d : ℕ → ℕ)
    (j0 L : ℕ)
    (hper : EvPeriodic d j0 L)
    (k : ℕ) :
    R d (j0 + k * L)
      =
    R d j0
      + (k : ℝ)
        * ((blockSum d j0 L : ℝ) - alpha * L) := by

  unfold R
  rw [s_eq_sr, s_eq_sr, sr_periodic d j0 L hper k]
  push_cast
  ring

/--
**Theorem A.**
A positive integer whose valuation word is eventually periodic is not
`c`-confined forever, for any real `c`.

The sign-sensitive input is the positivity of the repeated block carry.
-/
theorem not_confined_forever_of_evPeriodic_orbit
    (c : ℝ)
    (m0 j0 L : ℕ)
    (hm0 : Odd m0)
    (hL : 1 ≤ L)
    (hper : EvPeriodic (fun i => a (orbit m0 i)) j0 L) :
    ∃ N, ¬ Confined c (fun i => a (orbit m0 i)) N := by

  set d : ℕ → ℕ := fun i => a (orbit m0 i) with hd

  have hgrow :=
    three_pow_lt_two_pow_of_evPeriodic_orbit
      m0 j0 L hm0 hL hper

  have hΔ :
      0 <
        (blockSum d j0 L : ℝ)
          - alpha * L := by
    have hlt :=
      alpha_mul_lt_of_pow_lt
        L
        (blockSum d j0 L)
        hgrow
    linarith

  obtain ⟨k, hk⟩ :=
    exists_nat_gt
      ((c - R d j0) /
        ((blockSum d j0 L : ℝ) - alpha * L))

  refine ⟨j0 + k * L, fun hconf => ?_⟩

  have hR :=
    hconf (j0 + k * L) (le_refl _)

  rw [R_periodic d j0 L hper k] at hR

  have hmul :
      c - R d j0
        <
      (k : ℝ)
        * ((blockSum d j0 L : ℝ) - alpha * L) := by

    have hk' :=
      (div_lt_iff₀ hΔ).mp hk

    simpa [mul_comm] using hk'

  linarith [hR, hmul]

/-!
### Theorem A′ — abstract words

Confined + eventually periodic implies realizer escape.

The proof is by contrapositive through the integer theorem: a bounded
nondecreasing realizer sequence freezes at an integer realizing every
prefix. Its valuation word is then exactly `d`.
-/

theorem realizes_all_of_leastRealizer_const
    (d : ℕ → ℕ)
    (hd : ∀ i, 1 ≤ d i)
    (N0 : ℕ)
    (hN0 : 1 ≤ N0)
    (m : ℕ)
    (hconst : ∀ N, N0 ≤ N → leastRealizer d N = m) :
    ∀ j, a (orbit m j) = d j := by

  intro j

  have hN :
      N0 ≤ max N0 (j + 1) :=
    le_max_left _ _

  have hj :
      j < max N0 (j + 1) :=
    lt_of_lt_of_le
      (Nat.lt_succ_self j)
      (le_max_right _ _)

  have hodd : Odd m := by
    rw [← hconst N0 (le_refl _)]
    exact
      leastRealizer_odd
        d
        N0
        hN0
        (fun i _ => hd i)

  have hmod :=
    leastRealizer_modEq
      d
      (max N0 (j + 1))

  rw [hconst _ hN] at hmod

  have hreal :=
    (realizerCongruence
      d
      (max N0 (j + 1))
      m
      hodd
      (fun i _ => hd i)).2 hmod

  exact hreal.2 j hj

theorem leastRealizer_unbounded_of_confined_evPeriodic
    (c : ℝ)
    (d : ℕ → ℕ)
    (j0 L : ℕ)
    (hd : ∀ i, 1 ≤ d i)
    (hL : 1 ≤ L)
    (hper : EvPeriodic d j0 L)
    (hconf : ∀ N, Confined c d N) :
    ∀ M, ∃ N, M < leastRealizer d N := by

  intro M
  by_contra hno
  push_neg at hno

  have hmono :
      ∀ N,
        leastRealizer d N
          ≤ leastRealizer d (N + 1) :=
    fun N =>
      leastRealizer_mono
        d
        N
        (fun i _ => hd i)

  obtain ⟨N0, hN0⟩ :=
    eventually_const_of_mono_bounded
      (leastRealizer d)
      hmono
      M
      hno

  set N1 := max N0 1 with hN1

  have hconst :
      ∀ N,
        N1 ≤ N →
        leastRealizer d N =
          leastRealizer d N1 := by

    intro N hN

    rw [
      hN0 N
        (le_trans (le_max_left _ _) hN),
      hN0 N1
        (le_max_left _ _)
    ]

  have hword :=
    realizes_all_of_leastRealizer_const
      d
      hd
      N1
      (le_max_right _ _)
      _
      hconst

  have hper' :
      EvPeriodic
        (fun i =>
          a (orbit (leastRealizer d N1) i))
        j0
        L := by

    intro i hi
    simp only [hword]
    exact hper i hi

  have hodd :
      Odd (leastRealizer d N1) :=
    leastRealizer_odd
      d
      N1
      (le_max_right _ _)
      (fun i _ => hd i)

  obtain ⟨N, hN⟩ :=
    not_confined_forever_of_evPeriodic_orbit
      c
      _
      j0
      L
      hodd
      hL
      hper'

  apply hN

  intro j hj

  have hjconf :=
    hconf N j hj

  simpa [hword] using hjconf

/-- Corollary: infinitely many positive lifts. -/
theorem infinitely_many_positive_lifts_of_confined_evPeriodic
    (c : ℝ)
    (d : ℕ → ℕ)
    (j0 L : ℕ)
    (hd : ∀ i, 1 ≤ d i)
    (hL : 1 ≤ L)
    (hper : EvPeriodic d j0 L)
    (hconf : ∀ N, Confined c d N) :
    ∀ N0,
      ∃ N,
        N0 ≤ N
          ∧ leastRealizer d N
              < leastRealizer d (N + 1) := by

  intro N0
  by_contra hno
  push_neg at hno

  have hconst :
      ∀ N,
        N0 ≤ N →
        leastRealizer d N =
          leastRealizer d N0 := by

    intro N hN

    induction N with
    | zero =>
        have hz : N0 = 0 := by
          omega
        rw [hz]

    | succ n ih =>
        rcases Nat.lt_or_ge n N0 with h | h

        · have hs : N0 = n + 1 := by
            omega
          rw [hs]

        · have h1 :=
            hno n h

          have h2 :=
            leastRealizer_mono
              d
              n
              (fun i _ => hd i)

          have hi :=
            ih h

          omega

  obtain ⟨N, hN⟩ :=
    leastRealizer_unbounded_of_confined_evPeriodic
      c
      d
      j0
      L
      hd
      hL
      hper
      hconf
      (leastRealizer d N0)

  have hbig :=
    hconst
      (max N N0)
      (le_max_right _ _)

  have hmono :=
    mono_of_step
      (leastRealizer d)
      (fun N =>
        leastRealizer_mono
          d
          N
          (fun i _ => hd i))

  have hle :=
    hmono
      N
      (max N N0)
      (le_max_left _ _)

  omega

end EOC
