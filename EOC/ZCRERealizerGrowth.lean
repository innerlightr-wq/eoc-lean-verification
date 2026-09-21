import EOC.Realizer
import EOC.LiftDigits

/-!
# Bounded prefix realizers versus positive-integer realizability

Companion to `docs/ZCRE_REALIZER_GROWTH_AUDIT.md`. This file settles, with no dependence on the
Curry foundation or on the zero-corridor sector, the exact relationship between two notions for
a valuation word `d : ℕ → ℕ` with every digit `≥ 1`:

* **bounded prefix realizers**: `∃ M, ∀ N, leastRealizer d N ≤ M`;
* **positive-integer realizable**: `∃ m0, Odd m0 ∧ ∀ i, a (orbit m0 i) = d i`.

**Main result:** these are *equivalent* (`boundedPrefixRealizers_iff_positiveRealizer`), and
moreover a bounded prefix-realizer sequence is not merely bounded but **eventually constant**
(`leastRealizer_eventually_constant_of_bounded`), stabilizing exactly at the realizing seed.

This is the fact the audit report calls "UPR ⟺ ZCRE": the *Unbounded Prefix Realizer* property
asked about in that audit is not a new, independently attackable condition — for a specific
word `W`, "`W`'s prefix realizers are unbounded" and "`W` has no positive-integer realizer" are
literally the same statement. Both directions are proved here directly from the repository's
existing `leastRealizer`/`realizerCongruence` machinery (`EOC/Realizer.lean`) and the existing
`S_mono` (`EOC/LiftDigits.lean`); no new hypothesis or external interface is introduced, and
nothing here is specific to the Curry sector.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace ZCRERealizerGrowth

/-! ## Direction 1: a realizer of the prefix is never far from the true seed -/

/-- **Fixed-seed prefix lemma.** If `m0` (odd) realizes `d` up to `N`, the least prefix
realizer is exactly `m0 % 2^(S_N+1)` — in particular it never exceeds `m0`. -/
theorem leastRealizer_eq_mod_of_realizes (d : ℕ → ℕ) (N m0 : ℕ) (hd_pos : ∀ i < N, 1 ≤ d i)
    (hreal : Realizes d N m0) :
    leastRealizer d N = m0 % 2 ^ (S d N + 1) := by
  have hm0 : Odd m0 := hreal.1
  have hcong := (realizerCongruence d N m0 hm0 hd_pos).mp hreal
  have hmodlt : m0 % 2 ^ (S d N + 1) < 2 ^ (S d N + 1) := Nat.mod_lt _ (by positivity)
  have hmodcong : 3 ^ N * (m0 % 2 ^ (S d N + 1)) + q d N ≡ 2 ^ S d N [MOD 2 ^ (S d N + 1)] := by
    calc 3 ^ N * (m0 % 2 ^ (S d N + 1)) + q d N
        ≡ 3 ^ N * m0 + q d N [MOD 2 ^ (S d N + 1)] :=
          Nat.ModEq.add_right _ (Nat.ModEq.mul_left _ (Nat.mod_modEq m0 _))
      _ ≡ 2 ^ S d N [MOD 2 ^ (S d N + 1)] := hcong
  exact (leastRealizer_unique d N (m0 % 2 ^ (S d N + 1)) hmodlt hmodcong).symm

/-- **Fixed-seed prefix lemma, inequality form.** The least prefix realizer never exceeds a
seed that actually realizes the prefix — proved for *every* prefix length, unconditionally. -/
theorem leastRealizer_le_of_realizes (d : ℕ → ℕ) (N m0 : ℕ) (hd_pos : ∀ i < N, 1 ≤ d i)
    (hreal : Realizes d N m0) :
    leastRealizer d N ≤ m0 := by
  rw [leastRealizer_eq_mod_of_realizes d N m0 hd_pos hreal]
  exact Nat.mod_le m0 _

/-! ## Direction 2: bounded prefix realizers force a fixed positive-integer realizer -/

private theorem le_S_of_digits_pos (d : ℕ → ℕ) (hd_pos : ∀ i, 1 ≤ d i) (n : ℕ) : n ≤ S d n := by
  induction n with
  | zero => simp [S, s_zero]
  | succ n ih =>
    have hstep : S d (n + 1) = S d n + d n := s_succ d n
    have := hd_pos n
    omega

private theorem exists_modulus_gt (d : ℕ → ℕ) (hd_pos : ∀ i, 1 ≤ d i) (M : ℕ) :
    ∃ N0, M < 2 ^ (S d N0 + 1) := by
  obtain ⟨N0, hN0⟩ := pow_unbounded_of_one_lt M (by norm_num : (1 : ℕ) < 2)
  exact ⟨N0, lt_of_lt_of_le hN0
    (Nat.pow_le_pow_right (by norm_num) (by have := le_S_of_digits_pos d hd_pos N0; omega))⟩

/-- **Stabilization step.** Past a modulus large enough to dominate the bound `M`, extending
the prefix by one more digit cannot change the least realizer. -/
private theorem leastRealizer_stable_step (d : ℕ → ℕ) (hd_pos : ∀ i, 1 ≤ d i) (M N : ℕ)
    (hbdd : ∀ N, leastRealizer d N ≤ M) (hmod : M < 2 ^ (S d N + 1)) :
    leastRealizer d (N + 1) = leastRealizer d N := by
  have hd_pos' : ∀ i < N + 1, 1 ≤ d i := fun i _ => hd_pos i
  have hodd_succ : Odd (leastRealizer d (N + 1)) :=
    leastRealizer_odd d (N + 1) (by omega) hd_pos'
  have hreal_succ : Realizes d (N + 1) (leastRealizer d (N + 1)) :=
    (realizerCongruence d (N + 1) (leastRealizer d (N + 1)) hodd_succ hd_pos').mpr
      (leastRealizer_modEq d (N + 1))
  have hreal_N : Realizes d N (leastRealizer d (N + 1)) :=
    ⟨hodd_succ, fun i hi => hreal_succ.2 i (by omega)⟩
  have hlt : leastRealizer d (N + 1) < 2 ^ (S d N + 1) :=
    lt_of_le_of_lt (hbdd (N + 1)) hmod
  have hd_pos'' : ∀ i < N, 1 ≤ d i := fun i _ => hd_pos i
  have hcong := (realizerCongruence d N (leastRealizer d (N + 1)) hodd_succ hd_pos'').mp hreal_N
  exact leastRealizer_unique d N (leastRealizer d (N + 1)) hlt hcong

/-- **Eventual constancy.** If the least prefix realizers of an everywhere-positive-digit word
are bounded by `M`, they are eventually constant. -/
theorem leastRealizer_eventually_constant_of_bounded (d : ℕ → ℕ) (hd_pos : ∀ i, 1 ≤ d i)
    (M : ℕ) (hbdd : ∀ N, leastRealizer d N ≤ M) :
    ∃ N0, ∀ N ≥ N0, leastRealizer d N = leastRealizer d N0 := by
  obtain ⟨N0, hN0⟩ := exists_modulus_gt d hd_pos M
  have hmod_grows : ∀ N ≥ N0, M < 2 ^ (S d N + 1) := by
    intro N hN
    have hSmono : S d N0 ≤ S d N := LiftDigits.S_mono d hN
    exact lt_of_lt_of_le hN0 (Nat.pow_le_pow_right (by norm_num) (by omega))
  refine ⟨N0, fun N hN => ?_⟩
  induction N, hN using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [leastRealizer_stable_step d hd_pos M n hbdd (hmod_grows n hn), ih]

/-- **Positive-integer realizer, extracted.** If the least prefix realizers of an
everywhere-positive-digit word are bounded, some fixed positive odd integer realizes the
*entire* infinite word. -/
theorem exists_positiveRealizer_of_bounded (d : ℕ → ℕ) (hd_pos : ∀ i, 1 ≤ d i)
    (M : ℕ) (hbdd : ∀ N, leastRealizer d N ≤ M) :
    ∃ m0, Odd m0 ∧ ∀ i, a (orbit m0 i) = d i := by
  obtain ⟨N0, hN0⟩ := leastRealizer_eventually_constant_of_bounded d hd_pos M hbdd
  set N1 : ℕ := max N0 1 with hN1def
  have hN0N1 : N0 ≤ N1 := le_max_left _ _
  have hN11 : 1 ≤ N1 := le_max_right _ _
  have hstab1 : leastRealizer d N1 = leastRealizer d N0 := hN0 N1 hN0N1
  have hd_pos1 : ∀ j < N1, 1 ≤ d j := fun j _ => hd_pos j
  have hodd1 : Odd (leastRealizer d N1) := leastRealizer_odd d N1 hN11 hd_pos1
  refine ⟨leastRealizer d N1, hodd1, fun i => ?_⟩
  set N := max N1 (i + 1) with hNdef
  have hNN1 : N1 ≤ N := le_max_left _ _
  have hiN : i < N := lt_of_lt_of_le (Nat.lt_succ_self i) (le_max_right N1 (i + 1))
  have hstab : leastRealizer d N = leastRealizer d N1 := by
    rw [hN0 N (le_trans hN0N1 hNN1), hstab1]
  have hd_pos' : ∀ j < N, 1 ≤ d j := fun j _ => hd_pos j
  have hodd : Odd (leastRealizer d N) := leastRealizer_odd d N (by omega) hd_pos'
  have hreal : Realizes d N (leastRealizer d N) :=
    (realizerCongruence d N (leastRealizer d N) hodd hd_pos').mpr (leastRealizer_modEq d N)
  have := hreal.2 i hiN
  rwa [hstab] at this

/-! ## The equivalence -/

/-- **UPR ⟺ ZCRE, made precise.** For an everywhere-positive-digit valuation word, bounded
prefix realizers and positive-integer realizability are the same statement. Consequently, its
contrapositive — *unbounded* prefix realizers (`∀ M, ∃ N, leastRealizer d N > M`) — is not a
new, independently weaker sufficient condition for excluding a Type-II orbit's word: it is a
restatement of non-realizability. -/
theorem boundedPrefixRealizers_iff_positiveRealizer (d : ℕ → ℕ) (hd_pos : ∀ i, 1 ≤ d i) :
    (∃ M, ∀ N, leastRealizer d N ≤ M) ↔ (∃ m0, Odd m0 ∧ ∀ i, a (orbit m0 i) = d i) := by
  constructor
  · rintro ⟨M, hM⟩
    exact exists_positiveRealizer_of_bounded d hd_pos M hM
  · rintro ⟨m0, hm0, hreal⟩
    exact ⟨m0, fun N => leastRealizer_le_of_realizes d N m0 (fun i _ => hd_pos i)
      ⟨hm0, fun i hi => hreal i⟩⟩

end ZCRERealizerGrowth
end EOC
