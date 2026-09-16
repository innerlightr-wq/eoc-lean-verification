import EOC.LiftDigits

/-!
# The lift gap: a cheap word's least realizer stabilizes

`LiftDigits.leastRealizer_succ` gives `r_{j+1} = r_j + 2^(S_j+1)·τ_j`, so a single nonzero lift
digit costs a
full `2^(S_j+1)`.  Consequently a word whose *final* least realizer is small cannot lift at all once
the
modulus exceeds that bound:

* `leastRealizer_mono` — prefix least realizers are nondecreasing.
* `liftDigit_eq_zero_of_gap` — if `r_N ≤ B < 2^(S_j+1)` and `j < N` then `τ_j = 0`.
* `leastRealizer_eq_of_gap` — hence `r_j = r_N` for every such `j`: the representative
**stabilizes**, i.e.
  the tail of the word is the orbit word of the single integer `r_N` ("prefix locking", now for
  arbitrary
  admissible words rather than for a seed's own word).

This is the engine behind the record-frontier identity `r_min(N,c) = min{m : L_c(m) ≥ N}`: searching
cheap
words is the same as searching small seeds.  It carries no information beyond that identity — see
`scratch/cheap_2026-09-16/REPORT.md`.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace LiftGap

open LiftDigits

variable {d : ℕ → ℕ}

theorem S_mono {j N : ℕ} (hj : j ≤ N) : S d j ≤ S d N := by
  induction N with
  | zero =>
    have : j = 0 := by omega
    rw [this]
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hj with rfl | h
    · exact le_rfl
    · exact le_trans (ih (by omega)) (by rw [S_succ' d n]; omega)

/-- Prefix least realizers are nondecreasing. -/
theorem leastRealizer_mono {j N : ℕ} (hd : ∀ i < N, 1 ≤ d i) (hj : j ≤ N) :
    leastRealizer d j ≤ leastRealizer d N := by
  have h := leastRealizer_mod hd hj
  rw [← h]
  exact Nat.mod_le _ _

/-- **Lift gap.**  If the final least realizer is at most `B` and the modulus at step `j` already
exceeds `B`,
the lift digit at `j` vanishes. -/
theorem liftDigit_eq_zero_of_gap {N j B : ℕ} (hd : ∀ i < N, 1 ≤ d i)
    (hB : leastRealizer d N ≤ B) (hj : j < N) (hgap : B < 2 ^ (S d j + 1)) :
    liftDigit d j = 0 := by
  by_contra h
  have h1 : 1 ≤ liftDigit d j := Nat.one_le_iff_ne_zero.mpr h
  have hsucc : leastRealizer d (j + 1) = leastRealizer d j + 2 ^ (S d j + 1) * liftDigit d j :=
    leastRealizer_succ (fun i hi => hd i (by omega))
  have hge : 2 ^ (S d j + 1) ≤ leastRealizer d (j + 1) := by
    have : 2 ^ (S d j + 1) * 1 ≤ 2 ^ (S d j + 1) * liftDigit d j :=
      Nat.mul_le_mul_left _ h1
    omega
  have hle : leastRealizer d (j + 1) ≤ leastRealizer d N := leastRealizer_mono hd (by omega)
  omega

/-- **Stabilization.**  With the same hypotheses, every prefix from `j` on has the *same* least
realizer. -/
theorem leastRealizer_eq_of_gap {N j B : ℕ} (hd : ∀ i < N, 1 ≤ d i)
    (hB : leastRealizer d N ≤ B) (hgap : B < 2 ^ (S d j + 1)) (hj : j ≤ N) :
    leastRealizer d j = leastRealizer d N := by
  induction N with
  | zero =>
    have : j = 0 := by omega
    rw [this]
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hj with rfl | hlt
    · rfl
    · have hjn : j ≤ n := by omega
      have hdn : ∀ i < n, 1 ≤ d i := fun i hi => hd i (by omega)
      have hzero : liftDigit d n = 0 :=
        liftDigit_eq_zero_of_gap hd hB (by omega)
          (lt_of_lt_of_le hgap (Nat.pow_le_pow_right (by norm_num) (by
            have := S_mono (d := d) hjn; omega)))
      have hsucc : leastRealizer d (n + 1) = leastRealizer d n := by
        rw [leastRealizer_succ (fun i hi => hd i (by omega)), hzero]; ring
      rw [hsucc]
      exact ih hdn (by rw [← hsucc]; exact hB) hjn

end LiftGap
end EOC
