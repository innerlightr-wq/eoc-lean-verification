import EOC.Periodic
import EOC.TaoLike.Cylinder

/-!
# Cylinder additivity

Concatenating a realized prefix `d` (length `t`, valuation sum `S d t`) with a continuation
`e` (length `u`, valuation sum `S e u`) gives a realizer cylinder of modulus
`2^(S d t + S e u + 1)`. Reuses `orbit_add` from `EOC.Periodic`.
-/

namespace EOC

open Finset

/-- Concatenation: the first `t` letters come from `d`, the rest from `e`. -/
def wordAppend (d : ℕ → ℕ) (t : ℕ) (e : ℕ → ℕ) : ℕ → ℕ :=
  fun j => if j < t then d j else e (j - t)

theorem wordAppend_lt (d : ℕ → ℕ) (t : ℕ) (e : ℕ → ℕ) {j : ℕ} (hj : j < t) :
    wordAppend d t e j = d j := by
  show (if j < t then d j else e (j - t)) = d j
  rw [if_pos hj]

theorem wordAppend_add (d : ℕ → ℕ) (t : ℕ) (e : ℕ → ℕ) (j : ℕ) :
    wordAppend d t e (t + j) = e j := by
  show (if t + j < t then d (t + j) else e (t + j - t)) = e j
  rw [if_neg (by omega), Nat.add_sub_cancel_left]

/-- Valuation sums add under concatenation. -/
theorem S_wordAppend (d : ℕ → ℕ) (t : ℕ) (e : ℕ → ℕ) (u : ℕ) :
    S (wordAppend d t e) (t + u) = S d t + S e u := by
  unfold S s
  rw [Finset.sum_range_add]
  congr 1
  · exact Finset.sum_congr rfl (fun i hi => wordAppend_lt d t e (Finset.mem_range.mp hi))
  · exact Finset.sum_congr rfl (fun i _ => wordAppend_add d t e i)

/-- Realizing a concatenation = realizing the prefix, then the continuation from `orbit m t`. -/
theorem realizes_wordAppend_iff (d : ℕ → ℕ) (t : ℕ) (e : ℕ → ℕ) (u m : ℕ) :
    Realizes (wordAppend d t e) (t + u) m ↔
      Realizes d t m ∧ (∀ j < u, a (orbit (orbit m t) j) = e j) := by
  constructor
  · rintro ⟨hodd, hval⟩
    refine ⟨⟨hodd, fun j hj => ?_⟩, fun j hj => ?_⟩
    · have h := hval j (by omega)
      rwa [wordAppend_lt d t e hj] at h
    · have h := hval (t + j) (by omega)
      rwa [wordAppend_add, orbit_add] at h
  · rintro ⟨⟨hodd, hval1⟩, hval2⟩
    refine ⟨hodd, fun j hj => ?_⟩
    by_cases hjt : j < t
    · rw [wordAppend_lt d t e hjt]
      exact hval1 j hjt
    · have h := hval2 (j - t) (by omega)
      rw [← orbit_add, show t + (j - t) = j from by omega] at h
      have hw : wordAppend d t e j = e (j - t) := by
        show (if j < t then d j else e (j - t)) = e (j - t)
        rw [if_neg hjt]
      rw [hw]
      exact h

/-- **Cylinder additivity.** Restarting inside the cylinder of `d` and then imposing `e`
composes the moduli by adding valuation sums: the combined cylinder is modulo
`2^(S d t + S e u + 1)`. -/
theorem cylinder_additivity (d : ℕ → ℕ) (t : ℕ) (e : ℕ → ℕ) (u m k : ℕ)
    (hd : Realizes d t m) (he : ∀ j < u, a (orbit (orbit m t) j) = e j) :
    Realizes (wordAppend d t e) (t + u) (m + 2 ^ (S d t + S e u + 1) * k) ∧
    orbit (m + 2 ^ (S d t + S e u + 1) * k) (t + u)
      = orbit m (t + u) + 2 * 3 ^ (t + u) * k := by
  have hreal : Realizes (wordAppend d t e) (t + u) m :=
    (realizes_wordAppend_iff d t e u m).mpr ⟨hd, he⟩
  have h := cylinder_restart (wordAppend d t e) (t + u) m k hreal
  rwa [S_wordAppend] at h

end EOC
