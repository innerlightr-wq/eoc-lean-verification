/-
Copyright (c) 2026 E. De Jesús. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: E. De Jesús
-/
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Generic occupancy bound: label-distinct pair counting versus capacity

The finite counting core behind the obstruction to beating a capacity bound by rejecting pairs on
a low-residue label alone.  Nothing here mentions the Collatz map: `z` is an arbitrary labelling.

Let `s` be a finite set of size `n`, `z` a labelling, and `nOcc y = #{ω ∈ s | z ω = y}` the
occupancies.  Let `candidates` be the ordered pairs that are **diagonal or label-distinct** —
exactly the pairs surviving a rejection test based only on label-distinctness.  Then

* `sum_nOcc` — `∑ y, nOcc y = n`;
* `card_sameLabel` — `#{label-equal pairs} = ∑ y, (nOcc y)^2`;
* `card_candidates_add_card_sameLabel` — `P + ∑ y, (nOcc y)^2 = n^2 + n`;
* `sum_sq_nOcc_le` — `nOcc y ≤ q` for all `y` gives `∑ y, (nOcc y)^2 ≤ q * n`;
* `mul_succ_le_candidates_add` — `n * (n+1) ≤ P + q * n`;
* `capacity_lt_candidates` — `0 < n` and `q + h < n + 1` give `n * h < P`.

Everything is in `ℕ`; no truncated subtraction is used anywhere.

**Scope.** This says that counting *every* pair which survives a label-distinctness test cannot
beat a capacity bound `n * h` once `q + h < n + 1`.  It does not exclude other uses of label
information, and it contains **no Collatz instantiation**: applying it requires the accelerated
longest-common-prefix valuation law and the identification of `z` with a low-residue class, neither
of which is formalized here.

No `sorry`, `admit`, new `axiom`, or `opaque`.
-/

namespace EOC
namespace Occupancy

open Finset

variable {Ω κ : Type*} [DecidableEq κ] (s : Finset Ω) (z : Ω → κ)

/-- Occupancy of the label `y`: the number of elements of `s` carrying it. -/
def nOcc (y : κ) : ℕ := (s.filter fun ω => z ω = y).card

/-- The ordered pairs from `s` whose labels agree. -/
def sameLabel : Finset (Ω × Ω) := (s ×ˢ s).filter fun p => z p.1 = z p.2

/-- The ordered pairs from `s` that are diagonal or label-distinct. -/
def candidates [DecidableEq Ω] : Finset (Ω × Ω) :=
  (s ×ˢ s).filter fun p => p.1 = p.2 ∨ z p.1 ≠ z p.2

@[simp] theorem mem_sameLabel {p : Ω × Ω} :
    p ∈ sameLabel s z ↔ (p.1 ∈ s ∧ p.2 ∈ s) ∧ z p.1 = z p.2 := by
  unfold sameLabel; rw [mem_filter, Finset.mem_product]

@[simp] theorem mem_candidates [DecidableEq Ω] {p : Ω × Ω} :
    p ∈ candidates s z ↔ (p.1 ∈ s ∧ p.2 ∈ s) ∧ (p.1 = p.2 ∨ z p.1 ≠ z p.2) := by
  unfold candidates; rw [mem_filter, Finset.mem_product]

/-- The occupancies sum to the size of `s`. -/
theorem sum_nOcc : ∑ y ∈ s.image z, nOcc s z y = s.card :=
  (card_eq_sum_card_fiberwise fun _ hw => mem_image_of_mem z hw).symm

/-- The label-equal pairs are counted by the sum of squared occupancies. -/
theorem card_sameLabel :
    (sameLabel s z).card = ∑ y ∈ s.image z, (nOcc s z y) ^ 2 := by
  classical
  have hmem : ∀ p ∈ sameLabel s z, z p.1 ∈ s.image z := fun p hp =>
    mem_image_of_mem z ((mem_sameLabel s z).mp hp).1.1
  rw [card_eq_sum_card_fiberwise hmem]
  refine sum_congr rfl fun y _ => ?_
  have hfib : (sameLabel s z).filter (fun p : Ω × Ω => z p.1 = y)
      = (s.filter fun ω => z ω = y) ×ˢ (s.filter fun ω => z ω = y) := by
    ext p
    rw [mem_filter, mem_sameLabel, Finset.mem_product, mem_filter, mem_filter]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, heq⟩, hy⟩
      exact ⟨⟨h1, hy⟩, ⟨h2, heq.symm.trans hy⟩⟩
    · rintro ⟨⟨h1, hy1⟩, ⟨h2, hy2⟩⟩
      exact ⟨⟨⟨h1, h2⟩, hy1.trans hy2.symm⟩, hy1⟩
  rw [hfib, card_product, sq]
  rfl

/-- **The pair-counting identity.**  The diagonal is label-equal and every pair is either
label-equal or label-distinct, so the candidate count and the label-equal count add to `n^2 + n`. -/
theorem card_candidates_add_card_sameLabel [DecidableEq Ω] :
    (candidates s z).card + (sameLabel s z).card = s.card ^ 2 + s.card := by
  classical
  set D : Finset (Ω × Ω) := (s ×ˢ s).filter (fun p : Ω × Ω => p.1 = p.2) with hD
  set E : Finset (Ω × Ω) := (s ×ˢ s).filter (fun p : Ω × Ω => z p.1 ≠ z p.2) with hE
  have hdiag : D.card = s.card := by
    have : D = s.diag := by
      ext p
      rw [hD, mem_filter, Finset.mem_product, mem_diag]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2 ▸ h.1⟩, h.2⟩⟩
    rw [this, diag_card]
  have hsplit : candidates s z = D ∪ E := by
    ext p
    rw [mem_candidates, mem_union, hD, hE, mem_filter, mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨hm, h | h⟩
      · exact Or.inl ⟨hm, h⟩
      · exact Or.inr ⟨hm, h⟩
    · rintro (⟨hm, h⟩ | ⟨hm, h⟩)
      · exact ⟨hm, Or.inl h⟩
      · exact ⟨hm, Or.inr h⟩
  have hdisj : Disjoint D E := by
    rw [disjoint_left]
    intro p hp hp'
    rw [hD, mem_filter] at hp
    rw [hE, mem_filter] at hp'
    exact hp'.2 (congrArg z hp.2)
  have hcomp : (sameLabel s z).card + E.card = s.card ^ 2 := by
    unfold sameLabel
    rw [hE, card_filter_add_card_filter_not (fun p : Ω × Ω => z p.1 = z p.2), card_product, sq]
  rw [hsplit, card_union_of_disjoint hdisj, hdiag]
  omega

/-- If every occupancy is at most `q`, the squared occupancies sum to at most `q * n`. -/
theorem sum_sq_nOcc_le {q : ℕ} (hq : ∀ y, nOcc s z y ≤ q) :
    ∑ y ∈ s.image z, (nOcc s z y) ^ 2 ≤ q * s.card := by
  calc ∑ y ∈ s.image z, (nOcc s z y) ^ 2
      ≤ ∑ y ∈ s.image z, q * nOcc s z y := by
        refine sum_le_sum fun y _ => ?_
        rw [sq]
        exact Nat.mul_le_mul_right _ (hq y)
    _ = q * s.card := by rw [← mul_sum, sum_nOcc]

/-- **`n(n+1) ≤ P + q·n`** — the subtraction-free form of the obstruction. -/
theorem mul_succ_le_candidates_add [DecidableEq Ω] {q : ℕ} (hq : ∀ y, nOcc s z y ≤ q) :
    s.card * (s.card + 1) ≤ (candidates s z).card + q * s.card := by
  have h1 := card_candidates_add_card_sameLabel s z
  have h2 := sum_sq_nOcc_le s z hq
  have h3 := card_sameLabel s z
  have hsq : s.card * (s.card + 1) = s.card ^ 2 + s.card := by
    rw [Nat.mul_add, Nat.mul_one, sq]
  omega

/-- **Capacity comparison.**  If `s` is nonempty and `q + h < n + 1`, the candidate count strictly
exceeds the capacity `n * h`.  With `h = H / 2` for an even interval length `H`, this is the
statement that label-distinctness rejection alone cannot beat the capacity bound `n * H / 2`. -/
theorem capacity_lt_candidates [DecidableEq Ω] {q h : ℕ} (hq : ∀ y, nOcc s z y ≤ q)
    (hpos : 0 < s.card) (hcard : q + h < s.card + 1) :
    s.card * h < (candidates s z).card := by
  have hmain := mul_succ_le_candidates_add s z hq
  have hstep : s.card * (q + h + 1) ≤ s.card * (s.card + 1) :=
    Nat.mul_le_mul_left _ hcard
  have hexp : s.card * (q + h + 1) = q * s.card + s.card * h + s.card := by
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_comm s.card q]
  omega

end Occupancy
end EOC
