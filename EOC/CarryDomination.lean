/-
Copyright (c) 2026 E. De Jesús. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: E. De Jesús
-/
import Mathlib.Data.ZMod.Basic

/-!
# Two-class domination for a one-bit carry

The elementary counting core of the carry-robust bound. If a quantity `T` differs from `Z` by a
carry taking only the values `0` and `1`, then each fibre of `T` is covered by two fibres of `Z`:

* `filter_subset_union` — `{i | T i = t} ⊆ {i | Z i = t} ∪ {i | Z i = t - 1}`;
* `card_filter_le` — hence `#{i | T i = t} ≤ #{i | Z i = t} + #{i | Z i = t - 1}`.

No independence, equidistribution or cancellation hypothesis is used, and nothing is assumed about
how the carry depends on `Z`. This is the step that lets an arbitrary binary carry be absorbed at a
factor-two cost in an *upper* counting bound.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace CarryDomination

open Finset

variable {ι : Type*} {q : ℕ} [DecidableEq (ZMod q)]

/-- The fibre of `T = Z + c` over `t`, for a carry `c` valued in `{0, 1}`, is contained in the
union of the fibres of `Z` over `t` and over `t - 1`. -/
theorem filter_subset_union [DecidableEq ι] (s : Finset ι) (Z c T : ι → ZMod q)
    (hc : ∀ i, c i = 0 ∨ c i = 1) (hT : ∀ i, T i = Z i + c i) (t : ZMod q) :
    s.filter (fun i => T i = t) ⊆
      s.filter (fun i => Z i = t) ∪ s.filter (fun i => Z i = t - 1) := by
  intro i hi
  rw [mem_filter] at hi
  obtain ⟨his, hit⟩ := hi
  rw [mem_union, mem_filter, mem_filter]
  rcases hc i with h0 | h1
  · left
    refine ⟨his, ?_⟩
    rw [hT i, h0, add_zero] at hit
    exact hit
  · right
    refine ⟨his, ?_⟩
    rw [hT i, h1] at hit
    exact eq_sub_of_add_eq hit

/-- **Two-class domination.** A one-bit carry costs at most a factor two in an upper count:
`#{i | T i = t} ≤ #{i | Z i = t} + #{i | Z i = t - 1}` for every target residue `t`. -/
theorem card_filter_le (s : Finset ι) (Z c T : ι → ZMod q)
    (hc : ∀ i, c i = 0 ∨ c i = 1) (hT : ∀ i, T i = Z i + c i) (t : ZMod q) :
    (s.filter (fun i => T i = t)).card
      ≤ (s.filter (fun i => Z i = t)).card + (s.filter (fun i => Z i = t - 1)).card := by
  classical
  calc (s.filter (fun i => T i = t)).card
      ≤ (s.filter (fun i => Z i = t) ∪ s.filter (fun i => Z i = t - 1)).card :=
        card_le_card (filter_subset_union s Z c T hc hT t)
    _ ≤ (s.filter (fun i => Z i = t)).card + (s.filter (fun i => Z i = t - 1)).card :=
        card_union_le _ _

end CarryDomination
end EOC
