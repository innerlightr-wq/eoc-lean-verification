import EOC.ChangHistory
import EOC.CurryFoundation

/-!
# Chang's burst statistics against the zero corridor

Companion to `docs/CHANG_CROSS_SCALE_REALIZER_AUDIT.md`.

Chang's burst indicator is `X_t = 1[n_t ≡ 1 (mod 4)] = 1[v₂(3n_t+1) ≥ 2]`, which
`ChangHistory.a_ge_two_iff` already identifies with `2 ≤ a n`. So in valuation-word
coordinates a *burst* is exactly a step with `d_t ≥ 2` and a *gap step* is `d_t = 1`.
Chang's burst density is therefore the density of digits `≥ 2` in the valuation word.

Two facts relating that statistic to the Curry zero corridor `S_j ≤ ⌊jα⌋`:

* `burstCount_le_of_confined` — zero confinement caps the burst count:
  `#{t < k : d_t ≥ 2} ≤ (α − 1)·k`, i.e. Chang's burst density is at most
  `α − 1 = 0.5849625…`. This follows from the **total valuation alone** (each burst
  costs at least one extra unit of valuation over the `d = 1` baseline), so it is a
  consequence of ordinary digit counting and not of any residue arithmetic. It is also
  not binding in practice: Chang reports `ρ ≈ 0.54` for typical orbits.

* `changWord_not_zeroConfined` — the canonical Chang word `β(y₀)…β(y_{K−1})` of
  `ChangHistory` is **never** zero-confined, for a completely elementary reason: every
  block begins with `d = 2`, so `S_1 = 2`, while the corridor allows only
  `S_1 ≤ ⌊α⌋ = 1`.

The second is a statement about the *canonical construction*, not about Chang histories.
The audit's computational finding (§M) is that every Chang label history of length
`K ≤ 10` **is** realized by some zero-confined word once padding digits are allowed —
so the obstruction below is an artifact of the canonical packing, not a restriction on
the achievable label language.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace ChangZeroCorridor

open Finset ChangHistory

/-! ## 1. Zero confinement caps Chang's burst density -/

/-- Chang's burst count over the first `k` steps: the number of digits `≥ 2`. -/
def burstCount (d : ℕ → ℕ) (k : ℕ) : ℕ :=
  ((range k).filter (fun t => 2 ≤ d t)).card

/-- Every valuation word pays at least one unit per step plus one extra per burst. -/
theorem add_burstCount_le_S {d : ℕ → ℕ} (hd : ∀ i, 1 ≤ d i) (k : ℕ) :
    k + burstCount d k ≤ s d k := by
  unfold burstCount s
  have hcard : ((range k).filter (fun t => 2 ≤ d t)).card
      = ∑ t ∈ range k, (if 2 ≤ d t then 1 else 0) := by
    rw [Finset.card_filter]
  rw [hcard]
  calc k + ∑ t ∈ range k, (if 2 ≤ d t then 1 else 0)
      = ∑ t ∈ range k, (1 + if 2 ≤ d t then 1 else 0) := by
        rw [Finset.sum_add_distrib]; simp
    _ ≤ ∑ t ∈ range k, d t := by
        refine Finset.sum_le_sum fun t _ => ?_
        by_cases h : 2 ≤ d t
        · rw [if_pos h]; omega
        · rw [if_neg h]; have := hd t; omega

/-- **Zero confinement caps the Chang burst density.**  If the prefix sums stay on or
below the critical line, `S_k ≤ α·k`, then the number of bursts among the first `k`
steps is at most `(α − 1)·k`.

Numerically `α − 1 = 0.5849625…`. Chang reports a typical burst density `ρ ≈ 0.54`, so
the corridor does constrain the statistic but is not binding for typical orbits. The
proof uses only the total valuation, so this is ordinary digit counting: it is **not**
residue information, and §K of the audit classifies it accordingly. -/
theorem burstCount_le_of_confined {d : ℕ → ℕ} (hd : ∀ i, 1 ≤ d i) (k : ℕ)
    (hconf : (s d k : ℝ) ≤ alpha * k) :
    (burstCount d k : ℝ) ≤ (alpha - 1) * k := by
  have h := add_burstCount_le_S hd k
  have h' : ((k : ℝ)) + (burstCount d k : ℝ) ≤ (s d k : ℝ) := by exact_mod_cast h
  nlinarith [h', hconf]

/-! ## 2. The canonical Chang word is never zero-confined -/

/-- Every canonical Chang block begins with the digit `2`. -/
theorem changWord_zero (ys : List Bool) (hys : ys ≠ []) : changWord ys 0 = 2 := by
  cases ys with
  | nil => exact absurd rfl hys
  | cons b bs =>
      cases b <;>
        simp [changWord, changWordList, changBlock, List.getD, List.getElem?_cons_zero]

/-- The canonical word's first prefix sum is `2`. -/
theorem changWord_S_one (ys : List Bool) (hys : ys ≠ []) : s (changWord ys) 1 = 2 := by
  simp [s, Finset.sum_range_one, changWord_zero ys hys]

/-- `⌊α⌋ = 1`, since `1 < α < 2`. -/
theorem floor_alpha : ⌊alpha⌋ = 1 := by
  have h1 : (1 : ℝ) < alpha := one_lt_alpha
  have h2 : alpha < 2 := CurryFoundation.alpha_lt_two
  rw [Int.floor_eq_iff]
  constructor <;> push_cast <;> linarith

/-- **The canonical Chang construction never lies in the exact zero corridor.**

`ChangHistory` realizes every finite Chang label history by the word
`β(y₀)…β(y_{K−1})`, with `β(0) = (2,1,1)` and `β(1) = (2,1,2)`. Every such word starts
with `d₀ = 2`, so `S_1 = 2`, while the corridor at `j = 1` permits only
`S_1 ≤ ⌊1·α⌋ = 1`.

This is an artifact of the packing, not a restriction on Chang histories: allowing
padding digits, every label history of length `K ≤ 10` is realized by a zero-confined
word (audit §M, computational). So no finite Chang-history obstruction survives inside
the corridor. -/
theorem changWord_not_zeroConfined (ys : List Bool) (hys : ys ≠ []) :
    ¬ (∀ j : ℕ, 1 ≤ j → (s (changWord ys) j : ℝ) ≤ (⌊(j : ℝ) * alpha⌋ : ℝ)) := by
  intro h
  have h1 := h 1 le_rfl
  rw [changWord_S_one ys hys] at h1
  have : ((1 : ℕ) : ℝ) * alpha = alpha := by norm_num
  rw [this, floor_alpha] at h1
  norm_num at h1

end ChangZeroCorridor
end EOC
