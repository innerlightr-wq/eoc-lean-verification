import EOC.ChangZeroCorridor

/-!
# Zero-corridor deficit calculus and the Chang emission gadget

Companion to `docs/CHANG_INFINITE_COMPATIBILITY_AUDIT.md`.

The previous round found, computationally, that every finite Chang label history of length
`K ≤ 11` is realized by some zero-confined valuation word. This file supplies the **exact
arithmetic behind a constructive proof** that replaces that search: a bounded gadget emits
either Chang label while preserving the exact corridor `S_j ≤ ⌊jα⌋`, and padding with the
digit `1` recharges the deficit reserve it spends.

Everything here is about **valuation words**, i.e. symbols. Nothing in this file asserts that
the resulting infinite word has a positive-integer realizer — §Q of the audit explains why that
is exactly the step Chang's framework cannot take.

## The calculus

Write `Δ_N = ⌊Nα⌋ − S_N` for the deficit (`CurryFoundation.deficit`), and
`b_{N+1} = ⌊(N+1)α⌋ − ⌊Nα⌋` for the Beatty gap, so `Δ_{N+1} = Δ_N + b_{N+1} − d_N`
(`CurryFoundation.deficit_succ`). `CurryFoundation.beatty_gap_mem` gives `b ∈ {1,2}`. This file
adds the **multi-step** gaps, which is what the gadget needs:

* `beatty_two_step` — `⌊(N+2)α⌋ − ⌊Nα⌋ ≥ 3`, so **no two consecutive Beatty gaps are both 1**;
* `beatty_three_step` — `⌊(N+3)α⌋ − ⌊Nα⌋ ≥ 4`.

Both come from `⌊x⌋ + ⌊c⌋ ≤ ⌊x + c⌋` with `⌊2α⌋ = 3` and `⌊3α⌋ = 4`, which need the sharper
bounds `3/2 < α < 8/5` proved here (`three_halves_lt_alpha`, `alpha_lt_eight_fifths`) — the
repository previously had only `1 < α < 2`.

## Consequences recorded

* `le_floor_succ_of_le_floor` — appending the digit `1` preserves zero confinement, so **every
  finite zero-confined word has an infinite zero-confined extension** (audit §D).
* `emitZero_cost`, `emitOne_cost` — the label-0 block `(2,1,1)` (valuation 4) never costs
  deficit, and the label-1 block `(2,1,3)` (valuation 6) costs at most 2.
* `recharge_two` — any two consecutive `1`s gain at least one unit of deficit.

The label-1 block is `(2,1,3)`, **not** the canonical `(2,1,2)` of `ChangHistory`. With
`(2,1,2)` followed by a padding `1`, the digit pair `(2,1)` recurs at the third position and
creates a *spurious* Chang event; `ChangHistory`'s canonical word avoids this by starting the
next block with `2`, which is incompatible with padding. Using `3` keeps the label (`d ≥ 2`)
while making the following pair `(3,1)`, which is not an event.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace ChangInfiniteCompatibility

open CurryFoundation

/-! ## 1. Sharper bounds on `α` -/

/-- `3/2 < α`, equivalently `8 < 9`. -/
theorem three_halves_lt_alpha : (3 : ℝ) / 2 < alpha := by
  unfold alpha Real.logb
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [lt_div_iff₀ hl2]
  have h8 : Real.log 8 < Real.log 9 := Real.log_lt_log (by norm_num) (by norm_num)
  have e8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have e9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  rw [e8, e9] at h8; linarith

/-- `α < 8/5`, equivalently `3^5 = 243 < 256 = 2^8`. -/
theorem alpha_lt_eight_fifths : alpha < (8 : ℝ) / 5 := by
  unfold alpha Real.logb
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_lt_iff₀ hl2]
  have h : Real.log 243 < Real.log 256 := Real.log_lt_log (by norm_num) (by norm_num)
  have e1 : Real.log 243 = 5 * Real.log 3 := by
    rw [show (243 : ℝ) = 3 ^ (5 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have e2 : Real.log 256 = 8 * Real.log 2 := by
    rw [show (256 : ℝ) = 2 ^ (8 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  rw [e1, e2] at h; linarith

/-- `⌊2α⌋ = 3`. -/
theorem floor_two_alpha : ⌊2 * alpha⌋ = 3 := by
  have h1 := three_halves_lt_alpha
  have h2 := alpha_lt_eight_fifths
  rw [Int.floor_eq_iff]
  constructor <;> push_cast <;> linarith

/-- `⌊3α⌋ = 4`. -/
theorem floor_three_alpha : ⌊3 * alpha⌋ = 4 := by
  have h1 := three_halves_lt_alpha
  have h2 := alpha_lt_eight_fifths
  rw [Int.floor_eq_iff]
  constructor <;> push_cast <;> linarith

/-! ## 2. Multi-step Beatty gaps -/

private theorem floor_add_floor_le (x c : ℝ) : ⌊x⌋ + ⌊c⌋ ≤ ⌊x + c⌋ :=
  Int.le_floor.mpr (by push_cast; linarith [Int.floor_le x, Int.floor_le c])

/-- **No two consecutive Beatty gaps are both `1`.**  `⌊(N+2)α⌋ − ⌊Nα⌋ ≥ 3`.

Since each single gap is `1` or `2` (`beatty_gap_mem`), a gap of `1` forces the next to be `2`.
This is what lets the emission gadget survive its worst-case intermediate step. -/
theorem beatty_two_step (N : ℝ) :
    ⌊N * alpha⌋ + 3 ≤ ⌊(N + 2) * alpha⌋ := by
  have h : ⌊N * alpha⌋ + ⌊2 * alpha⌋ ≤ ⌊N * alpha + 2 * alpha⌋ :=
    floor_add_floor_le (N * alpha) (2 * alpha)
  rw [floor_two_alpha] at h
  have e : N * alpha + 2 * alpha = (N + 2) * alpha := by ring
  rwa [e] at h

/-- `⌊(N+3)α⌋ − ⌊Nα⌋ ≥ 4`: three accelerated steps always supply at least four units of
Beatty budget, which is exactly the valuation of the label-0 block `(2,1,1)`. -/
theorem beatty_three_step (N : ℝ) :
    ⌊N * alpha⌋ + 4 ≤ ⌊(N + 3) * alpha⌋ := by
  have h : ⌊N * alpha⌋ + ⌊3 * alpha⌋ ≤ ⌊N * alpha + 3 * alpha⌋ :=
    floor_add_floor_le (N * alpha) (3 * alpha)
  rw [floor_three_alpha] at h
  have e : N * alpha + 3 * alpha = (N + 3) * alpha := by ring
  rwa [e] at h

/-! ## 3. Zero-confined words extend forever -/

/-- **Extendibility by the digit `1`.**  If `S ≤ ⌊Nα⌋` then `S + 1 ≤ ⌊(N+1)α⌋`.

Hence every finite zero-confined valuation word has an infinite zero-confined extension:
append `1`s forever. This is a purely symbolic statement — it says nothing about whether the
resulting infinite word has a positive-integer realizer. -/
theorem le_floor_succ_of_le_floor (N : ℝ) (S : ℤ) (hS : S ≤ ⌊N * alpha⌋) :
    S + 1 ≤ ⌊(N + 1) * alpha⌋ := by
  have h1 : (1 : ℝ) < alpha := one_lt_alpha
  have h : ⌊N * alpha⌋ + 1 ≤ ⌊(N + 1) * alpha⌋ := by
    have hle : ⌊N * alpha⌋ + ⌊alpha⌋ ≤ ⌊N * alpha + alpha⌋ :=
      floor_add_floor_le (N * alpha) alpha
    rw [ChangZeroCorridor.floor_alpha] at hle
    have e : N * alpha + alpha = (N + 1) * alpha := by ring
    rwa [e] at hle
  omega

/-! ## 4. The emission gadget -/

/-- **Label-0 block `(2,1,1)`, total valuation 4.**  Three steps supply at least four units of
Beatty budget (`beatty_three_step`), so the block never costs deficit: if `S ≤ ⌊Nα⌋` then
`S + 4 ≤ ⌊(N+3)α⌋`. -/
theorem emitZero_cost (N : ℝ) (S : ℤ) (hS : S ≤ ⌊N * alpha⌋) :
    S + 4 ≤ ⌊(N + 3) * alpha⌋ := by
  have := beatty_three_step N; omega

/-- **Label-1 block `(2,1,3)`, total valuation 6.**  It costs at most two units of deficit:
if `S + 2 ≤ ⌊Nα⌋` then `S + 6 ≤ ⌊(N+3)α⌋`.

So a reserve of `2` suffices to emit the label `1`. The digit `3` rather than `2` is what stops
the following padding `1` from creating a spurious Chang event (see the header). -/
theorem emitOne_cost (N : ℝ) (S : ℤ) (hS : S + 2 ≤ ⌊N * alpha⌋) :
    S + 6 ≤ ⌊(N + 3) * alpha⌋ := by
  have := beatty_three_step N; omega

/-- **Recharge.**  Two consecutive padding digits `1` gain at least one unit of deficit:
if `S ≤ ⌊Nα⌋` then `S + 2 + 1 ≤ ⌊(N+2)α⌋`.

Combined with `emitOne_cost` this is the invariant of the construction: a reserve of `2` is
restored after at most four padding steps, so the gadget can be iterated forever with **bounded
spacing**, hence at positive event density. -/
theorem recharge_two (N : ℝ) (S : ℤ) (hS : S ≤ ⌊N * alpha⌋) :
    S + 2 + 1 ≤ ⌊(N + 2) * alpha⌋ := by
  have := beatty_two_step N; omega

/-- **The intermediate step of either block is safe given reserve 1.**  After the first digit
`2` of a block, the prefix sum is `S + 2` and one Beatty gap has been supplied; a reserve of
`1` absorbs the worst case `b = 1`. -/
theorem emit_first_step (N : ℝ) (S : ℤ) (hS : S + 1 ≤ ⌊N * alpha⌋) :
    S + 2 ≤ ⌊(N + 1) * alpha⌋ := by
  have h : ⌊N * alpha⌋ + 1 ≤ ⌊(N + 1) * alpha⌋ := by
    have hle : ⌊N * alpha⌋ + ⌊alpha⌋ ≤ ⌊N * alpha + alpha⌋ :=
      floor_add_floor_le (N * alpha) alpha
    rw [ChangZeroCorridor.floor_alpha] at hle
    have e : N * alpha + alpha = (N + 1) * alpha := by ring
    rwa [e] at hle
  omega

end ChangInfiniteCompatibility
end EOC
