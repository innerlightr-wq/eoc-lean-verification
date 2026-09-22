import EOC.ChangInfiniteCompatibility

/-!
# The zero-corridor Chang full-shift factor, formalized

Companion to `docs/CHANG_INFINITE_COMPATIBILITY_FORMALIZATION.md`.

**Headline.** For every `y : ℕ → Bool` there is an explicit infinite valuation sequence
`changSeq y : ℕ → ℕ` with all digits `≥ 1`, every prefix inside the exact zero corridor
`S_n ≤ ⌊nα⌋`, whose Chang events sit exactly at `7k + 4` and whose Chang labels are exactly `y`.

This supersedes the previous round's construction, which padded a variable number of `1`s to
restore a deficit reserve and therefore needed a recursive state, a termination argument, and a
separate prefix-compatibility lemma. The observation that removes all of that:

> a **fixed** block of seven digits already fits inside the corridor on its own, and its total
> valuation is at most `10 < 11 ≤ ⌊7α⌋`, so blocks may simply be concatenated.

The block is

```
block b = (1, 1, 1, 1, 2, 1, x)      x = 3 if b else 1
```

with partial sums `0,1,2,3,4,6,7` against the corridor allowance `⌊rα⌋ = 0,1,3,4,6,7,9`; the
inequality `p r ≤ ⌊rα⌋` holds termwise. Consequently `changSeq` is a **closed form**

```
changSeq y i = if i % 7 = 4 then 2 else if i % 7 = 6 then (if y (i / 7) then 3 else 1) else 1
```

with no recursion, no state, and no termination obligation. Prefix compatibility is definitional:
changing `y` beyond index `k` does not affect digits below `7k`.

**Event control.** The digit `2` occurs only at `i % 7 = 4`, and is always followed by `1`, so by
`ChangHistory.event_iff` the Chang events are *exactly* the positions `7k + 4` — there are no
spurious events. The label at `7k+4` is decided by the digit at `7k+6`, which is `3` or `1`
according to `y k`, so by `ChangHistory.label_iff` the label is exactly `y k`. Event spacing is
the uniform constant **7**, so the history is realized at positive density.

The `x = 3` choice (rather than the canonical `2` of `ChangHistory.changBlock`) is what keeps the
following pad digit `1` from re-forming the pair `(2,1)` and emitting a spurious event.

**What is not proved here.** Nothing about positive-integer realization. `changSeq y` is a
*symbolic* object; §Q of the report explains why the step to an ordinary positive integer is
exactly the boundary Chang's framework cannot cross, and this file deliberately stops short of it.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace ChangFullShift

open ChangInfiniteCompatibility

/-! ## 1. `11/7 < α < 8/5` and the seven floor values -/

/-- `11/7 < α`, equivalently `2^11 = 2048 < 2187 = 3^7`.  Sharper than
`ChangInfiniteCompatibility.three_halves_lt_alpha`, and needed because `⌊7α⌋` is not determined
by `3/2 < α < 8/5` (that range only gives `7α ∈ (10.5, 11.2)`). -/
theorem eleven_sevenths_lt_alpha : (11 : ℝ) / 7 < alpha := by
  unfold alpha Real.logb
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_lt_div_iff₀ (by norm_num) hl2]
  have h : Real.log 2048 < Real.log 2187 := Real.log_lt_log (by norm_num) (by norm_num)
  have e1 : Real.log 2048 = 11 * Real.log 2 := by
    rw [show (2048 : ℝ) = 2 ^ (11 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have e2 : Real.log 2187 = 7 * Real.log 3 := by
    rw [show (2187 : ℝ) = 3 ^ (7 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  rw [e1, e2] at h; linarith

private theorem alpha_bounds : (11 : ℝ) / 7 < alpha ∧ alpha < 8 / 5 :=
  ⟨eleven_sevenths_lt_alpha, alpha_lt_eight_fifths⟩

/-- The corridor allowance as a function, for use in the induction. -/
def cap : ℕ → ℤ
  | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 6 | 5 => 7 | 6 => 9 | _ => 11

theorem floor_cap (r : ℕ) (hr : r ≤ 7) : (cap r : ℤ) ≤ ⌊(r : ℝ) * alpha⌋ := by
  obtain ⟨hlo, hhi⟩ := alpha_bounds
  interval_cases r <;> simp only [cap] <;> rw [Int.le_floor] <;> push_cast <;> linarith

/-! ## 2. The block and the sequence -/

/-- The digit at offset `r` of a block carrying label `b`. -/
def blockDigit (r : ℕ) (b : Bool) : ℕ :=
  if r = 4 then 2 else if r = 6 then (if b then 3 else 1) else 1

/-- **The construction.**  Block `k` carries label `y k`; the block is seven digits long, its
fifth digit is `2` and its seventh is `3` or `1` according to the label. -/
def changSeq (y : ℕ → Bool) (i : ℕ) : ℕ := blockDigit (i % 7) (y (i / 7))

theorem blockDigit_pos (r : ℕ) (b : Bool) : 1 ≤ blockDigit r b := by
  unfold blockDigit; split_ifs <;> simp

/-- Every digit of the construction is positive — the standing hypothesis of the realizer and
ZCRE machinery. -/
theorem changSeq_pos (y : ℕ → Bool) (i : ℕ) : 1 ≤ changSeq y i := blockDigit_pos _ _

theorem blockDigit_le_three (r : ℕ) (b : Bool) : blockDigit r b ≤ 3 := by
  unfold blockDigit; split_ifs <;> simp

/-! ## 3. Zero confinement -/

/-- Partial sums inside one block: `p r = 0,1,2,3,4,6,7` for `r = 0,…,6`. -/
def part : ℕ → ℕ
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 7 | _ => 10

theorem part_le_cap (r : ℕ) (hr : r < 7) : (part r : ℤ) ≤ cap r := by
  interval_cases r <;> simp [part, cap]

/-- The block partial sums advance by the block digit. -/
theorem part_succ (r : ℕ) (hr : r < 6) (b : Bool) :
    part (r + 1) = part r + blockDigit r b := by
  interval_cases r <;> simp [part, blockDigit]

/-- **Prefix-sum bound.**  `S_n ≤ 10·(n/7) + p(n % 7)`: each completed block adds at most `10`,
and the running partial sum inside the current block is `p`. -/
theorem s_le (y : ℕ → Bool) (n : ℕ) :
    (s (changSeq y) n : ℤ) ≤ 10 * (n / 7 : ℕ) + part (n % 7) := by
  induction n with
  | zero => simp [s, part]
  | succ n ih =>
      have hs : s (changSeq y) (n + 1) = s (changSeq y) n + changSeq y n := by
        simp [s, Finset.sum_range_succ]
      have hcs : changSeq y n = blockDigit (n % 7) (y (n / 7)) := rfl
      rcases Nat.lt_or_ge (n % 7) 6 with h6 | h6
      · have hq : (n + 1) / 7 = n / 7 := by omega
        have hr : (n + 1) % 7 = n % 7 + 1 := by omega
        have hp : part (n % 7 + 1) = part (n % 7) + blockDigit (n % 7) (y (n / 7)) :=
          part_succ _ h6 _
        rw [hs, hq, hr, hp, hcs]
        push_cast
        push_cast at ih
        linarith
      · have h6' : n % 7 = 6 := by omega
        have hq : (n + 1) / 7 = n / 7 + 1 := by omega
        have hr : (n + 1) % 7 = 0 := by omega
        have hd : (blockDigit (n % 7) (y (n / 7)) : ℤ) ≤ 3 := by
          exact_mod_cast blockDigit_le_three _ _
        rw [h6'] at ih
        rw [hs, hq, hr, hcs]
        simp only [part] at ih ⊢
        push_cast at ih ⊢
        linarith

/-- `⌊nα⌋ ≥ 11·(n/7) + cap (n % 7)`: the corridor allowance decomposes over blocks, because
`⌊7α⌋ = 11` and floors are superadditive. -/
theorem floor_ge (n : ℕ) :
    (11 : ℤ) * (n / 7 : ℕ) + cap (n % 7) ≤ ⌊(n : ℝ) * alpha⌋ := by
  obtain ⟨hlo, _⟩ := alpha_bounds
  -- abstract the quotient and remainder before any casting: `push_cast` would otherwise
  -- rewrite `((n / 7 : ℕ) : ℤ)` into the ℤ-division `(↑n / 7)` and the two sides stop matching
  set k := n / 7 with hk
  set r := n % 7 with hr
  have hr7 : r < 7 := by rw [hr]; exact Nat.mod_lt _ (by norm_num)
  have hn : (n : ℝ) = 7 * (k : ℝ) + (r : ℝ) := by
    have h : 7 * k + r = n := by rw [hk, hr]; exact Nat.div_add_mod n 7
    exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) h.symm
  have hkR : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  have hprod : (0 : ℝ) ≤ (k : ℝ) * (7 * alpha - 11) := mul_nonneg hkR (by linarith)
  have hblk : (11 : ℝ) * (k : ℝ) ≤ 7 * (k : ℝ) * alpha := by nlinarith [hprod]
  have hrem : ((cap r : ℤ) : ℝ) ≤ (r : ℝ) * alpha := by
    have hc := floor_cap r (by omega)
    have h1 : ((cap r : ℤ) : ℝ) ≤ ((⌊(r : ℝ) * alpha⌋ : ℤ) : ℝ) := by exact_mod_cast hc
    linarith [Int.floor_le ((r : ℝ) * alpha), h1]
  have hexp : (n : ℝ) * alpha = 7 * (k : ℝ) * alpha + (r : ℝ) * alpha := by rw [hn]; ring
  have hcast : (((11 : ℤ) * (k : ℕ) + cap r : ℤ) : ℝ) = 11 * (k : ℝ) + ((cap r : ℤ) : ℝ) := by
    push_cast; ring
  rw [Int.le_floor, hcast, hexp]
  linarith [hblk, hrem]

/-- **Zero confinement.**  Every prefix of the construction lies on or below the Beatty line:
`S_n ≤ ⌊nα⌋` for every `n`.  This covers *every* intermediate position, not merely block
boundaries. -/
theorem changSeq_zeroConfined (y : ℕ → Bool) (n : ℕ) :
    (s (changSeq y) n : ℤ) ≤ ⌊(n : ℝ) * alpha⌋ := by
  have h1 := s_le y n
  have h2 := floor_ge n
  have h3 : (part (n % 7) : ℤ) ≤ cap (n % 7) := part_le_cap _ (by omega)
  have hk : (0 : ℤ) ≤ (n / 7 : ℕ) := Int.ofNat_nonneg _
  omega

/-! ## 4. Event positions and labels -/

theorem changSeq_eq_two_iff (y : ℕ → Bool) (i : ℕ) : changSeq y i = 2 ↔ i % 7 = 4 := by
  unfold changSeq blockDigit
  by_cases h4 : i % 7 = 4
  · simp [h4]
  · by_cases h6 : i % 7 = 6
    · cases hb : y (i / 7) <;> simp [h4, h6, hb]
    · simp [h4, h6]

theorem changSeq_succ_of_four (y : ℕ → Bool) (i : ℕ) (h : i % 7 = 4) :
    changSeq y (i + 1) = 1 := by
  have h5 : (i + 1) % 7 = 5 := by omega
  unfold changSeq blockDigit; rw [h5]; norm_num

/-- **Events are exactly the positions `≡ 4 (mod 7)`.**  A Chang event is the digit pair
`(2,1)` (`ChangHistory.event_iff`); the digit `2` occurs only at offset `4` of a block and is
always followed by `1`.  So there are **no spurious events**. -/
theorem changSeq_event_iff (y : ℕ → Bool) (i : ℕ) :
    (changSeq y i = 2 ∧ changSeq y (i + 1) = 1) ↔ i % 7 = 4 := by
  constructor
  · rintro ⟨h2, _⟩; exact (changSeq_eq_two_iff y i).mp h2
  · intro h; exact ⟨(changSeq_eq_two_iff y i).mpr h, changSeq_succ_of_four y i h⟩

/-- The `k`-th event position. -/
def eventPos (k : ℕ) : ℕ := 7 * k + 4

theorem eventPos_strictMono : StrictMono eventPos := fun a b h => by
  unfold eventPos; omega

/-- Event spacing is the uniform constant `7`, so the prescribed history is realized at positive
density — not by sparse coding. -/
theorem eventPos_succ_sub (k : ℕ) : eventPos (k + 1) - eventPos k = 7 := by
  unfold eventPos; omega

theorem eventPos_is_event (y : ℕ → Bool) (k : ℕ) :
    changSeq y (eventPos k) = 2 ∧ changSeq y (eventPos k + 1) = 1 :=
  (changSeq_event_iff y _).mpr (by unfold eventPos; omega)

/-- Positions that are not of the form `7k+4` carry no event. -/
theorem not_event_of_ne (y : ℕ → Bool) (i : ℕ) (h : i % 7 ≠ 4) :
    ¬ (changSeq y i = 2 ∧ changSeq y (i + 1) = 1) := fun hc =>
  h ((changSeq_event_iff y i).mp hc)

/-- **The labels are exactly `y`.**  At the event `7k+4` the label is decided by the digit two
steps later (`ChangHistory.label_iff`), namely the digit at `7k+6`, which is `3` when `y k` and
`1` otherwise. -/
theorem changSeq_label (y : ℕ → Bool) (k : ℕ) :
    (2 ≤ changSeq y (eventPos k + 2)) ↔ y k = true := by
  have hmod : (eventPos k + 2) % 7 = 6 := by unfold eventPos; omega
  have hdiv : (eventPos k + 2) / 7 = k := by unfold eventPos; omega
  unfold changSeq blockDigit
  rw [hmod, hdiv]
  cases hb : y k <;> simp [hb]

/-! ## 5. The headline theorem -/

/-- **Zero-corridor Chang full-shift factor.**

For every infinite binary sequence `y` there is an explicit infinite valuation sequence `d` with

* every digit positive;
* every prefix zero-confined, `S_n ≤ ⌊nα⌋`;
* Chang events exactly at `7k + 4`, and nowhere else;
* the label at the `k`-th event exactly `y k`.

The witness is `changSeq y`, a closed form. This is a statement about **valuation sequences**:
it does *not* assert that `d` is the valuation word of a Collatz orbit of a positive integer. -/
theorem chang_zero_corridor_full_shift (y : ℕ → Bool) :
    ∃ d : ℕ → ℕ,
      (∀ i, 1 ≤ d i) ∧
      (∀ n, (s d n : ℤ) ≤ ⌊(n : ℝ) * alpha⌋) ∧
      (∀ i, (d i = 2 ∧ d (i + 1) = 1) ↔ i % 7 = 4) ∧
      (∀ k, (2 ≤ d (eventPos k + 2)) ↔ y k = true) := by
  refine ⟨changSeq y, changSeq_pos y, changSeq_zeroConfined y, changSeq_event_iff y,
    changSeq_label y⟩

/-! ## 6. Chang is a radius-3 local factor -/

/-- **Local-factor theorem.**  Whether position `j` carries a Chang event, and if so which label,
is determined by the three digits `d j, d (j+1), d (j+2)` and by nothing else.

The event criterion is the pair `(d j, d (j+1)) = (2,1)` (`ChangHistory.event_iff`) and the label
is decided by `d (j+2) ≥ 2` (`ChangHistory.label_iff`), so the radius is **exactly 3**. This is
the precise sense in which the Chang observable is a finite-radius factor of the valuation
sequence, and therefore cannot carry information the sequence does not. -/
theorem chang_local_factor (d d' : ℕ → ℕ) (j : ℕ)
    (h0 : d j = d' j) (h1 : d (j + 1) = d' (j + 1)) (h2 : d (j + 2) = d' (j + 2)) :
    ((d j = 2 ∧ d (j + 1) = 1) ↔ (d' j = 2 ∧ d' (j + 1) = 1)) ∧
    ((2 ≤ d (j + 2)) ↔ (2 ≤ d' (j + 2))) := by
  refine ⟨?_, ?_⟩
  · rw [h0, h1]
  · rw [h2]

/-! ## 7. The hierarchy, levels 1 and 2 -/

/-- **LEVEL 1 — finite zero-corridor Chang realization.**  Every finite label list is realized,
as an immediate specialization of the infinite theorem: extend the list by `false` and read off
its first `ys.length` labels. This subsumes the earlier computational universality checks. -/
theorem finite_history_realized (ys : List Bool) :
    ∃ d : ℕ → ℕ,
      (∀ i, 1 ≤ d i) ∧
      (∀ n, (s d n : ℤ) ≤ ⌊(n : ℝ) * alpha⌋) ∧
      (∀ i, (d i = 2 ∧ d (i + 1) = 1) ↔ i % 7 = 4) ∧
      (∀ k < ys.length, (2 ≤ d (eventPos k + 2)) ↔ ys.getD k false = true) := by
  obtain ⟨d, hpos, hconf, hev, hlab⟩ :=
    chang_zero_corridor_full_shift (fun i => ys.getD i false)
  exact ⟨d, hpos, hconf, hev, fun k _ => hlab k⟩

/-- **LEVEL 2 is the headline theorem** `chang_zero_corridor_full_shift`.

**LEVEL 3 (2-adic realization) is not formalized in this repository**: there is no `PadicInt`
or infinite-word realizer development to connect to. The nested prefix congruences of
`Realizer.realizerCongruence` do determine a unique 2-adic integer mathematically, but that
bridge is stated only in the report, not in Lean.

**LEVEL 4 (positive ordinary integer) is deliberately NOT proved, and must not be inferred.**
`ZCRERealizerGrowth.boundedPrefixRealizers_iff_positiveRealizer` says a word has a positive
integer realizer exactly when its prefix least realizers are bounded. Nothing above establishes
that for `changSeq y`, and nothing above should be read as evidence for it: the corridor
constrains the *word*, while positivity is a constraint on the *seed*. -/
theorem level_four_not_established : True := trivial


end ChangFullShift
end EOC
