# Formalizing infinite zero-corridor Chang compatibility

Follow-up to [`docs/CHANG_INFINITE_COMPATIBILITY_AUDIT.md`](CHANG_INFINITE_COMPATIBILITY_AUDIT.md),
which gave a constructive argument for infinite symbolic Chang universality but left the recursive
assembly unformalized.

**Result: the assembly is formalized, and the construction turned out to be much simpler than the
one it replaces.**

```
chang_zero_corridor_full_shift (y : ℕ → Bool) :
    ∃ d : ℕ → ℕ,
      (∀ i, 1 ≤ d i) ∧                                        -- positive digits
      (∀ n, (s d n : ℤ) ≤ ⌊(n : ℝ) * alpha⌋) ∧                -- exact zero corridor, every prefix
      (∀ i, (d i = 2 ∧ d (i + 1) = 1) ↔ i % 7 = 4) ∧          -- events exactly at 7k+4, none spurious
      (∀ k, (2 ≤ d (eventPos k + 2)) ↔ y k = true)            -- labels exactly y
```

Machine-checked, axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`.

**The simplification.** The previous round padded a *variable* number of `1`s to restore a deficit
reserve, which forced a recursive state, a termination argument, and a separate prefix-compatibility
lemma. None of that is needed: a **fixed** seven-digit block already fits inside the corridor on its
own, and its total valuation is at most `10 < 11 ≤ ⌊7α⌋`, so blocks simply concatenate. The witness
is a closed form with no recursion at all.

**Where this stops.** LEVEL 3 (2-adic realization) is *not* formalized — the repository has no
`PadicInt` or infinite-word realizer development to connect to. LEVEL 4 (positive ordinary integer)
is deliberately not proved and must not be inferred.

---

## A. Starting state

| | |
|---|---|
| branch point | `chang-infinite-compatibility` = `7b10c6d342ddcda1d49b136f369dcf7c41460729` |
| new branch | `chang-infinite-compatibility-formal` |
| worktree | isolated; Mathlib shared by read-only symlink |

Both hashes in the brief were **verified against `origin`, not trusted**:
`chang-cross-scale-realizer-audit = 522714a16622c0fd49232b039ba07df536ce5193` ✓ and
`chang-infinite-compatibility = 7b10c6d342ddcda1d49b136f369dcf7c41460729` ✓.

Ordinary checkout on `research-sparse-visits-2026-09-16`, 53 dirty files, untouched. `main`
(`1c4d6700`) unmodified.

## B. Existing Lean inventory

### `EOC/ChangHistory.lean` — the observable (unchanged, reused)

| declaration | statement |
|---|---|
| `a_ge_two_iff` | `2 ≤ a n ↔ n % 4 = 1` |
| `a_eq_one_iff` | `a n = 1 ↔ n % 4 = 3` |
| `a_eq_two_iff` | `a n = 2 ↔ n % 8 = 1` |
| `event_iff` | `n % 16 = 9 ↔ a n = 2 ∧ a (T n) = 1` |
| `label_iff` | `n % 16 = 9 → (n % 32 = 25 ↔ 2 ≤ a (T (T n)))` |
| `changBlock` | `if b then [2,1,2] else [2,1,1]` |
| `changWord_S` | `S (changWord ys) (3 * ys.length) = 4 * ys.length + ys.count true` |
| `finite_chang_history_realizable`, `every_finite_history_is_a_consecutive_chang_history` | finite universality, **without** corridor confinement |

`event_iff`/`label_iff` are what make "Chang event at `j`" equal to "`(d_j,d_{j+1}) = (2,1)`" and
"label 1" equal to "`d_{j+2} ≥ 2`". This round uses that translation and does not re-derive it.

### `EOC/ChangZeroCorridor.lean` — Gate 1 inventory

| declaration | Lean type | meaning | kind | deps |
|---|---|---|---|---|
| `burstCount` | `(ℕ → ℕ) → ℕ → ℕ` | `#{t < k : 2 ≤ d t}` | definition | — |
| `add_burstCount_le_S` | `(∀ i, 1 ≤ d i) → k + burstCount d k ≤ s d k` | each burst costs an extra unit | **digit-sum inequality** | — |
| `burstCount_le_of_confined` | `… → (s d k : ℝ) ≤ alpha * k → (burstCount d k : ℝ) ≤ (alpha − 1) * k` | corridor caps Chang burst density | **zero confinement** (weak form `S ≤ αk`) | above |
| `floor_alpha` | `⌊alpha⌋ = 1` | — | **Beatty arithmetic** | `one_lt_alpha`, `alpha_lt_two` |
| `changWord_zero`, `changWord_S_one` | `changWord ys 0 = 2`, `s (changWord ys) 1 = 2` | canonical block head | event control | `ChangHistory` |
| `changWord_not_zeroConfined` | `ys ≠ [] → ¬(∀ j ≥ 1, s (changWord ys) j ≤ ⌊jα⌋)` | canonical words miss the corridor | **zero confinement**, negative | above |

### `EOC/ChangInfiniteCompatibility.lean` — previous round

`three_halves_lt_alpha`, `alpha_lt_eight_fifths`, `floor_two_alpha (⌊2α⌋ = 3)`,
`floor_three_alpha (⌊3α⌋ = 4)`, `beatty_two_step`, `beatty_three_step`,
`le_floor_succ_of_le_floor`, `emitZero_cost`, `emitOne_cost`, `recharge_two`, `emit_first_step`.

**What was present versus missing for the infinite builder.** Present: the Beatty budget lemmas and
the per-gadget cost inequalities. Missing: everything that turns them into a sequence — a definition
of the infinite word, a prefix-sum bound valid at *every* index, event-position control, label
correctness, and the assembly. This round supplies all of those, and in doing so found that the
cost/recharge lemmas are **not needed** by the simpler construction (see §C); they remain as
reusable Beatty arithmetic, and `alpha_lt_eight_fifths` is used.

### 2-adic / infinite-word machinery

Searched for `Phi`, `PadicInt`, `ℤ_[2]`, `Stream`, infinite valuation word, prefix realizer.
**None exists.** `EOC/RealizerLift.lean` mentions "2-adic separation lower bound" in prose only.
`EOC/ZCRERealizerGrowth.lean` works with `d : ℕ → ℕ` and `leastRealizer d N`, i.e. finite prefixes.
So there is no 2-adic abstraction to reuse, and none was invented (§P).

## C. Mathematical construction

The previous round's construction maintained a deficit reserve `Δ ≥ 2`, emitted `(2,1,1)` or
`(2,1,3)`, and padded with a *variable* number of `1`s to recharge. The key observation of this
round removes the variability:

> **The seven-digit block `(1,1,1,1,2,1,x)` with `x ∈ {1,3}` is zero-confined on its own, and its
> valuation sum is `8` or `10`, both `< 11 ≤ ⌊7α⌋`.**

Block partial sums against the corridor allowance:

| `r` | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|---|---|---|
| partial sum `p r` | 0 | 1 | 2 | 3 | 4 | 6 | 7 | `7+x` |
| allowance `⌊rα⌋` | 0 | 1 | 3 | 4 | 6 | 7 | 9 | 11 |

`p r ≤ ⌊rα⌋` holds termwise, and at `r = 7` gives `7 + x ≤ 11` since `x ≤ 3`. Because each block
*gains* at least `1` of deficit (`11 − 10`), blocks concatenate freely. So there is no reserve to
track, no recharge to schedule, and no recursion:

```
changSeq y i = blockDigit (i % 7) (y (i / 7))
blockDigit r b = if r = 4 then 2 else if r = 6 then (if b then 3 else 1) else 1
```

Digit `2` occurs only at `r = 4`; it is followed by `r = 5`, always `1`. So events are exactly the
positions `≡ 4 (mod 7)` — **no spurious events**, and the label at `7k+4` is read off the digit at
`7k+6`, which is `3` or `1` according to `y k`.

`x = 3` rather than the canonical `2` is what makes this work: with `2` the pair `(2,1)` would
re-form at offset 6 against the next block's leading `1`, emitting an unwanted event. This was the
correction identified in the previous round, and it is what the fixed-block layout needs.

## D. State invariant

**There is no state.** `changSeq` is a closed form, so the fields a recursive builder would have
carried — prefix, depth, cumulative valuation, deficit, emitted history, endpoint flag — are all
derivable:

| would-be field | replaced by |
|---|---|
| depth `n` | the index `i` |
| block number | `i / 7` |
| offset in block | `i % 7` |
| cumulative `S_n` | `s (changSeq y) n`, bounded by `s_le` |
| deficit `Δ_n ≥ 2` | not needed — the block is self-confined |
| emitted history | `y` itself |
| endpoint condition | `changSeq_event_iff`, an `iff` over all `i` |

The induction in `s_le` carries the single invariant `S_n ≤ 10·(n/7) + p(n % 7)`, which is the
minimal statement strong enough to close.

## E. Recharge theorem

**Not needed, and therefore not proved in this round.** The fixed block is self-financing: each
block consumes at most `10` and is allowed `11`, so deficit is non-decreasing across blocks and no
recharge phase exists.

The previous round's recharge lemmas remain available and correct —
`ChangInfiniteCompatibility.recharge_two` (`S ≤ ⌊Nα⌋ → S + 3 ≤ ⌊(N+2)α⌋`, i.e. two padding `1`s
gain a unit) and `le_floor_succ_of_le_floor` (appending `1` preserves confinement) — and
`le_floor_succ_of_le_floor` still answers Gate 2's separate question: *every* finite zero-confined
word extends to an infinite one.

The Beatty fact behind recharge, *no two consecutive increments are both `1`*, is
`beatty_two_step : ⌊Nα⌋ + 3 ≤ ⌊(N+2)α⌋`, proved from `⌊2α⌋ = 3`. It is verified in Lean and is
what would give the explicit bound Gate 8 asks for (shortfall `q` repaired in `≤ 2q` steps) if the
variable-padding route were ever needed again.

## F. Label-0 emission

Absorbed into the uniform block. The label-0 block is `(1,1,1,1,2,1,1)`, valuation `8`:

- **confinement** — `s_le` plus `floor_ge`, covering every internal offset (§L);
- **label** — `changSeq_label`, with `changSeq y (7k+6) = 1 < 2`;
- **no unintended event** — `changSeq_event_iff`, an `iff` that rules out every position not `≡ 4`;
- **ending deficit** — the block spends `8` of an allowance `11`, so deficit gains `≥ 3`.

The previous round's standalone statement `emitZero_cost : S ≤ ⌊Nα⌋ → S + 4 ≤ ⌊(N+3)α⌋` remains in
`ChangInfiniteCompatibility`.

## G. Label-1 emission

Block `(1,1,1,1,2,1,3)`, valuation `10`, same four properties, with
`changSeq y (7k+6) = 3 ≥ 2` giving label `1` and a deficit gain of `≥ 1`.

Safety of the following digit is not a side condition here but part of `changSeq_event_iff`: the
digit after the block is the next block's leading `1`, and `(3,1)` is not the pair `(2,1)`.

The negative curiosity — why `(2,1,2)` followed by `1` is unsafe — is documented in the module
header and in §C, and **not formalized**, per Gate 5's guidance.

## H. Unified emission step

The `Bool` parameter enters through `blockDigit`, so a single definition covers both labels and a
single theorem covers both cases. `changSeq_event_iff` and `changSeq_label` are already the unified
pre/post-condition pair; there are no per-label proofs to unify.

## I. Finite encoder

`finite_history_realized (ys : List Bool)` — for every finite label list there is a zero-confined
valuation sequence with events exactly at `7k+4` whose first `ys.length` labels are `ys`. Proved by
specializing the infinite theorem at `fun i => ys.getD i false`.

Length bound: the first `K` labels are complete by index `7K`, and the total valuation of the first
`K` blocks is `7K + Σ x_i ≤ 10K`, explicitly bounded. This subsumes the previous rounds'
computational universality checks (`K ≤ 11`).

## J. Prefix compatibility

**True by construction, definitionally.** `changSeq y i` depends on `y` only through `y (i / 7)`,
so for `i < 7K` the digit is unchanged by any modification of `y` at indices `≥ K`. There is no
encoder whose outputs must be shown to nest, which is exactly the obligation the variable-padding
construction created and this one avoids. No lemma is needed, and none was written.

## K. Infinite builder

`changSeq : (ℕ → Bool) → ℕ → ℕ`, the repo-native representation (`ZCRERealizerGrowth`,
`Confinement` and `Realizer` all use `ℕ → ℕ`). No stream framework imported. Every position is
fixed outright rather than in a limit, so "eventually fixed" is trivial.

## L. Global zero confinement

```
changSeq_zeroConfined (y) (n) : (s (changSeq y) n : ℤ) ≤ ⌊(n : ℝ) * alpha⌋
```

quantified over **all** `n`, so every intermediate position inside a block is covered, not just
block boundaries. Proof in two halves:

- `s_le : (s (changSeq y) n : ℤ) ≤ 10 * (n / 7) + part (n % 7)` — induction on `n`, splitting on
  whether the step closes a block (`n % 7 = 6`, where the digit is `≤ 3`) or advances inside one
  (where `part` advances by exactly the block digit);
- `floor_ge : 11 * (n / 7) + cap (n % 7) ≤ ⌊nα⌋` — from `⌊7α⌋ = 11` via superadditivity of the
  floor, with `cap r = ⌊rα⌋` tabulated;
- combined with `part_le_cap : part r ≤ cap r` and `n / 7 ≥ 0`.

A formalization note worth recording: `push_cast` rewrites `((n / 7 : ℕ) : ℤ)` into the **ℤ-division**
`(↑n / 7)`, after which the two sides of the cast lemma no longer match. `floor_ge` abstracts the
quotient and remainder with `set` before any casting; the module comments this so the trap is not
re-hit.

## M. Exact Chang-history realization

Event indexing is explicit: `eventPos k = 7 * k + 4`.

| theorem | statement |
|---|---|
| `changSeq_eq_two_iff` | `changSeq y i = 2 ↔ i % 7 = 4` |
| `changSeq_event_iff` | `(changSeq y i = 2 ∧ changSeq y (i+1) = 1) ↔ i % 7 = 4` |
| `not_event_of_ne` | `i % 7 ≠ 4 → ¬(event at i)` — **no spurious events** |
| `eventPos_is_event` | every `eventPos k` is an event |
| `eventPos_strictMono` | `eventPos` is strictly increasing |
| `changSeq_label` | `2 ≤ changSeq y (eventPos k + 2) ↔ y k = true` |

"The Chang label sequence equals `y`" means precisely: the events are exactly `{7k+4 : k ∈ ℕ}`,
enumerated in increasing order by `eventPos`, and the label at the `k`-th of them is `y k`. Both
halves are `iff`s over all indices, so nothing is hidden in prose — in particular
`changSeq_event_iff` being an `iff` is what rules out extra events, which a one-directional
statement would not.

Event/label are expressed in the digit form that `ChangHistory.event_iff` and `label_iff` equate to
`m_j ≡ 9 (mod 16)` and `m_j ≡ 25 (mod 32)`. That equivalence is about an orbit of a realizer; since
LEVEL 4 is not established here, the digit form is the honest one to state, and it is the one used.

## N. Event spacing

**Proved, and exact rather than a bound:** `eventPos_succ_sub (k) : eventPos (k+1) − eventPos k = 7`.

So the uniform constant of Gate 14 is `L = 7`, and `eventPos k = 7k + 4` exactly. This replaces the
previous round's empirical range 3.10–5.22 steps per label with a theorem, and it establishes that
the history is realized at **positive event density** `1/7`, not by sparse coding.

## O. Full-shift formulation

`chang_zero_corridor_full_shift` is stated in repo-native terms (`s`, `alpha`, `ℕ → ℕ`) with
explicit event indexing. It is the factor statement in substance: the zero-corridor valuation space
surjects onto `{0,1}^ℕ` under the Chang observable read along `eventPos`.

**No symbolic-dynamics framework was imported.** Per Gate 21, topological or shift-space
abstractions would add terminology without changing the content, so the theorem is stated directly.
The word "factor" appears only in prose.

## P. 2-adic realizer bridge

**Not formalized. Status: absent from the repository, not merely unproved here.**

There is no `Phi`, `PadicInt`, `ℤ_[2]` or infinite-word realizer development anywhere in `EOC/`
(§B). `Realizer.realizerCongruence` pins prefix realizers modulo `2^{S_N+1}`, and those classes are
nested with `S_N → ∞`, so mathematically they determine a unique 2-adic integer — but turning that
into Lean means building the 2-adic interface first, which is a project of its own and was not
started here.

Accordingly the report's claim is weakened as Gate 24 directs: the chain is formalized from
`y : ℕ → Bool` to an explicit zero-confined valuation sequence with exact Chang history, and the
2-adic step is stated mathematically but **not machine-checked**.

## Q. Positive-integer boundary

**Not proved, not claimed, and explicitly guarded.**

Nothing here asserts that `changSeq y` is the valuation word of a Collatz orbit of a positive
integer. The theorem quantifies over valuation *sequences*; the corridor constrains the *word*,
whereas positivity is a constraint on the *seed*.

The module carries a named guard, `level_four_not_established`, whose docstring states that LEVEL 4
is deliberately unproved and must not be inferred — so a future reader following the file cannot
silently collapse LEVEL 3 into LEVEL 4 (Gate 18's requirement).

## R. ZCRE relation

`ZCRERealizerGrowth.boundedPrefixRealizers_iff_positiveRealizer (d) (hd_pos : ∀ i, 1 ≤ d i)`:

```
(∃ M, ∀ N, leastRealizer d N ≤ M)  ↔  (∃ m₀, Odd m₀ ∧ ∀ i, a (orbit m₀ i) = d i)
```

with `leastRealizer_eventually_constant_of_bounded` and
`leastRealizer_eq_mod_of_realizes : leastRealizer d N = m₀ % 2^(S d N + 1)`.

`changSeq y` satisfies the hypothesis `∀ i, 1 ≤ d i` (`changSeq_pos`), so the equivalence *applies*
to it. **Does the construction give any theorem about prefix-realizer boundedness? No.**

Nothing in this round bounds `leastRealizer (changSeq y) N`, and there is no reason to expect a
bound: the equivalence would then hand back a positive-integer realizer for an *arbitrary* `y`,
which is exactly the unresolved boundary. The expected answer was NO and no theorem was
manufactured.

## S. Local-factor status

```
chang_local_factor (d d' : ℕ → ℕ) (j : ℕ)
    (h0 : d j = d' j) (h1 : d (j+1) = d' (j+1)) (h2 : d (j+2) = d' (j+2)) :
    ((d j = 2 ∧ d (j+1) = 1) ↔ (d' j = 2 ∧ d' (j+1) = 1)) ∧ ((2 ≤ d (j+2)) ↔ (2 ≤ d' (j+2)))
```

**Radius exactly 3**: the event uses `(d_j, d_{j+1})`, the label uses `d_{j+2}`. This packages the
observation that Chang is a finite-radius factor of the valuation sequence and therefore cannot
carry information the sequence does not. It depends on **no axioms at all**.

## T. Theorem dependency map

```
eleven_sevenths_lt_alpha  (3^7 = 2187 > 2048 = 2^11)
alpha_lt_eight_fifths     (3^5 = 243 < 256 = 2^8)   [ChangInfiniteCompatibility]
        └─> alpha_bounds
                ├─> floor_cap  (⌊rα⌋ for r ≤ 7: 0,1,3,4,6,7,9,11)
                │       └─> floor_ge ──┐
                └─> floor_ge           │
                                       ├─> changSeq_zeroConfined ──┐
part / part_le_cap / part_succ         │                           │
blockDigit_le_three ──> s_le ──────────┘                           │
                                                                   │
changSeq_eq_two_iff ──> changSeq_event_iff ────────────────────────┤
changSeq_succ_of_four ─┘                                           ├─> chang_zero_corridor_full_shift
blockDigit_pos ──> changSeq_pos ───────────────────────────────────┤        │
changSeq_label ────────────────────────────────────────────────────┘        └─> finite_history_realized

chang_local_factor        (independent; no axioms)
eventPos_succ_sub         (independent; spacing = 7)
```

Note that `floor_two_alpha`/`floor_three_alpha` and the emission-cost lemmas of the previous round
are **not** on this path — the fixed-block construction bypasses them. They remain as reusable
Beatty arithmetic.

## U. Axiom audit

```
EOC.ChangFullShift.chang_zero_corridor_full_shift : [propext, Classical.choice, Quot.sound]
EOC.ChangFullShift.changSeq_zeroConfined          : [propext, Classical.choice, Quot.sound]
EOC.ChangFullShift.changSeq_event_iff             : [propext, Quot.sound]
EOC.ChangFullShift.changSeq_label                 : [propext, Classical.choice, Quot.sound]
EOC.ChangFullShift.finite_history_realized        : [propext, Classical.choice, Quot.sound]
EOC.ChangFullShift.eleven_sevenths_lt_alpha       : [propext, Classical.choice, Quot.sound]
EOC.ChangFullShift.floor_cap                      : [propext, Classical.choice, Quot.sound]
EOC.ChangFullShift.s_le                           : [propext, Classical.choice, Quot.sound]
EOC.ChangFullShift.floor_ge                       : [propext, Classical.choice, Quot.sound]
EOC.ChangFullShift.eventPos_succ_sub              : [propext, Quot.sound]
EOC.ChangFullShift.chang_local_factor             : does not depend on any axioms
```

Standard Mathlib axioms only. `grep -nE '\bsorry\b|\badmit\b|^axiom |\bopaque\b'` on the new module
returns only the header disclaimer line.

## V. Build/test status

| command | result |
|---|---|
| `lake build EOC.ChangHistory` | success, **1137 jobs** |
| `lake build EOC.ChangZeroCorridor` | success, **2040 jobs** |
| `lake build EOC.ChangInfiniteCompatibility` | success, **2041 jobs** |
| `lake build EOC.ChangFullShift` | success, **2042 jobs**, 0 errors |

No unrelated file was modified to repair anything.

Independent cross-check by `#eval`: for `y k = (k % 3 == 0)` the first 21 digits are
`[1,1,1,1,2,1,3, 1,1,1,1,2,1,1, 1,1,1,1,2,1,1]` and the event positions are `[4, 11, 18]` — exactly
matching the construction tested in Python over 320 histories (all-1s, all-0s, alternating,
periodic, 60 random, and all `2^8` histories of length 8), with zero confinement violations, zero
spurious events, and exact label agreement in every case.

## W. Files changed

```
new:  EOC/ChangFullShift.lean                                   27 declarations
new:  docs/CHANG_INFINITE_COMPATIBILITY_FORMALIZATION.md        this report
```

`EOC/ChangZeroCorridor.lean` and `EOC/ChangInfiniteCompatibility.lean` were **not** modified — the
new material lives in its own module, keeping the finite arithmetic/gadget lemmas separate as the
brief directs. No existing Lean file changed; no theorem statement altered.

## X. Commits

Branch `chang-infinite-compatibility-formal`, from `7b10c6d`.

| commit | contents |
|---|---|
| `c53e97d` | `EOC/ChangFullShift.lean` |
| (this file) | this report |

## Y. Push status

Branch pushed to `origin/chang-infinite-compatibility-formal`. **No pull request opened.** `main`
unmodified; dirty ordinary checkout untouched.

## Z. Remaining formal gap

Two, both stated rather than papered over:

1. **The 2-adic bridge (LEVEL 3) is not formalized** (§P). It needs a 2-adic realizer interface
   that does not exist in the repository. Mathematically routine; a real piece of work in Lean.
2. **The bridge from the digit form of the observable to Chang's congruence form is not
   instantiated for `changSeq`.** `ChangHistory.event_iff` and `label_iff` equate
   `(d_j,d_{j+1}) = (2,1)` with `m_j ≡ 9 (mod 16)` *along an orbit*; since `changSeq y` is not
   known to come from a seed, there is no orbit to instantiate them at. This is not a defect of the
   construction — it is LEVEL 4 again, seen from the observable's side.

Neither gap affects the headline theorem, which is stated entirely in digit terms.

## AA. Research closure

**Chang is now formally closed at the positive-integer boundary, with LEVEL 3 documented but not
machine-checked.**

Levels 1 and 2 are machine-checked: every finite label list (`finite_history_realized`) and every
infinite binary sequence (`chang_zero_corridor_full_shift`) is realized by an explicit zero-confined
valuation sequence, with events exactly at `7k+4`, no spurious events, and uniform spacing 7. The
observable is proved to be a radius-3 local factor (`chang_local_factor`).

Level 3 is mathematically available and blocked only by missing repository infrastructure (§P).
Level 4 is not proved, is guarded in the module, and is where the route ends: the corridor
constrains the word, positivity constrains the seed, and no result here crosses between them.

The next frontier is therefore exactly as the brief anticipated — *what arithmetic or Archimedean
property distinguishes the positive ordinary integers among the compatible 2-adic realizers?* — and
it is **not pursued in this branch**.

---

## Research verdict

**`INFINITE SYMBOLIC FULL SHIFT FORMALIZED`**

The deepest rigorously completed level. LEVEL 1 (finite) and LEVEL 2 (infinite symbolic) are
machine-checked with standard axioms; LEVEL 3 (2-adic) is not formalized because the repository has
no 2-adic interface to build on (§P), so `INFINITE SYMBOLIC + 2-ADIC REALIZATION FORMALIZED` would
overstate what is checked; and `CHANG FORMALLY CLOSED AT POSITIVE-INTEGER BOUNDARY` would suggest
the full chain including the 2-adic step had been verified, which it has not.
