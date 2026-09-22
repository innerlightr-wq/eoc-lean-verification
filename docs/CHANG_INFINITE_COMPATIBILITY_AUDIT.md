# Chang infinite compatibility and the positive-integer boundary

Follow-up to [`docs/CHANG_CROSS_SCALE_REALIZER_AUDIT.md`](CHANG_CROSS_SCALE_REALIZER_AUDIT.md),
which found finite Chang universality inside the exact zero corridor computationally for `K ≤ 11`.

**Question.** What happens when the quantifiers change from *for every finite history there exists
a finite zero-confined realization* to *for one infinite history, one infinite zero-confined
sequence* — and then to *one fixed positive integer*?

**Answer: Chang reaches the first three levels of the hierarchy and stops at the fourth.**

| level | status |
|---|---|
| 1. finite history | **universal** — previous round `K ≤ 11`; now superseded by an explicit construction |
| 2. infinite symbolic history | **universal, constructively** — bounded gadget, bounded spacing, no compactness needed (§H, §I) |
| 3. 2-adic realizer | **universal** — every infinite zero-confined word has a 2-adic realizer (§P) |
| 4. positive ordinary integer | **Chang is silent** (§Q) |

The construction that settles level 2 is a three-digit emission block plus padding with `1`s, and
its arithmetic core is now formalized (`EOC/ChangInfiniteCompatibility.lean`, 9 theorems). One
subtlety had to be fixed to make it work at all: the canonical label-1 block `(2,1,2)` followed by
a padding `1` creates a **spurious Chang event**; replacing it with `(2,1,3)` keeps the label and
removes the event.

All five of Gate 30's stop conditions now hold.

---

## A. Starting state

| | |
|---|---|
| branch point | `chang-cross-scale-realizer-audit` = `522714a16622c0fd49232b039ba07df536ce5193` (fetched and verified) |
| new branch | `chang-infinite-compatibility` |
| worktree | isolated; Mathlib shared by read-only symlink |

**A correction to the brief's premise, recorded for accuracy.** The brief states that
`EOC/ChangZeroCorridor.lean` exists and builds on that branch. When this round began, the branch
pointed at `71d7609` and **nothing was committed** — the previous round was interrupted before its
report was written or its work committed. That round was therefore completed first (report written,
work committed as `522714a`, pushed), and this round branches from the resulting real tip. The
module and its build/axiom status are as the brief describes; only the commit state differed.

Ordinary checkout on `research-sparse-visits-2026-09-16`, 53 dirty files, untouched. `main`
(`1c4d6700`) unmodified.

## B. New ChangZeroCorridor Lean inventory

Read in full. **Five declarations.** Stated exactly, without inferring more than is proved:

| declaration | exact statement | concerns |
|---|---|---|
| `burstCount (d : ℕ → ℕ) (k : ℕ) : ℕ` | `((range k).filter (fun t => 2 ≤ d t)).card` | definition — Chang's burst count in valuation coordinates |
| `add_burstCount_le_S` | `(∀ i, 1 ≤ d i) → k + burstCount d k ≤ s d k` | a **numerical inequality** on digit sums; no confinement, no floors |
| `burstCount_le_of_confined` | `(∀ i, 1 ≤ d i) → (s d k : ℝ) ≤ alpha * k → (burstCount d k : ℝ) ≤ (alpha − 1) * k` | zero confinement (in the weak form `S ≤ αk`, **not** `S ≤ ⌊αk⌋`) |
| `floor_alpha` | `⌊alpha⌋ = 1` | `⌊α⌋` only |
| `changWord_not_zeroConfined` | `ys ≠ [] → ¬ (∀ j, 1 ≤ j → (s (changWord ys) j : ℝ) ≤ ⌊(j:ℝ) * alpha⌋)` | **canonical Chang words**; a non-existence statement |

Supporting: `changWord_zero` (`changWord ys 0 = 2`), `changWord_S_one` (`s (changWord ys) 1 = 2`).

**What it does not prove.** Nothing about arbitrary histories, and **no existence of witnesses**.
`changWord_not_zeroConfined` is negative — it says the *canonical* construction misses the
corridor. There is no finite-universality theorem in the file.

**Reusable declarations in `EOC/ChangHistory.lean`** (exact names):
`a_ge_two_iff : 2 ≤ a n ↔ n % 4 = 1`; `a_eq_one_iff : a n = 1 ↔ n % 4 = 3`;
`a_eq_two_iff : a n = 2 ↔ n % 8 = 1`; `T_of_a_eq_one`, `T_of_a_eq_two`;
`event_iff : n % 16 = 9 ↔ a n = 2 ∧ a (T n) = 1`;
`label_iff : n % 16 = 9 → (n % 32 = 25 ↔ 2 ≤ a (T (T n)))`;
`changBlock`, `changWordList`, `changWord`, `changWord_S : S (changWord ys) (3 * ys.length) = 4 * ys.length + ys.count true`;
`changSeed`, `changSeed_realizes`, `changSeed_lt`; `chang_history_labels`;
`changWord_event_positions`, `chang_event_positions`, `no_internal_chang_event`;
`finite_chang_history_realizable`; `every_finite_history_is_a_consecutive_chang_history`.

From `EOC/CurryFoundation.lean`: `beatty_gap_mem`, `deficit`, `deficit_succ`, `deficit_succ_le`,
`alpha_lt_two`. From `EOC/Confinement.lean`: `alpha`, `R`, `one_lt_alpha`.

## C. Finite zero-corridor universality status

`K = 11` completed: **2048/2048**, full universality (the run finished after the previous report
was drafted; recorded here).

**The Lean file does not prove finite universality** (§B), so per Gate 1 the gap had to be
identified. It is now closed by a stronger route: §H gives an explicit construction that realizes
*any* finite or infinite history, superseding the brute-force search entirely. **No further
brute-force `K` was run**, as Gate 1 directs.

## D. Extendibility of zero-confined words

**Proved and formalized** (`le_floor_succ_of_le_floor`).

If `S ≤ ⌊Nα⌋` then `S + 1 ≤ ⌊(N+1)α⌋`, because `⌊(N+1)α⌋ ≥ ⌊Nα⌋ + ⌊α⌋ = ⌊Nα⌋ + 1` (using
`⌊x⌋ + ⌊c⌋ ≤ ⌊x+c⌋` and `⌊α⌋ = 1`). So appending the digit `1` always preserves zero confinement.

**Corollary.** Every finite zero-confined valuation word has an infinite zero-confined extension —
append `1`s forever.

**This is purely symbolic.** It asserts nothing about positive-integer realizability, and the
all-`1`s tail is exactly the kind of word whose realizer behaviour is unconstrained by the corridor.

## E. Infinite-history prefix tree

Nodes: finite zero-confined words whose *determined* Chang labels agree with the corresponding
prefix of `y`. "Determined" matters: the label at event `j` needs `d_{j+2}`, so a word of length
`L` determines labels only for events with `j + 2 < L` — the same endpoint convention as
`ChangHistory` (whose canonical word controls event status through `j = 3K−2`, first uncontrolled
event at `j = 3K−1`).

The tree is **prefix-closed** by construction (a prefix of a zero-confined word is zero-confined,
and dropping the tail only removes determined labels). Every level relevant to `K` is nonempty by
§H. Branching is finite by §F.

## F. Finite branching

Under zero confinement the next digit is bounded: `S_{N+1} = S_N + d_N ≤ ⌊(N+1)α⌋` forces

```
d_N  ≤  ⌊(N+1)α⌋ − S_N  =  Δ_N + b_{N+1},     b_{N+1} ∈ {1,2}  (beatty_gap_mem),
```

so `1 ≤ d_N ≤ Δ_N + 2`. Each node has at most `Δ_N + 2` one-digit extensions — **finite**. This is
the repository's `deficit_succ` read as a bound rather than a recurrence.

## G. Compactness / König argument

Available but **not used**, and the reason is worth recording because Gate 6 warns against
invoking it silently.

König needs an infinite, finitely-branching tree *all of whose nodes are admissible prefixes*. §F
gives finite branching and §E prefix-closure, so the argument would be valid **provided** every
level is nonempty — which is exactly what finite universality would have to supply, and finite
universality as established in the previous round was computational (`K ≤ 11`) rather than proved.
Compactness would therefore have converted a finite computation into an infinite claim on the
strength of an unproved premise.

The witness-compatibility obstruction Gate 6 raises is real: a witness for `y|K+1` need not extend
a witness for `y|K`. §H avoids the issue entirely by making the witnesses nested by construction.

## H. Infinite symbolic Chang universality

> **Theorem (Zero-Corridor Chang Full-Shift Factor).** For every infinite binary sequence
> `y ∈ {0,1}^ℕ` there is an infinite valuation word `D` with `d_i ≥ 1` such that
> `S_j(D) ≤ ⌊jα⌋` for every `j ≥ 1`, and the sequence of Chang labels of `D` — read at every
> position `j` with `(d_j, d_{j+1}) = (2,1)`, in order — is exactly `y`.

*Construction.* Write `Δ_N = ⌊Nα⌋ − S_N`. Maintain the invariant `Δ ≥ 2`.

- **Initialise.** Append `1,1`. Then `Δ_2 = ⌊2α⌋ − 2 = 3 − 2 = 1`; continue appending `1`s until
  `Δ ≥ 2`.
- **Emit label 0:** append `(2,1,1)`, total valuation 4.
- **Emit label 1:** append `(2,1,3)`, total valuation 6.
- **Recharge:** append `1`s until `Δ ≥ 2` again.

*Corridor preservation.* The three-step Beatty budget is `⌊(N+3)α⌋ − ⌊Nα⌋ ≥ ⌊3α⌋ = 4`
(`beatty_three_step`), so the label-0 block costs nothing (`emitZero_cost`) and the label-1 block
costs at most 2 (`emitOne_cost`). Intermediates: after the first digit `2` a reserve of 1 suffices
(`emit_first_step`); after the second digit the two-step budget `⌊(N+2)α⌋ − ⌊Nα⌋ ≥ ⌊2α⌋ = 3`
(`beatty_two_step`) has already restored the loss. Padding never decreases `Δ`
(`le_floor_succ_of_le_floor`), and any two consecutive padding digits gain at least one unit
(`recharge_two`), so the reserve is restored in at most four padding steps.

*No spurious events.* A Chang event is a digit pair `(2,1)`. In the emitted stream the only `2`s
are the block heads, each followed by `1` — the intended events. The digit after a block is either
`1` (preceded by `1` or `3`, giving `(1,1)` or `(3,1)`, neither an event) or the next block head
`2` (preceded by `1` or `3`, giving `(1,2)` or `(3,2)`, neither an event). **This is where `(2,1,3)`
is needed:** with the canonical `(2,1,2)`, the third digit `2` followed by a padding `1` forms the
pair `(2,1)` and emits an unwanted event. `ChangHistory`'s canonical word escapes this only because
the next block starts with `2` — which forbids padding, and padding is what the corridor requires.

*Validation.* 44 histories of length 40 (all-`1`s, all-`0`s, alternating, periodic `110`, and 40
random) were constructed and checked: every word zero-confined at every prefix, every label
sequence **exactly** equal to the target, **no spurious events** (event count equals history
length in every case).

**Status: proved, with the arithmetic core formalized and the assembly not.** The four cost/budget
lemmas are Lean theorems (§AA); the induction that threads them into the infinite word is written
out above but not formalized, because it needs a recursive word-builder with a carried invariant.
That is stated as remaining work, not glossed.

**It is a statement about valuation words only.** It is not an orbit theorem.

## I. Constructive gadget alternative

§H *is* the constructive alternative, and it is strictly better than the compactness route: it is
uniform in `y`, needs no unproved level-nonemptiness premise, and yields bounded spacing (§L),
which König would not give.

The gadget in Gate 16's requested form: with state `q = Δ` (the deficit reserve, an integer),

```
Δ ≥ 2  --G_0-->  Δ' ≥ 2        G_0 = (2,1,1)            emits label 0
Δ ≥ 2  --G_1-->  Δ' ≥ 0        G_1 = (2,1,3)            emits label 1
Δ      --pad-->  Δ + 1         two digits 1             restores reserve
```

Gadget length is uniformly bounded (3 emit + ≤ 4 pad), and the state is a single integer
thresholded at 2 — a genuinely finite-state description.

## J. Recharge mechanism

`Δ_{N+1} = Δ_N + b_{N+1} − d_N` with `b ∈ {1,2}` (`deficit_succ`, `beatty_gap_mem`). With `d = 1`
the deficit changes by `b − 1 ∈ {0,1}`, so padding is monotone and gains a unit whenever `b = 2`.
Since **no two consecutive gaps are both 1** (`beatty_two_step`: `⌊(N+2)α⌋ − ⌊Nα⌋ ≥ 3`), any two
consecutive padding digits gain at least one unit. The asymptotic density of `b = 2` is
`α − 1 = 0.5849625`, so reserve accumulates linearly under padding.

**Is this ordinary digit freedom?** Largely yes, and that is the honest reading: the corridor is a
one-sided constraint and the minimum digit is 1, so slack accumulates automatically. The content of
§H is not that recharging is possible but that the **emission blocks are cheap enough** (cost ≤ 2)
relative to the recharge rate that the reserve is an invariant — that is what makes the spacing
bounded rather than growing.

## K. Bi-extendible core

Every node with `Δ ≥ 2` is Chang-bi-extendible: §H emits either label from such a node and returns
to `Δ ≥ 2`. The set `{Δ ≥ 2}` is therefore an invariant bi-extendible core, reached from any node
by padding (§J) and never left. Pruning is unnecessary — no node in the core ever loses a branch.

So the zero-corridor valuation dynamics **does** contain a full 2-shift factor, and this rests on
the construction of §H rather than on finite computation.

## L. Event-density / spacing issue

**Bounded spacing, positive density** — so Gate 19's caveat does not bite.

Measured over the 44 validation histories: **3.10 to 5.22 accelerated steps per label, mean 3.61**.
The worst case is bounded a priori by 3 (emit) + 4 (recharge) = 7.

This matters for interpreting the result. Chang's Open Problem concerns burst-ending times, which
occur at positive density in a real orbit; a construction that could only realize labels at
vanishing density would not be commensurable with it. The construction here emits at density
between `1/5.22` and `1/3.10`, comparable to natural event densities, so the full-shift factor is
not an artifact of sparse coding.

## M. Chang labels as a local factor

Established in the previous round and unchanged: the label at event `j` is `1[d_{j+2} ≥ 2]` and the
event indicator is `1[(d_j,d_{j+1}) = (2,1)]`, so **`ChangLabel_j` depends on exactly the window
`(d_j, d_{j+1}, d_{j+2})` — width 3**, via `ChangHistory.event_iff` and `label_iff`. Verified on
14,403 positions with 0 mismatches.

The Chang label process is a finite-radius factor of the valuation sequence. It cannot contain more
raw information than the valuation word; any new arithmetic must come from a theorem, not the
encoding.

## N. Fiber size and information loss

Fibers of the Chang-history map, within matched `(N,S)` shells:

| `N` | `S` | words | distinct histories | max fiber | mean fiber |
|---|---|---|---|---|---|
| 12 | 18 | 2652 | 27 | 700 | 98.2 |
| 13 | 20 | 8045 | 36 | 1937 | 223.5 |
| 14 | 20 | 9592 | 48 | 2118 | 199.8 |
| 14 | 21 | 17637 | 48 | **3824** | 367.4 |

**Fibers grow exponentially.** The observable is extremely lossy: at `(14,21)`, `2^{14.11}` words
map onto `2^{5.58}` histories.

## O. Conditional entropy estimate

Summed over the `k = 14` shells: `log₂(#words) = 72.66`, `log₂(#histories) = 30.13`.

**The Chang history captures 41.5% of the valuation-word entropy; ~59% remains undetermined.**

Knowing `K` Chang bits removes `Θ(K)` bits — not `o(K)`, so the observable is not vacuous — but it
leaves a constant fraction of the word free, and that fraction does not shrink with depth over the
range tested. Finite estimates; not extrapolated.

## P. 2-adic realization

For an infinite valuation word with all digits `≥ 1`, the prefix congruences
`r(D|N) ≡ (2^{S_N} − C_N(D)·3^{−N}) (mod 2^{S_N+1})` (P1 Prop 5.2) are nested and `S_N → ∞`, so
they determine a **unique 2-adic integer**. The repository's `EOC/RealizerLift.lean` records the
`2^{S_N+1}` separation as a lower bound on 2-adic separation.

So level 3 of the hierarchy is universal too: combining with §H, **every infinite binary Chang
history is realized by a zero-confined infinite valuation word, hence by a 2-adic integer.**

What this does **not** give is a positive ordinary integer: the nested classes shrink to a point in
`Z₂`, and nothing forces that point into `Z_{>0}`.

## Q. Positive-integer distinction

**Chang's framework never distinguishes `Z_{>0}` from `Z₂`.** Every object in
arXiv:2603.25753 is congruential — burst indicator (mod 4), gap outcome (mod 8), the observable
(mod 32), the extension index (mod `2^{K+3}`), and the Map Balance Theorem, which counts over
`Z/2^K`. All are invariant under passing to `Z₂`.

The single Archimedean ingredient anywhere is the bit-growth lemma (quoted by Chang from his
companion paper), and it is a *consequence* of the orbit being a positive integer, not a constraint
that could exclude one.

This is the terminal limitation, and it is exactly where the hierarchy breaks: levels 1–3 are
2-adic/symbolic and Chang is universal there; level 4 is Archimedean and Chang is silent.

## R. ZCRE interaction

`ZCRERealizerGrowth.boundedPrefixRealizers_iff_positiveRealizer`, exactly:

```
(∃ M, ∀ N, leastRealizer d N ≤ M)  ↔  (∃ m₀, Odd m₀ ∧ ∀ i, a (orbit m₀ i) = d i)
```

together with `leastRealizer_eventually_constant_of_bounded` and
`leastRealizer_eq_mod_of_realizes : leastRealizer d N = m₀ % 2^(S d N + 1)`.

**Does infinite Chang symbolic realizability add anything?** Of Gate 8's three possibilities, the
first holds:

1. **No.** Chang labels are a width-3 factor of the valuation word (§M), and the ZCRE equivalence is
   already stated for an *arbitrary* word `d` with `d_i ≥ 1`. Adding "…and its Chang labels are `y`"
   restricts which words are considered; it does not change the equivalence, and by §H no label
   sequence is excluded.
2. No history forces prefix-realizer growth — §U.
3. No history is incompatible with eventual realizer constancy — §U.

## S. Spectator-bit activation test

Gate 21's specific question: can continuing activation of new spectator bits force new high bits of
the seed to change forever?

**No — activation reveals bits, it does not require new ones.** Chang's extension index is
`e_i ≡ (n_{t_i} − b)/2^K (mod 8)`: a *read* of digits `K, K+1, K+2` of the orbit value at visit `i`.
For a fixed positive seed `m`, every orbit value `n_t` is determined by `m`, so every `e_i` is a
function of bits already fixed in `m`. Reading further digits of a fixed integer is not a
contradiction with anything; it is just reading.

The distinction Gate 21 asks for is exactly the right one, and it lands on the harmless side:
**revealing fixed bits**, not **requiring incompatible new bits**. Nothing in Chang's framework
produces a constraint of the second kind, and he does not claim one — Proposition 5.16 is
equidistribution "under the ensemble model", with transfer to individual orbits identified by Chang
himself as the open problem.

## T. Nested congruence/lift sets

For a fixed Chang history `h_K`, let `A_K` be the set of compatible seed residues. By §M each
compatible word contributes one residue class (P1 §6's shell injectivity: distinct words in a shell
give distinct residues), so `A_K` is a union of classes, one per word in the fiber.

- **Are the projections `A_{K+1} → A_K` surjective?** Yes — §H extends *any* corridor node with
  `Δ ≥ 2` to emit either next label, and §J shows any node reaches `Δ ≥ 2` by padding. No branch
  dies.
- **Fiber sizes?** Exponentially large (§N): `|A_{K+1}|/|A_K|` grows rather than shrinks.
- **Does a fixed infinite history determine one 2-adic seed?** **No.** A single *word* does (§P),
  but a *history* has exponentially many compatible words, so the compatible 2-adic set is large.
- **No seed?** No — nonempty at every level.

So the nested-lift picture gives the opposite of leverage: the tree branches without bound.

## U. Does any history force realizer growth?

**No history tested forces anything.** Within the shell `(N,S) = (14,21)`, the most populous
history has 3824 compatible words whose `log₂ r` spans `[9.81, 22.00]`, against `[6.15, 22.00]` for
the whole shell. Fixing the history leaves realizer size essentially free.

Structurally this is forced by §H and §N: every history is realizable, with exponentially many
witnesses, so no history can imply unbounded `r_N` or infinitely many distinct `r_N`. The specific
histories Gate 10 lists (all-0s, all-1s, alternating, periodic, high-discrepancy, generic) are all
realized by the construction of §H with bounded spacing — §H's validation set includes the first
four explicitly.

**Gate 11's caution is respected:** a periodic Chang history does *not* force a periodic valuation
word. §H realizes the periodic history `(110)^∞` with padding whose length varies with the local
Beatty pattern, so the valuation word is not periodic. The periodic realizer-floor machinery
(P1 Thm 5.8/5.9) therefore does **not** apply, and was not imported.

## V. Moving-anchor information rate

| quantity | rate |
|---|---|
| A. valuation-word entropy (zero-confined) | ≈ 1.12 bits / accelerated step (measured, `k = 15`) |
| B. zero-corridor entropy rate | same as A |
| C. Chang labels | ≤ 1 bit / event; events at ≥ 1 per 3.1–5.2 steps (§L) ⇒ ≤ 0.32 bits / step |
| D. conditional entropy after labels | ≈ 59% of A ⇒ ≈ 0.66 bits / step (§O) |
| E. residue-space bit growth `S_N` | `α = 1.585` bits / step |

The Chang labels determine at most `C/E ≈ 0.20` of the anchor's bits, and by the measured
conditional entropy (§O) closer to `0.41 × 1.12 / 1.585 ≈ 0.29`. **A bounded fraction, not a growing
one.**

This is a heuristic about information content, not an anti-concentration statement, and it is not
treated as one.

## W. Open Problem D connection

Open Problem D asks for a deterministic arithmetic property of the moving anchor
`−C_N(D)·3^{−N} (mod 2^{S_N})` preventing exceptionally small realizers.

`K` Chang labels constrain at most `K` bits of a quantity living on `S_N ≈ 1.585N` bits, with
`K ≤ N/3.1` (§L), so labels touch at most ≈ 20–29% of the anchor (§V) — and only through a width-3
local factor (§M). **The labels determine a bounded-fraction, local projection of the anchor, so
they cannot directly solve Open Problem D.**

P1 §6's conclusion stands unchanged: any successful pointwise argument must detect arithmetic
information finer than bulk entropy, shell counting, confinement and extreme-value statistics.

## X. New theorem or observation

1. **Zero-Corridor Chang Full-Shift Factor (§H)** — every infinite binary sequence is the Chang
   label sequence of some infinite zero-confined valuation word, by explicit construction, at
   bounded spacing. **Genuinely new**; supersedes the previous round's `K ≤ 11` computation and
   needs no compactness. Arithmetic core formalized; assembly not.
2. **The `(2,1,2)` spurious-event obstruction and its `(2,1,3)` repair (§H)** — the canonical
   `ChangHistory` block cannot be used with padding. **New, elementary, and necessary**: without it
   the construction silently emits extra labels.
3. **`beatty_two_step` / `beatty_three_step` with `3/2 < α < 8/5` (§AA)** — no two consecutive
   Beatty gaps are both 1. Elementary; the repository previously had only `1 < α < 2`. Reusable
   beyond Chang.
4. **Fiber and conditional-entropy measurements (§N, §O)** — the Chang observable leaves ≈59% of
   valuation entropy undetermined, with exponentially growing fibers. New measurements.

**Nothing found constrains positive-integer realization.**

## Y. Closed routes

Adding to the previous round's list, future agents should not retry:

- **compactness arguments over the Chang prefix tree** — unnecessary, since §H is constructive, and
  the nonemptiness premise König needs is exactly what was in doubt (§G);
- **any obstruction from an infinite Chang history** — §H realizes all of them inside the corridor;
- **spectator bits as a source of forced bit-changes** — they read already-fixed digits (§S);
- **using a periodic Chang history to invoke the periodic realizer-floor machinery** — the valuation
  word is not periodic (§U);
- **the canonical `(2,1,2)` block in any padded construction** — it emits spurious events (§H);
- **Chang labels as a route to Open Problem D** — bounded-fraction local projection of the anchor
  (§V, §W).

## Z. Surviving Chang interface

**None that is actionable for EOC.** Every level Chang can reach — finite, infinite symbolic,
2-adic — is universal inside the zero corridor, so Chang imposes no restriction there; and the one
level that matters for ZCRE, positive-integer placement, is outside his framework's expressive
range (§Q).

Chang's own open problem remains open and is unaffected by this audit. What is settled is that it
is not a route to the EOC realizer problem.

## AA. Lean formalization

**New module `EOC/ChangInfiniteCompatibility.lean`**, 9 theorems, no `sorry`/`admit`/`axiom`/
`opaque`.

| theorem | statement |
|---|---|
| `three_halves_lt_alpha` | `3/2 < α` (from `8 < 9`) |
| `alpha_lt_eight_fifths` | `α < 8/5` (from `3^5 = 243 < 256 = 2^8`) |
| `floor_two_alpha` | `⌊2α⌋ = 3` |
| `floor_three_alpha` | `⌊3α⌋ = 4` |
| `beatty_two_step` | `⌊Nα⌋ + 3 ≤ ⌊(N+2)α⌋` — no two consecutive Beatty gaps are both 1 |
| `beatty_three_step` | `⌊Nα⌋ + 4 ≤ ⌊(N+3)α⌋` |
| `le_floor_succ_of_le_floor` | `S ≤ ⌊Nα⌋ → S + 1 ≤ ⌊(N+1)α⌋` — **§D extendibility** |
| `emitZero_cost` | `S ≤ ⌊Nα⌋ → S + 4 ≤ ⌊(N+3)α⌋` — label-0 block is free |
| `emitOne_cost` | `S + 2 ≤ ⌊Nα⌋ → S + 6 ≤ ⌊(N+3)α⌋` — label-1 block costs ≤ 2 |
| `recharge_two` | `S ≤ ⌊Nα⌋ → S + 3 ≤ ⌊(N+2)α⌋` — two padding digits gain a unit |
| `emit_first_step` | `S + 1 ≤ ⌊Nα⌋ → S + 2 ≤ ⌊(N+1)α⌋` — the intermediate step is safe |

(plus the private helper `floor_add_floor_le : ⌊x⌋ + ⌊c⌋ ≤ ⌊x+c⌋`).

**Deliberately not formalized**, per Gate 28: the assembly of §H into an infinite word (needs a
recursive builder carrying the `Δ ≥ 2` invariant — real work, flagged as remaining); the fiber and
entropy measurements (empirical); any spectator-bit interpretation; any positive-integer conclusion.

`ChangZeroCorridor.lean` was **not** modified — the new material lives in its own module, per
Gate 29.

## AB. Files changed

```
new:  EOC/ChangInfiniteCompatibility.lean            9 theorems + 1 private helper
new:  scratch/chang_infinite_compatibility.py        constructive gadget + fiber census
new:  docs/CHANG_INFINITE_COMPATIBILITY_AUDIT.md     this report
```

No existing Lean file modified. No theorem statement changed. No manuscript or PDF edited.

## AC. Tests/build

| command | result |
|---|---|
| `lake build EOC.ChangZeroCorridor` | success, 2040 jobs |
| `lake build EOC.ChangInfiniteCompatibility` | **success, 2041 jobs, 0 errors** |
| `lake build EOC.ChangHistory` | success (no regression) |
| `python3 scratch/chang_infinite_compatibility.py` | exit 0; §H validation, §L spacing, §N/§O fibers |
| grep `sorry`/`admit`/`axiom`/`opaque` | none |

Key numbers: `⌊2α⌋ = 3`, `⌊3α⌋ = 4`; 1-/2-/3-step Beatty gaps `{1,2}`, `{3,4}`, `{4,5}`;
44/44 histories constructed correctly with 0 spurious events; spacing 3.10–5.22 steps/label;
max fiber 3824; conditional-entropy fraction 0.415.

## AD. Axiom audit

All nine headline theorems: `[propext, Classical.choice, Quot.sound]` — the three standard
Mathlib axioms, no custom axiom, no `sorry`.

## AE. Commits

Branch `chang-infinite-compatibility`, from `522714a`.

| commit | contents |
|---|---|
| `347f9b9` | `EOC/ChangInfiniteCompatibility.lean` + `scratch/chang_infinite_compatibility.py` |
| (this file) | this audit report |

## AF. Push status

Branch pushed to `origin/chang-infinite-compatibility`. **No pull request opened.** `main`
unmodified; dirty ordinary checkout untouched.

## AG. Research verdict

**`CHANG PATH CLOSED AT POSITIVE-INTEGER BOUNDARY`**

Earlier milestones reached along the way, listed as Gate 30 requires:

1. **Finite zero-corridor Chang universality** — previous round, `K ≤ 11` computational; now
   superseded by (2).
2. **Infinite symbolic Chang universality, constructively** (§H) — the Zero-Corridor Chang
   Full-Shift Factor, at bounded spacing and positive event density, with its arithmetic core
   formalized. This is the deepest *positive* result of the round.
3. **2-adic universality** (§P) — every such infinite word has a 2-adic realizer.

All five of Gate 30's stop conditions hold: arbitrary finite histories survive exact zero
confinement (§C, §H); arbitrary infinite histories survive symbolically and 2-adically (§H, §P);
the Chang state is a width-3 lossy factor leaving ≈59% of valuation entropy undetermined (§M, §N,
§O); spectator-bit evolution reads already-fixed higher seed bits rather than requiring new ones
(§S); and no Chang quantity constrains positive-integer realization or prefix-realizer stabilization
(§R, §T, §U).

**Where Chang stops is now exact.** He reaches levels 1–3 of the hierarchy — finite, infinite
symbolic, 2-adic — and is universal at all three, which means he imposes *no* restriction there.
Level 4, positive ordinary integer placement, is invisible to a framework whose every object is a
congruence mod `2^K` (§Q).

That is an informative closure rather than a null result: **the missing EOC information is not
finite symbolic freedom, not zero-corridor admissibility, and not 2-adic realizability. It is the
Archimedean placement of the nested realizer** — which is precisely the moving-anchor problem, now
in sharper form. Any future route must supply an Archimedean or positivity-sensitive ingredient;
purely congruential machinery, however deep, cannot.
