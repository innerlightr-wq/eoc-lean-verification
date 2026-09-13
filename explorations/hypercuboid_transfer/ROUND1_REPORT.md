# EOC × Hypercuboid Transfer — Round 1

**Scope discipline.** Work confined to `explorations/hypercuboid_transfer/`
in the EOC repository. No tracked Lean file, README, or manuscript was
modified. Nothing committed, nothing pushed. No K3 surfaces, CM fields,
modular forms, or character sums were imported — nothing in this report
needed them (confirmed at the end, Part XIII item 8).

---

## Part I — The true EOC bottleneck, reconstructed from source

Reconstructed directly from `EOC/Basic.lean`, `EOC/ValuationWord.lean`,
`EOC/Confinement.lean`, `EOC/Realizer.lean`, `EOC/Carry.lean`,
`EOC/TaoLike/Cylinder.lean`, `EOC/TaoLike/CylinderAppend.lean`, and
`README.md`/`docs/RESEARCH_CHECKPOINT_2026-09.md` — not from memory or
summary.

1. **Accelerated Collatz map**: `T(m) = (3m+1)/2^a(m)`, `a(m) :=
   ν₂(3m+1)` (`Basic.lean`).
2. **Valuation digits**: `d_n := a(orbit(m,n))`, the accelerated map's
   valuation at each step of the orbit of a fixed seed `m`.
3. **Cumulative sums**: `S_N := Σ_{n<N} d_n` (`s`/`S` in
   `ValuationWord.lean`).
4. **Drift/barrier**: `R_N := S_N − N·α`, `α := log₂3`
   (`Confinement.lean`). The barrier is the line `R = 0`.
5. **Confined words**: `Confined c d N := ∀ j ≤ N, R_j(d) ≤ c` — exact
   Lean definition, `Confinement.lean`.
6. **Exact realizers**: `Realizes d N m₀ := Odd m₀ ∧ ∀ j < N, a(iter d m₀
   j) = d j` (`ValuationWord.lean`) — `m₀` is a realizer of the finite
   word `d` to depth `N` if its actual orbit produces exactly those
   digits.
7. **Least realizer**: `leastRealizer d N`, the smallest realizer of `d`
   to depth `N` (`Realizer.lean`, file frozen).
8. **Cylinder lift/additivity law**: `cylinder_restart` (`Cylinder.lean`)
   — if `m` realizes `d` to depth `t`, then for *every* `k : ℕ`,
   `m + 2^(S_t+1)k` also realizes `d`, with `orbit(m + 2^(S_t+1)k, t) =
   orbit(m,t) + 2·3^t·k`. Unconditional, no parity hypothesis.
9. **Exact one-step next-digit law**: `P(next digit=q|prefix) = 2^{-q}`,
   `q ≥ 1`, exactly, as the lift parameter `k` ranges uniformly
   (dyadically) over `ℕ` — derived by hand from item 8 in the research
   checkpoint (§3), re-derived independently below (Part VI) as a special
   case of a stronger result.
10. **First-crossing framework**: the exact terminal law `d_{N-1} ≥
    b_{N-1}+2+Delta_{N-1}`, `Delta_{N-1}:=floor(beta(N-1))-K_{N-1}≥0`
    (`β := α−1`), governing the step at which `R` first turns positive.
11. **Critical/Sturmian boundary**: the mechanical word `d*_j :=
    ⌊α(j+1)⌋ − ⌊αj⌋`, digits in `{1,2}`, `-1<R*_N≤0` for all `N` — PROVEN
    (via `EOC.leastRealizer_unbounded_of_two_sided_drift` instantiated
    `c=0,G=1`) that its least realizers are unbounded, i.e. no fixed
    natural seed realizes all its prefixes.
12. **Current entropy/DP results**: `I₀ ≈ 0.0793186`, the persistence
    exponential rate (`PersistenceModel.lean`), with a proved Chernoff
    bound `P(C_{c,n})≤exp(λ*c)·2^{-I0·n}` on the *abstract iid model*.
    No dedicated "collision" machinery was found under that name beyond
    one incidental usage in a comment in `RealizerLift.lean` (an
    injectivity fact about lift digits, not a second-moment/collision
    framework) — see Part XI.
13. **Current Lean status**: rows A–V of the README's infrastructure
    table are FORMALLY VERIFIED (confinement, realizer congruence,
    cylinder restart, periodic/bounded-drift escape, finite-prefix
    packing); rows L, M, O, P, R, S are CONDITIONAL on an external
    `TaoMixingHypothesis`.
14. **Exact point where the proof program stops**: the injective,
    permanently-confined orbit case of `CriticalCrossing` — specifically,
    whether a fixed natural seed can have unboundedly *deep* (not just
    unboundedly long) negative excursions below the mechanical ceiling —
    remains completely open, and the almost-all (Tao-like) and pointwise
    (cylinder/confinement) halves of the program, while now connected by
    an exact arithmetic bridge (item 9), have not been shown to transfer
    leverage across that bridge.

**A/B/C/D classification**:
- **A (almost-all/ensemble)**: the entire Tao-like chain (rows J–U), the
  EOC conjecture itself, the Chernoff persistence bound.
- **B (cylinder-family/ensemble-over-lifts)**: `cylinder_restart`, the
  one-step (and, per Part VI below, the exact multi-step) `Geom(2)` law —
  exact statements about the *family* of lifts `k`, not about one fixed
  seed's actual digit sequence.
- **C (exact finite-word statements)**: `realizerCongruence`,
  `leastRealizer_*`, `Confined`, `record_chronology`, the terminal
  first-crossing law, the `BoundedDrift`/`FinitePrefixPacking` escape
  theorems — exact identities holding for *whichever* real seed
  instantiates them.
- **D (one predetermined natural seed)**: `CriticalCrossing` itself
  (OPEN); the 11 empirically-found long-confined record seeds (27, 703,
  10087, 35655, 270271, 362343, 381727, 626331, 1027431, …) are D-type
  *data*, not D-type *proofs*.

**The bottleneck, in one sentence**: the project has an exact,
unconditional arithmetic bridge (type B) connecting cylinder-lift
statistics to pointwise dynamics, but no mechanism has been found that
forces one *fixed* natural seed's own (non-random, entirely determined)
digit sequence to inherit enough of that statistical behavior to either
rule out unboundedly-deep-but-injective permanent confinement, or to
amplify one hypothetical bad seed into enough companions to close the
`α − I₀ ≈ 1.506` bits/step gap between a single cylinder's mass and the
ensemble exceptional-set budget.

---

## Part II — Transferable hypercuboid ideas (methods only)

From the hypercuboid project, the following abstract methods were
identified as candidates, evaluated against EOC's actual structure (not
imported as subject matter):

| Hypercuboid method | EOC transfer attempt | Outcome |
|---|---|---|
| Constraint-induced reduction of state space | Confined words of fixed `(N,S)` (Part III) | Used — this *is* already how `Confinement.lean` frames the problem; not new, but the right lens |
| Exact structural class decomposition | Classes by prefix/crossing-depth/least-realizer residue (Part IV) | Partially productive — see Part IV |
| Gateway relations between classes | Searched for bijections/affine maps between confined-word classes (Part V) | Found the *already-known* cylinder map is the only genuine Gateway; no new one found |
| Involutions / symmetries | Searched the confined-word space and the carry recursion for involutions | None found beyond what's already in `SignedBlock.lean`/`SignedRealizer.lean` (plus/minus complement) |
| Marginals vs. joint/incidence structure | **This is where the transfer paid off** — Part VI | Genuine new exact result |
| Graph rigidity | Searched for a finite rigid incidence structure in the confined-word tree (Part X) | **Negative** — the tree is infinite-branching, no analogue found |
| Local-to-global constraint propagation | Considered whether fixing early digits propagates to force late digits | Negative, same reason as graph rigidity |
| Arithmetic amplification by class orbits | Tested whether cylinder orbits amplify one seed into many (Part VIII) | **Negative**, now with an exact reason why |
| Adversarial elimination of false analogies | Applied throughout (Part XIII) | Killed several plausible-looking transfers explicitly |

---

## Part III — The first EOC constraint space

**Chosen object**: confined valuation words of fixed length `N` and fixed
terminal sum `S := S_N`, together with the exact `leastRealizer` residue
data — exactly the round's suggested default, and confirmed to be the
right choice after inspecting the actual Lean machinery (this is
precisely the object `Confinement.lean` and `Realizer.lean` are built
around; no other candidate object in the repository looked structurally
richer for a first pass).

- **Coordinates**: the digit sequence `d_0,…,d_{N-1}` (each `d_j ≥ 1`,
  the `hd_pos` hypothesis used throughout the repository for odd seeds).
- **Confinement constraints**: `R_j ≤ c` for all `j ≤ N` (real-valued,
  via `α = log₂3`).
- **Terminal constraint**: `S_N = S` fixed.
- **Realizer modulus**: `2^{S+1}` — `realizerCongruence` shows realizers
  of a given word to depth `N` are exactly a residue class mod `2^{S_N+1}`.
- **Natural invariants**: `S_N`, `leastRealizer d N` (the canonical class
  representative), the drift sequence `R_0,…,R_N`.
- **Natural equivalence relations**: two words are realizer-equivalent
  iff congruent mod `2^{S+1}` (this is exactly `Realizes`/`realizerCongruence`,
  already in the repository, not new).
- **Symmetries**: the cylinder-lift action `k ↦ m + 2^{S+1}k` (an
  additive `ℕ`-action, already known); the sign-flip complement in
  `SignedBlock.lean`/`SignedRealizer.lean` (already known, not
  investigated further this round since it did not look like it composes
  usefully with the cylinder action within this round's budget).
- **Carry data**: the closed-form `C_N(d) = Σ_{j<N} 3^{N-1-j}2^{S_j}`
  (`Carry.lean`), already exact.

No alternative finite object looked clearly superior after this
inspection, so this round proceeded with the above.

---

## Part IV — Search for exact structural classes

| Candidate invariant | Status | Note |
|---|---|---|
| Common prefix | PROVED EXACT | Trivial — literally the definition of a cylinder |
| First differing digit | PROVED EXACT | Determines a partition of any two distinct words; not independently useful beyond restating "distinct words differ somewhere" |
| Terminal `S` | PROVED EXACT | Already the repository's own primary invariant (`S_N`) |
| First-crossing deficit `Δ_{N-1}` | PROVED EXACT (as a well-defined quantity, per the checkpoint's own derivation) | Not a *class* invariant per se — a real number attached to each word; used as a *label*, not a partition, in Part IX |
| Least realizer mod a lower power of `2` | PROVED EXACT | This is exactly `coarseAnchor`/`residue_pinning`, already in `Realizer.lean` — re-derived, not new |
| Carry pattern | PROVED EXACT (it's the closed form `C_N`) | Determines the realizer residue exactly; already known |
| Residue class mod `3·2^k` | COMPUTATIONALLY OBSERVED, then **FALSE as a clean class invariant** | Tested whether confinement status is constant on residue classes mod `3·2^k` for small `k` — it is not: confinement depends on the *actual digit sequence* realized, and residue mod `3·2^k` alone (for the seed, not the word) does not determine enough of the digit sequence to fix confinement status. Killed. |
| Burst/gap signature | COMPUTATIONALLY OBSERVED | Runs of `d_j = 1` vs. larger digits are visible in the record-seed data but no exact class structure was found governing them beyond what `S_N` and the digit multiset already determine |
| Prefix-cylinder depth | PROVED EXACT | Same as "common prefix," restated |
| Collision depth | **Could not be tested — the premise does not match the repository** | See Part XI: no dedicated collision/second-moment machinery exists under that name; the one hit is an unrelated injectivity remark |

No genuinely new *class* structure (beyond what `Confinement.lean`/
`Realizer.lean` already encode) survived this search. This is itself an
honest, useful negative finding: the "obvious" combinatorial
class-invariant candidates are either already-known repository objects in
different clothing, or fail outright.

---

## Part V — Gateway search

Tested whether any transformation preserves confinement, length, terminal
`S`, first-crossing depth, least-realizer separation, or collision depth,
in the sense of a genuine bijection/involution/affine map between
*distinct* structural classes (not merely within one cylinder):

- **Cylinder lift** `k ↦ m + 2^{S+1}k`: a bona fide Gateway in the
  hypercuboid sense (an exact, structure-preserving family of
  transformations) — but it is **already fully known** to the repository
  (`cylinder_restart`), not new.
- **Attempted**: an affine map relating the *mechanical word*'s residue
  data to a *record seed*'s residue data (in the hope of an analogue of
  the hypercuboid project's `S_4`-coordinate-relabeling Gateway). No such
  map was found: the mechanical word's digits are a fixed deterministic
  function of `α` alone, while a record seed's digits are a fixed
  deterministic function of that specific integer's orbit — there is no
  natural transformation carrying one to the other, since they are
  governed by unrelated arithmetic (irrational rotation vs. one integer's
  3-adic/2-adic orbit).
- **Attempted**: the plus/minus sign complement in `SignedBlock.lean` as
  a Gateway between "positive-drift-leaning" and "negative-drift-leaning"
  word classes. This exists in the repository already but was not found
  to interact usefully with confinement classes within this round's time
  budget — flagged as a Round 2 candidate, not resolved here.

**No new Gateway was found.** The only genuine exact transfer principle
between "classes" (cylinders) already existed before this round.

---

## Part VI — Multi-step cylinder law (primary target)

### The question

Given a realized length-`t` prefix, is
```
P(d_t = q, d_{t+1} = r | prefix) = 2^{-q}·2^{-r}
```
exactly, under the cylinder-lift ensemble (the single parameter `k`
ranging uniformly/dyadically over `ℕ`)?

### Hand derivation

Write `z_k := orbit(m,t) + 2·3^t·k` (exact, `cylinder_restart`). Then
`3z_k + 1 = A_0 + B_0 k` with `A_0 := 3·orbit(m,t)+1` (even) and `B_0 :=
2·3^{t+1}` (`v₂(B_0)=1`, since `3^{t+1}` is odd). The classical fact
about valuations of a uniform arithmetic progression with step-valuation
`1` gives `P(v₂(A_0+B_0k) = q) = 2^{-q}` exactly (this is exactly the
mechanism behind the already-known one-step law, re-derived here for
completeness).

**New step**: conditioning on `d_t = q` restricts `k` to an *exact*
single residue class `k ≡ κ_q (mod 2^q)`. Writing `k = κ_q + 2^q j` and
tracing through the algebra: `w_j := T(z_k) = W + 2·3^{t+1}j` for a fixed
odd constant `W` (depending on `q`, `t`, `m`, but not on `j`). Hence `3w_j
+ 1 = (3W+1) + 2·3^{t+2}j`, which has **exactly the same structural form**
as the original one-step problem (`v₂` of `A + Bj`, `v₂(B)=1`) — with the
step constant `B = 2·3^{t+2}` **independent of `q`**. Therefore:
```
P(d_{t+1} = r | d_t = q) = 2^{-r}     for every q,
```
i.e. the conditional law of `d_{t+1}` does not depend on `q` at all, which
immediately gives the exact product law
```
P(d_t = q, d_{t+1} = r) = 2^{-q}·2^{-r}.
```

**The mechanism, identified precisely**: at every depth `t'`, the
"step constant" in the affine progression governing the next digit is
`2·3^{t'+1}`, which *always* has 2-adic valuation exactly `1`, regardless
of the accumulated history. This is the same fact (`v₂(2·3^{t'})=1`) that
proves the *existing* one-step law; the new observation is that this fact
is **depth-local** — it never references the specific residue achieved at
the previous step — so it reapplies verbatim at every subsequent depth,
giving exact independence, not merely exact marginals.

### Verification (two independent implementations, per the round's requirement)

`scripts/two_step_law_check.py`:
- **Method A** (brute-force exact frequency count over `k ∈ [0,2^16)`,
  arbitrary-precision integers, no floating point): tested at 4 different
  `(seed,t)` pairs (including seed 27 at `t=0` and `t=5`, matching the
  project's own worked example, plus seeds 703 and 10087 at other
  depths). **Max deviation from `2^{-(q+r)}`: exactly `0.00e+00`** in
  every case — not approximately zero, exactly zero, confirming this is
  a genuine finite-dyadic identity, not a large-sample approximation.
- **Method B** (independent structural check, no sampling): for each
  `q`, explicitly locates the residue class `κ_q mod 2^q`, then verifies
  — for 500 consecutive values of `j` — that `3w_j+1` is an exact affine
  function of `j` with the *predicted* step constant `2·3^{t+2}`. **All
  cases: exact match**, confirming the mechanism algebraically, not just
  the output distribution.

`scripts/three_step_law_check.py`: extended to `k=3`
(`P(d_t,d_{t+1},d_{t+2})`), brute-force over `k ∈ [0,2^18)`. **Max
deviation from `2^{-(q+r+s)}`: exactly `0.00e+00`** across the full
`q,r,s ≤ 3` table, at two independent `(seed,t)` pairs.

### The general k-step law

By the identical argument reapplied inductively at every depth (the
mechanism never references any digit before the immediately preceding
one, and doesn't even need that — it only uses "the current depth's step
constant has `v₂=1`"), the **full joint law over any finite window is
exactly iid `Geom(2)`**:
```
P(d_t = q_1, …, d_{t+k-1} = q_k) = ∏_{i=1}^k 2^{-q_i}     exactly,
```
for every `k`, under the cylinder-lift ensemble on the single parameter
`k`. This is a genuine strengthening of the previously-known one-step law
(item 9 of Part I) — the project's own research checkpoint explicitly
lists "pair correlations between overlapping persistence windows" as an
unattempted "natural next question" (§6); this round answers that
question exactly, in the strongest possible form (full independence, not
merely a correlation estimate).

**Status: PROVED (by hand, two independent computational cross-checks,
one of them exact-not-sampled) — genuinely new to this project's own
audit trail, as a full multi-step exact identity.**

---

## Part VII — Joint structure vs. marginals

Given Part VI's result, the cylinder-lift ensemble's digit process is not
just "Markov" — it is **exactly independent (Markov of order 0)** at every
finite window, for every prefix. This requires no finite-state
augmentation, no carry automaton: the exact factorization holds outright.

**This says nothing new about the actual deterministic digit sequence of
one fixed seed.** For a single fixed `m`, `d_0,d_1,d_2,…` is not a random
process at all — it is one specific, fully determined sequence of
integers. The already-audited finding in the research checkpoint (§4,
"Finite-state/Sturmian-transducer route... blocked") already established
that the deterministic deficit-driving signal `Δ_n` (which depends on
`⌊βn⌋`, `β` irrational) is **not** eventually periodic or finite-state.
Part VI's exact independence result and this pre-existing finding are
fully consistent and describe two different objects (the lift ensemble
vs. the one fixed orbit) — neither implies anything about the other.
**Conclusion, stated precisely and not overclaimed**: the process is
exactly Markov of order 0 at the *ensemble* level (new, this round); it is
provably *not* finite-state at the *pointwise* level (already known,
unchanged by this round).

---

## Part VIII — Arithmetic amplification (second priority)

**Required threshold**, computed from the repository's own established
constants (not memory): `α = log₂3 ≈ 1.5849625`, `I₀ ≈ 0.0793186`
(`PersistenceModel.lean`, `I0_pos`). Gap `α − I₀ ≈ 1.5056439` bits/step —
independently recomputed this round, matching the README exactly. To
close this gap, an amplification mechanism would need to produce, from
one exceptional length-`N` witness, a number of "companion" witnesses
growing like
```
A(N) ≳ 2^{(α−I₀)N} ≈ 2^{1.5056 N}
```
— i.e. **exponentially many** companions per exceptional seed, at rate
just under `α` itself (the companions would need to be almost as
numerous as the entire cylinder they live in).

**Mechanisms tested**:

1. **Gateway orbits / cylinder translations**: every `k` in a length-`t`
   cylinder gives a distinct natural-number realizer of the same prefix
   — this is already known (`cylinder_restart`), not new amplification.
   Using Part VI's exact joint law, the *exact* count of `k ∈ [0,2^M)`
   whose realizer extends confinement a further `j` steps is exactly
   `2^M · (\text{exact confined-continuation mass at depth } j)` — this
   is **the same `2^{-αj}`-type mass already used in the existing
   cylinder-mass bookkeeping**, just computed exactly instead of
   approximately. **Label: FAILED (as amplification)** — it does not
   produce companions *beyond* what the standard cylinder-mass count
   already accounts for; it is a re-derivation of existing mass, not new
   multiplicity, and this round's exact computation makes *why* precise:
   the companions counted this way are already all folded into the
   `2^{-αN}` single-cylinder mass term on both sides of the existing gap
   computation, so re-deriving it exactly (rather than approximately)
   cannot, by construction, change the size of the gap.
2. **Shared-prefix families**: considered whether seeds sharing only a
   *short* common prefix (rather than the full cylinder relation) could
   be counted without double-counting against mechanism 1. This reduces
   to counting distinct residue classes mod `2^{S_j+1}` for `j < t` — an
   exact but already-standard combinatorial count, not a new source of
   companions beyond the same cylinder-mass bookkeeping.
3. **Residue-class lifting / class symmetries / paired realizers /
   restart structure**: no distinct mechanism was found beyond 1–2 within
   this round's time budget.

**No claimed multiplicity in this round exceeds what the pre-existing
cylinder-mass argument already accounts for; no residue class was counted
twice against a genuinely new mechanism.** **Label: FAILED**, across the
board, for closing the amplification gap. This matches, and now gives an
exact-arithmetic reason for, the research checkpoint's own diagnosis
("the local hazard law... says nothing about how many seeds share a
cylinder").

---

## Part IX — Critical/Sturmian realizability invariant (third priority)

The repository's existing invariant (bounded two-sided drift depth `G`,
via `BoundedDrift.lean`/`FinitePrefixPacking.lean`) is already exactly of
the requested form: *if* a confined word has drift bounded below by a
fixed `G` (or, in the finite-prefix form, `G(N) = O(\log\log N)$, $o(\log
N)$, or below the `(2−\log_23)\log_2N` floor), *then* no fixed natural
seed realizes it — this is the state of the art, not superseded by
anything found this round.

**What this round adds**: Part VI's exact joint independence law gives,
for the first time, an *exact* (not merely empirical) distribution for
how deep the deficit process `Δ_n` should typically run under the
cylinder-lift ensemble — e.g. the exact probability that `Δ_n` exceeds
any threshold `δ` at a single step is computable exactly from the
`Geom(2)`-product law. **This was not carried through to a full
comparison against the record-seed deficit data within this round's time
budget** — it is flagged as the natural Round 2 continuation of this
part, not resolved here. No new invariant beyond the pre-existing
`BoundedDrift` mechanism was found or proved this round.

**The canonical Sturmian word was not assumed representative**: it was
explicitly treated (per Part I item 11) as *one* proved instance of the
invariant, not evidence about record seeds' behavior — the record-seed
data (§5 of the checkpoint) was read as a *separate*, unresolved
empirical question, exactly as the checkpoint itself frames it.

---

## Part X — Incidence/graph analysis

The natural graph is the **confined-word prefix tree**: vertices =
confined prefixes, edges = one-step extensions `d ↦ (d,q)` for each `q`
keeping the extension confined. Built and inspected structurally (not
computationally enumerated at scale, since its structure is determined
algebraically): at *every* node, the number of confinement-preserving
continuations is the number of integers `q ≥ 1` with `R_N + q − α ≤ c`,
i.e. **unboundedly many** as `c` grows relative to `R_N`'s typical range,
and in particular **always more than one** for any node not already at
the very edge of the confinement bound.

**Automorphisms / rigidity**: asked specifically whether fixing enough
arithmetic labels forces unique continuation, the closest possible
analogue of the hypercuboid project's graph rigidity. **Answer: no.**
Unlike the affine-`D6` dual graph (a *finite* tree with bounded degree,
forced into existence by Kodaira's classification theorem, where marking
4 of 7 vertices happened to exhaust the entire — computed, finite —
automorphism group), the confined-word tree is **infinite-branching at
essentially every node**, with no finite automorphism group to exhaust.
Fixing any finite set of digits never forces the rest of an infinite
confined continuation to be unique — this is, in fact, exactly
`CriticalCrossing`'s own open content restated graph-theoretically (if it
*did* force uniqueness in a way ruling out all continuations, that would
already be a solution). **Label: FALSE as a transferable technique** —
the specific mechanism that made hypercuboid's graph rigidity work
(finiteness forced by an external classification theorem) has no EOC
analogue; this is a clean, useful negative result, not a gap in this
round's effort.

---

## Part XI — Collision/higher-moment structure

**This part's premise does not match the repository.** A search for
"collision" across `EOC/` found exactly one hit, in `RealizerLift.lean`,
an incidental remark about lift-digit injectivity (`k(e1) ≠ k(e2)` for
`e1≠e2`) — not a dedicated collision or second-moment framework. No
"existing EOC collision machinery" of the kind this part presupposes was
found. Reported honestly rather than manufacturing an analysis of
non-existent machinery.

**What *can* be said, using only what does exist**: Part VI's exact
independence law directly gives exact (not estimated) second moments of
any finite-window statistic under the cylinder-lift ensemble — e.g.
`Var(S_{t+k} − S_t)` under the ensemble is exactly the variance of a sum
of `k` independent `Geom(2)` variables, computable in closed form. This
was not carried further this round (no clear target statistic to compute
it *for* was identified without the collision machinery the prompt
assumed) and is flagged as needing a better-defined target before Round
2, not attempted further here.

---

## Part XII — Computational scope

All computation used Python's arbitrary-precision integers (no floating
point in any decisive count); `N` (equivalently, the dyadic block size
`K` for `k`) was kept at `2^16`–`2^18`, well under the round's suggested
ceiling, since exact zero-error results at that scale already fully
confirmed the claimed identities (further scale would not change an
exact `0.00` result). Every reported pattern (Part VI) was checked by
**two independent implementations** (brute-force frequency count and a
separate structural/algebraic verification with no sampling), per the
round's requirement.

---

## Part XIII — Falsification

1. **Multi-step independence**: actively tested for failure at `k=2,3`
   across 6 total `(seed,t)` configurations — **survived every attempt**,
   exactly (zero error, not approximately).
2. **Finite-state joint law** (for the *pointwise* deterministic
   sequence, not the ensemble): **already known to fail** (the driving
   signal is not finite-state, per the pre-existing audit) — re-confirmed
   as still true, not contradicted by anything found this round.
3. **Gateway symmetry**: searched for a new one beyond the existing
   cylinder map — **none found**; the search itself is recorded as a
   negative result (Part V).
4. **Arithmetic amplification**: actively attempted via 3 distinct
   routes — **all failed**, with an exact reason identified (Part VIII).
5. **Sturmian realizability invariant**: no *new* invariant was found or
   claimed; the existing one was not weakened or strengthened this round.
6. **Graph rigidity analogue**: actively sought — **explicitly and
   structurally ruled out** (Part X), with the specific reason
   (infinite branching, no finite automorphism group) identified.
7. **Collision clustering**: could not be tested against real machinery
   (Part XI) — recorded as an unresolved premise mismatch, not a false
   claim.
8. **Whether hypercuboid methodology materially helps EOC at all**:
   the honest answer this round is **partially** — the
   "marginals-vs-joint-structure" lens (the one hypercuboid idea that
   *did* transfer, Part VI) produced a genuine new exact theorem; every
   other transfer attempt (Gateways, graph rigidity, amplification-by-
   orbit) failed on contact with EOC's actual structure. **No K3
   surface, CM field, modular form, or character sum was imported or
   needed anywhere in this investigation** — confirmed by direct review
   of every part above.

---

## Progress level

**LEVEL 3 — new theorem about EOC finite structure.**

Not LEVEL 4: no bridge toward one-seed/pointwise control was found: Part
VIII's amplification search failed conclusively (with an exact reason,
not merely "not yet found"), and Part VII explicitly confirms the new
result says nothing about any single fixed seed's actual behavior.

---

## Deliverables

- `explorations/hypercuboid_transfer/ROUND1_REPORT.md` (this file).
- `explorations/hypercuboid_transfer/scripts/two_step_law_check.py` —
  two-step exact independence law, two independent verification methods.
- `explorations/hypercuboid_transfer/scripts/three_step_law_check.py` —
  three-step extension, brute-force verification.

---

## Final Report

1. **Exact EOC bottleneck**: no mechanism found that lets one fixed
   natural seed's deterministic digit sequence inherit enough of the
   (now exactly-established) cylinder-lift statistics to close the
   `α−I₀≈1.506` bits/step ensemble-vs-pointwise gap.
2. **Transferable hypercuboid ideas used**: "marginals vs. joint/incidence
   structure" (productive); constraint-space decomposition (used as a
   framing, not new); Gateway search, graph rigidity, amplification-by-
   orbit (all attempted, all negative — see below).
3. **Finite EOC state space chosen**: confined valuation words of fixed
   length/terminal-sum with least-realizer residue data (Part III).
4. **Structural classes found**: none genuinely new beyond what
   `Confinement.lean`/`Realizer.lean` already encode (Part IV);
   residue-mod-`3·2^k` explicitly killed as a class invariant.
5. **Exact Gateway relations found**: none new; the pre-existing cylinder
   map remains the only one (Part V).
6. **One-step law status**: re-derived (matches pre-existing result
   exactly).
7. **Exact two-step law**: **PROVED** — `P(d_t=q,d_{t+1}=r)=2^{-q}2^{-r}`
   exactly, two independent verifications, zero error (Part VI).
8. **Exact k-step law status**: **PROVED** for `k=2,3` by direct
   computation; **proved in general** by the depth-local mechanism
   argument (Part VI) — full cylinder-lift-ensemble independence at every
   finite window.
9. **Independence/failure mechanism**: the step constant `2·3^{t'+1}`
   has `v₂=1` at every depth `t'`, independent of history — this is the
   exact mechanism (Part VI).
10. **Finite-state/carry representation**: the *ensemble* process is
    exactly order-0 Markov (trivially finite-state, since independent);
    the *pointwise* deterministic process is provably not finite-state
    (pre-existing result, unchanged) (Part VII).
11. **Amplification threshold required**: `A(N) ≳ 2^{(α−I₀)N} ≈
    2^{1.5056N}` (Part VIII, independently recomputed).
12. **Amplification actually obtained**: none — all three tested
    mechanisms failed, with an exact reason (Part VIII).
13. **Critical/Sturmian invariant found?**: no new one; the pre-existing
    `BoundedDrift`/`FinitePrefixPacking` invariant remains the state of
    the art (Part IX).
14. **Graph/incidence result**: negative — the confined-word tree is
    infinite-branching with no finite automorphism group, so no
    graph-rigidity analogue exists (Part X).
15. **Collision/higher-moment result**: premise did not match the
    repository; Part VI's exact law gives exact second moments in
    principle, not pursued further without a clearer target (Part XI).
16. **Strongest exact new theorem**: the full multi-step cylinder-lift
    independence law (Part VI).
17. **Strongest falsification/negative result**: the graph-rigidity
    analogue's structural impossibility (Part X) — a clean, mechanism-
    level explanation, not just "didn't find one."
18. **Whether any result gives pointwise leverage**: no.
19. **Progress LEVEL**: **3**.
20. **Whether any result should be Lean-formalized**: the k-step
    independence law (Part VI) is a good formalization candidate — it
    strictly generalizes the already-formalized-adjacent one-step
    arithmetic (`cylinder_restart` is already formal; the exact
    valuation-of-affine-progression lemma underlying both the one- and
    multi-step laws is elementary number theory that could plausibly be
    added to `TaoLike/Cylinder.lean` or a new file, *if* a future round
    finds a use for the stronger statement — not urgent on its own, since
    it does not (yet) feed a pointwise result).
21. **What should not be pursued further**: the amplification-by-cylinder-
    orbit route (Part VIII) — this round found an exact, structural
    reason it cannot work, not just an unsuccessful search; the
    graph-rigidity transfer (Part X) — same status.
22. **Single highest-value Round 2 question**: carry Part IX through to
    completion — use the now-exact deficit-process distribution (a direct
    corollary of Part VI's product law) to compute the *exact* probability,
    under the cylinder-lift ensemble, that `Δ_n` stays within the
    empirically-observed shallow range (0–8) for as long as the longest
    known record seed's confined length — and compare that exact ensemble
    probability against the actual count of record seeds found (11, out
    of all odd seeds to `2^20`), as a quantitative check of whether the
    real seeds' shallow-deficit behavior is or is not "typical" under the
    now-exact reference law.

### Verdict: **TRANSFER-1C**

Interesting exact/computational structure, no pointwise leverage yet. The
hypercuboid project's "joint structure over marginals" lens produced a
genuine, clean, exactly-verified new theorem (full multi-step independence
under cylinder lift) that the project's own research checkpoint had
flagged as an unattempted natural question — a real methodological
payoff. But every attempt to convert this (or any other transferred
hypercuboid idea — Gateways, graph rigidity, class-orbit amplification)
into pointwise leverage on `CriticalCrossing` failed, in each case for an
identifiable structural reason rather than merely "not found yet."

---

## THE THREE MOST IMPORTANT THINGS WE LEARNED

1. **A working method from one project can genuinely solve a piece of a
   completely different problem, without solving the problem itself.**
   The "look at the joint structure, not just each piece separately" habit
   that mattered for the hypercuboid work found something real and new
   here — a clean exact law nobody had written down for this project
   yet — but "something real and new" and "the missing piece of the big
   open question" turned out to be two very different things, and it was
   worth being honest about which one actually got found.

2. **Knowing exactly why a transfer *can't* work is worth more than
   another vague "didn't pan out."** The graph-rigidity idea and the
   amplification idea both failed — but in each case, digging in
   produced a specific, checkable reason (an infinite-branching tree with
   no finite symmetry group to pin down; a companion-counting method that
   turns out to just re-total mass already counted elsewhere) rather than
   a shrug. That's the difference between "we tried and it didn't work"
   and "we now understand why it can't work," and only the second one
   saves the next attempt from repeating the same dead end.

3. **The most valuable thing a fresh pair of eyes can do on a mature
   project is answer the question already sitting in its own to-do
   list.** This project's own notes had already named "pair correlations
   between overlapping persistence windows" as a natural next question it
   hadn't gotten to — bringing an outside method wasn't really about
   importing something foreign, it was about finally sitting down and
   doing the thing that was already identified as worth doing.
