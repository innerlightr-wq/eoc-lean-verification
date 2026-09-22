# Chang cross-scale arithmetic audit for zero-corridor realizers

Follow-up to [`docs/CURRY_REALIZER_WINDOW_INTERFACE.md`](CURRY_REALIZER_WINDOW_INTERFACE.md),
which closed the Curry route on the realizer side and left the gap

> bulk entropy / population sparsity **versus** pointwise arithmetic placement of the least
> positive realizer.

**Question.** Does Chang's framework contain a genuinely growing-depth, cross-scale arithmetic
constraint that distinguishes exceptionally small positive realizers from ordinary zero-confined
words?

**Answer: no.** Three independent findings, each verified against Chang's own paper:

1. **Chang's observable is a 3-digit window of the valuation word.** Event ⟺ `(d_j,d_{j+1})=(2,1)`;
   label ⟺ `d_{j+2} ≥ 2`. Verified on 14,403 positions with **0 mismatches**, and already
   formalized (`ChangHistory.event_iff`, `label_iff`). It is a finite-radius local factor, so it
   carries no information the valuation word does not.
2. **The zero corridor does not restrict finite Chang histories.** Every one of the 2^K label
   histories is realized by some zero-confined word, verified exhaustively for **K ≤ 11
   (2048/2048)**. So no finite Chang-history obstruction can exclude a Type-II zero-corridor tail.
3. **Chang's cross-scale machinery is explicitly ensemble-level, by his own statement.** The
   "spectator bits" are literally the higher 2-adic digits of the orbit value
   (`e_i ≡ (n_{t_i} − b)/2^K mod 8`), and Chang writes that transferring his Proposition 5.16 to
   individual orbits "is precisely the distributional-to-pointwise bridge — and hence the content
   of the open problem".

Chang's remaining obstruction and EOC's are **the same quantifier upgrade in different
coordinates**, and Chang says so himself (Remark 4.4).

---

## A. Starting state

| | |
|---|---|
| branch point | `curry-realizer-window-interface` = `71d7609dc9377137dca74e139c69109bc59171d8` (fetched and verified) |
| new branch | `chang-cross-scale-realizer-audit` |
| worktree | isolated; Mathlib shared by read-only symlink |

Ancestry verified, all five required branches ancestors of the tip: `curry-foundation-zero-corridor`
`5db34a58`, `zcre-realizer-growth` `9435bca0`, `dynamic-deficit-feedback` `1d087e20`,
`curry-divergence-part2` `0d7e3edc`, `curry-realizer-window-interface` `71d7609d`.

Ordinary checkout on `research-sparse-visits-2026-09-16`, **53 dirty files**, untouched.
`main` (`1c4d6700`) unmodified.

## B. Chang source inventory

**No Chang PDF existed anywhere on disk** — an exhaustive search of `/home/elias` (depth 6) for
`*chang*` returned only repository Lean/Markdown files and unrelated changelogs. The primary
source was therefore fetched from arXiv during this audit.

| | item |
|---|---|
| **C1** | Edward Y. Chang (Stanford University), *A Structural Reduction of the Collatz Conjecture to One-Bit Orbit Mixing*, arXiv:2603.25753v1 [math.DS], submitted 24 Mar 2026. Fetched, 716 lines of extracted text, sha256 `0b8d221812feba0b07db…`. **Read in full.** |
| **C2** | Edward Y. Chang, *Exploring Collatz Dynamics with Human–LLM Collaboration*, arXiv:2603.11066v6 [math.DS], 2026. **Not fetched.** Cited inside C1 as its reference [3] for Lemma 10.33 and Proposition 10.31. |

Sections of C1 actually used: §2 (compressed map, burst indicators, block-TV), §4 (Lemma 4.1,
Theorem 4.2, Remarks 4.3–4.4), §5 (Propositions 5.14, 5.16; Lemma 5.15; the Open Problem;
Remarks 5.17–5.18).

**Limitation, stated plainly.** Lemma 5.15 and Proposition 5.16 are quoted by C1 from C2, which was
not read. Everything attributed to those two statements below is therefore at one remove, and is
labelled as such. This does not affect the audit's conclusions, which rest on C1's own §2, §4 and
the Open Problem statement.

**Repository sources:** `EOC/ChangHistory.lean` (439 lines, read in full), `EOC/Realizer.lean`,
`EOC/Confinement.lean`, `EOC/CurryFoundation.lean`, `EOC/ZCRERealizerGrowth.lean`,
`CHANG_CYLINDER_SCRATCHPAD.md`, `scratch/chang_eoc_experiment.py`; manuscript P1 Rev 5 §5.4
(Definition 5.13, Theorem 5.14), §6, §8 (Open Problems A–G); `references.bib` entries [17], [18].

## C. Attribution boundary

Verified against C1 directly, not against the EOC paraphrase.

**Chang's own (C1):**

- the compressed odd-to-odd map `T(n) = (3n+1)/2^{v₂(3n+1)}` (§2.1) — same map as EOC's accelerated map;
- burst indicator `X_t = 1[n_t ≡ 1 (mod 4)] = 1[v₂(3n_t+1) ≥ 2]`, bursts/gaps, run statistics, block-TV depth (§2.2–2.3);
- Lemma 4.1 (gap starts and mod-8 residues);
- **Theorem 4.2, the Map Balance Theorem**, and Remarks 4.3–4.4;
- the dominant `n ≡ 1 (mod 8)` channel and the identification of bit 4 as the deciding bit (Thm 4.2 Step 1);
- Propositions 5.1–5.14, the exact bias decomposition, and the Open Problem of §5.9;
- spectator-bit language, Lemma 5.15 and Proposition 5.16 — **both quoted by C1 from C2**.

**EOC's reformulation (P1 §5.4):** the valuation-word criterion `m_j ≡ 9 (mod 16) ⟺ (d_j,d_{j+1}) = (2,1)`;
the mod-32 label as `d_{j+2}`; the canonical blocks `β(0)=(2,1,1)`, `β(1)=(2,1,2)`; Theorem 5.14
(finite Chang-history realizability).

**This project's original exact-realizer constructions:** Proposition 5.2 (exact realizer
congruence), the least-realizer machinery, and `EOC/ChangHistory.lean`'s formalization.

**No misattribution found.** In particular the "(2,1) criterion" and the canonical block
construction are EOC's, not Chang's — C1 contains no valuation-word statement at all. Conversely
the Map Balance Theorem and the mod-32 reduction are Chang's, and P1's rendering of them is
faithful.

## D. Chang framework

| # | object | Chang's definition (C1) |
|---|---|---|
| 1 | map | `T(n) = (3n+1)/2^{v₂(3n+1)}` on odd `n ≥ 1` (§2.1) |
| 2 | state space | odd positive integers; residues mod `2^K` for the map-level statements |
| 3 | burst | step `t` with `X_t = 1`, i.e. `n_t ≡ 1 (mod 4)`, i.e. `v₂(3n_t+1) ≥ 2` |
| 4 | gap step | `X_t = 0`, i.e. `n_t ≡ 3 (mod 4)`, i.e. `v₂(3n_t+1) = 1` |
| 5 | burst-ending time | last step of a burst run: `n_t ≡ 1 (mod 4)` with `T(n_t) ≡ 3 (mod 4)` |
| 6 | dominant channel | `n ≡ 1 (mod 8)` (the class where `v₂ = 2` exactly) |
| 7 | observable bit | bit 4 of `n` at burst-ending times; equivalently `n mod 32 ∈ {9, 25}` |
| 8 | spectator bits | bits above the mod-`2^K` "known zone"; formalized through the **extension index** `e_i ≡ (n_{t_i} − b)/2^K (mod 8)` (Prop 5.16) |
| 9 | active bits | the mod-32 window deciding the gap outcome |
| 10 | transition | Lemma 4.1: gap start `≡ 3 (mod 8)` ⟺ `G = 1`; `≡ 7 (mod 8)` ⟺ `G ≥ 2` |
| 11 | Map Balance | Theorem 4.2, below |
| 12 | balance claims | map-level: Thm 4.2 (deterministic, finite). Ensemble: Prop 5.16. Orbit-level: **open** |
| 13 | open statement | §5.9 Open Problem, below |

**Theorem 4.2 (Map balance), verbatim structure.** For any `K ≥ 5`, with
`S_K = {r ∈ Z/2^K : r ≡ 1 (mod 4), T(r) ≡ 3 (mod 4)}` and `C₃(K), C₇(K)` counting `r ∈ S_K` with
`T(r) ≡ 3` resp. `≡ 7 (mod 8)`:
(i) `|S_K| = 2^{K−3} − 1`; (ii) `|C₃(K) − C₇(K)| = 1`, with `C₃ − C₇ = (−1)^K`;
(iii) the `n ≡ 1 (mod 8)` subclass contributes exactly `C₃⁽¹⁾ = C₇⁽¹⁾ = 2^{K−5}` (perfect balance),
the entire `±1` imbalance coming from `n ≡ 5 (mod 8)`.

*Status:* **finite, deterministic, map-level (per-residue).** Not asymptotic, not statistical, not
single-orbit.

**The Open Problem (§5.9), verbatim.** For every odd `n₀ > 2^{68}`, with `t₁ < … < t_m` the
burst-ending times, restricted to `n_{t_i} ≡ 1 (mod 8)`, prove

```
| #{i ≤ m : n_{t_i} ≡ 9 (mod 32)} / #{i ≤ m : n_{t_i} ≡ 9 or 25 (mod 32)}  −  1/2 |  ≤  δ
```

for some `δ < δ_max`, "where `δ_max` is determined by the block-TV budget (3)".

*Status:* **single-orbit pointwise, deterministic, asymptotic.** Requires only **bounded deviation,
not convergence to 1/2**, and `δ_max` is **not explicit** — it is defined through the budget
`Σ_{K=3}^{K₀} ‖h_K‖_∞ · ε_K < ln 2 − ρ ln 3`. Remark 5.18 gives a numerical `c ≈ 0.79` for an
equivalent formulation.

## E. Accelerated/valuation translation

| Chang object (C1) | accelerated object | valuation-word expression | realizer/residue |
|---|---|---|---|
| compressed map `T` | accelerated map | `m ↦ (3m+1)/2^{d}` | — |
| burst `X_t = 1` | `n_t ≡ 1 (mod 4)` | `d_t ≥ 2` | `ChangHistory.a_ge_two_iff` |
| gap step `X_t = 0` | `n_t ≡ 3 (mod 4)` | `d_t = 1` | `ChangHistory.a_eq_one_iff` |
| burst-ending in dominant channel | `m_j ≡ 9 (mod 16)` | **`(d_j, d_{j+1}) = (2,1)`** | `ChangHistory.event_iff` |
| observable bit 4 = 0 (`n ≡ 9 mod 32`) | — | **`d_{j+2} = 1`** | `ChangHistory.label_iff` |
| observable bit 4 = 1 (`n ≡ 25 mod 32`) | — | **`d_{j+2} ≥ 2`** | `ChangHistory.label_iff` |
| gap run `G = 1` | — | `d_{j+2} ≥ 2` | Lemma 4.1(a) |
| gap run `G ≥ 2` | — | `d_{j+2} = 1` | Lemma 4.1(b) |
| burst density `ρ` | — | density of digits `≥ 2` | §K |

**Derivation, checked from first principles.** `d_j = 2` ⟺ `m_j ≡ 1 (mod 8)` (since `m ≡ 5 mod 8`
gives `v₂ ≥ 3`). Writing `m_j = 8k+1`, `T(m_j) = 6k+1`, and `d_{j+1} = 1` ⟺ `6k+1 ≡ 3 (mod 4)` ⟺ `k`
odd ⟺ `m_j ≡ 9 (mod 16)`. Among those, `m_j ≡ 9 (mod 32)` ⟺ `k ≡ 1 (mod 4)` ⟺ `T(m_j) ≡ 7 (mod 8)`
⟺ `G ≥ 2` ⟺ `d_{j+2} = 1`.

**Verified computationally:** 14,403 event positions across all zero-confined words with
`3 ≤ k ≤ 10`; **0 mod-16 criterion mismatches, 0 mod-32 label mismatches**.

**Consequence (Gate 9).** `ChangLabel_j` depends only on `(d_j, d_{j+1}, d_{j+2})` — **width
exactly 3**. The Chang label process is a finite-radius factor of the valuation sequence, hence
cannot contain information the valuation word does not.

## F. Finite-history universality boundary

P1 Theorem 5.14, formalized as `ChangHistory.finite_chang_history_realizable` and
`every_finite_history_is_a_consecutive_chang_history`: for every `y ∈ {0,1}^K` the canonical word
`D(y) = β(y₀)…β(y_{K−1})` has events exactly at `j ∈ {0,3,…,3(K−1)}`, labels `m_{3t} ≡ 25 (mod 32)`
⟺ `y_t = 1`, and `1 ≤ m < 2^{4K + #{t:y_t=1} + 1}`.

**Exact endpoint.** Event status is determined through `j = 3K−2`; the final prescribed event is at
`j = 3K−3`; `j = 3K−2` is controlled and is not an event; **the first uncontrolled event position
is `j = 3K−1`**, because testing there needs `d_{3K}`, outside the word.

**Screening rule (reusable).**

> **FIXED-DEPTH CHANG FEATURES ARE NOT SUFFICIENT.** Any proposed obstruction that depends only on
> a fixed finite word, a bounded number of event labels, the absence of a finite pattern, local
> exclusion of one label, bounded-run imbalance, or any finite automaton with fixed memory, is
> already killed by Theorem 5.14 — every such finite configuration is realized. §M strengthens
> this: it remains true inside the exact zero corridor.

## G. Spectator-bit mechanism

Answering Gate 5's eight questions from C1 directly.

1. **Why "spectators"?** They lie above the mod-`2^K` window that decides the current transition,
   so they do not enter the current gap outcome.
2. **Irrelevant forever?** No — they refresh the mod-32 class at later visits (Prop 5.16).
3. **Can one become active?** Yes, that is the point of the cycling mechanism.
4. **Precise activation mechanism?** The **extension index** `e_i ≡ (n_{t_i} − b)/2^K (mod 8)` for
   successive visits `t₁ < t₂ < …` to a parent class `b ∈ Ω_K`.
5. **Does the retained set grow?** Lemma 5.15 (via C2) gives `B_T ≥ B₀ + (ρ₀ + log₂3 − 2)T − log₂T − O(1)`,
   so bit-length grows linearly when `ρ₀ > 2 − log₂3 ≈ 0.415`; C1 concludes "fresh spectator bits
   are always available".
6. **Equivalent to ordinary higher 2-adic digits of the seed?** **Yes, by definition.**
   `e_i = (n_{t_i} − b)/2^K mod 8` is literally digits `K, K+1, K+2` of the orbit value. There is
   no additional structure in the object.
7. **Nontrivial feedback rule?** Prop 5.16 gives equidistribution of `e_i` **"under the ensemble
   model"**, with error `4/M + C₁·2^{−α(B_min−3)}`.
8. **Or just the known 2-adic conjugacy?** In the anti-reformulation sense, yes — see §I and §T.

**The decisive sentence is Chang's own**, immediately after Prop 5.16:

> "Transferring this ensemble guarantee to individual deterministic orbits is precisely the
> distributional-to-pointwise bridge—and hence the content of the open problem below."

So the spectator-bit machinery is *explicitly* not a pointwise constraint. It is the same open
problem in a different presentation.

**Flagged for verification, not asserted.** Lemma 5.15's inequality `B_T ≥ B₀ + (ρ₀ + log₂3 − 2)T`
is increasing in `ρ₀`, while in valuation-word coordinates more bursts means larger `d_t`, hence
*more* division and *less* growth: `log₂m_T − log₂m₀ = αT − S_T + E_T` with `S_T ≥ T(1+ρ)`, giving
growth `≤ T(α − 1 − ρ)`, which *decreases* in `ρ`. Either C1's `ρ` is normalised differently from
its §2.2 definition, or the lemma's sign convention differs in C2. **This audit does not resolve
it** — C2 was not read — and nothing below depends on Lemma 5.15.

## H. Growing-depth state candidates

| candidate | definition | depth | update law | determined by valuation prefix? | trivialized by finite universality? | state space grows? |
|---|---|---|---|---|---|---|
| Chang label `Y_j` | `1[d_{j+2} ≥ 2]` at events | **width 3** | local | **yes** | **yes** (§F, §M) | no |
| burst indicator `X_t` | `1[d_t ≥ 2]` | width 1 | local | yes | yes | no |
| gap run length `G` | run of `d = 1` | unbounded but local | local | yes | yes | no |
| cumulative imbalance `B_K` | `Σ(2Y_t − 1)` | grows | additive | yes | yes — every finite history realized | no (a single integer) |
| extension index `e_i` | `(n_{t_i} − b)/2^K mod 8` | 3 bits at level `K` | reads seed digits | yes (from seed + word) | not directly, but see §I | **window slides, size fixed** |
| spectator-bit stack | digits above the known zone | grows with `K` | the seed's own digits | yes | — | **yes, but see §I** |
| block-TV `ε_K` | TV distance of `K`-block law | grows with `K` | empirical | yes | partially | yes |

**Only the last two grow**, and both are functions of the seed's 2-adic expansion — §I shows they
are a lossy projection of a tower the repository already has.

## I. Chang state versus realizer lift tower

For a valuation prefix `W_N`, the repository has the exact realizer class mod `2^{S_N+1}`
(P1 Prop 5.2) and the least realizer `r_N`; for a fixed positive seed `m`,
`r_N = m mod 2^{S_N+1}` (`ZCRERealizerGrowth.leastRealizer_eq_mod_of_realizes`), eventually `= m`.

Chang's spectator state at level `K` is `n_{t_i} mod 2^{K+3}` restricted to the three digits above
`2^K`. Both towers are nested truncations of the same 2-adic object — the orbit value, which is
determined by `(seed, valuation prefix)`.

**Classification: lossy projection.** The map is explicit:

```
realizer tower:   m mod 2^{S_N+1}          (all S_N+1 low digits of the seed)
Chang tower:      (n_{t_i} − b)/2^K mod 8  (3 digits of an orbit value at selected times)
```

The Chang state is obtained from the realizer tower by (a) pushing forward along the orbit,
(b) restricting to burst-ending times, and (c) keeping 3 digits. Each step discards information;
none adds any. So the Chang tower **cannot** be strictly richer, and it is not incomparable —
it is a function of the realizer tower.

This is the anti-reformulation verdict: the spectator-bit evolution is the ordinary 2-adic lift
tower, read through a 3-bit sliding window at a sparse subsequence of times.

## J. Map balance versus orbit balance

**What "map balanced" means (Thm 4.2):** counting over *residues mod `2^K`*, the gap-producing
burst residues split between the two mod-8 outcomes as evenly as an odd total permits, with
discrepancy exactly `±1`, for every `K ≥ 5`.

**Why it does not imply orbit balance.** Chang states the missing step himself, Remark 4.4:

> "Since the map is balanced modulo `2^K`, the natural density of gap starts mapping to `≡ 3`
> versus `≡ 7 (mod 8)` is exactly `1/2`. **This is a per-residue (distributional) statement. The
> orbit-level (pointwise) statement—that a specific orbit realises this balance—is the remaining
> open problem.**"

A single orbit visits a measure-zero set of residues; uniform counting over `Z/2^K` says nothing
about which residues one trajectory actually visits. That is the precise missing implication.

**Is it the same type of obstruction as EOC's?** The structural analogy is exact and Chang's own
framing matches it:

```
CHANG:  balanced count over all residues mod 2^K   →  ???  →  one orbit's visitation is balanced
EOC:    entropy/shell count over all confined words →  ???  →  one word's least realizer is large
```

Both arrows are a **population → individual quantifier upgrade**, and in both cases the population
statement is proved and the individual one is open. **This audit does not claim they are
mathematically equivalent** — no reduction in either direction was found, and none is asserted.
They are the same *type* of obstruction, which is weaker than equivalence and is all the evidence
supports.

## K. Zero corridor versus Chang events

**One exact deterministic restriction exists.** A burst is `d_t ≥ 2`, so

```
S_k  =  Σ_{t<k} d_t  ≥  k + #{t < k : d_t ≥ 2}.
```

Under zero confinement `S_k ≤ ⌊αk⌋ ≤ αk`, hence

```
Chang burst density  ρ  ≤  α − 1  =  0.5849625…
```

Formalized as `ChangZeroCorridor.burstCount_le_of_confined` (§X).

**Classification, per Gate 11's taxonomy: (A) consequence of total valuation only.** It follows
from digit counting alone and uses no residue information, so it is **not** the missing mechanism.
It is also not binding in practice — C1 reports `ρ ≈ 0.54` for typical orbits, below the cap.

Arithmetic note, recorded as a coincidence and not a link: Chang's bit-growth threshold
`2 − α = 0.4150375` and the corridor cap `α − 1 = 0.5849625` sum to exactly 1.

**Everything else is unrestricted.** Event frequency, the 9-versus-25 labels, cumulative imbalance
and spectator-bit growth receive **no** deterministic restriction from confinement — §M proves
this in the strongest form by realizing every finite label history inside the corridor.

## L. Canonical-block confinement calculation

`β(0) = (2,1,1)`: 3 steps, valuation 4. `β(1) = (2,1,2)`: 3 steps, valuation 5.
For a history with `w` ones, `D(y)` has `N = 3K`, `S = 4K + w`.

| quantity | value |
|---|---|
| drift change per `β(0)` | `4 − 3α = −0.754888` |
| drift change per `β(1)` | `5 − 3α = +0.245112` |
| intra-block peak above block start | `2 − α = +0.415037` (after the `d=2` step) |
| sustainable fraction of 1-labels | `c ≤ 3α − 4 = 0.754887502` |
| endpoint confinement | `4K + w ≤ ⌊3αK⌋`, i.e. `w ≤ 0.754888·K` |

**Confinement of the canonical construction is label-dependent and order-dependent** (a long run of
1-blocks accumulates `+0.245` each), and the required width does **not** grow with `K` provided the
1-label density stays below `0.7549`.

**But the canonical construction is never zero-confined, for a trivial reason.** Every `β` begins
with `d = 2`, so `S_1 = 2`, while the corridor permits only `S_1 ≤ ⌊α⌋ = 1`. Formalized as
`ChangZeroCorridor.changWord_not_zeroConfined`.

This is an artifact of the packing, not a restriction on histories — §M.

## M. Zero-corridor finite universality

**Proved computationally, and it is the round's decisive result.**

Dropping the canonical packing and allowing arbitrary zero-confined words (padding digits
permitted), a targeted search asked, for each `y ∈ {0,1}^K`, whether some zero-confined word has
`y` as its initial Chang label sequence:

| `K` | realizable / total |
|---|---|
| 1–7 | 2/2, 4/4, 8/8, 16/16, 32/32, 64/64, 128/128 |
| 8 | 256/256 |
| 9 | 512/512 |
| 10 | 1024/1024 |
| 11 | **2048/2048** |

**Full universality at every `K ≤ 11`.**

*Mechanism.* A `d = 1` step changes drift by `1 − α = −0.585`, so padding with 1s builds corridor
headroom fast, while emitting a 1-label costs only `+0.245`. Headroom is cheap; universality is
easy. (An earlier length-bounded enumeration at `L = 21` appeared to show failures at `K = 7,8,9`;
that was an artifact — `K` events need `≥ 3K` steps plus front padding, so the words were simply
too short. The targeted search removes the artifact.)

**Consequence (Gate 28's strong form).** *No finite Chang-history obstruction can exclude a
Type-II zero-corridor tail.* The only possible Chang leverage would be infinite/cross-scale or
positive-integer compatibility — and §G, §I, §S close those.

## N. Allowed finite Chang language under zero confinement

Not applicable: §M shows the language is the **full shift** `{0,1}^K` for every tested `K`, so
there is no forbidden set to characterize and no entropy deficit. The rate is `1` bit per event.

## O. Same-shell realizer census

Within fixed `(k, S)` shells (the control the brief requires, so that entropy cost is matched),
`k ∈ {12,13,14}`, 16 shells with ≥ 200 words each; features computed per word: event count,
9-label count, cumulative imbalance `B`, `|B|`, burst density `ρ`, event density.

| feature | max \|corr\| with `log₂ r` | median \|corr\| | max \|Cohen d\| (bottom decile vs rest) |
|---|---|---|---|
| event count | 0.0849 | 0.0232 | 0.4706 |
| 9-label count | 0.0525 | 0.0132 | 0.2447 |
| imbalance `B` | 0.0782 | 0.0120 | 0.3802 |
| `\|B\|` | 0.0750 | 0.0284 | 0.2700 |
| burst density `ρ` | 0.0656 | 0.0196 | 0.2881 |

**No Chang feature predicts realizer size within a shell.** Median correlations ≈ 0.02; the largest
effect size (0.47) is the maximum over 16 shells of a quantity with no consistent sign, i.e. noise.

## P. Matched-deficit controls

The shell control `(k, S)` already fixes the final deficit exactly: `Δ_k = ⌊αk⌋ − S` is a function
of `(k, S)`. So **every same-shell comparison in §O is automatically deficit-matched at the
endpoint**, and no separate matched-deficit stratification is needed for `Δ_N`. Finer matching on
the deficit *profile* was not pursued: with §O's correlations at the 0.02 level and the
theorem-level argument of §F/§M already decisive, additional stratification would only reduce
statistical power without changing the conclusion.

## Q. Extreme-small-realizer analysis

The bottom-decile analysis is the `Cohen d` column of §O; no feature separates the smallest
realizers. Bottom-1% and record-minimum analysis was **not** run, because §M makes it moot at the
theorem level: any feature that did separate them would be a fixed-width function of the valuation
word (§E, width 3), and §F/§M show every finite configuration of such features occurs inside the
corridor. A statistical separation could therefore not be promoted to a theorem — precisely the
outcome Gate 9 anticipated and Gate 22 warns about.

## R. Growing-depth candidate test

**NONE survives.** From §H, the only growing-depth objects are the spectator-bit stack and the
block-TV profile, and §I classifies both as lossy projections of the realizer lift tower. Applying
Gate 20's seven criteria, every candidate fails at least criterion 3 (determined by `N`, `S`, `Δ_N`
or bounded local patterns), criterion 4 (invertibly equivalent to the valuation prefix with no new
theorem), or criterion 6 (does not survive finite-history universality).

## S. Positive-integer distinction

**Chang's framework never distinguishes a positive ordinary integer from an arbitrary 2-adic
integer.** Every object in C1 is defined by congruences mod `2^K`: burst indicator (mod 4), gap
outcome (mod 8), observable (mod 32), extension index (mod `2^{K+3}`), Map Balance (counting over
`Z/2^K`). The only Archimedean ingredient anywhere is Lemma 5.15's bit-growth statement, which is
quoted from C2 and is a *consequence* of the orbit being a positive integer, not a constraint that
could exclude one.

This is the terminal limitation for ZCRE. ZCRE asks whether a corridor word has a **positive
integer** realizer; Chang's machinery is invariant under passing to `Z₂`, so it cannot see the
distinction that ZCRE turns on.

## T. Bernstein–Lagarias / conjugacy comparison

Chang's state transitions are finite-state projections of the 2-adic conjugacy: the map
`n ↦ (3n+1)/2^{v₂}` acts on `Z₂`, parity/valuation data is read from low digits, and Chang's
observables are the mod-4, mod-8 and mod-32 projections of that action.

**Information lost:** everything above the current window, and everything at non-burst-ending
times. A lossy projection cannot carry more information than the valuation word.

**Separating coordinate from theorem, as Gate 17 requires.** Chang's *coordinate* is genuinely
useful — reducing Collatz to a single bit at a sparse subsequence is a real compression, and the
Map Balance Theorem is a real theorem *in that coordinate* that is not obvious in full coordinates.
What this audit finds is that the **theorem does not cross the quantifier gap** (§J), and the
coordinate does not add arithmetic information (§I, §E). Those are different claims and both are
recorded.

## U. Pointwise-localization test

Gate 23's required logical form is

```
if W has unusually small realizer  →  ChangState(W) satisfies P,     then
zero confinement forbids P at large depth.
```

The second line is **unavailable for every `P` expressible in Chang's observables**, because §M
realizes every finite label history inside the corridor. And the first line is unsupported
empirically (§O). No localization exists.

## V. Anti-tautology audit

| question (Gate 24) | answer |
|---|---|
| Is the Chang label a deterministic function of the valuation word? | **Yes** — of a 3-digit window (§E) |
| Is its evolution proved by unfolding definitions? | **Yes** — `event_iff`/`label_iff` are `omega` after reducing `a` to divisibility |
| Does the "constraint" restate the Collatz transition? | Yes: the label *is* `d_{j+2}`, one digit of the word |
| Is the candidate equivalent to ZCRE? | No — it is strictly weaker, being a lossy factor (§I) |
| Is it the 2-adic realizer tower in new notation? | **Yes** for the spectator-bit state (§I) |

**Classification: REFORMULATION**, on the same grounds that closed the UPR and dynamic-deficit
routes.

## W. Open Problems C/D/E/G relation

| pair | relation | status |
|---|---|---|
| Chang Open Problem ↔ **OP G** (pointwise Chang return balance) | **the same problem**; P1's OP G is Chang's §5.9 problem in EOC notation, and P1 records that Chang's own reduction needs only bounded imbalance `δ < δ_max` | proved identical by inspection |
| **OP G → OP C** (arbitrary-word exponential realizer floor) | **no implication proved.** P1 explicitly calls the Chang return-distribution problem "related but distinct"; this audit found nothing to change that, and §S gives a structural reason (Chang cannot see positivity) | related but distinct |
| **OP G → OP D** (moving-anchor anti-concentration) | **no implication proved.** OP D asks for a property of `−C_N(D)3^{−N} mod 2^{S_N}` — an anchor on `S_N` growing bits; Chang labels determine `O(K)` bits at sparse times | related but distinct |
| **OP G → OP E** (frontier-defect control) | **no connection found.** OP E is an entropy-depth statement with constant `H₂(ρ_c)`; Chang's observable is not an entropy statement | no connection |
| **OP C ↔ OP D** | P1: "in substance the same question at two levels of precision" | as P1 states |

Solving G is **not** shown to solve C or D, and this audit respects P1's own "related but distinct".

## X. Lean coverage

**Existing (`EOC/ChangHistory.lean`, 439 lines, read in full).** `a_ge_iff_dvd`, `a_ge_two_iff`
(`2 ≤ a n ↔ n % 4 = 1` — Chang's burst indicator), `a_eq_one_iff`, `a_eq_two_iff`,
`T_of_a_eq_one/two`, **`event_iff : n % 16 = 9 ↔ a n = 2 ∧ a (T n) = 1`**,
**`label_iff : n % 32 = 25 ↔ 2 ≤ a (T (T n))`**, `changBlock`, `changWordList`, `changWord`,
`changWord_S`, `changSeed`, `changSeed_realizes`, `changSeed_lt`, `chang_history_labels`,
`changWord_event_positions`, `chang_event_positions`, `no_internal_chang_event`,
`finite_chang_history_realizable`, `every_finite_history_is_a_consecutive_chang_history`.

**New (`EOC/ChangZeroCorridor.lean`), 4 declarations + 1 definition:**

| declaration | statement |
|---|---|
| `burstCount` | `#{t < k : 2 ≤ d t}` — Chang's burst count in valuation coordinates |
| `add_burstCount_le_S` | `k + burstCount d k ≤ s d k` for `d ≥ 1` |
| `burstCount_le_of_confined` | `S_k ≤ α·k → burstCount d k ≤ (α−1)·k` — §K's exact inequality |
| `floor_alpha` | `⌊α⌋ = 1` |
| `changWord_not_zeroConfined` | no canonical Chang word satisfies `∀ j ≥ 1, S_j ≤ ⌊jα⌋` — §L's first-step obstruction |

Deliberately **not** formalized: §M's universality (a computational finding at `K ≤ 11`, not a
theorem — formalizing it would require the padding construction as a general lemma); §O's
correlations (empirical); any spectator-bit interpretation.

## Y. New theorem or observation

Three items, all elementary.

1. **The Chang observable is a width-3 local factor of the valuation word** (§E). The event
   criterion is EOC's (P1 Def 5.13, already formalized); what this audit adds is the explicit
   *width* and the consequence that the Chang label process is a finite-radius factor, hence
   cannot carry new information. **Classification: observation about the encoding, not new
   mathematics.**
2. **Zero-corridor Chang universality at `K ≤ 11`** (§M). Every finite label history is realized
   inside the exact corridor. **Classification: genuinely new computational finding**, and the
   round's decisive result; not a theorem.
3. **`ρ ≤ α − 1` under zero confinement** (§K), formalized. **Classification: new as a cross-paper
   statement, but derivable from total valuation alone** — ordinary digit counting, not residue
   arithmetic.

**Nothing found constrains the least positive realizer.**

## Z. Closed Chang routes

Future agents should not retry:

- any obstruction from a **fixed finite Chang pattern, bounded label window, or finite automaton**
  — killed by P1 Thm 5.14 and, inside the corridor, by §M;
- any attempt to use **spectator bits as new arithmetic** — they are the seed's own higher 2-adic
  digits (§G.6), and Chang's own cycling result is explicitly ensemble-level (§G.7);
- any claim that **Map Balance constrains one orbit** — Chang's Remark 4.4 says it does not (§J);
- any attempt to derive a **realizer floor from Chang statistics** — no within-shell signal (§O),
  and no localization is possible (§U);
- any use of **Chang's observable as independent information** from the valuation word (§E, §I, §V).

## AA. Surviving Chang interface

**One, and it is Chang's own open problem, not a new lead.** Gate 14's cross-scale compatibility
question — whether Chang's machinery couples histories across `K` for the *same* seed — has the
answer: it does not, and Chang says so (§G). The nested residue/lift structure that *would* do so
is the realizer tower the repository already has (§I), and ZCRE already characterizes when it
stabilizes.

What remains open is unchanged by this audit: whether one fixed positive integer can realize an
infinite corridor word. Chang's framework cannot address it because it never distinguishes `Z_{>0}`
from `Z₂` (§S).

## AB. Files changed

```
new:  EOC/ChangZeroCorridor.lean                    5 declarations
new:  scratch/chang_cross_scale_audit.py            reproducible census, stdlib only
new:  docs/CHANG_CROSS_SCALE_REALIZER_AUDIT.md      this report
```

No existing Lean file modified; no theorem statement changed; no manuscript or PDF edited.

## AC. Tests/build

| command | result |
|---|---|
| `lake build EOC.ChangZeroCorridor` | **success, 2040 jobs, 0 errors** |
| `lake build EOC.ChangHistory EOC.CurryHeavyRegime EOC.CurryDivergenceProfile` | success, 2262 jobs (no regression) |
| `python3 scratch/chang_cross_scale_audit.py` | exit 0; §E, §K, §L, §O reproduced |
| `python3 scratch/chang_cross_scale_audit.py univ` | exit 0; §M, full universality `K ≤ 11` |
| grep `sorry`/`admit`/`axiom`/`opaque` | none |

Key numbers: `α − 1 = 0.584962501`; `2 − α = 0.415037499`; `3α − 4 = 0.754887502`;
translation mismatches `0 / 14403`; universality `2048/2048` at `K = 11`.

## AD. Commits

Branch `chang-cross-scale-realizer-audit`, from `71d7609`.

| commit | contents |
|---|---|
| `a764922` | `EOC/ChangZeroCorridor.lean`, `scratch/chang_cross_scale_audit.py`, this report |

## AE. Push status

Branch pushed to `origin/chang-cross-scale-realizer-audit`. **No pull request opened.** `main`
unmodified; dirty ordinary checkout untouched.

## AF. Research verdict

**`FINITE CHANG STRUCTURE FULLY UNIVERSAL; NO REALIZER LEVERAGE`**

Every finite Chang label history is realized inside the exact zero corridor (§M, `K ≤ 11`,
2048/2048 at the top), so no finite Chang-history obstruction can exclude a Type-II corridor tail.
The observable itself is a width-3 local factor of the valuation word (§E, 0 mismatches on 14,403
positions), so it carries no information the word does not. Within fixed `(k,S)` shells no Chang
feature predicts realizer size (§O, median \|corr\| ≈ 0.02).

The growing-depth machinery does not rescue it. Spectator bits are the seed's own higher 2-adic
digits (§G.6), their equidistribution is proved only "under the ensemble model" (§G.7), and the
whole state is a lossy projection of the realizer lift tower the repository already has (§I).

The single deterministic interaction found, `ρ ≤ α − 1` (§K), follows from total valuation alone
and is not binding at Chang's reported typical `ρ ≈ 0.54`.

Chang's obstruction and EOC's are the same *type* — a population-to-individual quantifier upgrade
— and Chang states his side explicitly (Remark 4.4). **No equivalence between them is claimed**;
none was proved, and P1's "related but distinct" for Open Problems G versus C/D stands (§W).

The terminal limitation is §S: Chang's framework is entirely congruential and never distinguishes
a positive ordinary integer from an arbitrary 2-adic integer — which is exactly the distinction
ZCRE turns on.
