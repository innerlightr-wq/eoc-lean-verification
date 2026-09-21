# The zero-corridor realizability frontier

*Research specification for the phase after the Curry foundation. Nothing in this document is
proved; it defines the object, separates what is easy from what is hard, inventories existing
machinery against it, and specifies (but does not run) a computational experiment.*

---

## 20. The exact surviving object

A **valuation word** is `W = (d_0, d_1, …)`, `d_i ∈ ℤ_{≥1}`. Define

```
S_n(W) = Σ_{i<n} d_i,          Δ_n(W) = ⌊αn⌋ - S_n(W),      α = log₂3.
```

**Symbolic admissibility** (established unconditionally for the tail of any hypothetical
Type-II orbit, by `docs/CURRY_FOUNDATION.md` §8.5–8.6, contingent only on Curry's audited
Theorem 2.3):

```
Δ_n(W) ≥ 0        for all n ≥ 1,
Δ_n(W) → ∞         as n → ∞.
```

**Arithmetic realizability** is a separate condition. The classical noniterative 2-adic
realizer (Bernstein 1994; the exponent sequence is exactly the valuation word) is

```
Φ(W) = -Σ_{j≥0} 2^{S_j(W)} · 3^{-(j+1)}   ∈ ℤ₂ (the 2-adic integers).
```

`W` is **positive-integer realized** if there is an actual odd positive integer whose
accelerated Collatz orbit has valuation word `W` — equivalently (Bernstein–Lagarias 1996's
conjugacy `Φ ∘ S ∘ Φ⁻¹ = T`), if the 2-adic limit `Φ(W)` happens to land on
`ℤ_{>0}` when finite truncations are read off correctly, i.e. every finite prefix `W|_N` is
realized by a genuine positive integer through step `N`, consistently as `N → ∞`.

## 21. Why symbolic admissibility is easy and arithmetic realizability is hard

The symbolic conditions (`Δ_n ≥ 0`, `Δ_n → ∞`) constrain only the *digit sum*, at one
prefix-length resolution. An enormous space of sequences `(d_i)` satisfies them — e.g. take
any sequence with `d_i = 1` on a density-1 subset and occasional larger digits spaced to keep
the running deficit growing; the recurrence `Δ_{k+1} = Δ_k + b_{k+1} - d_k` (§8.6) makes this
constructively trivial. **This is the "easy part," and it is the part Curry's chain
resolves.** Arithmetic realizability is a global, non-local condition: whether *the specific
infinite 2-adic number* `Φ(W)` is (in the limit sense above) a positive ordinary integer is a
question about the arithmetic structure of the whole tail simultaneously, not decomposable into
per-prefix checks. This is exactly the manuscript's own **moving-anchor problem** (§5.3–5.4 of
the manuscript, Remark 5.12), independently flagged there as open for reasons that have nothing
to do with Curry or the drift axis.

Three populations, in increasing order of difficulty:

* **Population A — generic zero-corridor words.** Only the symbolic conditions above. Vast,
  easy to construct, of no direct arithmetic interest by itself.
* **Population B — finite positive-integer-realizable prefixes.** Finite words `W|_N` whose
  least positive realizer `r(W|_N)` exists via the exact residue class (`EOC.Realizer.
  leastRealizer` and its congruence machinery) — every finite word is realized by *some*
  positive integer (finite realizability is classical/unconditional; see
  `EOC/RealizerLift.lean`), so this population is also large and not yet the hard question.
* **Population C — infinite words with an actual positive-integer orbit.** The genuine
  candidate counterexample population: infinite words realized *coherently*, at every prefix
  length, by the *same* growing positive integer (i.e., by a real orbit). **This is what the
  next research phase must characterize**, restricted to the zero-corridor, diverging-deficit
  subclass identified by the Curry chain.

## 22. Inventory of existing invariants

| Invariant | Where | Distinguishes realizable zero-corridor words from generic ones? |
|---|---|---|
| Least realizer `r(W\|_N)` (`EOC.Realizer.leastRealizer`) | `Realizer.lean` | **NO — already known insufficient** by itself: every finite word has one (classical residue-class argument), so it says nothing about *infinite*, *coherent* realizability. |
| Residue anchor `ξ(W)` / coarse anchor `ξ_N` | `Realizer.lean`, `TransportCollapse.lean`, `PrescribedMatching.lean` | **MAYBE.** For eventually-periodic `W`, the anchor is a single fixed rational and forces `r(W\|_N) → ∞` (Theorem 5.9) — a genuine discriminator, but only within the periodic sector; for a general word "there is no single fixed rational number to invoke periodicity of" (Remark 5.12) — this is precisely why the sector is open. |
| Infinite realizer `Φ(W)` (Bernstein series) | classical (cited, not a repository construction) | **UNKNOWN as a computational discriminator.** Exactly the quantity Population C's condition is stated in terms of; no repository tool currently decides membership from `Φ(W)` alone for a general word. |
| Carry `C(W)`, `C_N(D)` closed form | `Carry.lean` | **NO — already known insufficient** on its own: it is a finite polynomial in the digits, well-defined for *every* finite word regardless of realizability; the pairwise-collision law built from it (§5.4 of the manuscript) was investigated and found to "reduce to ordinary symbolic prefix geometry, with no residual arithmetic content" — a checked negative result, not a discriminator. |
| Reduced rational denominator / rational height | not separately isolated in the repository | **UNKNOWN.** No repository theorem currently connects denominator growth to realizability of an infinite word; plausible direction, unproved. |
| Periodic anchor (Theorem 5.9) | `Confinement.lean`, `Realizer.lean` | **YES — proven discriminator, but only for the periodic/eventually-periodic sector** (see §23): forces `r(W\|_N) → ∞`, hence (via `Population C` requiring bounded-size coherent realization at each step) rules out coherent realization by a *bounded* seed for that sector — it does not bound realizers within the sector by a growing seed the way an actual orbit would, so it is a genuine exclusion mechanism there. |
| Bulk/first-defect anchor stability (Prop. 5.10) | `Confinement.lean` region (manuscript) | **YES, within its sector** (bounded number of defects after a periodic run) — same caveat as above: controlled sector only. |
| Bounded-defect retraction (Remark 5.11) | manuscript | **NO — checked and refuted** as a general mechanism: late periodic recovery does *not* restore anchor precision for sparse, growing-gap defects; recorded as a negative result, not a discriminator. |
| Prefix/suffix decomposition, collision law | `PrefixSuffixBilinear.lean`, `FirstDivergence.lean` | **NO — reduces to symbolic geometry**, per the checked negative result above. |
| Shell injectivity / survivor clustering | `SurvivorClusters.lean`, `SurvivorDensity.lean`, `SurvivorCounting.lean` | **UNKNOWN** as applied to this specific question; these tools count/cluster survivors under confinement bounds, not under the zero-corridor/diverging-deficit condition specifically — untested in this combination. |
| Moving-anchor obstruction itself | manuscript §5.3, Remark 5.12 | **This *is* the open problem**, not a tool for attacking it; restated here as the frontier's own subject. |

## 23. Sectors already controlled

| Sector | Rigorous control | Empirical only | Still open |
|---|---|---|---|
| Periodic (`W` eventually a fixed repeating block) | ✓ Theorem 5.9: `r(W\|_N) → ∞`, realizer floor exists | | |
| Eventually periodic (fixed finite prefix + periodic tail) | ✓ Theorem 5.9 (transformed anchor argument) | | |
| Single first defect after a periodic run of length `a` | ✓ Proposition 5.10: `r(D) ≥ 2^{aS_X - B_X}` for `a` large, independent of what follows the defect | | |
| Bounded number of defects, growing gaps, "recovery restores precision" | | | ✗ **Refuted** (Remark 5.11) as a control mechanism — recorded as negative, not as "controlled" |
| Sturmian / mechanical words (`d*_j = ⌊α(j+1)⌋ - ⌊αj⌋`) | ✓ stays below the critical line; least realizers unbounded (corollary of row G, `BoundedDrift*.lean`) | | Relation to López–Stoll's 3x+1-conjugacy-over-Sturmian-words result flagged **UNCERTAIN** in `docs/NOVELTY_AND_PROVENANCE.md` row 24 — same map/word class, question asked may differ |
| Morphic words (general substitution systems) | | | ✗ **Not investigated** by this repository at all |
| Bounded-term `S`-unit / bulk-defect reductions beyond Prop. 5.10's exact shape | | some numeric exploration in `scratch/` (e.g. `scratch/pair_valuation_2026-09-14/`) is diagnostic, not a theorem | ✗ open |
| **Zero-corridor, unboundedly-many-defects, diverging-deficit** (this document's Population C) | | some record-holder seeds studied in `scratch/horizon_2026-09-14/`, `scratch/pair_valuation_2026-09-14/` (diagnostic only, not aimed at this exact condition) | ✗ **open — this is the frontier** |

## 24. Characterizing "genuinely irregular," precisely

After removing every sector controlled in §23, what survives and must be justified feature by
feature — no adjective is included below without a specific reason:

* **Aperiodic / non-eventually-periodic** — justified: Theorem 5.9 already controls every
  eventually-periodic word, so the surviving sector must avoid that shape entirely.
* **Unbounded defect count** — justified: Proposition 5.10 controls any word with a periodic
  run followed by a *single* defect (or, by iterating, any word reducible to finitely many such
  events with the *stable* mechanism); Remark 5.11 shows growing-gap sparse defects are **not**
  rescued by recovery, so an unbounded, non-decaying defect structure is exactly what escapes
  both positive results.
* **No fixed rational anchor / moving anchor** — justified: this is the manuscript's own
  characterization of exactly the surviving sector (Remark 5.12), restated here as a
  requirement rather than merely a description.
* **Diverging deficit `Δ_n → ∞`** — justified: new to this audit, forced unconditionally on any
  Type-II orbit's tail by the Curry chain (§8.6); not present in the manuscript's own
  characterization of the moving-anchor sector, and worth carrying forward as an *additional*
  constraint the surviving sector must satisfy, on top of (not instead of) moving-anchor status.

Explicitly **not** included, for lack of justification found anywhere in this repository or the
audited literature: "unbounded rational-height complexity" and "no bounded-term `S`-unit
representation" — plausible-sounding but not established as necessary properties of the
surviving sector by anything reviewed here. A future argument that needs either should prove it
directly rather than assume it.

## 25. The exact theorem that would kill Type II

**Zero-Corridor Realizability Exclusion (ZCRE), provisional formulation:**

```
ZCRE:  For every valuation word W = (d_i)_{i≥0} realized by an odd positive integer m with
       injective accelerated orbit, some prefix exceeds the Beatty line:
              ∃ k ≥ 1 :  S_k(W) > ⌊αk⌋.
```

**Scope check.** ZCRE is restricted to *injective* orbits from the start — this is not an
afterthought but load-bearing: the known `1`-cycle (`orbit 1 = 1, 2, 1, 2, …` under the
unaccelerated map; the accelerated map's fixed behavior at the trivial cycle) is
**non-injective**, hence outside ZCRE's hypothesis entirely, exactly as it is outside every
hypothesis in the Curry chain (§8.8, §U). ZCRE as formulated above does *not* accidentally
exclude the trivial cycle or any other known eventually-periodic behavior, because it only ever
makes a claim about words belonging to *injective* orbits.

**The logical package.** Combining ZCRE with the zero-corridor tail theorem (§8.5): if `m` has
an injective accelerated orbit, its tail word satisfies `S_k ≤ ⌊αk⌋` for all `k ≥ 1` past some
`n₀` (Curry chain) — but ZCRE says every word realized by an injective orbit has *some* `k`
with `S_k > ⌊αk⌋`. Restricting ZCRE's witness `k` to lie past `n₀` (a minor reformulation —
"eventually" rather than "somewhere" — needed to make the two statements collide; see the
intermediate targets in §26 for why the eventual form may be the more tractable one to attack
first) gives a direct contradiction:

```
Curry + ZCRE (eventual form)  ⟹  no injective accelerated orbit exists  ⟹  no Type-II
divergent orbit exists.
```

This says **nothing about Type-I nontrivial cycles**, which remain a fully separate exclusion
problem (§U of the Curry Verification Audit; unchanged by anything in this document).

## 26. Intermediate targets, ranked by logical usefulness

Not by estimated probability of success — by how directly each, if proved, would narrow the
problem, and how each relates logically to ZCRE.

1. **(A) Realizer-growth obstruction.** Show the least positive realizer of successive
   zero-corridor prefixes must eventually exceed any fixed positive integer. *Relation to
   ZCRE:* **sufficient but not obviously equivalent** — if realizers are forced unbounded for
   *every* zero-corridor word (not just periodic ones, where this is already Theorem 5.9), no
   fixed seed can realize the whole infinite word, which is a route to ZCRE via a different
   mechanism than the direct combinatorial one. The natural generalization of the repository's
   *only* currently-proved discriminator (Theorem 5.9) to the full zero-corridor sector.
2. **(B) Moving-anchor escape.** Show the anchors `ξ_n(W)` of any zero-corridor,
   diverging-deficit word cannot 2-adically stabilize to a positive ordinary integer unless
   eventually periodic. *Relation to ZCRE:* **plausibly equivalent** — this is close to a direct
   restatement of what "positive-integer realized" should mean 2-adically, via
   Bernstein–Lagarias conjugacy; proving it would likely *be* a form of ZCRE rather than a
   stepping stone to it.
3. **(C) Carry-cancellation obstruction.** Show positive-integer realization forces a carry
   relation incompatible with `Δ_n → ∞`. *Relation to ZCRE:* **genuinely weaker, if true** — a
   carry-only obstruction (via `EOC.Carry.C`, `q`) would be a narrower, more mechanical target
   than the full anchor-based (B), and its failure or success would clarify whether the
   obstruction (if one exists) is "arithmetic" (carry-based, near (C)) or "geometric" (anchor/
   2-adic, near (B)) in character — valuable to know either way.
4. **(D) Complexity escalation.** Show a positive-integer-realized zero-corridor word cannot
   sustain the necessary unbounded irregularity (some complexity measure must stay bounded for
   realizable words, contradicting the unbounded-defect requirement of §24). *Relation to
   ZCRE:* **sufficient if a suitable complexity measure can be found and shown realizability-
   incompatible with unboundedness** — but no such measure is currently identified or justified
   in this repository (§24 deliberately excludes "unbounded rational-height complexity" for
   exactly this reason); this target is contingent on first solving a definitional problem.
5. **(E) Recurrence obstruction.** Show positive-integer realization forces some block
   recurrence incompatible with injectivity or deficit divergence. *Relation to ZCRE:*
   **already partially tested and found NOT to hold in the form investigated** — the
   pairwise-collision-law route (manuscript §5.4) was checked and found to reduce to symbolic
   prefix geometry with "no residual arithmetic content" (a genuine negative result). A
   *different* recurrence mechanism than the one already tried would be needed for this target
   to be live; the burden is on identifying what mechanism, specifically, differs from the
   checked one.

**Recommendation for where to start:** (A), because it is the direct, minimal generalization of
the *one* mechanism already proved to work in a sub-sector (Theorem 5.9), and its failure would
be informative (it would show the periodic sector's mechanism does not generalize, sharpening
exactly where the real difficulty lives) even if its success does not immediately hand over
ZCRE outright.

## 27. Routes already known not to work, or not new

The next phase should not repeat, without a genuinely new ingredient:

* Chain A Fourier / dangerous-window audit (the repository's Tao-style machinery is a
  *conditional* result gated on `TaoMixingHypothesis`, an unproved external interface — it does
  not currently reach this frontier and re-running it here would not either, absent progress on
  that hypothesis itself);
* arbitrary complexity statistics with no realizability-connection criterion (see §28 — any
  candidate must pass this bar first);
* generic entropy counting (already fully spent on the Curry/window-sparsity axis; nothing left
  to extract from entropy counting alone for the *residue* axis);
* fixed-modulus congruence packing (proved terminal at `B < 8/9` for exactly this reason,
  independently of Curry — manuscript Theorem 4.5, Appendix D/E);
* Pell / continued-fraction drift approximants (no repository result connects these to
  realizability; would need to be developed from scratch with a stated realizability
  connection, not assumed);
* periodic-only arguments (Theorem 5.9's mechanism, already fully used; the surviving sector is
  defined by *excluding* periodicity);
* bounded-defect-only arguments (Proposition 5.10's mechanism, already fully used and shown
  **not** to extend via naive recovery — Remark 5.11);
* cross-repository analogy hunting without a stated, checked connection back to `Φ(W) ∈ ℤ_{>0}`;
* recovery-efficiency alone (the specific mechanism Remark 5.11 already refuted).

A future argument that reduces to one of these without a new ingredient should be flagged
immediately, not re-run to confirm the known outcome.

## 28. Discriminator criterion

For any future candidate invariant `I(W)`, before spending further effort on it, require an
answer to:

> **Does `I` distinguish finite prefixes coming from a fixed positive-integer orbit from
> matched synthetic zero-corridor words?**

A candidate invariant should ideally interact with the exact arithmetic identity

```
m_0 - ξ_n  =  3^{-n} 2^{S_n} m_n
```

(or an equivalent exact identity already in the repository, e.g. `orbit_mul_two_rpow_R`'s
underlying carry relation) — because this identity is the one place a *purely symbolic*
statistic is forced to interact with the *actual* growing seed `m_n`, which is exactly the
gap between Population A and Population C in §21. Purely symbolic statistics (digit
histograms, block-recurrence counts, entropy of the word alone) are **insufficient on their
own** unless shown to connect back to this identity or an equivalent one — this is the lesson
of the checked-negative pairwise-collision-law result (§26, item E), which was a purely
symbolic statistic and, unsurprisingly in hindsight, carried no arithmetic content.

## 29. Suggested computational experiment — specification only

*Not run in this phase. Protocol only, so a future session can execute it without re-deriving
the design.*

**Populations to construct, matched:**

* **Actual:** prefixes of real accelerated-Collatz orbits (odd seeds, `EOC.orbit`), filtered to
  those staying at or below the zero-corridor line for as long as computationally feasible
  (candidates: extend the repository's existing record-holder search infrastructure in
  `scratch/pair_valuation_2026-09-14/` and `scratch/horizon_2026-09-14/`, which already track
  long-confined / long-surviving seeds, rather than writing new orbit-generation code).
* **Synthetic:** zero-corridor words constructed directly from the deficit recurrence (§8.6),
  matched to the actual population on: length, total valuation `S_N`, deficit profile
  `(Δ_n)_{n≤N}`, and (where useful) digit histogram.

**Statistics to compare, per matched pair:**

* least realizer `r(W|_N)` (`EOC.Realizer.leastRealizer`) and its growth rate with `N`;
* anchor movement `ξ_n - ξ_{n-1}` (or the coarse anchor sequence);
* carry `C_N(D)` and its growth;
* reduced rational height of the realizer (numerator/denominator size after `gcd` reduction);
* prefix-realizer growth rate (`log r(W|_N) / N`, compared against the Theorem 5.9 rate for the
  periodic sector as a reference point);
* denominator/gcd cancellation patterns across the prefix sequence;
* defect spacing (gaps between successive `k` with `d_k` "large," in the sense of the deficit
  recurrence);
* recurrence statistics (block-repetition counts, to re-test whether the checked-negative
  pairwise-collision result was specific to its exact formulation or general).

**Explicit goal.** Not a predictive or machine-learning exercise — the goal is to surface an
**exact arithmetic discriminator candidate**: some statistic that behaves detectably
differently on the Actual population versus the Synthetic population, in a way traceable back
to a specific identity (per the §28 criterion), which could then be conjectured and pursued as
a proof target (most naturally feeding into intermediate target (A) or (C) from §26).
