# EOC Lean Verification

Formal infrastructure for the accelerated 3x+1 map, valuation words, realizer
arithmetic, confinement, and Tao-style almost-all estimates.

> **The Collatz conjecture remains open.** This repository does **not** claim
> a proof of the Collatz conjecture.
>
> **The Global Occupation Conjecture (EOC)** — this project's own guiding
> conjecture — **is itself open.**
>
> Some results below are **conditional on an explicit interface to
> Tao-style valuation mixing** (`TaoMixingHypothesis`, see below) and
> therefore do **not** constitute a formalization or proof of Tao's theorem
> itself.

This repository is a companion artifact to the current manuscript revision:

> Elias De Jesús (2026). *A Global Occupation Conjecture for the Accelerated
> 3x + 1 Map: Divergent-Orbit Sparsity, Exact Realizers, and the
> Moving-Anchor Problem.* Zenodo.
> [doi:10.5281/zenodo.22286812](https://doi.org/10.5281/zenodo.22286812)
> (all-versions DOI: [10.5281/zenodo.20569293](https://doi.org/10.5281/zenodo.20569293))

**Revision 5 (September 2026)** reorganized the manuscript around two axes:
the **drift/Archimedean axis** (sparsity and drift behavior of a
hypothetical divergent orbit) and the **residue/arithmetic-placement axis**
(how small the exact integer realizing a prescribed valuation word can be
— the axis this repository's Lean formalization targets). Its principal
mathematical additions are summarized in
[Manuscript highlights (Revision 5)](#manuscript-highlights-revision-5)
below.

Every theorem labeled **FORMALLY VERIFIED** below compiles against a pinned
Mathlib revision with `lake build`. Results labeled otherwise are marked
accordingly — see the [status legend](#formalization-status-legend).

## Current verified milestone — ShapeTail (2026-09-16)

- **PROVED (LEAN):** for every even j ≥ 300, the actual Collatz barrier b(j) = ⌊j log₂ 3⌋ satisfies the repository's
  `ShapeTail` estimate (N₀ = 10, K = ⌊j/25⌋, ρ₁ = 2^{−⌊j/300⌋}). Badly shaped confined words occupy an
  exponentially small share of the top shell.
- **Explicit rate:** ρ₁ ≤ 2·2^{−j/300}.
- **Main theorem:** `EOC.ShapeUnconditional.shapeTail_allEven_rate` (also `shapeTail_allEven`, `shapeTail_cofinal`).
- Kernel checked, standard Lean/Mathlib axioms only (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`,
  no `native_decide`.
- **Pressure-only chain (PROVED (LEAN), `EOC/AverageOddDark.lean`):** `AverageOddDarkPressure ⇒ CriticalWhiteCount ⇒
  LowFreqDecay` with no ShapeTail hypothesis; at s = 3 the averaged pressure must stay below ≈ 0.14 (N₀ = 30) or
  ≈ 0.17 (N₀ = 100).
- **Main remaining analytic blocker:** the arithmetic input below (OPEN). Nothing here proves `CriticalWhiteCount` or
  `LowFreqDecay` unconditionally, improves the exceptional exponent, or proves EOC or Collatz.

### Current arithmetic frontier

The formal chain now isolates one explicit OPEN hypothesis, `PowerOfTwoDangerousWindowSparsity`
(`EOC/ArithmeticFrontier.lean`). Lean proves (PROVED (LEAN), standard axioms only):

    PowerOfTwoDangerousWindowSparsity  ⇒  SummedOddDarkPressure  ⇒  LowFreqDecay
      (summedPressure_of_powerOfTwoSparsity; lowFreqDecay_of_powerOfTwoSparsity, using the proved ShapeTail and the
       frequency-summed form of the CriticalWhiteCount argument)

So `LowFreqDecay` follows by a PROVED (LEAN) implication from the OPEN `PowerOfTwoDangerousWindowSparsity` hypothesis.
The hypothesis bounds how many logarithmic windows can carry odd-dark pressure above rate 1/10. For the lowest
frequency shell (λ = 1) it is a statement about leading ternary digit patterns of powers of 2, in the same general
family as classical unresolved digit questions; it is **not** known and **not** claimed equivalent to any named
conjecture. A 1230-environment scan found no dangerous window, and the worst exact certified rate is 0.09124
(COMPUTATIONAL; evidence, not proof). Details: [`docs/ARITHMETIC_FRONTIER.md`](docs/ARITHMETIC_FRONTIER.md).

Details: [`docs/SHAPETAIL_UNCONDITIONAL.md`](docs/SHAPETAIL_UNCONDITIONAL.md). How this relates to the literature:
[`docs/LITERATURE_CONTEXT.md`](docs/LITERATURE_CONTEXT.md).

## Current status — September 2026

A dated, detailed account is in [`docs/RESEARCH_STATUS.md`](docs/RESEARCH_STATUS.md). Labels there: PROVED (LEAN),
PROVED (MATH), EXTERNAL THEOREM, COMPUTATIONAL, HEURISTIC, CONJECTURAL, REFUTED, OPEN.

**Formally verified** (Lean, `lake build` passes, 94 modules, no `sorry`, standard axioms only):

- pair-valuation, transport and survivor-counting results (`PairValuation`, `SuffixTransport`, `TransportCollapse`,
  `UpperEscape`, `SurvivorCounting`, …) and the baseline exceptional exponent H₂(1/α) ≈ 0.949956
  (`ExceptionalPowerBound`);
- the exact Tao triangle geometry for U(a,b) = (2^{−a} mod 3^b)/3^b: recurrences, propagation, merging
  (`TriangleArray`);
- the pair-block Fourier interface: `BlockCubeHyp` instantiated for L = 2 blocks (`BlockCubeInstance`), and
  positive-density-good-angle ⇒ low-frequency decay ⇒ `WeightedFourier` (`GoodAngles`, `DecayInterface`,
  conditional on explicit hypotheses);
- the Rényi-2 / prefix-sharing barrier (`RenyiBarrier`, `RenyiInstance`);
- the sharp distinct-triangle hop theorem: consecutive black cells in distinct triangles need (2^d + 3)η > 1, i.e.
  d ≥ 6 at η = 1/54, with a kernel-checked witness (160,5) → (154,6) (`TriangleHop`);
- the deterministic black-run decomposition n ≤ (2H₁+1)W + Occ(R₁) + H₁N₆ + 2H₁ (`TriangleHop`);
- the formal reduction of the p-adic Subspace Theorem (hypothesis `SubspaceInstance`) to sublinear maximal triangle
  size (`MaxTriangle`);
- (2026-09-16) unconditional `ShapeTail` for every even j ≥ 300 with rate 2·2^{−j/300} (`ShapeTail`, `ShapeBridge`,
  `ShapeCertificate`, `ShapeUnconditional`); white-cell contraction for pair blocks and the reduction
  `ShapeTail + OddDarkPressure ⇒ CriticalWhiteCount ⇒ LowFreqDecay/WeightedFourier` (`WhiteContraction`, `OddBlack`).

**Externally grounded mathematical result.** The p-adic Subspace Theorem (Schlickewei; Ridout case) together with the
repository's reduction implies **R_max(L) = o(L)** for Tao-black triangles along the critical corridor, for every fixed
η. The result is ineffective: no rate and no computable threshold. **It does not imply positive-density good angles or
A > 1/α.**

**Computational evidence** (not proofs):

- triangle sizes appear approximately exponentially distributed, P(size ≥ r) ≈ e^{−r};
- R_max is numerically compatible with O(log L) (R_max ≈ 8.2 at J = 6400);
- black occupation ≈ 2η;
- distinct-triangle hopping is rare;
- all of this resembles a random-unit environment.

**Open:**

- exponentially concentrated control of Tao-black triangle occupation under the critical confined law, now reduced
  to the named hypothesis `PowerOfTwoDangerousWindowSparsity` (the current bottleneck; `ShapeTail`, the other input
  of `CriticalWhiteCount`, is proved);
- any fixed low-frequency decay exponent γ > 0;
- any proof of A > 1/α (the exceptional exponent stays at H₂(1/α) ≈ 0.949956);
- EOC and the Collatz conjecture themselves (see below).

## Contents

- [Current verified milestone — ShapeTail](#current-verified-milestone--shapetail-2026-09-16)
- [Current status — September 2026](#current-status--september-2026)
- [The problem and the core map](#the-problem-and-the-core-map)
- [The Global Occupation Conjecture](#the-global-occupation-conjecture-eoc)
- [Manuscript highlights (Revision 5)](#manuscript-highlights-revision-5)
- [Formally verified infrastructure](#formally-verified-infrastructure)
- [The Tao-like almost-all program](#the-tao-like-almost-all-program)
- [Exact cylinder / next-digit arithmetic](#exact-cylinder--next-digit-arithmetic)
- [Proved mathematically, not yet Lean-packaged](#proved-mathematically-not-yet-lean-packaged)
- [The critical Sturmian boundary](#the-critical-sturmian-boundary)
- [Where the proof currently stops](#where-the-proof-currently-stops)
- [Natural next questions](#natural-next-questions)
- [Context: divergent orbits and Banach density](#context-divergent-orbits-and-banach-density)
- [Relation to prior Collatz literature](#relation-to-prior-collatz-literature)
- [Current research checkpoint](#current-research-checkpoint)
- [Repository map](#repository-map)
- [Formalization status legend](#formalization-status-legend)
- [Reproducing the build](#reproducing-the-build)
- [Literature](#literature)
- [License, citing, acknowledgments](#license-citing-acknowledgments)

## The problem and the core map

The accelerated odd-to-odd Collatz map:

```
T(m) = (3m + 1) / 2^a(m),      a(m) = ν₂(3m + 1)
```

For an orbit `m₀, m₁ = T(m₀), m₂ = T(m₁), ...`, define the **valuation word**
`d_n := a(m_n)`, its prefix sum `S_N := Σ_{n<N} d_n`, and

```
alpha := log₂ 3 ≈ 1.58496
R_N   := S_N − alpha·N        (the "drift" at step N)
```

`R_N` and `alpha·N` relate to the actual orbit values through the **exact
drift identity**

```
log₂(m_N / m₀) = N·alpha + E_N − S_N,      E_N := Σ_{n<N} log₂(1 + 1/(3m_n)) ≥ 0
```

equivalently `R_N = log₂(m₀/m_N) + E_N`. **PROVED MATHEMATICALLY** (derived
by hand from the repository's exact carry/orbit identities across several
audit milestones); it is not currently packaged as a single named Lean
theorem.

**Provenance (corrected, September 2026).** This identity is **not new**: it
is the base-2 logarithm of the product identity
`T^(j)(n)/n = 2^(−j)·Π_{k<q}(3 + 1/m_k)`, which is Lemma 2.5 of Rozier
(2017), itself a generalization of a formula of Eliahou (1993) for cycles.
The match is term for term, including the correction `E_N`. What belongs to
this repository is the drift bookkeeping, the confinement framing and the
formal packaging — not the identity. See
[`docs/NOVELTY_AND_PROVENANCE.md`](docs/NOVELTY_AND_PROVENANCE.md) §1.1.

## The Global Occupation Conjecture (EOC)

For fixed `c > 0`, define the **occupation count**

```
O_c(m₀) := #{ n ≥ 0 : R_n(m₀) ≤ c }
```

**EOC** conjectures logarithmic pointwise occupation: `O_c(m₀) = O(log m₀)`
for every odd `m₀` (with quantifiers exactly as stated in the manuscript's
Conjectures 3.1–3.4). **This conjecture is OPEN** — nothing in this
repository proves any tier of it.

**EOC is a weaker consequence of Rozier's Lower Bound Hypothesis.** LBH
(2017) conjectures `n ≥ j^(−C)·2^((1−H(q/j))·j)` for the least integer
realizing a length-`j` parity pattern with `q` odd terms — an
entropy-governed placement lower bound for the same map, which Rozier shows
would already imply that every trajectory reaches `1`.

**Theorem 3.11 of the manuscript proves LBH ⇒ EOC**: assuming LBH,
`O_c(m₀) ≤ (1/I(α))·log₂ m₀ + O_c(log log m₀)` for every fixed `c > 0`, so
LBH implies the sharp-leading tier and hence the existence tier. The proof
applies Rozier's own Theorem 4.1 manoeuvre at occupation times instead of at
total stopping time. EOC is therefore an **occupation-time shadow** of LBH,
not an independent conjecture — and no easier to reach, since LBH is itself
open and arguably harder.

The **converse (EOC ⇒ LBH) is open**; no equivalence is claimed, and Rozier
did not formulate the occupation functional. Details in
[`docs/NOVELTY_AND_PROVENANCE.md`](docs/NOVELTY_AND_PROVENANCE.md) §1.2.

Two weaker, related qualitative statements are also discussed in the
repository's audit trail:

- **Eventual escape / `CriticalCrossing`**: every odd seed `M` eventually has
  `R_N(M) > 0` for some `N` — equivalently, no natural seed realizes an
  infinite `0`-confined valuation word. **OPEN.**
- **Finite occupation**: `O_c(m₀) < ∞` for every `c, m₀`. **OPEN**, and
  logically weaker than EOC's `O(log m₀)` rate.

**None of EOC, `CriticalCrossing`, or the drift statements above eliminate a
hypothetical nontrivial positive cycle by themselves.** A separate
no-nontrivial-cycle input is required before any of this could bear on the
Collatz conjecture; this repository does **not** claim `EOC ⇒ Collatz`.

## Manuscript highlights (Revision 5)

These are results of the **manuscript** (paper-level mathematics, cited
above), not of this repository's Lean formalization, except where a
cross-reference to a specific tracked file is given. They are recorded here
so the README reflects the manuscript's current content; none of them are
claimed as Lean theorems unless a file is named.

**García–Tal mechanism; Curry quantitative theorem (divergent-orbit
sparsity).** Two separable pieces, not one joint result:

- **García and Tal (1999)** (see [Literature](#literature), item 2): the
  *qualitative* Banach-density-zero result for aperiodic/infinite orbits in
  generalized `3n+1` systems, via a collision-free/windowed pigeonhole
  mechanism. García–Tal do **not** state or prove an explicit power-saving
  exponent.
- **Curry (2026)**, "An Explicit Windowed Sparsity Bound for Divergent
  3x+1 Orbits, with Logarithmic-Floor Exclusion beyond the Harmonic
  Barrier" (see [Literature](#literature), item 3): a short,
  self-contained *explicit quantitative* sharpening of that same
  collision-free/window mechanism, combined with explicit Terras–Everett
  parity-prefix counting. Curry's Theorem 2.3: for a collision-free set `A`
  and every `β > β*`, there is `C_β` with
  ```
  #(A ∩ [a,a+X)) ≤ C_β · X^β · log(2X)     (uniformly in a)
  ```
  where
  ```
  β* = γ* log₂3 = H(γ*) ≈ 0.9653844,      γ* ≈ 0.6090897 solves H(γ) = γ·log₂3
  ```
  (`γ*` identified by Curry with Rozier's critical ones-ratio `r_H`). An
  infinite aperiodic orbit's value set is collision-free, so Curry's
  Proposition 3.1 gives `Σ_{x∈orbit} 1/x < ∞` for a divergent orbit — for
  this repository's accelerated odd iterates `m_n`, `Σ_n 1/m_n < ∞`, so the
  drift-identity correction term `E_N = Σ_{k<N} log₂(1+1/(3m_k))` (see
  above) stays **bounded** along any divergent orbit. Curry's Theorem 4.1,
  Theorem 4.2, and Corollary 4.3 then exclude every eventual logarithmic
  drift floor `R_n ≥ −B·log₂n + O(1)` for `B < 1/β* ≈ 1.0358567` —
  crossing the harmonic threshold `B = 1`.

**PRIMARY-SOURCE VERIFIED NEW QUANTITATIVE DEVELOPMENT** (by direct
inspection of Curry's paper by this repository's maintainer; the paper was
not independently re-derived or re-checked by an automated tool in this
documentation-correction session): Curry (2026) provides an explicit
quantitative sharpening of the García–Tal collision-free window mechanism,
obtaining `β* ≈ 0.9653844` and the floor-exclusion threshold
`1/β* ≈ 1.0358567`. Curry (Remark 2.4) states that the power saving is
implicit in García–Tal once the older exponents are made explicit, and that
he found no exact prior match for the explicit exponent `β*` or its
identification with Rozier's `r_H` — **this is Curry's own literature
assessment ("no exact match identified"), not an exhaustive independent
novelty verification performed here or in this repository.**

**This concerns hypothetical divergent orbits only; it does not prove EOC,
exclude nontrivial cycles, or resolve the arithmetic-placement/moving-anchor
problem below.**

**Corrected exact realizer congruence.** The manuscript's residue-axis
formulation places exact realizers of a length-`N` valuation word in one
residue class modulo `2^(S_N+1)` (not `2^(S_N)`), with the extra bit
enforcing terminal oddness. This is exactly what this repository formalizes
as `realizerCongruence` (row C, `Realizer.lean`) — **FORMALLY VERIFIED**,
already covered above.

**Fixed anchors and the moving-anchor problem.** For (eventually) periodic
valuation words, realizer floors arise from a *fixed* rational 2-adic
anchor — formalized here as the periodic-sector result (row F,
`Periodic.lean`/`PeriodicCore.lean`). For genuinely irregular words, the
relevant anchor *moves* with the word; deterministic anti-concentration in
this **moving-anchor problem** is the manuscript's name for the central
unresolved residue-axis obstruction. This is the same frontier this
repository's own audit trail independently arrived at and describes in
[Where the proof currently stops](#where-the-proof-currently-stops) below
(there, framed via `CriticalCrossing`, cylinder lifts, and the injective
bounded-drift case) — two descriptions of one open problem, not two
separate ones.

**Finite Chang-history universality.** Using a mod-32 return observable
related to Edward Y. Chang's one-bit orbit-mixing framework, the manuscript
proves every nonempty finite binary history is realized as consecutive
prescribed events of a genuine accelerated Collatz orbit, via canonical
length-3 valuation blocks `0 ↦ (2,1,1)`, `1 ↦ (2,1,2)`. **FORMALLY
VERIFIED** in this repository — row I, `ChangHistory.lean` (`changWord`,
`changSeed`, and supporting lemmas). This is a **finite** universality
theorem only: it does not establish asymptotic 1/2 balance, realization of
arbitrary infinite histories, a full-shift structure, EOC, or the Collatz
conjecture — see the module docstring for the complete list of what it does
not imply.

## Formally verified infrastructure

Only entries confirmed against compiled, tracked source are listed.

| Area | File(s) | Status | What is verified |
|---|---|---|---|
| A. Accelerated orbit / valuation words | `Basic.lean`, `ValuationWord.lean` | FORMALLY VERIFIED | `a`, `T`, affine closure; `Realizes`, the dynamical/formal-iteration bridge |
| B. Carry identities, exact finite-word realization | `Carry.lean` | FORMALLY VERIFIED | Carry recursion `q`, closed form `C`, `q_eq_C`, `iter_carry_eq` |
| C. Least-realizer congruence | `Realizer.lean` (frozen) | FORMALLY VERIFIED | `realizerCongruence`, `leastRealizer_*`, `coarseAnchor_*`, `residue_pinning` |
| D. Confinement / record-chronology | `Confinement.lean` | FORMALLY VERIFIED | `Confined`, `rmin`, `record_chronology`, `rmin_mono`, `single_window_equiv[_log]`, `coarse_depth_window` |
| E. Cylinder restart / affine transport | `TaoLike/Cylinder.lean`, `TaoLike/CylinderAppend.lean` | FORMALLY VERIFIED | `cylinder_restart`, `cylinder_restart_leastRealizer`, `cylinder_additivity` |
| F. Periodic-sector realizer escape | `PeriodicCore.lean`, `Periodic.lean` | FORMALLY VERIFIED | eventually-periodic confined word ⇒ `leastRealizer → ∞` |
| G. Bounded two-sided drift escape | `BoundedDriftCore.lean`, `BoundedDrift.lean` | FORMALLY VERIFIED | two-sided bounded drift ⇒ `leastRealizer → ∞` (pigeonhole/dyadic-packing argument) |
| H. Signed block / plus-minus realizer arithmetic | `SignedBlock.lean`, `SignedRealizer.lean` | FORMALLY VERIFIED | Sign-sensitive block recurrences; plus/minus realizer complement — statements about the recurrences only, not EOC/DTC/Collatz |
| I. Finite Chang-history realizability | `ChangHistory.lean` | FORMALLY VERIFIED | every finite binary "Chang history" is realized by some odd natural seed |
| J. Harmonic AP discrepancy | `TaoLike/HarmonicAP.lean` | FORMALLY VERIFIED | finite, deterministic residue-class discrepancy bounds (counting and harmonic-weighted) |
| K. Conditional residue total variation | `TaoLike/ResidueTV.lean` | FORMALLY VERIFIED | restarted cylinder state is quantitatively close to uniform on odd residues mod `2^Q` |
| L. External Tao mixing interface | `TaoLike/TaoInterface.lean` | **CONDITIONAL FORMAL RESULT** | `TaoMixingHypothesis`/`TaoMixingProperty` (M38: starting law must satisfy `IsProbabilityLaw`) — see [warning](#the-external-tao-interface) below |
| M. Conditional future valuation mixing | `TaoLike/ConditionalMixing.lean` | CONDITIONAL FORMAL RESULT | conditioned on a realized prefix, the future valuation vector is `TaoMixingHypothesis`-close to iid `Geom(2)^n` |
| N. iid geometric persistence Chernoff bound | `TaoLike/PersistenceModel.lean` | FORMALLY VERIFIED | exponential-rate upper bound on the abstract iid `Geom(2)^n` persistence event (not yet transferred to real orbits at this layer) |
| O. Shifted persistence transfer | `TaoLike/ShiftedPersistence.lean` | CONDITIONAL FORMAL RESULT | one restart + one future block, real-orbit persistence bound |
| P. Early/late decomposition | `TaoLike/EarlyLate.lean` | CONDITIONAL FORMAL RESULT | GOOD/BAD prefix split; iid upper-tail bound |
| Q. Prefix partition / restart-law alignment | `TaoLike/PrefixPartition.lean`, `TaoLike/RestartLawAlignment.lean` | FORMALLY VERIFIED | deterministic finite-probability bookkeeping — no `TaoMixingHypothesis` used |
| R. Fixed late-shift persistence | `TaoLike/LateShiftPersistence.lean` | CONDITIONAL FORMAL RESULT | true harmonic-window persistence bound, one fixed shift |
| S. All-shifts averaged persistence | `TaoLike/AllShiftsAveragedPersistence.lean` | CONDITIONAL FORMAL RESULT | finite-horizon union-over-shifts persistence bound |
| T. Normalized harmonic law | `TaoLike/NormalizedHarmonicLaw.lean` | FORMALLY VERIFIED / CONDITIONAL* | proves the harmonic window's probability mass genuinely normalizes to 1 (unconditional), then transfers R–S to the normalized law (conditional, inherited) |
| U. Harmonic exceptional-set summability | `TaoLike/HarmonicExceptionalSetSummability.lean` | CONDITIONAL FORMAL RESULT | dyadic-window summability of the exceptional (persistent) event; **audited explicitly not to yield a pointwise/soft-EOC conclusion** (ensemble statement only) |
| V. Finite-prefix injective drift-depth bound | `FinitePrefixPacking.lean` | FORMALLY VERIFIED | for `M` odd, injectivity of `orbit M` through `2^L` together with a uniform drift floor `R_j ≥ -g` through `2^L` forces `(3·2^L − 2)·2^(L+1) ≤ 2^g · M · 3^(L+1)` (`finite_prefix_injective_drift_depth_bound`), with a power-form corollary `2^(2(L+1)) ≤ 2^g · M · 3^(L+1)` for `L ≥ 1` (`finite_prefix_injective_drift_depth_power_bound`) — unconditional, no `TaoMixingHypothesis`; a finite-horizon refinement of the packing mechanism behind row G |
| W. Coprime-six harmonic packing / `8/9` logarithmic-floor exclusion | `HarmonicPacking.lean` | FORMALLY VERIFIED | for `M` odd with injective orbit and every real `B < 8/9`, `R_k ≥ −B·log₂ k` fails for infinitely many `k` (`injective_orbit_not_eventually_log_floor`, `injective_orbit_log_floor_fails_infinitely_often`; manuscript Thm 4.5), via the explicit carry budget `E_N ≤ (1/9)·log₂ N + 7/(9 ln 2)` (`carryE_le`; Lemma 4.3) and the exact carry demand `U_{k+1} − U_k = 2^(R_k)/(3m_0)` (`carryU_succ_sub`; Lemma 4.4) — unconditional, no `TaoMixingHypothesis`; formalizes the elementary fixed-modulus argument of manuscript §4.1 on top of row V's mod-`6` residue facts. **Prior art:** this uses the mechanism of Rozier (2017) Thm 2.6 — orbit distinctness bounds `Σ 1/m_k`, which bounds the carry budget — and reaches a **weaker** threshold than both that theorem in its regime and Curry's published `B < 1/β* ≈ 1.0359`. A formalization of an elementary argument, not a frontier result |
| X. Finite valuation words | `FiniteValuationWord.lean` | FORMALLY VERIFIED | finite-word representation `Fin N → ℕ` with prefix sums, total and positivity, and bridge lemmas to the existing valuation-word API: `prefixSum_eq_s` (finite prefix sums agree with `s`) and `paperConfined_alpha_iff_confined` (for `c ≥ 0`, confinement over `1 ≤ j ≤ N` is equivalent to `Confined`) — representation infrastructure only, no new Collatz dynamics |
| Y. Valuation-shell counting | `CompositionCounting.lean` | FORMALLY VERIFIED | exact cardinality of fixed-sum positive valuation shells, `#{compositions of s into N positive parts} = C(s−1, N−1)` for `1 ≤ N ≤ s` (`valuationShell_card`, classical stars and bars), and the cumulative count `∑_{N ≤ s ≤ B} C(s−1, N−1) = C(B, N)` for `N ≥ 1` (`terminalCount_eq_choose`, hockey-stick identity) — standard combinatorics, no new Collatz dynamics |
| Z. Chord rotation | `ChordRotation.lean` | FORMALLY VERIFIED | existence of a cyclic rotation whose prefix sums lie on or below the endpoint chord: for `0 < N` and a word of total `s`, some `r < N` has `N · S_j ≤ j · s` for all `j ≤ N` (`chord_rotation_nat`, real form `chord_rotation_real`), via the zero-sum cyclic-list lemma `exists_rotate_take_sum_nonpos` — existence of one rotation index only; the full confined-shell lower bound is **not** proved here, and nothing about EOC or Collatz dynamics is claimed |

\* Row T is split: the normalization theorem itself needs no external
hypothesis; the persistence-transfer corollaries it proves inherit the
`TaoMixingHypothesis` dependency from rows O/R/S.

`Realizer.lean` is deliberately **frozen**: later files import it read-only
and reprove anything needed locally from its public lemmas, so no later
change can silently alter an already-checked upstream result.

## The Tao-like almost-all program

The chain of results (rows J–U above) runs:

```
harmonic sampling
  -> residue equidistribution (K)
  -> external Tao-style valuation mixing (L, EXTERNAL)
  -> comparison with iid Geom(2) (M)
  -> persistence rarity (N)
  -> shifted / all-shifts exceptional-set estimates (O, P, Q, R, S)
  -> generic dyadic summability framework (T, U)
```

The **iid reference law**: `P(G = q) = 2^{-q}`, `q ≥ 1` (`geom2` in
`TaoInterface.lean`).

The **persistence exponential rate**:

```
I₀ = alpha − alpha·log₂(alpha) + (alpha−1)·log₂(alpha−1)
   = alpha·(1 − H₂(1/alpha))
   ≈ 0.0793186127748554
```

(`I0` in `PersistenceModel.lean`, proved positive by `I0_pos`.)

The **proven Chernoff-type model bound** (on the abstract iid model,
`geometric_persistence_upper_bound`):

```
P(C_{c,n}) ≤ exp(lambda* · c) · 2^{-I₀·n}
```

with `lambda* = log(alpha / (2(alpha−1)))` (`lambdaStar`, proved `> 0`).

**The repository does not currently prove a pointwise implication from these
almost-all estimates.** The remaining almost-all-to-pointwise bridge is
**OPEN** — see [Where the proof currently stops](#where-the-proof-currently-stops).

## Exact cylinder / next-digit arithmetic

Foundational, unconditional (no Tao dependency) fact used throughout the
Tao-like chain and the more recent audit work below:

If a seed `m` realizes a valuation prefix of cumulative valuation `S_t`,
then for **every** `k : ℕ`, `m + 2^(S_t+1)·k` realizes the *same* prefix,
and

```
orbit(m + 2^(S_t+1)·k, t) = orbit(m, t) + 2·3^t·k.
```

**FORMALLY VERIFIED** — `cylinder_restart`, `cylinder_restart_leastRealizer`
(`TaoLike/Cylinder.lean`), `cylinder_additivity` (`TaoLike/CylinderAppend.lean`).

## Proved mathematically, not yet Lean-packaged

The following two results come from a recent audit-only research phase
(exploring whether the almost-all machinery above can be pushed toward a
genuine pointwise statement). They are **derived and cross-checked by exact
computation, but not yet stated or proved as Lean theorems** in tracked
source.

### Exact next-digit law from cylinder lifting

**PROVED MATHEMATICALLY; NOT YET PACKAGED AS A LEAN THEOREM.**

Fix a realized prefix and vary the cylinder lift parameter `k` (from
`cylinder_restart`, above) uniformly modulo increasing powers of two. Then

```
P(next valuation digit = q | prefix) = 2^{-q},    q ≥ 1
```

*exactly*, independent of the prefix's own specific data. This is an
**exact arithmetic consequence** of the cylinder lift parameterization —
proved via a direct ultrametric/2-adic argument on `ν₂(A + 2·3^t·k)` — not
an assumption of temporal independence, and it was cross-checked by exact
enumeration (`k` up to `2^20`) against a concrete prefix.

**This does not claim that successive valuation digits along one actual
orbit are independent.** It gives an internal arithmetic derivation of the
same `Geom(2)` one-step law used as the iid reference distribution in the
Tao-like persistence model above (`geom2`) — a clean bridge between the two
halves of the program, but not new pointwise leverage.

### First crossing of the critical drift barrier

**PROVED MATHEMATICALLY; NOT YET LEAN-PACKAGED.**

Let `beta := alpha − 1`, `K_n := S_n − n`, so `R_n = K_n − beta·n`. For a
first crossing at `N` (i.e. `R_j ≤ 0` for `j < N`, `R_N > 0`), define

```
Delta_{N-1} := floor(beta·(N-1)) − K_{N-1} ≥ 0
b_{N-1}     := floor(beta·N) − floor(beta·(N-1)) ∈ {0, 1}
```

Then the final valuation digit must obey

```
d_{N-1} ≥ b_{N-1} + 2 + Delta_{N-1}
```

— verified both algebraically and numerically against every tested
long-confined record seed. Under uniform cylinder refinement (previous
subsection), this gives an exact one-step crossing hazard

```
h(Delta, b) = 2^{-(b + 1 + Delta)}.
```

**Again: this is a one-step conditional law on cylinder lifts, not a
pointwise probability law for one deterministic orbit.**

## The critical Sturmian boundary

The abstract "mechanical word" `d*_j := floor(alpha(j+1)) − floor(alpha·j)`
has digits in `{1, 2}` and satisfies `S*_N = floor(alpha·N)`, hence stays
strictly below the critical line `R = 0` for every `N > 0` — **PROVED
MATHEMATICALLY** (elementary, using only that `alpha` is irrational).
**Infinite abstract confined words therefore exist trivially**; the entire
difficulty is **natural-integer realizability**, not the existence of an
abstract confined path.

**PROVED MATHEMATICALLY (corollary of an existing formal theorem), not merely
computational**: the mechanical word has digits `d*_j ∈ {1,2}` (so `d*_j ≥
1`) and satisfies `-1 < R*_N ≤ 0` for every `N` (immediate from `floor(x) ≤ x
< floor(x) + 1` applied to `alpha·N`). Instantiating the already-formalized
`EOC.leastRealizer_unbounded_of_two_sided_drift` (row G, `BoundedDrift.lean`)
with upper bound `c = 0` and lower-drift bound `G = 1` shows directly that
`leastRealizer d* N` is unbounded as `N → ∞` — i.e. **no fixed natural seed
realizes all finite prefixes of this infinite mechanical word** (the least
realizers required grow without bound as the prefix length grows, so no
single fixed seed can keep up realizing the whole infinite word). This is a
corollary of an existing theorem instantiated on this specific word, not a
new Lean theorem about the mechanical word itself, and it says nothing about
other confined words. It is corroborated computationally: finite-prefix
least realizers of this canonical mechanical word were computed exactly
(via modular inverse, not brute-force search) up to `N = 1000`; they did
**not** stabilize, with bit-length growing approximately linearly in `N` at
slope `≈ alpha`, consistent with the corollary above.

## Where the proof currently stops

Almost-all persistence rarity (the Tao-like program above) does not exclude
one predetermined exceptional natural seed. A single length-`N` realizer
cylinder has mass roughly `2^{-alpha·N}`, while the aggregate persistence
event's exponential scale is `2^{-I₀·N}`. Since

```
alpha − I₀ ≈ 1.506 bits/step,
```

a single exceptional cylinder can remain far smaller than the total
exceptional-set allowance the summability theorem (row U) can afford to
spend on it. **The missing ingredient is not merely a sharper first-moment
probability bound.**

Possible missing mechanisms (all **OPEN RESEARCH DIRECTIONS**, none
currently supported by a proof in this repository):

- arithmetic amplification of one bad seed into many companion seeds;
- repeated, correlated restart structure across shifts;
- pointwise rigidity distinguishing natural seeds from generic 2-adic
  realizers (audited: no such rigidity was found — an eventually-zero
  seed tail is fully compatible with the fresh-bit exclusions imposed by
  non-crossing, so no contradiction was forced this way);
- higher-moment / survivor-clustering structure.

A related, audited limitation: the original two-sided (infinite-horizon)
bounded-drift pigeonhole mechanism (row G) requires a depth bound `G`
independent of `N`. The **finite-prefix** quantitative refinement of this
same packing argument (row V, `finite_prefix_injective_drift_depth_bound`)
supersedes any earlier claim that the mechanism could only exclude an
`O(log log N)` depth floor: it is a genuine **logarithmic** magnitude-packing
obstruction. **MATHEMATICALLY DERIVED** from row V (not itself a packaged
Lean theorem): whenever `orbit M` is injective through `N` with a uniform
drift floor `−G(N)`, `G(N) ≥ (2 − log₂3)·log₂N − O_M(1)`
(`2 − log₂3 ≈ 0.4150374993`). This excludes every fixed lower drift
bound, every `O(log log N)` or `o(log N)` floor, and every logarithmic floor
with coefficient below `2 − log₂3` — strictly stronger than the `O(log log
N)` ceiling previously stated here. It does **not** exclude an arbitrary
`O(log N)` floor with larger coefficient, an `N^θ`-scale floor, or
`sqrt(N)`-scale negative drift, so it still falls short of (and by itself
does not rule out) the empirically shallow depth observed on long-confined
record seeds (numerically consistent with roughly logarithmic growth over
the tested record range — see the record list below; not a proved
asymptotic rate). It still cannot be triggered by first-passage
words as they actually behave.

## Natural next questions

Not promises — directions the audit trail has flagged as plausible next
statistical experiments, not yet attempted:

- conditioned deficit moments `E[Delta_N | confinement]`,
  `Var(Delta_N | confinement)`;
- pair correlations between overlapping persistence windows;
- second moments of the number of bad shifts;
- whether rare survivors cluster in special arithmetic cylinders;
- whether such clustering could produce an almost-all-to-pointwise
  amplification mechanism.

**Variance/second-moment information, even if obtained, would not by itself
yield pointwise control** — it would still be an ensemble statement.

## Context: divergent orbits and Banach density

García and Tal (1999) prove Banach-density-zero results for orbit
representative sets in generalized `3n+1` systems, under their stated
hypotheses. **This repository's Lean formalization does not use, extend, or
reprove their result**, and does not attribute any quantitative
power-saving exponent to García and Tal's own paper — they state none. The
companion manuscript's Revision 5 *does* use an explicit quantitative
windowed-sparsity refinement of this qualitative result — see
[Manuscript highlights](#manuscript-highlights-revision-5) above — but that
refinement (the exponent `β* ≈ 0.9653844` and the resulting
`B < 1/β* ≈ 1.0358567` floor-exclusion threshold) is Michael John Curry's
own theorem (2026; primary source now inspected directly by this
repository's maintainer — see [Literature](#literature), item 3), built on
top of the García–Tal mechanism, not a result of García and Tal's own 1999
paper, and is not (yet) formalized in this repository.

## Current research checkpoint

**FORMALLY VERIFIED** (rows A–K, N, Q, V of the table above):
exact accelerated-orbit / valuation infrastructure; carry identities;
realizer congruences; confinement/record-chronology; cylinder restart and
additivity; periodic-sector and bounded-two-sided-drift realizer escape;
harmonic AP and residue-TV infrastructure; iid persistence Chernoff
estimate; prefix-partition/restart-law bookkeeping; the finite-prefix
injective drift-depth packing bound (row V).

**CONDITIONAL FORMAL RESULT, on `TaoMixingHypothesis`** (rows L, M, O, P, R,
S, and the transfer half of T):
the full conditional-mixing → shifted-persistence → all-shifts →
(normalized) exceptional-set-summability pipeline.

**PROVED MATHEMATICALLY, NOT YET FORMALIZED**:
first-crossing terminal-digit threshold; exact `Geom(2)` next-digit law
under cylinder refinement; exact one-step crossing hazard; the exact drift
identity `R_N = log₂(m₀/m_N) + E_N`.

**COMPUTATIONAL**:
long confined record seeds (up to length 114, seed 1,027,431, among all odd
seeds `≤ 2^20`); canonical
critical-mechanical-word realizer growth (to `N = 1000`); record-holder
deficit/shadowing observations.

**OPEN**:
pointwise `CriticalCrossing`; quantitative EOC (any tier); the
almost-all-to-pointwise amplification mechanism; exclusion of nontrivial
positive cycles; the Collatz conjecture itself.

## Repository map

**Core dynamics**
`Basic.lean` · `ValuationWord.lean` · `Carry.lean`

**Realizer / cylinder arithmetic**
`Realizer.lean` (frozen) · `TaoLike/Cylinder.lean` · `TaoLike/CylinderAppend.lean`

**Confinement**
`Confinement.lean`

**Periodic-sector and bounded-drift escape**
`PeriodicCore.lean` · `Periodic.lean` · `BoundedDriftCore.lean` · `BoundedDrift.lean` ·
`FinitePrefixPacking.lean`

**Signed-block / Chang-history arithmetic**
`SignedBlock.lean` · `SignedRealizer.lean` · `ChangHistory.lean`

**Tao-like probability infrastructure**
`TaoLike/HarmonicAP.lean` · `TaoLike/ResidueTV.lean` · `TaoLike/TaoInterface.lean` ·
`TaoLike/ConditionalMixing.lean`

**Almost-all persistence pipeline**
`TaoLike/PersistenceModel.lean` · `TaoLike/ShiftedPersistence.lean` ·
`TaoLike/EarlyLate.lean` · `TaoLike/PrefixPartition.lean` ·
`TaoLike/RestartLawAlignment.lean` · `TaoLike/LateShiftPersistence.lean` ·
`TaoLike/AllShiftsAveragedPersistence.lean` · `TaoLike/NormalizedHarmonicLaw.lean` ·
`TaoLike/HarmonicExceptionalSetSummability.lean`

**Realizer / transport / survivor layer (2026-09-14)**
`PairValuation.lean` · `SuffixTransport.lean` · `TransportCollapse.lean` · `PrescribedMatching.lean` ·
`LogCorridor.lean` · `UpperEscape.lean` · `UpperCertificates.lean` · `SurvivorCounting.lean` ·
`CapacityBounds.lean` · `SurvivorDensity.lean` · `EntropyBounds.lean` · `SurvivorClusters.lean` ·
`ExceptionalPowerBound.lean` · `SplitPrefix.lean` · `LiftDigits.lean` · `ResidueDiscrepancy.lean`

**Fourier / exponent chain (2026-09-14/15)**
`ShellWeyl.lean` · `PrefixSuffixBilinear.lean` · `PrefixCollision.lean` · `PrefixStateFormula.lean` ·
`ShellwiseChain.lean` · `SwapBound.lean` · `SwapCollatz.lean` · `TwistExpansion.lean` · `WeightedChain.lean` ·
`FirstDivergence.lean` · `BlockCube.lean` · `ShellDecomposition.lean` · `ShellRefined.lean` · `ThreeBlock.lean` ·
`WhiteRun.lean` · `IntervalSieve.lean` · `SpacingChain.lean` · `PsiSieve.lean` · `PsiShellBound.lean` ·
`PowerOrbit.lean` · `RenyiBarrier.lean` · `DecayInterface.lean` · `RenyiInstance.lean` · `GoodAngles.lean`

**Tao-triangle layer (2026-09-15)**
`TriangleArray.lean` · `BlockCubeInstance.lean` · `MaxTriangle.lean` · `TriangleHop.lean`

**White count / ShapeTail layer (2026-09-16)**
`WhiteContraction.lean` · `OddBlack.lean` · `LocalWindow.lean` · `ShapeTail.lean` · `ShapeBridge.lean` ·
`ShapeCertificate.lean` · `ShapeUnconditional.lean` · `AverageOddDark.lean` · `BinomialEntropy.lean` ·
`LogAbsorb.lean`

**Pointwise-descent side results (2026-09-16; `DirectDescent` assumes the OPEN `LinearRealizerFloor`)**
`DirectDescent.lean` · `HarmonicFloor.lean` · `LiftGap.lean`

**Experimental / historical**
`scratch/` (tracked in git, but deliberately outside the `EOC` Lean library
target — see `lakefile.toml`) holds the exact/numerical experiments and the
per-round research reports; see [`scratch/README.md`](scratch/README.md) for
reproduction commands. None of its contents are proofs; the computational
evidence quoted in [Current status](#current-status--september-2026) is
labeled COMPUTATIONAL. `CHANG_CYLINDER_SCRATCHPAD.md`'s own file
inventory (§10) and open-question list (§9, OQ4) additionally mention
`CHANG_CYLINDER_SCRATCHPAD.md.bak`, `EOC/PeriodicRealizer.lean`, and three
`scratch/transport_*`/`tcc2.py` scripts: none of these exist anywhere in this
repository's working tree or git history (verified by `git log --all` /
`git ls-tree`) — they are unavailable, not merely untracked, and any claim
resting on them should be read as historical/unreproducible from this repo
alone. The earlier audit-only research phase is narrated in
[`docs/RESEARCH_CHECKPOINT_2026-09.md`](docs/RESEARCH_CHECKPOINT_2026-09.md); the
2026-09-15 checkpoint of the triangle / Subspace rounds is in
[`docs/RESEARCH_STATUS.md`](docs/RESEARCH_STATUS.md), with literature in
[`docs/LITERATURE_SUBSPACE_TRIANGLES.md`](docs/LITERATURE_SUBSPACE_TRIANGLES.md). The 2026-09-16 ShapeTail milestone is
documented in [`docs/SHAPETAIL_UNCONDITIONAL.md`](docs/SHAPETAIL_UNCONDITIONAL.md), and the relation to the 3x+1
literature in [`docs/LITERATURE_CONTEXT.md`](docs/LITERATURE_CONTEXT.md).

## Formalization status legend

| Label | Meaning |
|---|---|
| **FORMALLY VERIFIED** | Compiles in Lean and the theorem exists in tracked source, with no external hypothesis |
| **CONDITIONAL FORMAL RESULT** | Compiles in Lean, but the theorem assumes an explicit external hypothesis (here, always `TaoMixingHypothesis`) |
| **PROVED MATHEMATICALLY** | Derived and audited by hand (and, where noted, cross-checked by exact computation), but not yet packaged as a Lean theorem |
| **COMPUTATION** | An exact or numerical experiment; evidence, not proof |
| **OPEN** | No proof currently known in this project |

### The external Tao interface

`TaoMixingHypothesis` / `TaoMixingProperty` (`TaoLike/TaoInterface.lean`) is
an **EXTERNAL THEOREM INTERFACE**: an explicit hypothesis structure — not a
Lean `axiom` — quoting Tao's Proposition 1.9 (arXiv:1909.03562, v7) and
consumed as a parameter by any downstream theorem that needs it.

**The repository does not contain a Lean formalization of Tao's analytic
proof.** Any theorem depending on `TaoMixingHypothesis` is conditional on
that external result being true, exactly as Tao proved it in his own paper
— it is not re-derived here.

**M38 (probability-law boundary repair).** Before M38, `EventProb α := Set
α → ℝ` was only an extensional carrier — a bare set function with no
additivity or normalization requirement — and `TaoMixingHypothesis`
quantified its starting law `N` over arbitrary such functionals, constrained
only by an odd-support condition. M38 adds `IsProbabilityLaw P`
(`TaoInterface.lean`): `P` must equal `genEventProb w` for some nonnegative,
summable atom-weight function `w` with `∑' x, w x = 1`.
`TaoMixingHypothesis.finite_valuation_mixing` and `TaoMixingProperty` now
require `IsProbabilityLaw N` before their conclusion applies, closing the
interface to arbitrary non-probability set functions. The canonical laws the
pipeline actually uses — `iidGeom2VectorProb`
(`iidGeom2VectorProb_isProbabilityLaw`), `unifOddResidues`
(`unifOddResidues_isProbabilityLaw`), and `conditionalRestartLaw` under its
stated normalization hypotheses (`conditionalRestartLaw_isProbabilityLaw`,
`TaoLike/ConditionalMixing.lean`) — are all certified `IsProbabilityLaw`, so
the repair is not vacuous. `TaoMixingHypothesis` itself remains, exactly as
above, an **EXTERNAL THEOREM INTERFACE**: the repository still does not
prove Tao's theorem; M38 repairs the mathematical fidelity of the boundary
so that downstream conditional theorems can no longer instantiate Tao mixing
against an arbitrary non-probability set function. `lake build` succeeds on
the full repository; no `sorry`, `admit`, or custom axiom was introduced,
and `#print axioms` on `TaoMixingHypothesis`,
`conditionalRestartLaw_isProbabilityLaw`,
`conditional_future_valuation_mixing`, and `harmonic_exceptional_summability`
shows only Lean's standard core axioms (`propext`, `Classical.choice`,
`Quot.sound`).

## Reproducing the build

```bash
git clone https://github.com/innerlightr-wq/eoc-lean-verification
cd eoc-lean-verification
lake exe cache get   # downloads prebuilt Mathlib .olean files
lake build
```

A successful run ends with `Build completed successfully`. To check a single
file in isolation:

```bash
lake env lean EOC/Confinement.lean
```

- **Lean**: `4.34.0-rc1`
- **Mathlib**: pinned revision in `lake-manifest.json` — do not `lake update`
  without expecting to re-verify.

## Relation to prior Collatz literature

EOC builds on a long classical literature, and a Zotero-assisted provenance
audit (September 2026) reduced several of this repository's framings
accordingly. The full claim-by-claim matrix is in
[`docs/NOVELTY_AND_PROVENANCE.md`](docs/NOVELTY_AND_PROVENANCE.md);
the narrative provenance is in
[`docs/LITERATURE_CONTEXT.md`](docs/LITERATURE_CONTEXT.md); the verified
bibliography is [`references.bib`](references.bib).

**What is classical and used here as input.** The accelerated / Syracuse map
and the parity-vector encoding (Terras; Everett); the congruence
"parity vector of length `j` ⇔ residue class mod `2^j`" and its 2-adic
closed form (Terras; Bernstein 1994; Bernstein–Lagarias 1996); the exact
product identity relating an orbit's endpoints to its odd terms, whose
logarithm is this repository's drift identity (Eliahou 1993; Rozier 2017
Lemma 2.5); composition counting and the cycle lemma (Dvoretzky–Motzkin);
stochastic/iid models (Lagarias–Weiss; Kontorovich–Lagarias; Sinai);
almost-all results in logarithmic density (Tao), used only as an explicit
hypothesis; the p-adic Subspace and Ridout theorems (Schlickewei; Ridout),
used as external theorems.

**What is closest to this repository's own conjectural layer.** Rozier's
**Lower Bound Hypothesis** (2017) is an entropy-governed lower bound on the
least integer realizing a prescribed parity pattern, proved unconditionally
for ones-ratio `≤ 1/log₂3` under orbit distinctness, and sufficient for the
absence of divergent trajectories. It is the closest published relative of
the Global Occupation Conjecture and of this repository's `H₂(1/α)`
exponent, and it was previously uncited here. Curry (2026) supplies the
explicit quantitative divergent-orbit sparsity used by the manuscript, and
is **stronger** than this repository's own `8/9` logarithmic-floor
exclusion.

**What remains defensibly distinct after the audit.** Only the following,
and each with its stated scope:

- the **exact confined-word ensemble** and its layered-kernel analysis —
  `ShapeTail` unconditionally for every even `j ≥ 300` with rate
  `2·2^{−j/300}`, via an explicit super-eigenvector certificate. No
  equivalent statement was identified in the literature reviewed;
- the **formal architecture** itself: the `CriticalWhiteCount ⇒ LowFreqDecay
  ⇒ WeightedFourier ⇒ exceptional-set bound` chain as machine-checked
  implications, and the isolation of one named arithmetic hypothesis
  (`PowerOfTwoDangerousWindowSparsity`);
- the **Lean formalization of classical results** — the parity-vector
  congruence, the 2-adic reconstruction, the composition count, the cycle
  lemma. Known mathematics, and a genuine formalization contribution;
- the **negative result** internal to the approach: the Rényi-2 /
  prefix-sharing barrier.

Nothing here proves EOC or Collatz, and the exceptional-set exponent remains
`H₂(1/α) ≈ 0.949956`.

**Scope note.** Both literature documents list only work that is part of the
repository's **provenance** — used, depended on, formalized, or required as
closest prior art. Papers read during exploration without contributing a
theorem, method, or claim are deliberately not listed.

## Literature

A verified reference list with context (Terras, Everett, Lagarias, Lagarias–Weiss, Tao, Rozier, Eliahou, Bernstein, …)
is in [`docs/LITERATURE_CONTEXT.md`](docs/LITERATURE_CONTEXT.md), with machine-readable records in
[`references.bib`](references.bib) and per-claim provenance in
[`docs/NOVELTY_AND_PROVENANCE.md`](docs/NOVELTY_AND_PROVENANCE.md).

1. Terence Tao, "Almost all orbits of the Collatz map attain almost bounded
   values," *Forum of Mathematics, Pi* **10** (2022), e12.
   [arXiv:1909.03562](https://arxiv.org/abs/1909.03562).
   Source for the logarithmic-density almost-all result, the Syracuse
   acceleration, and the probabilistic transport/mixing context behind
   `TaoMixingHypothesis`.

2. Manuel V. P. Garcia and Fabio A. Tal, "A note on the generalized 3n+1
   problem," *Acta Arithmetica* **90**(3) (1999), 245–250.
   Source for generalized `3n+1` systems and Banach-density-zero orbit
   results — see [Context](#context-divergent-orbits-and-banach-density).

3. Michael John Curry, "An Explicit Windowed Sparsity Bound for Divergent
   3x + 1 Orbits, with Logarithmic-Floor Exclusion beyond the Harmonic
   Barrier," Zenodo, 2026.
   DOI: [10.5281/zenodo.22087163](https://doi.org/10.5281/zenodo.22087163).
   Source for the explicit quantitative sharpening of the García–Tal
   mechanism (`β* ≈ 0.9653844`, floor exclusion `B < 1/β* ≈ 1.0358567`) and
   reciprocal summability cited in
   [Manuscript highlights](#manuscript-highlights-revision-5) above; primary
   source inspected directly by this repository's maintainer, not by an
   automated tool in this session.

4. Yakov G. Sinai, "Statistical (3x+1)-problem," *Communications on Pure
   and Applied Mathematics* **56**(7) (2003), 1016–1028.
   DOI: [10.1002/cpa.10084](https://doi.org/10.1002/cpa.10084).
   Background on statistical/probabilistic approaches to the 3x+1 dynamics.

5. Alex V. Kontorovich and Jeffrey C. Lagarias, "Stochastic Models for the
   3x+1 and 5x+1 Problems," in *The Ultimate Challenge: The 3x+1 Problem*,
   American Mathematical Society, 2010. Also
   [arXiv:0910.1944](https://arxiv.org/abs/0910.1944).
   Background on stochastic/iid modeling of valuation sequences.

6. Günther J. Wirsching, *The Dynamical System Generated by the 3n+1
   Function*, Lecture Notes in Mathematics 1681, Springer, 1998.
   DOI: [10.1007/BFb0095985](https://doi.org/10.1007/BFb0095985).

7. Jeffrey C. Lagarias, "The 3x+1 Problem: An Overview,"
   [arXiv:2111.02635](https://arxiv.org/abs/2111.02635).

8. Jeffrey C. Lagarias, "The 3x+1 problem and its generalizations,"
   *American Mathematical Monthly* **92** (1985), 3–23.
   DOI: [10.1080/00029890.1985.11971528](https://doi.org/10.1080/00029890.1985.11971528).

9. Olivier Rozier, "The 3x+1 problem: a lower bound hypothesis,"
   *Functiones et Approximatio Commentarii Mathematici* **56** (2017),
   no. 1, 7–23.
   DOI: [10.7169/facm/1583](https://doi.org/10.7169/facm/1583).
   [arXiv:1510.01610](https://arxiv.org/abs/1510.01610).
   Source for the Lower Bound Hypothesis, for the unconditional entropy
   bound at ones-ratio `≤ 1/log₂3` under orbit distinctness, and for the
   product identity (Lemma 2.5) whose logarithm is this repository's drift
   identity. **Added September 2026**; previously referred to only
   second-hand through Curry's identification of `γ*` with `r_H`.

10. Shalom Eliahou, "The 3x+1 problem: new lower bounds on nontrivial cycle
    lengths," *Discrete Mathematics* **118** (1993), 45–56.
    DOI: [10.1016/0012-365X(93)90052-U](https://doi.org/10.1016/0012-365X(93)90052-U).
    Origin of the product identity generalized by Rozier's Lemma 2.5.

11. Daniel J. Bernstein, "A noniterative 2-adic statement of the 3N+1
    conjecture," *Proceedings of the American Mathematical Society* **121**
    (1994), 405–408.
    DOI: [10.1090/S0002-9939-1994-1186982-9](https://doi.org/10.1090/S0002-9939-1994-1186982-9).
    Closed-form 2-adic reconstruction from an exponent (valuation) sequence.

12. Daniel J. Bernstein and Jeffrey C. Lagarias, "The 3x+1 conjugacy map,"
    *Canadian Journal of Mathematics* **48** (1996), 1154–1169.
    DOI: [10.4153/CJM-1996-060-x](https://doi.org/10.4153/CJM-1996-060-x).
    The 2-adic conjugacy behind the valuation-word/residue-class
    correspondence.

13. Josefina López and Peter Stoll, "The 3x+1 conjugacy map over a Sturmian
    word," *Integers* **9** (2009), A13.
    DOI: [10.1515/integ.2009.014](https://doi.org/10.1515/integ.2009.014).
    Adjacent prior art for the Sturmian material; flagged for close reading.

14. Edward Y. Chang, "A Structural Reduction of the Collatz Conjecture to
    One-Bit Orbit Mixing," [arXiv:2603.25753](https://arxiv.org/abs/2603.25753)
    (2026). DOI: [10.48550/arXiv.2603.25753](https://doi.org/10.48550/arXiv.2603.25753).
    Source of the one-bit mixing observable behind `ChangHistory.lean`. The
    finite realizability theorem there is this repository's, not Chang's.

## License, citing, acknowledgments

- The **paper** (linked above) is CC BY 4.0, per its Zenodo record. The
  manuscript text is governed by its own publication / Zenodo terms and is
  not distributed in this repository.
- The **Lean source in this repository** is released under
  [Apache License 2.0](LICENSE), matching Mathlib's own license. The same
  license covers the other files in this repository (scripts, reports and
  documentation) unless a file states otherwise. Third-party papers and
  lecture notes are not redistributed here; see the literature files for
  links.
- Citation metadata for the repository is in [`CITATION.cff`](CITATION.cff).

If you use this formalization, please cite the paper (DOI above). If you
want to cite the formalization itself, cite this repository together with
the specific release tag/commit you built against, given the pinned-Mathlib
nature of the build.

Portions of this formalization — proof strategy drafting, Mathlib API
verification, iterative debugging against compiler output, and the recent
audit-only research phase — were produced with AI assistance (Anthropic's
Claude). All mathematical judgment, the decision of what to formalize and
what to explicitly leave out of scope, and responsibility for the
correctness of what is claimed here rest with the repository author.
