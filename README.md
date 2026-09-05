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

## Contents

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
log₂(m₀ / m_N) = N·alpha + E_N − S_N,      E_N := Σ_{n<N} log₂(1 + 1/(3m_n)) ≥ 0
```

equivalently `R_N = log₂(m₀/m_N) + E_N`. **PROVED MATHEMATICALLY** (derived
by hand from the repository's exact carry/orbit identities across several
audit milestones); it is not currently packaged as a single named Lean
theorem.

## The Global Occupation Conjecture (EOC)

For fixed `c > 0`, define the **occupation count**

```
O_c(m₀) := #{ n ≥ 0 : R_n(m₀) ≤ c }
```

**EOC** conjectures logarithmic pointwise occupation: `O_c(m₀) = O(log m₀)`
for every odd `m₀` (with quantifiers exactly as stated in the manuscript's
Conjectures 3.1–3.4). **This conjecture is OPEN** — nothing in this
repository proves any tier of it.

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

**Garcia–Tal/Curry divergent-orbit sparsity.** The manuscript combines the
collision-free orbit-sparsity mechanism of Garcia and Tal (1999) — see
[Literature](#literature), item 2 — with an explicit quantitative windowed
sparsity refinement attributed in the manuscript to M. J. Curry (2026):

```
#(orbit ∩ [a, a+X)) ≤ C_β · X^β · log(2X),    β > β* ≈ 0.9653844
```

Applied to the accelerated Collatz orbit, the manuscript derives reciprocal
summability along any hypothetical divergent orbit and excludes every
eventual logarithmic drift floor `R_n ≥ −B·log₂n + O(1)` for
`B < 1/β* ≈ 1.0358567` — crossing the harmonic threshold `B = 1`. **This
concerns hypothetical divergent orbits only; it does not prove EOC, exclude
nontrivial cycles, or resolve the arithmetic-placement/moving-anchor
problem below.** *(Curry's refinement is cited here exactly as attributed
in the manuscript; this repository has not independently verified or
formalized it, and no separate bibliographic record for it was located.)*

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
| L. External Tao mixing interface | `TaoLike/TaoInterface.lean` | **CONDITIONAL FORMAL RESULT** | `TaoMixingHypothesis`/`TaoMixingProperty` — see [warning](#the-external-tao-interface) below |
| M. Conditional future valuation mixing | `TaoLike/ConditionalMixing.lean` | CONDITIONAL FORMAL RESULT | conditioned on a realized prefix, the future valuation vector is `TaoMixingHypothesis`-close to iid `Geom(2)^n` |
| N. iid geometric persistence Chernoff bound | `TaoLike/PersistenceModel.lean` | FORMALLY VERIFIED | exponential-rate upper bound on the abstract iid `Geom(2)^n` persistence event (not yet transferred to real orbits at this layer) |
| O. Shifted persistence transfer | `TaoLike/ShiftedPersistence.lean` | CONDITIONAL FORMAL RESULT | one restart + one future block, real-orbit persistence bound |
| P. Early/late decomposition | `TaoLike/EarlyLate.lean` | CONDITIONAL FORMAL RESULT | GOOD/BAD prefix split; iid upper-tail bound |
| Q. Prefix partition / restart-law alignment | `TaoLike/PrefixPartition.lean`, `TaoLike/RestartLawAlignment.lean` | FORMALLY VERIFIED | deterministic finite-probability bookkeeping — no `TaoMixingHypothesis` used |
| R. Fixed late-shift persistence | `TaoLike/LateShiftPersistence.lean` | CONDITIONAL FORMAL RESULT | true harmonic-window persistence bound, one fixed shift |
| S. All-shifts averaged persistence | `TaoLike/AllShiftsAveragedPersistence.lean` | CONDITIONAL FORMAL RESULT | finite-horizon union-over-shifts persistence bound |
| T. Normalized harmonic law | `TaoLike/NormalizedHarmonicLaw.lean` | FORMALLY VERIFIED / CONDITIONAL* | proves the harmonic window's probability mass genuinely normalizes to 1 (unconditional), then transfers R–S to the normalized law (conditional, inherited) |
| U. Harmonic exceptional-set summability | `TaoLike/HarmonicExceptionalSetSummability.lean` | CONDITIONAL FORMAL RESULT | dyadic-window summability of the exceptional (persistent) event; **audited explicitly not to yield a pointwise/soft-EOC conclusion** (ensemble statement only) |

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

**COMPUTATIONAL EVIDENCE only**: finite-prefix least realizers of this
canonical mechanical word were computed exactly (via modular inverse, not
brute-force search) up to `N = 1000`; they did **not** stabilize, with
bit-length growing approximately linearly in `N` at slope `≈ alpha`. This is
evidence against natural-integer realizability of this *specific* canonical
word — it is **not** a theorem that the limiting 2-adic seed is non-natural,
and it says nothing about other confined words.

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

A related, explicitly audited dead end: the existing two-sided bounded-drift
pigeonhole mechanism (row G) requires a depth bound `G` essentially
independent of `N` (rigorously, `O(log log N)`) — far stricter than even the
empirically shallow depth observed on long-confined record seeds
(`Θ(log N)`-ish). It cannot be triggered by first-passage words as they
actually behave.

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

Garcia and Tal (1999) prove Banach-density-zero results for orbit
representative sets in generalized `3n+1` systems, under their stated
hypotheses. **This repository's Lean formalization does not use, extend, or
reprove their result**, and does not attribute any quantitative
power-saving exponent to Garcia and Tal's own paper beyond what it states.
The companion manuscript's Revision 5 *does* use an explicit quantitative
windowed-sparsity refinement of this qualitative result — see
[Manuscript highlights](#manuscript-highlights-revision-5) above — but that
refinement is attributed there to M. J. Curry (2026), not to Garcia and
Tal, and is not (yet) formalized in this repository.

## Current research checkpoint

**FORMALLY VERIFIED** (rows A–K, N, Q of the table above):
exact accelerated-orbit / valuation infrastructure; carry identities;
realizer congruences; confinement/record-chronology; cylinder restart and
additivity; periodic-sector and bounded-two-sided-drift realizer escape;
harmonic AP and residue-TV infrastructure; iid persistence Chernoff
estimate; prefix-partition/restart-law bookkeeping.

**CONDITIONAL FORMAL RESULT, on `TaoMixingHypothesis`** (rows L, M, O, P, R,
S, and the transfer half of T):
the full conditional-mixing → shifted-persistence → all-shifts →
(normalized) exceptional-set-summability pipeline.

**PROVED MATHEMATICALLY, NOT YET FORMALIZED**:
first-crossing terminal-digit threshold; exact `Geom(2)` next-digit law
under cylinder refinement; exact one-step crossing hazard; the exact drift
identity `R_N = log₂(m₀/m_N) + E_N`.

**COMPUTATIONAL**:
long confined record seeds (up to length ~109, seed ~381727); canonical
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
`PeriodicCore.lean` · `Periodic.lean` · `BoundedDriftCore.lean` · `BoundedDrift.lean`

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

**Experimental / historical**
Untracked research scratchpads (`scratch/`, `CHANG_CYLINDER_SCRATCHPAD.md.bak`,
`EOC/PeriodicRealizer.lean`) are deliberately outside the tracked Lean build
and are not part of any claim in this README. A more detailed narrative of
the recent (untracked, audit-only) research phase is in
[`docs/RESEARCH_CHECKPOINT_2026-09.md`](docs/RESEARCH_CHECKPOINT_2026-09.md).

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

## Literature

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

3. Yakov G. Sinai, "Statistical (3x+1)-problem," *Communications on Pure
   and Applied Mathematics* **56**(7) (2003), 1016–1028.
   DOI: [10.1002/cpa.10084](https://doi.org/10.1002/cpa.10084).
   Background on statistical/probabilistic approaches to the 3x+1 dynamics.

4. Alex V. Kontorovich and Jeffrey C. Lagarias, "Stochastic Models for the
   3x+1 and 5x+1 Problems," in *The Ultimate Challenge: The 3x+1 Problem*,
   American Mathematical Society, 2010. Also
   [arXiv:0910.1944](https://arxiv.org/abs/0910.1944).
   Background on stochastic/iid modeling of valuation sequences.

5. Günther J. Wirsching, *The Dynamical System Generated by the 3n+1
   Function*, Lecture Notes in Mathematics 1681, Springer, 1998.
   DOI: [10.1007/BFb0095985](https://doi.org/10.1007/BFb0095985).

6. Jeffrey C. Lagarias, "The 3x+1 Problem: An Overview,"
   [arXiv:2111.02635](https://arxiv.org/abs/2111.02635).

7. Jeffrey C. Lagarias, "The 3x+1 problem and its generalizations,"
   *American Mathematical Monthly* **92** (1985), 3–23.

## License, citing, acknowledgments

- The **paper** (linked above) is CC BY 4.0, per its Zenodo record.
- The **Lean source in this repository** is released under
  [Apache License 2.0](LICENSE), matching Mathlib's own license.

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
