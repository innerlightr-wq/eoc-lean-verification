# Research checkpoint — September 2026

This document expands on the README's ["Proved mathematically, not yet
Lean-packaged"](../README.md#proved-mathematically-not-yet-lean-packaged) and
["Where the proof currently stops"](../README.md#where-the-proof-currently-stops)
sections with the reasoning behind them. It records a recent audit-only
research phase (no permanent Lean files were changed in producing it) that
investigated whether the repository's existing formal machinery — the
confinement/realizer apparatus and the Tao-like almost-all pipeline — could
be pushed toward a genuine **pointwise** statement about individual Collatz
orbits, as opposed to the "almost all" statements the formal Tao-like chain
already supports.

Nothing in this document is a Lean theorem. Every claim below is either
**PROVED MATHEMATICALLY** (a hand derivation, cross-checked against the
repository's exact compiled definitions and, where noted, against exact or
numerical computation) or explicitly labeled **COMPUTATION**. None of it
should be cited as a formal result of this repository; it is a research log
explaining the current frontier and why it is currently stuck.

## 1. The target: `CriticalCrossing`

The cleanest pointwise target identified is:

```
CriticalCrossing := ∀ odd seed M, ∃ N > 0, R_M(N) > 0
```

i.e. no natural seed realizes an infinite `0`-confined valuation word. Three
equivalent formulations were established (by hand, from `Confinement.lean`'s
existing `rmin`, `record_chronology`, `leastRealizer` machinery — no new
Lean code):

- `CriticalCrossing`
- `rmin(0, N) → ∞` as `N → ∞`
- no odd `M` has an infinite `0`-confined actual orbit

The hard direction of this equivalence (bounded `rmin` ⇒ an actual infinite
confined seed) uses a pigeonhole argument over the finitely many odd seeds
below the bound, combined with `leastRealizer_lt`/`leastRealizer_odd`/
`realizerCongruence` to show the pigeonholed witness's abstract word
representative is *automatically* that seed's own true prefix — so no
separate compactness/König's-lemma step is needed; nesting is automatic.

Splitting on whether the witness seed's orbit is eventually injective:

- **Non-injective case: fully resolved.** `Periodic.lean`'s
  `not_confined_forever_of_evPeriodic_orbit` (an eventually-periodic
  confined word forces `R_N → +∞` along period boundaries) settles this case
  unconditionally, using only the *upper* confinement bound.
- **Injective case: the entire remaining open content.** The existing
  `BoundedDriftCore.no_injective_orbit_of_lower_drift` pigeonhole mechanism
  needs a genuinely `N`-independent lower drift bound `G` — reverse-
  engineering its proof shows it can tolerate at best `G = O(log log N)`
  if only guaranteed up to a finite prefix length `N`. This is far
  stricter than even the empirically observed depth of long-confined
  record seeds (`Θ(log N)`-ish, see §4) — one exponential level too weak.
  **No rescue of this mechanism was found.**

## 2. First-passage arithmetic

Writing `beta := alpha − 1`, `K_n := S_n − n`, so `R_n = K_n − beta·n`, the
*first crossing* of a confined prefix (the step where `R` first becomes
positive) obeys an exact terminal law:

```
d_{N-1} ≥ b_{N-1} + 2 + Delta_{N-1}
```

where `Delta_{N-1} := floor(beta(N-1)) − K_{N-1} ≥ 0` (the deficit below the
"mechanical ceiling") and `b_{N-1} := floor(beta·N) − floor(beta(N-1)) ∈
{0,1}` (the Sturmian phase bit). This was derived by pure algebra from the
unconditional fact "for integer `n`, real `x`: `n ≤ x ⟺ n ≤ ⌊x⌋`" plus the
irrationality of `alpha` (needed for the ceiling-side translation;
`alpha·N ∈ ℤ` for `N ≥ 1` would require `3^N = 2^k`, impossible — not
currently a named Lean lemma, but elementary). It was checked numerically
against every tested long-confined record seed (27, 703, 10087, 35655,
381727): the law holds exactly at every step, non-crossing and crossing
alike.

## 3. The exact `Geom(2)` next-digit law

The repository's `cylinder_restart` (`TaoLike/Cylinder.lean`) already gives,
for a seed `m` realizing a length-`t` prefix, the exact affine transport
`orbit(m + 2^{S_t+1}k, t) = orbit(m,t) + 2·3^t·k` for every lift parameter
`k`. Appending one more digit is a valuation condition `ν₂(3z+1) = q` on
`z := orbit(m,t) + 2·3^t·k`. Because `2·3^t` has 2-adic valuation exactly 1
(as `3^t` is odd), multiplication by its odd cofactor is a bijection modulo
any `2^K`, which reduces the question to the classical fact about the
2-adic valuation of a uniform arithmetic progression with step-valuation 1.
Working this out exactly gives:

```
P(next valuation digit = q | prefix) = 2^{-q},    q ≥ 1
```

*exactly*, for every prefix — independent of the prefix's own data (in
particular, independent of the "default" digit the seed itself would
produce at lift parameter `k = 0`). This was verified both algebraically
and by exact brute-force enumeration (`k` up to `2^20`) against a concrete
prefix taken from seed 27's own orbit; the observed frequencies match
`2^{-q}` to the resolution tested.

This is a genuinely new (to this project) internal-arithmetic explanation
of the `Geom(2)` law used as the iid reference distribution throughout the
Tao-like pipeline (`geom2` in `TaoInterface.lean`) — it shows the law is a
consequence of the *cylinder lift structure itself*, not merely an external
modeling choice. It is **not** a statement about one deterministic orbit's
successive digits, which are not free/random — they are whatever that
seed's fixed dynamics produce.

Combining this with the first-passage law (§2) gives an exact one-step
crossing hazard `h(Delta, b) = 2^{-(b+1+Delta)}` under uniform cylinder
refinement — checked against all five record seeds at every step (hazard
formula's inputs self-consistent throughout).

## 4. Why this doesn't (yet) close the gap

Several routes toward turning the above into a pointwise obstruction were
tried and explicitly ruled out:

- **Realizer jump from crossing.** The least-realizer "jump" from appending
  the minimal crossing digit is bounded by the same trivial ceiling
  `leastRealizer d N < 2^{S_N+1}` already known — no extra, prefix-
  independent growth is forced by crossing itself.
- **Fresh-bit / natural-tail argument.** Non-crossing at step `n` excludes
  specific residue classes of the lift parameter (hence specific bits of
  the seed above position `S_n`). But this is fully compatible with a seed
  whose bits above its own bit-length are all zero — no forced infinite
  1-bit pattern was found. Asking "can an eventually-zero seed tail stay
  confined forever" turns out to be logically identical to asking whether
  `CriticalCrossing` fails for that seed — a reformulation, not new
  leverage.
- **Finite-state / Sturmian-transducer route.** The natural driving state
  for a hypothetical automaton would need `Delta_n`, which depends on
  `floor(beta·n)` — and `beta = alpha − 1` is irrational, so this driving
  signal is provably not eventually periodic / finite-state. This blocks
  any finite-automaton argument outright.
- **Canonical mechanical word.** The obvious "always confined" abstract
  word `d*_j = floor(alpha(j+1)) − floor(alpha·j)` is confined forever
  abstractly (elementary, exact), but its finite-prefix least realizers
  computed exactly to `N = 1000` grow without bound rather than
  stabilizing — **COMPUTATION**, evidence (not proof) that this specific
  canonical word is not realized by any natural seed.
- **Companion-seed amplification gap.** A single length-`N` cylinder has
  mass `≈ 2^{-alpha·N}`, while the aggregate persistence event the Tao-like
  summability theorem controls has mass `≈ 2^{-I₀·N}`, with
  `alpha − I₀ ≈ 1.506` bits/step. No mechanism was found by which the
  cylinder-lift arithmetic (§3) amplifies one bad seed into enough
  companions to close this gap — the local hazard law is a genuinely local,
  one-step fact and says nothing about how many seeds share a cylinder.

**Net conclusion**: the ensemble-vs-pointwise gap identified across this
entire audit trail persists. The almost-all machinery (Tao-like pipeline)
and the pointwise realizer/confinement machinery are now connected by a
clean, exact arithmetic bridge (§3), but that bridge has not (yet) produced
new leverage on the one remaining open sub-case — an injective, permanently
confined orbit with unboundedly deep (not just unboundedly long) negative
excursions below the mechanical ceiling.

## 5. Computational data referenced above

All computations were run in scratch Python scripts (exact big-integer
arithmetic where noted; no floating point in any decisive count), never
committed to the repository. They are reproducible from the definitions in
`Confinement.lean`, `Realizer.lean`, and `Carry.lean`.

- **Long-confined record seeds** (direct orbit simulation, all odd seeds up
  to `2^20`): confined-length records at seeds 3 (1 step), 7 (3), 27 (36),
  703 (50), 10087 (65), 35655 (84), 381727 (108).
- **Canonical mechanical word realizer growth**: computed exactly (modular
  inverse, not brute force) for `N` up to 1000; bit-length grows at slope
  `≈ alpha ≈ 1.585`, consistent with no stabilization.
- **Record-seed deficit (`Delta_n`) shadowing**: stays in the range
  `0`–`8` across the tested record seeds, with the maximum growing slowly
  (roughly `Θ(log(confined length))`) across successive, longer records —
  "shallow" in a qualitative sense, but still far too deep for the
  `O(log log N)` requirement identified in §1.

## 6. Natural next questions (not promises)

- Conditioned deficit moments `E[Delta_N | confinement]`,
  `Var(Delta_N | confinement)`.
- Pair correlations between overlapping persistence windows.
- Second moments of the number of "bad" shifts in the all-shifts theorem.
- Whether rare survivors cluster in special arithmetic cylinders, and
  whether such clustering could produce an amplification mechanism.

None of these, even if carried out, would by themselves yield pointwise
control — they would remain ensemble/statistical statements. They are
recorded here as plausible next experiments, not as a roadmap with a
promised endpoint.
