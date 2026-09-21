# The Curry foundation

*Companion to `EOC/CurryFoundation.lean`. Records what the audited external theorem of
Michael John Curry gives the Effective Occupation Conjecture (EOC) program, and — just as
importantly — what it does not give it.*

---

## 8.1 Status

Curry's paper, *"An Explicit Windowed Sparsity Bound for Divergent 3x + 1 Orbits, with
Logarithmic-Floor Exclusion beyond the Harmonic Barrier"* (24 Aug 2026), was **independently
audited** by this project: its two lemmas and its central theorem (Theorem 2.3) were
reconstructed line by line from the classical parity-prefix facts it cites (Terras 1976,
Everett 1977) and elementary pigeonhole, cross-checked against 20,000 randomized and several
exhaustive computational tests of both lemmas, and re-derived independently without following
the published proof's structure, recovering an identical bound with an identical constant.
The numerical exponent `β* ≈ 0.9653844…` and its identification with Rozier's critical
ones-ratio `r_H` were recomputed at 50-digit precision and checked algebraically (both solve
the same entropy-crossing equation `H(γ) = γ log₂3`), not merely matched to a decimal.

**What "audited" means here, precisely:** a from-scratch mathematical verification and
independent reconstruction of the proof, plus computational stress-testing of its two lemmas
and its main counting bound, carried out by this project's maintainer using this project's own
tooling. **It is not peer review** — Curry's paper has not been through a journal refereeing
process as far as this project is aware — and this project's audit is not a substitute for
that. Nor is the result **community-accepted**: it is accepted by this project, on the basis of
the audit above, as an external theorem strong enough to build on, in exactly the sense that
`LogFloorExclusion` already entered `EOC/LogCorridor.lean` as an explicit, never-formalized
hypothesis. Curry's Theorem 2.3 is **not formalized in this repository** and is not planned to
be in the near term (see §W below).

## 8.2 Curry's theorem

For the raw map `T₀(n) = n/2` (n even), `(3n+1)/2` (n odd), a set `A ⊂ ℕ` is *collision-free* if
no two distinct `u₁, u₂ ∈ A` ever satisfy `T₀^j(u₁) = T₀^j(u₂)` for any `j ≥ 0`. The value set
of an infinite aperiodic (equivalently: divergent, equivalently: injective-in-time) orbit is
collision-free.

> **Theorem 2.3 (Curry).** Let `A` be collision-free and `γ ∈ (1/2, 1/λ)`, `λ = log₂3`. Then
> for all integers `a ≥ 1`, `X ≥ 2`:
>
> `#(A ∩ [a, a+X)) ≤ 6(⌊log₂X⌋+1) · (X^H(γ) + X^(γλ))`.
>
> At `γ* = 0.6090897…` (the unique root of `H(γ) = γλ` on `(1/2, 1/λ)`),
> `β* = H(γ*) = γ*λ = 0.9653844…`: for every `β > β*` there is a constant `C_β` with
>
> `#(A ∩ [a, a+X)) ≤ C_β · X^β log(2X)`, **uniformly in `a`**.

The constant `C_β` depends **only on `β`** — not on `A`, the orbit, the seed, or `a`. This is
verified from the proof, not inferred from the statement: the entire argument (a dyadic
window shift, a pigeonhole on the number of odd steps in a length-`N` parity prefix, an
entropy-tail bound in the "heavy" case, and a Lemma-2.2 contraction argument forcing a
collision in the "light" case) never references any quantitative feature of `A`, only the
qualitative collision-free hypothesis.

## 8.3 Reciprocal summability

> **Proposition 3.1 (Curry).** For the value set `O` of a divergent orbit, `Σ_{x∈O} 1/x < ∞`.
> Equivalently, for the accelerated odd iterates `m_n`, `Σ_n 1/m_n < ∞`.

Proved by summing Theorem 2.3 over dyadic blocks `[2^i, 2^{i+1})`, using `β < 1` (available
since `β* ≈ 0.965 < 1`). Tracing the proof further than Curry's own statement shows the bound
obtained is in fact **orbit-independent**: `Σ 1/m_n ≤ K(β)` for a single constant `K(β)`
depending only on `β`, valid for every divergent orbit of every seed simultaneously — stronger
than "finite, but possibly growing without bound across different seeds." This does not change
any conclusion below, but it is worth recording, since it settles (more than requested) the
"graded harmonic-thinness" input the occupation program's Open Problem 12.8 asked for.

## 8.4 EOC consequences: `E_∞`, `Q_∞`, `R_n → -∞`, `Σ 2^{R_n} < ∞`

Reusing the repository's own carry-budget notation (`EOC.HarmonicPacking.carryE`,
`carryU`, `EOC.Confinement.R`, `EOC.ValuationWord.orbit`/`s`) rather than introducing parallel
definitions:

| Statement | Level | Lean |
|---|---|---|
| `E_n → E_∞ < ∞` | B | `CurryFoundation.carryE_tendsto` |
| `Q_n → Q_∞ < ∞` | B | `CurryFoundation.carryU_tendsto` |
| `m_n → ∞` (injective orbit) | elementary | `CurryFoundation.orbit_tendsto_atTop` |
| `R_n → -∞` | B | `CurryFoundation.R_tendsto_atBot` |
| `Σ 2^{R_n} < ∞` | B | `CurryFoundation.summable_two_rpow_R` |

`m_n → ∞` needs **no external input**: any injective sequence of positive integers tends to
infinity, because only finitely many positive integers lie below any fixed bound. `E_∞`,
`Q_∞ < ∞` are direct consequences of reciprocal summability via the comparison
`log₂(1+x) ≤ x/ln2` (Curry states `Q_n ↑ Q_∞ < ∞` himself, in the course of proving his own
Theorem 4.1). `R_n → -∞` combines the two: `R_n = log₂(m₀/m_n) + E_n`, with `E_n` bounded and
`log₂(m_n) → ∞`. `Σ 2^{R_n} < ∞` follows from the exact identity `m_n·2^{R_n} = m₀·Q_n`
(Curry's Lemma 2.2 exponentiated / the repository's `orbit_mul_two_rpow_R`), giving
`2^{R_n} ≤ m₀Q_∞/m_n` and hence `Σ 2^{R_n} ≤ m₀Q_∞ Σ 1/m_n < ∞`.

None of these four are stated by Curry in this form. `R_n → -∞` is presupposed as background
in the surrounding literature (Curry's own introduction: "a divergent orbit must have
`g_n → +∞`"), but not proved within his note; the derivation above is this audit's own, and is
short enough to be fully checked (and is formalized: see §8.9).

## 8.5 Zero-corridor tail

`R_n → -∞` forces `R_n` to attain a global maximum, and — because only finitely many indices
can exceed any fixed threshold once the sequence is heading to `-∞` — there is a **last** index
`n₀` attaining it. Restarting there, `R'_k := R_{n₀+k} - R_{n₀}` satisfies `R'_0 = 0` and
`R'_k < 0` strictly for every `k ≥ 1` (by *last*-maximality: a later tie would contradict
`n₀` being the last maximizer).

Writing `R'_k = S'_k - kα` (`S'_k := s_{n₀+k} - s_{n₀}`, the restarted partial valuation sum;
`α = log₂3`) and using that `S'_k` is an integer:

> **Zero-Corridor Tail Theorem.** `R'_k < 0` for integer `S'_k` gives, by the plain definition
> of the floor, `S'_k ≤ ⌊kα⌋` for every `k ≥ 1`.

**A correction to an earlier framing.** This step does *not* need irrationality of `α`: for
integer `S'_k`, `S'_k < kα` implies `S'_k ≤ ⌊kα⌋` regardless of whether `kα` happens to be an
integer, by maximality of the floor (`Int.le_floor`). Formalizing the step is what surfaced
this — an instance of exactly the kind of over-attribution the governing audit asked to be
caught. Irrationality of `α` (`α = log₂3`, proved directly here rather than assumed: `3^k = 2^j`
is impossible for `k ≥ 1` by a parity/size argument, since `3^k` is always odd and `2^j` is
even for `j ≥ 1`) is genuinely load-bearing elsewhere — for the Beatty-gap fact `b_k ∈ {1,2}`
used in the deficit recurrence below.

## 8.6 Deficit formulation

`Δ_k := ⌊kα⌋ - S'_k ≥ 0` follows immediately from §8.5. Writing `R'_k = -Δ_k + θ_k` with
`θ_k = ⌊kα⌋ - kα ∈ (-1, 0)`, the bounded correction `θ_k` does not affect divergence:

> `R'_k → -∞ ⟺ Δ_k → ∞.`

With `b_k := ⌊kα⌋ - ⌊(k-1)α⌋ ∈ {1,2}` (the Beatty gap for `1 < α < 2`) and `d_k` the `k`-th
valuation digit of the restarted word, the recurrence is pure algebra from the definitions:

> `Δ_{k+1} = Δ_k + b_{k+1} - d_k.`

## 8.7 What this DOES establish

A precise **necessary-condition** theorem: *if* a Type-II (divergent, injective) accelerated
Collatz orbit exists, and *if* Curry's audited Theorem 2.3 is correct, then after its last
global drift maximum its valuation word satisfies, unconditionally:

* `S_k ≤ ⌊αk⌋` for every `k ≥ 1` (zero-confined);
* `Δ_k → ∞` (diverging deficit);
* `Σ 1/m_k < ∞`, `Q_k ↑ Q_∞ < ∞`, `Σ 2^{R_k} < ∞`.

This is a genuine narrowing of the space of possible Type-II counterexamples: the surviving
class must satisfy a permanent, unbounded-margin arithmetic-density condition, not merely an
asymptotic average bound.

## 8.8 What this DOES NOT establish

Explicitly, none of the following follow from the chain above, and none are claimed by it:

* **Not EOC.** The Global Occupation Conjecture is a statement about convergent-orbit
  occupation counts; this chain is entirely about the *divergent*-orbit branch and is silent on
  it (Curry's own scope note: "Nothing here bears on the sub-critical occupation of convergent
  orbits").
* **Not the Collatz conjecture.**
* **Not exclusion of divergent orbits.** The chain describes what a divergent orbit's tail
  *must* look like; it does not show no orbit can look that way.
* **Not exclusion of nontrivial cycles (Type I).** A periodic orbit is not aperiodic and lies
  outside every hypothesis used here (§U in the audit; Curry's own scope note).
* **Not an arbitrary-word realizer floor.** Nothing here bounds the least positive integer
  realizing an arbitrary (non-zero-corridor) confined word.
* **Not a positive-integer realizability obstruction.** The zero-corridor condition is purely
  symbolic/combinatorial; whether a symbolic word satisfying it is realized by an actual
  positive integer is untouched.
* **Not a solution of the moving-anchor problem** (manuscript §5.3, Remark 5.12, Open
  Problem D) — the pre-existing, independently-flagged open core of the residue/arithmetic-
  placement axis, which this chain does not narrow at all.

## 8.9 Remaining frontier

> Determine whether an infinite zero-confined, diverging-deficit valuation word can be
> realized by a positive ordinary integer under the accelerated Collatz map.

See `docs/ZERO_CORRIDOR_REALIZABILITY_FRONTIER.md` for the research specification.

---

## Level labels used throughout this document and `EOC/CurryFoundation.lean`

* **Level A — Curry.** What Curry's paper proves, as stated (§8.2, §8.3).
* **Level B — Curry + elementary Collatz identities.** `E_∞`, `Q_∞`, `m_n → ∞`, `R_n → -∞`,
  `Σ 2^{R_n} < ∞` (§8.4). Short, checked derivations; not asserted by Curry.
* **Level C — Curry + tail normalization.** The zero-corridor and deficit theorems (§8.5,
  §8.6). Built on Level B via the generic last-global-maximum fact.

Nothing in Level B or C is attributed to Curry directly; each carries its own derivation and is
formalized independently in `EOC/CurryFoundation.lean`.

---

## Appendix: "CH" cleanup

A full-text search of every `.md` and `.lean` file in this repository (`grep -rniE
"\bCH\b|curry.?hypothesis|conditional curry"`) found **no artifact literally named "CH"** or any
variant of "Curry Hypothesis" / "Conditional Curry." The handful of raw `CH` matches are all
false positives — citation strings of the form "Ch. 8" (a chapter reference in the Schlickewei/
Evertse Diophantine-approximation citations in `docs/RESEARCH_STATUS.md`, `EOC/MaxTriangle.lean`,
and `scratch/ridout_2026-09-15/REPORT.md`).

| Occurrence | Classification |
|---|---|
| `docs/RESEARCH_STATUS.md:274`, `EOC/MaxTriangle.lean:11,100`, `scratch/ridout_2026-09-15/REPORT.md` | (5) unrelated use of "Ch" — chapter citation, not a hypothesis name |

No genuine occurrence exists to reclassify, so there is nothing to update or retract: any prior
working assumption referred to elsewhere (outside this repository's tracked sources) as "CH"
was never checked into this codebase in that name. §Q of the governing audit compares Curry's
proved content against the *candidate* strengthenings such a hypothesis could plausibly have
needed, in the absence of its literal text.
