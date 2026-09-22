# Divergence-exclusion survey

> **Consolidated ledger:** `docs/DIVERGENCE_REDUCTION_LEDGER.md` holds the theorem statements, the
> dependency ledger and the corrected scope in one place, and is the right entry point. The
> programme is paused there.

*Can the repository support a real step toward excluding divergent positive Collatz orbits?
Branch `divergence-exclusion-survey`, base `f5ef74e` (verified against `origin`). 36 remote branches
fetched and inspected. Revision 6 frozen, `main` and the dirty ordinary checkout untouched.*

> **SCOPE CORRECTED.** Four logical distinctions in this report were wrong and are corrected in
> `docs/DIVERGENCE_SURVEY_SCOPE_NOTE.md`, which supersedes this file wherever they conflict:
> divergence does **not** imply linear negative drift (only `R_n → −∞`, plus a *limsup* log bound);
> summability is not eventual superlinear growth; improving floor constants **does** remove more
> behaviours; the "must not use value-counting" conclusion was an unsupported universal; and the
> restricted target is **equivalent**, not strictly weaker. The verdict — no new mechanism — stands.

**Objective:** qualitative exclusion of divergence only. Hypothetical nontrivial cycles remain a
separate problem throughout, and nothing here assumes them away.

**Verdict in one line:** *no new exclusion mechanism was found*; one existing theorem closed a
connection left open last round, one genuine infrastructure gap was closed, two inherited results
were found to be superseded for this purpose, and the obstruction to every escape route in the
repository was localised to a single structural cap that is derived exactly in §5.

---

## 1. The exact chain and its proof-status ledger

```
divergent positive orbit
  (1)→  Σ_j 1/m_j < ∞                        [Curry]
  (2)→  E_n = log₂ Π(1+1/(3m_j)) ↑ E_∞ < ∞
  (3)→  R_n = log₂(m₀/m_n) + E_n → −∞
  (4)→  R has a LAST global maximum at n₀
  (5)→  m* = m_{n₀} is an actual positive odd seed, zero-confined forever
  (6)→  so: no positive realizer of an infinite zero-confined word ⟹ no divergence
```

| # | Statement | Where | Status |
|---|---|---|---|
| 1 | `Σ1/m_j < ∞` on a divergent orbit | `CurryFoundation.ReciprocalSummable` (a `def`, threaded as a hypothesis); Curry 2026 | **External, cited, never formalized.** The repo's own note says it "is not peer review… nor community-accepted". **There is no Lean statement of "divergent ⟹ ReciprocalSummable" at all** — the implication is assumed by using it as the hypothesis. |
| 2 | `E_n ↑ E_∞ < ∞` | `CurryFoundation.carryE_monotone/_bddAbove/_tendsto`, `carryU_tendsto` | **Lean.** Hypotheses exactly `Odd M`, `ReciprocalSummable M`. |
| 3 | `R_n → −∞` | `CurryFoundation.two_rpow_R_eq`, `R_tendsto_atBot`, `orbit_tendsto_atTop` | **Lean.** |
| 4 | last global maximum | `CurryFoundation.exists_last_atBot_max` | **Lean**, Collatz-independent; only input is `Tendsto f atTop atBot`. |
| 5 | restart is zero-confined | `CurryFoundation.zero_corridor_tail` (shifted-index form only) | **WAS A GAP — closed here.** See §6. |
| 6 | reduction to realizability | `paper/eoc_rev6.tex` Thm `thm:DEequiv` | **Paper-level only.** No Lean theorem, in either direction. Ingredients exist but the Curry interface and the realizer/ZCRE side never meet in Lean. |

**Cycles are handled explicitly, not silently.** Links (1)–(5) need no cycle exclusion
(`TIME_AXIS…AUDIT.md` §L: "No cycle assumption is used"); a periodic orbit simply fails
`ReciprocalSummable` (its reciprocals do not tend to `0`) — though that implication is an informal
remark in `CurryFoundation.lean`, **not a Lean lemma**. Cycles are needed only for the *converse* of
(6), where `lem:cycledrift` / `DriftExit.cycle_driftExit` /
`Periodic.not_confined_forever_of_evPeriodic_orbit` handle them. `cor:cycles` records that (DE) is
compatible with nontrivial cycles and is therefore strictly weaker than Collatz.

### The weakest sufficient target, and three restatements of it

| | Target | Relation |
|---|---|---|
| 1 | **Universal drift exit (DE):** `∀` odd `m`, `∃ n ≥ 1` with `3^n < 2^{S_n(m)}` | — |
| 2 | No infinite zero-confined positive orbit | **Equivalent to 1** (¬DE at `m` *is* zero confinement of `m`) |
| 3 | Unbounded least realizers for every infinite zero-confined word | **Equivalent to 2**, by `ZCRERealizerGrowth.boundedPrefixRealizers_iff_positiveRealizer` |
| 4 | Same, restricted to words also satisfying the *necessary* divergent-orbit conditions | **Equivalent**, not weaker — a zero-confined seed is automatically injective, hence divergent, hence already in the restricted class (scope note §D). It supplies more usable *hypotheses*, not a weaker *theorem*. |

1 ≡ 2 ≡ 3 are the same statement in three vocabularies. **A result phrased in vocabulary 3 is not
an advance over vocabulary 1**, and the repository's own closed-route audit already records this
(ZCRE "is a restatement of realization, not an independent handle"). **Target 4 is equivalent to
them as well** — see scope note §D; what it offers is extra hypotheses inside a proof, not a weaker
goal.

---

## 2. Repository inventory relevant to the chain

Every escape / non-realizability / unbounded-realizer theorem, with what it controls.

| Result | Hypotheses (exact) | Status | Class controlled | Missing ingredient for divergence | Strength vs target |
|---|---|---|---|---|---|
| `Periodic.leastRealizer_unbounded_of_confined_evPeriodic` | one-sided `∀N, Confined c d N`; `EvPeriodic d j0 L`, `1 ≤ L` | Lean | eventually periodic words | a coverage theorem placing divergence candidates here | **Zero coverage** — divergence candidates are aperiodic (a periodic word with `R ≤ 0` forces `R → +∞`) |
| `Periodic.not_confined_forever_of_evPeriodic_orbit` | eventually periodic *orbit* word | Lean | non-injective orbits | same | Zero coverage (divergent ⟹ injective) |
| `BoundedDrift.leastRealizer_unbounded_of_two_sided_drift` | `∀N, R d N ≤ c` **and** `∀N, −G ≤ R d N`, both fixed; **no periodicity** | Lean (**see §3**) | words in a fixed two-sided drift window | a lower wall | **Zero coverage** — divergence candidates have `R_n → −∞`, no lower wall |
| `BoundedDriftCore.no_injective_orbit_of_lower_drift` | injective + fixed integer lower wall `G` | Lean | injective orbits with a constant drift floor | a constant floor | Zero coverage (same reason) |
| `UpperEscape.bounded_orbit_not_upper_confined` | `∀n, orbit M n ≤ K` | Lean | orbits with bounded values | — | Zero coverage (divergent ⟹ unbounded) |
| `UpperEscape.exceptional_class` | `UpperConfinedForever U M` | Lean, unconditional | forever-upper-confined seeds | — | **Not an exclusion**: it is a *structure* theorem (drift dips below `−B log₂ n` i.o. for every `B < 8/9`, i.e. `m_n > c·n^B` i.o.). Superseded for this purpose — see §5 |
| `FinitePrefixPacking.finite_prefix_injective_drift_depth_bound` (+ variants) | injectivity on `[0,2^L]`, lower wall on the horizon | Lean | finite prefixes | — | Gives a seed-size bound, not non-realizability |
| `PrefixCollision.exceptional_count_le_of_prefixCollision` | **unproved** `PrefixCollisionBound` | Lean, conditional | density of confined seeds below `2^K` | — | Statistical; cannot exclude one exceptional seed |
| `ZCRERealizerGrowth.boundedPrefixRealizers_iff_positiveRealizer` | digits `≥ 1` | Lean | all words | — | **Equivalence, not a mechanism** (target 3 ≡ 2) |
| `SeparatedReturns.*` (corrected) | — | Lean | corridor episode structure | — | Occupation-level; no divergence content |
| `RealizerLiftDigit` | — | Lean | lift digits | — | Module doc states no theorem forcing infinitely many nonzero lift digits was found, and the obvious candidate "is equivalent to the problem itself" |
| `Realizer.realizerCongruence`, `leastRealizer_*` | digits `≥ 1` | Lean | exact residue class of realizers | — | Infrastructure |

No `sorry` / `admit` / `axiom` / `opaque` anywhere in `EOC/` (grep-verified). The gaps are missing
statements, not unproved ones.

---

## 3. A stale status banner, corrected

`EOC/BoundedDrift.lean` carries, at the top:

> `STATUS: NOT COMPILED IN THE AUDIT ENVIRONMENT (Mathlib cache unreachable there).`

**It compiles.** Built on this branch: `lake build EOC.BoundedDrift` succeeds with no errors, and

```
leastRealizer_unbounded_of_two_sided_drift     [propext, Classical.choice, Quot.sound]
leastRealizer_unbounded_of_int_drift           [propext, Classical.choice, Quot.sound]
BoundedDriftCore.no_injective_orbit_of_lower_drift  [propext, Classical.choice, Quot.sound]
```

Both `-- CHECK` markers (`Odd.pos`, `Real.rpow_logb`) resolve. The banner is stale — it was written
on the Mac-era machine that could not build Mathlib — and is corrected on this branch.

---

## 4. The §4 check, closed: the oscillating word

The closing report of the separated-returns correction left a disjunction: either the least prefix
realizers of the oscillating word `oscD c` are unbounded, or some positive integer realizes the
whole infinite word and hence never reaches `1`.

**The disjunction was unnecessary — an existing theorem settles it.** `oscD c` has a fixed
*two-sided* drift window, which is exactly the hypothesis of
`leastRealizer_unbounded_of_two_sided_drift` (no periodicity needed). The two walls, in exact
integer form (`EOC/OscillatingEscape.lean`):

```
2^{S_n} ≤ 2^{c+1}·3^n      (upper, from osc_invariant)          R_n ≤ c+1
3^n     ≤ 2·2^{S_n}        (lower, by induction)                R_n ≥ −1
```

The repository had the real→integer conversion (`three_pow_le_of_drift`) but not the reverse; that
bridge (`R_le_of_pow_le`) is supplied here. Conclusion:

> `osc_leastRealizer_unbounded`, `osc_no_positive_realizer` — **no positive integer realizes the
> infinite oscillating word**, unconditionally. The first alternative holds; the second is not
> needed and is not asserted.

**This is a restricted observation and is not progress on divergence.** It applies *precisely
because* `oscD c` has a constant lower drift wall. A divergence candidate has `R_n → −∞` and no
lower wall whatever, so this machinery is silent about it. Recorded, closed, and not counted as
progress.

*(Exact-rational check, `n < 200000`, `c = 1`: the drift obeys the rotation
`x_{n+1} = x_n + (2−α) mod 1` on `(−(α−1), 2−α]` with 0 violations; max `R_n − c = 0.415032 ≤ 2−α`;
no exact period `≤ 2000`; factor complexity `L+2`, so the word is aperiodic but of bounded
complexity. None of this is needed for the theorem — the two walls suffice.)*

---

## 5. Why every escape route in the repository stops short — derived, not asserted

All the mechanisms in §2 that actually exclude anything share one engine: **a lower drift wall is
converted into a ceiling on orbit values, and injectivity supplies a floor.** Making that exact is
what localises the obstruction.

From `BoundedDriftCore.state_bound`: a lower wall `R_j ≥ −G` with `N ≤ 2^L` gives

```
m_j · 2^{L+1} ≤ 2^G · m₀ · 3^{L+1}        i.e.   m_j ≤ 2^G · m₀ · (3/2)^{L+1} .
```

Taking `N = 2^L`, so `L = log₂ N`, the ceiling is `m_j ≤ (3/2)·m₀·2^G·N^{log₂(3/2)}` with
`log₂(3/2) = 0.5849625`. Injectivity gives the floor: `m₀,…,m_N` are `N+1` distinct positive
integers, so `max ≥ N+1`. A contradiction therefore needs

```
N^{0.4150375} > (3/2)·m₀·2^G        ⟺        G < 0.4150375·log₂ N − O(1) .
```

> **The packing engine tolerates a drift floor only up to `G(n) = O(log n)`.** With a floor
> `G(n) = δn` the ceiling is `2^{δn}` against a floor of `n`: no contradiction arises at any `n`, for
> any `δ > 0`, with any constants.

This is a cap on **that estimate**, and it explains the inventory: `BoundedDrift` takes `G`
constant; `FinitePrefixPacking` takes `G` constant on a horizon; the `8/9` logarithmic floor sits at
the same `log n` scale.

> **CORRECTION.** The original text continued "**Divergent orbits have `R_n ≍ −δn`** … the gap is
> `log n` vs `n`". That is **unsupported**: all that is established is `R_n → −∞`, plus Curry's
> *limsup* bound `limsup g_n/log₂n ≥ 1/β*`. Divergent orbits may a priori have **logarithmic**
> `g_n` (polynomial `y_n`), sublinear, or linear. The open range and the corrected statement are in
> `docs/DIVERGENCE_SURVEY_SCOPE_NOTE.md` §A.

### The `8/9` logarithmic floor is superseded *for this application*

`exceptional_class` says a forever-upper-confined seed has `R_n < −B log₂ n − K` infinitely often
for every `B < 8/9`, i.e. `m_n > c·n^B` infinitely often. But Curry — already assumed at link (1) —
gives `Σ 1/m_n < ∞`, and if `m_n = O(n^B)` with `B ≤ 1` then `Σ1/m_n ≥ c·Σ n^{−B} = ∞`. So:

> **Curry already forces `m_n` to grow faster than `n¹` on any divergent orbit, which is strictly
> stronger than the `B < 8/9` conclusion.** Conditional on Curry, the logarithmic-floor result
> contributes nothing to divergence exclusion.

Two honest riders. (i) `exceptional_class` is *Curry-independent*, so it remains the live route for
anyone wanting a Curry-free argument — but then one would need every `B`, not `B < 8/9`. (ii) It is
a lower bound on growth, i.e. a **structure** theorem; it contradicts nothing, since the growth
envelope permits `m_n` up to `(3/2)^n`.

> **CORRECTION.** The original text ended "Improving the constant enlarges no exclusion." That is
> **wrong**, and Curry's own note is the counterexample: Thm 4.1 reaches `B ≤ 1` and Cor 4.3 reaches
> `B < 1/β* = 1.0358567…`, each removing a new family of hypothetical polynomial growth rates `y_n ≍
> n^c`. What is true is that no finite `B` touches super-polynomial growth. See scope note §B.

---

## 6. The selected next lemma: link (5) at the seed level — **proved**

§1 shows link (5) was the one gap that was *assemblable* rather than open. What Lean had was the
shifted-index inequality on `M`'s own word. What link (6) consumes is a statement about an **actual
positive odd integer**. The paper states the latter with the status label
`\status{companion work; already formalized in the repository}` — **an over-claim**.

Assembled in `EOC/ZeroConfinedSeed.lean` from ingredients that all existed but were never combined
(`Periodic.orbit_add`, `SeparatedReturns.sum_concat`, `Confinement.odd_orbit`,
`CurryFoundation.exists_last_atBot_max` / `R_tendsto_atBot`):

```lean
s_orbWord_restart :  s (orbWord M) (n₀+k) = s (orbWord M) n₀ + s (orbWord (orbit M n₀)) k
R_restart         :  R (orbWord (orbit M n₀)) k = R (orbWord M) (n₀+k) − R (orbWord M) n₀
exists_neg_drift_seed          : ∃ m₀, Odd m₀ ∧ ∀ k ≥ 1, R (orbWord m₀) k < 0
exists_zero_confined_seed      : ∃ m₀, Odd m₀ ∧ ∀ N, Confined 0 (orbWord m₀) N
exists_zero_corridor_seed      : ∃ m₀, Odd m₀ ∧ ∀ k ≥ 1, s (orbWord m₀) k ≤ ⌊k·α⌋
exists_zero_confined_seed_tendsto :
    ∃ m₀, Odd m₀ ∧ (∀ N, Confined 0 (orbWord m₀) N) ∧ Tendsto (R (orbWord m₀)) atTop atBot
```

**A second defect, fixed by the same bridge.** `CurryDivergenceProfile.deficit_tendsto_atTop` claims
in its docstring to combine `Δ_k ≥ 0` with `Δ_k → ∞` "past the last global drift maximum", but is
proved by `refine ⟨0, ?_⟩` — at `n₀ = 0`. The statement is true (the `∃` is bare) but it is not that
combination, and at `n₀ = 0` the companion `deficit_nonneg` need not hold: **`Δ_k ≥ 0` and
`Δ_k → ∞` were nowhere available at the same `n₀`.** `exists_zero_confined_seed_tendsto` provides
both at the same seed.

**Label: infrastructure, not progress toward exclusion.** It closes a bookkeeping gap between two
halves of the repository. The mathematical content of the chain is unchanged and it remains
conditional on Curry's external, unformalized theorem. What it does buy: link (6) can now be stated
in Lean against a genuine seed, and the paper's status label can be corrected in Revision 7.

---

## 7. Rejected candidates, with narrow reasons

| Candidate | Reason rejected |
|---|---|
| Extend bounded-drift escape to linear floors | §5: the packing engine converts a floor `G(n)` into a ceiling `2^{G(n)}`; injectivity supplies only `n`. Caps at `G(n) = O(log n)`. Structural. |
| Improve the `8/9` logarithmic-floor constant | §5: conditional on Curry it is already subsumed (Curry forces faster-than-`n¹` growth); and it is a structure theorem that contradicts nothing. |
| Periodic / eventually periodic escape | Zero coverage: divergence candidates are aperiodic and injective by construction. Obligation (B) fails outright. |
| Unbounded-least-realizer reformulations | Equivalent to the target by ZCRE (§1). A renamed problem. |
| Prefix-collision density bounds | Statistical, and conditional on the unproved `PrefixCollisionBound`; cannot exclude one exceptional seed. |
| Lift-digit irregularity | `RealizerLiftDigit`'s own module doc records that no theorem forcing infinitely many nonzero lift digits was found and the obvious candidate is equivalent to the problem. |
| Word-level shadow criteria | The cardinality barrier does not forbid them, but the four known divergent-orbit shadows are shared by uncountably many unrealizable words, so sufficiency must be proved, not assumed. No new shadow was found. |
| Bounded two-sided drift applied to divergence | Zero coverage: `R_n → −∞`. (Its one legitimate use is §4.) |

---

## 8. Surviving candidates

Only one survives as a *stated* candidate, and it is labelled honestly as unfinished:

**C1 — the deficit as an added datum.** Beyond zero confinement, a divergence candidate's word
satisfies `Δ_k = ⌊kα⌋ − s_k → ∞` (now available with `Δ_k ≥ 0` at the same seed, §6). This is
strictly more information than zero confinement, and it *is* independently forced. What it does not
yet do is yield a new inequality: `Δ_k → ∞` restates `R_k → −∞`, which restates `m_k → ∞`, which is
divergence. **Obligation (A) is not met, and no candidate mechanism for it was found.** Recorded
rather than pursued, so it is not mistaken for a route.

Two further items are infrastructure, not candidates: a Lean statement of link (6), and a Lean
lemma `ReciprocalSummable M → orbit M injective` (currently an informal remark).

---

## 9. What remains open

The missing arithmetic input, stated precisely:

> The counting mechanisms **audited here** — the repository's packing engine and Curry's windowed
> parity-class pigeonhole — do not close the gap: the first caps at `O(log n)` drift floors, the
> second at `β*`. Both discard the same thing, namely the *specific residue class* the exact
> realizer congruence pins down; the first keeps only distinctness of values, the second only the
> parity-prefix weight. The open problem is to **combine counting with that discarded residue
> information**.

> **CORRECTION.** The original text read "What is needed is a mechanism that does **not** route
> through value-counting." That universal claim is unsupported — a future counting argument with
> added residue restrictions remains possible, and Curry's §5 says so. See scope note §C.

Nothing in the repository currently supplies that, and this survey did not find it. Also open, and
unchanged: Curry's theorem is external and unrefereed; the whole chain is conditional on it; link
(6) has no Lean statement; and cycles remain entirely separate — (DE) is compatible with them.

---

## 10. Verification performed

* Fetched `origin` and verified all 36 remote tips; `separated-returns-correction` confirmed at
  `f5ef74e` (not taken from prose). `main` at `1c4d670`, untouched; ordinary checkout left dirty and
  untouched; Revision 6 frozen.
* Built `EOC.BoundedDrift` (previously never compiled), `EOC.OscillatingEscape`,
  `EOC.ZeroConfinedSeed` — all clean.
* `#print axioms` on every new theorem and on the three `BoundedDrift` theorems relied on:
  standard axioms only (`oscS_upper` needs only `[propext, Quot.sound]`).
* No `sorry` / `admit` / `axiom` / `opaque` / `native_decide` in the new modules.
* Computational evidence kept separate from proofs: `scratch_sturmian.py` (exact-rational drift
  window and complexity of the oscillating word, `n < 200000`), and the §5 derivations checked
  numerically. None of it is used in any proof.

**Verdict: no new exclusion mechanism was found.** One existing result closed a missing connection
(§4); one genuine infrastructure gap was closed and two concrete errors corrected (§3, §6); and the
obstruction was localised to an exactly-derived structural cap (§5). The repository can support
real steps of this kind, but none of them is a step toward excluding divergence.
