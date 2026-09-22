# Divergence reduction: consolidated ledger

**Start here.** This file holds, in one place, the three things a future session needs before
touching the divergence programme: the exact theorem statements, the dependency ledger, and the
corrected scope. The programme is **paused** at this point; nothing below is an open invitation to
start another reformulation round.

Branch history: `separated-returns-correction` → `divergence-exclusion-survey` →
`curry-audit-and-scope-correction` → `power-saving-summable-bridge` → `divergence-reduction-ledger`.

---

## 1. The one distinction that must not be lost

```
windowed sparsity   +   universal drift exit   ⟹   no divergent orbits
   (EXTERNAL theorem:         (OPEN mathematical
    audited on paper,          hypothesis — this IS
    NOT formalized)            the target)
```

`PowerSavingSummable.no_divergent_orbit_of_windowed` takes **two hypotheses, of different kinds.**

| | `hws : WindowedSparsity` | `hDE` (universal drift exit) |
|---|---|---|
| kind | external theorem | open mathematical hypothesis |
| status | Curry Thm 2.3; audited correct in `docs/CURRY_INDEPENDENT_AUDIT.md`; **not formalized** | **unproved, and equivalent to the target** |
| what would discharge it | formalizing Curry's window theorem | *nothing currently in sight* |

> **Formalizing Curry's window theorem would remove the external dependency. It would not discharge
> `hDE`, and would not prove divergence exclusion.**

A previous summary called this "exactly one hypothesis". That was wrong, and the error is recorded
here so it is not repeated.

---

## 2. What is proved, exactly

**Reduction (Lean, modulo the two hypotheses above).**

```lean
PowerSavingSummable.no_divergent_orbit_of_windowed
  (hws : WindowedSparsity)
  (hDE : ∀ m₀, Odd m₀ → ∃ N, ¬ Confined 0 (orbWord m₀) N)
  {M : ℕ} (hM : Odd M) : ¬ DivergentOrbit M
```

**The pieces, all Lean, all standard axioms:**

| Statement | Name |
|---|---|
| injective ⟺ divergent, for the accelerated map | `CurryInterface.injective_iff_divergent` |
| windowed count + injectivity ⟹ reciprocal summability (the dyadic summation) | `PowerSavingSummable.powerSaving_implies_summable` |
| `E_n ↑ E_∞ < ∞`, `y_n → ∞`, `R_n → −∞` | `CurryFoundation.carryE_tendsto`, `orbit_tendsto_atTop`, `R_tendsto_atBot` |
| last global drift maximum | `CurryFoundation.exists_last_atBot_max` |
| restart at `m* = m_{n₀}`: an **actual positive odd seed**, zero-confined at every horizon, drift `→ −∞` | `ZeroConfinedSeed.exists_zero_confined_seed_tendsto` |
| divergence ⟹ such a seed exists | `CurryInterface.zero_confined_seed_of_divergent` |
| a zero-confined seed is automatically injective, hence divergent | `CurryInterface.injective_of_zero_confined`, `divergent_of_zero_confined` |

**The three-line summary of the whole programme:**

1. Windowed sparsity implies reciprocal summability — **in Lean**.
2. The downstream reduction identifies an **actual zero-confined positive seed** from hypothetical
   divergence — **in Lean**.
3. **Excluding that seed is the unresolved task.**

---

## 3. Corrected scope — the errors already made

Do not re-make these. Full derivations in `docs/DIVERGENCE_SURVEY_SCOPE_NOTE.md`.

| Claim once made here | Status | Correct statement |
|---|---|---|
| Divergent orbits have `R_n ≍ −δn` | **false** | Only `R_n → −∞` is known, plus Curry's *limsup* `limsup g_n/log₂n ≥ 1/β*`. Logarithmic, sublinear and linear regimes are all open |
| "the gap is `log n` vs `n`" | **false framing** | The logarithmic regime is itself the live frontier |
| Summability ⟹ `y_n/n → ∞` | **false** | Only: `y_n = O(n)` impossible, and `limsup y_n/n = ∞` |
| "improving the constant enlarges no exclusion" | **false** | Curry's own note refutes it: Thm 4.1 reaches `B ≤ 1`, Cor 4.3 reaches `B < 1/β* = 1.0358567`. No finite `B` reaches super-polynomial growth |
| the mechanism "must not use value-counting" | **unsupported universal** | The *audited* counting estimates do not close the gap. A future counting argument with residue restrictions is not excluded — Curry's §5 says the same |
| the restricted target is "strictly weaker" | **false** | It is **equivalent**: a zero-confined seed is automatically injective, hence divergent, hence already in the restricted class. Restriction gives more *hypotheses*, not a weaker *theorem* |
| bounded episode count (P) | **refuted** | Constructively; see `eoc-episode-count-unbounded` |
| "exactly one hypothesis" for the reduction | **misleading** | Two, of different kinds — §1 |

**Method.** Exact computations **corroborate**; the general proof arguments **establish**. A finite
check is never evidence for a universally quantified theorem. Statistical rarity does not exclude
one exceptional seed. A failed upper-bound method is not an impossibility theorem.

---

## 4. The open question, stated for an independent reviewer

> **Can the exact realizer congruence supply a lower bound unavailable from word counts, drift
> bounds, and injectivity alone?**

Why it is a fair question rather than a leading one: both audited counting arguments demonstrably
discard that information — the repository's packing engine keeps only *distinctness* of orbit
values, and Curry's windowed pigeonhole keeps only the *parity-prefix weight* (its entropy bound
counts residue classes, not which ones) — and Curry's §5 independently states that improving his
exponent needs "an input beyond parity counting". The gap is identified from two directions.

**The caveat belongs with the question.** It is **open**, not **promising**. Nothing in the survey
or the audit indicates the congruence *can* supply such a bound — only that nothing examined so far
rules it out. And any answer must avoid the `ZCRE` trap: by
`boundedPrefixRealizers_iff_positiveRealizer`, "unbounded least realizers" is a *restatement* of
non-realizability, so a reformulation in that vocabulary is not an answer.

One candidate is parked, not dead: the **deficit** `Δ_k = ⌊kα⌋ − S_k` fails *as a standalone
mechanism*, because `leastRealizer(d,N) < 2^{S_N+1}` means a larger deficit only lowers the cap
while unboundedness needs a lower bound. It is **not** ruled out in combination with residue
information — the all-ones word has maximal deficit and yet least realizer `2^{N+1}−1`.

---

## 5. Remaining formalization obligations

1. **Curry's Theorem 2.3** (`CurryInterface.WindowedSparsity`) — the only external input left.
   Substantial. Removing it strengthens verification and nothing else.
2. Link (6) of the chain as a single Lean equivalence (`thm:DEequiv`); the halves exist.
3. `ReciprocalSummable M → orbit M injective` — currently an informal remark in
   `CurryFoundation.lean`. Harmless (omitting a hypothesis only strengthens the theorems) but
   unformalized.

Manuscript consequences are in `docs/REVISION7_DEFERRED_ITEMS.md`. **Revision 6 stays frozen.**
