# Closed-route scope audit

*Every "closed" verdict in the EOC programme, checked against the precise theorem and hypotheses
that support it. Branch `closed-route-scope-audit`, base `5b09be6`.*

---

## A. The finding that prompted this audit

An external source review flagged that the Revision-6 programme-map report asserts

> "no collection of word-level global properties can *characterize* positive realization"

while the manuscript (after the freeze patch) asserts only the narrower statement about properties
shared by the constructed family. The reviewer judged the broad wording to go too far.

**It goes further than "too far": it is false, and refuted by a theorem already in this
repository.**

`EOC/Realizer.lean` defines

```lean
def leastRealizer (d : ℕ → ℕ) (N : ℕ) : ℕ
```

— a function of the valuation word `d` **alone**. Hence

```
P(d)  :≡  ∃ M, ∀ N, leastRealizer d N ≤ M
```

is a global property of the word, and `EOC/ZCRERealizerGrowth.lean` proves

```lean
theorem boundedPrefixRealizers_iff_positiveRealizer (d : ℕ → ℕ) (hd_pos : ∀ i, 1 ≤ d i) :
    (∃ M, ∀ N, leastRealizer d N ≤ M) ↔ (∃ m0, Odd m0 ∧ ∀ i, a (orbit m0 i) = d i)
```

So **a word-level global property that exactly characterizes positive-integer realization already
exists and is formalized.** Any claim that none can exist is wrong.

### Why the cardinality barrier does not contradict this

The barrier (`GlobalSeparation.not_all_realizable_of_injective` applied to `famWord`) shows that
the *four shadows shared by every member of that family* — zero confinement, linear negative drift,
summability of `Σ2^{R_n}`, and the `O(G)` occupation bound — cannot characterize realization,
because all members share them while all but countably many are unrealizable.

`boundedPrefixRealizers` escapes precisely because it is **not** shared by the family: it holds for
the countably many realizable members and fails for the rest. That is not a loophole; it is the
exact content of the theorem. The barrier constrains *criteria that factor through the shared
shadows*, not word-level criteria in general.

### Corrected statement

> **Scope.** The shared shadows of Theorem (cardinality barrier) do not characterize positive
> realization, and neither does any criterion depending only on properties shared by that family.
> Word-level criteria in general are *not* excluded — `boundedPrefixRealizers` is one, and it is
> exact. What the barrier rules out is the hope that the *divergent-orbit shadows* (confinement,
> drift, summability, occupation) could suffice.

---

## B. Classification scheme

| Code | Meaning |
|---|---|
| **PI** | *Proved impossible* — a precisely stated mechanism or argument shape is excluded by a theorem |
| **IA** | *Insufficient alone* — the ingredient is real but needs further information |
| **ER** | *Equivalent reformulation* — correct, but does not reduce the difficulty |
| **TU** | *Tested unsuccessfully* — the investigated version failed; broader possibilities remain open |

---

## C. Verdict-by-verdict audit

| # | Route | Supporting result | Correct class | Was it stated too broadly? |
|---|---|---|---|---|
| 1 | Fixed-modulus drift packing, terminal at 8/9 | Thm (8/9 exclusion) proved; terminality argued from "2, 3 are units mod p>3" plus a finite scan | **PI** for the 8/9 bound's own mechanism; **TU** for the terminality claim | **Yes, mildly.** The paper says the mechanism "supplies no further density reduction at any other fixed modulus"; the supporting scan is explicitly "consistent with, though not proving, this". The claim should read as a structural argument plus computation, not a theorem. |
| 2 | Bulk entropy / `I_Collatz` | none — a scope observation | **IA** | No. Correctly framed as population-vs-pointwise. |
| 3 | Shell injectivity | counting theorems | **IA** | No. |
| 4 | Moving-anchor collision law | none — interpretive | **TU** | No. |
| 5 | Chang finite/local exclusions | finite universality (theorem, formalized) + infinite full shift (machine-checked) | **PI** for finite-forbidden-pattern arguments | No. This is a genuine impossibility result for a precisely delimited class. |
| 6 | Lift digits | `liftDigit_eq_bitBlock` | **ER** | No. |
| 7 | Terminal zero gap | `g = ⌈E⌉` bracket | **ER** | No. |
| 8 | Normalized carry | identity | **ER** | No. |
| 9 | Transport survival budget | `Z = −n₀`; forced/excess split; disjoint-run bound | **ER** for the coordinates; the `O(log n₀)` regeneration bound is a *positive* theorem, not a closure | Minor: the closed-route table lists it as a closure, which understates that a real theorem came out of it. |
| 10 | External `p`-adic arithmetic | applicability audit against primary sources | **TU** | **Yes.** See §D. |
| 11 | Global word shadows | cardinality barrier | **PI** for criteria factoring through the family's shared shadows; **not** for word-level criteria generally | **Yes — the error in §A.** |
| 12 | Corridor-uniform lifetime | automatic-corridor proposition + converse | **ER**, and *harder* than needed | No; the paper already says "noncircular but substantially stronger". |
| 13 | Deep-drift recovery impossibility | self-financing inequality | **PI** for the named argument shape | No, provided the scope ("arguments of the form…") is kept. |

---

## D. External arithmetic (row 10) needs its label corrected

The super-budget audit concluded: *existing external arithmetic does not control cumulative
super-budget cancellation.* The supporting work established, from primary sources, that:

- `p`-adic linear forms in logarithms bound a **product** minus one, not an `N`-term sum, with
  constants at best geometric in the number of logarithms — and at `p = 2` with `2` among the bases
  the hypotheses fail and the quantity is identically zero;
- quantitative `S`-unit results bound the **number** of solutions, not their size, and are
  ineffective beyond two variables;
- the `p`-adic Subspace Theorem applies **formally** and gives a bound of the right shape, but is
  ineffective with dimension-dependent constants, and here the dimension is `N+1`.

That is a well-supported **TU**, not a **PI**. The audit itself recorded that a systematic
2010–2026 literature sweep was not performed. The paper's wording ("does not supply the uniform
cumulative pointwise bound required", "examined so far") is already correct; the *closed-route
table* compresses it to "wrong complexity scale", which reads as stronger than intended.

**Recommended table wording:** "no applicable uniform bound found; dimension grows with `N`".

---

## E. What actually needed changing

| location | old | new |
|---|---|---|
| `paper/eoc_rev6.tex` Remark 9.4 | broad | **already corrected in the freeze patch** — no further change |
| `docs/EOC_REVISION6_PROGRAM_MAP_REPORT.md` §M | "no collection of word-level global properties can characterize" — and attributed to the paper, which no longer says it | narrowed; ZCRE counterpoint added |
| `docs/GLOBAL_SINGLE_ORBIT_NONLOCAL_SEPARATION_AUDIT.md` §Y, verdict | "Word-level global conditions are defeated by cardinality" | narrowed |
| `EOC/GlobalSeparation.lean` module docstring and `not_all_realizable_of_injective` docstring | "every known word-level shadow… insufficient"; "Word-level global conditions are therefore defeated by cardinality" | narrowed; ZCRE counterpoint noted |
| memory `eoc-word-shadow-cardinality-barrier.md` | "judge any proposed global condition by whether it is expressible from `D` alone; if it is, the family already satisfies it" — **actively misleading**, false by ZCRE | corrected |

No Lean **proof** changed; docstrings only. The cardinality theorem itself stands exactly as
proved and formalized.

---

## F. Net effect on the programme map

The corrected barrier is narrower but still load-bearing, and arguably more useful stated
correctly:

> The divergent-orbit shadows — the properties a hypothetical Type-II orbit's word is *known* to
> have — cannot by themselves identify positive realization. Any successful word-level criterion
> must therefore distinguish members of the `famWord` family from one another, which means it must
> see something those shadows do not. `boundedPrefixRealizers` does exactly that, and is exact —
> but it is a restatement of realization, not an independent handle.

That sharpens rather than weakens the programme's conclusion: the gap is not "word-level
information is useless" but "the *known* word-level invariants of divergent orbits are too coarse,
and the one word-level invariant that is sharp enough is a tautology."

---

## G. Status

Corrections applied on branch `closed-route-scope-audit`. The manuscript required no further
change: the freeze patch had already narrowed it correctly, and this audit confirms that wording
against the precise theorem.
