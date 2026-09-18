# Novelty and provenance audit

*Zotero-assisted literature, provenance and novelty audit, September 2026. Carried out
**after** the mathematics, with the explicit purpose of making every important claim
traceable to the correct source and of **reducing** novelty wording wherever prior work is
closer than previously recognized.*

Companion documents: [`LITERATURE_CONTEXT.md`](LITERATURE_CONTEXT.md) (narrative
provenance), [`LITERATURE_SUBSPACE_TRIANGLES.md`](LITERATURE_SUBSPACE_TRIANGLES.md)
(Diophantine round), [`RESEARCH_STATUS.md`](RESEARCH_STATUS.md) (dated status and labels).
Bibliography: [`../references.bib`](../references.bib) — 34 entries, 33 with DOIs, every
record obtained from publisher or registry metadata, none typed from memory.

**Scope.** This document covers literature that is part of the repository's **provenance** —
work that a claim here uses, depends on, formalizes, or must be compared against as closest
prior art. Papers read during exploration that contributed no theorem, proof ingredient,
computational method, conjecture, or interpretation to the repository are deliberately
excluded, because listing them would imply a dependency that does not exist.

**Method and its limits.** Claim-level comparison was done from verified bibliographic
records, published abstracts, and — for the two sources that turned out to matter most —
full text that is openly available (`Rozier2017` via arXiv:1510.01610). This is a targeted
prior-art search, not a systematic review of a literature that runs to two book-length
annotated bibliographies (`LagariasBib1`, `LagariasBib2`). **Absence of a prior result here
means *not found in the sources reviewed*, never *does not exist*.** The preferred wording
throughout is *"no equivalent result was identified in the literature reviewed."*

---

## 1. Headline findings

Five findings change how the repository should describe itself. The first two are the
important ones.

### 1.1 The exact drift identity is a known identity — EQUIVALENT UNDER NOTATION CHANGE

The repository's exact drift identity, labelled **PROVED MATHEMATICALLY** and described as
"derived by hand from the repository's exact carry/orbit identities across several audit
milestones" (README), is

```
log₂(m_N/m₀) = N·α + E_N − S_N ,      E_N := Σ_{n<N} log₂(1 + 1/(3m_n)) ,   α = log₂ 3
```

Rozier's Lemma 2.5 (`Rozier2017`), stated there as a generalization of a formula of
Eliahou (`Eliahou1993`) for cycles, is

```
T^(j)(n)/n = 2^(−j) · Π_{k<q} (3 + 1/m_k)
```

where `m_0, …, m_{q−1}` are the odd terms among `n, T(n), …, T^(j−1)(n)`. Taking `log₂`:

```
log₂(T^(j)(n)/n) = −j + Σ_{k<q} log₂(3 + 1/m_k)
                 = −j + q·log₂ 3 + Σ_{k<q} log₂(1 + 1/(3m_k))
```

With `q ↔ N` (odd steps) and `j ↔ S_N` (total halvings), this is the repository's identity
**term for term**, including the correction `E_N`. This is not an analogy; it is the same
identity in multiplicative rather than logarithmic form.

**Action taken.** The identity is reclassified **CLASSICAL** with `Eliahou1993` and
`Rozier2017` cited. The logarithmic bookkeeping, the `R_N` drift framing and the Lean
packaging remain the repository's own; the identity does not.

### 1.2 Rozier's Lower Bound Hypothesis is prior art of the same type as EOC

`Rozier2017` formulates the **Lower Bound Hypothesis (LBH)**, Hypothesis 2.3: there is a
constant `C ≥ 0` such that for all positive `j, n` (not both 1),

```
n ≥ j^(−C) · 2^((1 − H(q/j))·j)
```

where `q` is the number of odd terms in `n, T(n), …, T^(j−1)(n)` and `H` is the binary
entropy function. This is a conjectural **entropy-governed lower bound on the least integer
realizing a prescribed parity pattern statistic** — the same question as the repository's
residue/arithmetic-placement axis ("how small the exact integer realizing a prescribed
valuation word can be"), at coarser `(j, q)` resolution.

Three further facts matter:

* **Rozier's Theorem 2.6 proves the inequality unconditionally** in the regime
  `r = q/j ≤ 1/log₂ 3 = 0.630…`, provided the orbit terms `n, T(n), …, T^(j)(n)` are all
  **distinct**: `n ≥ j^(−1/6) · 2^((1−ρr)j)` with `ρ = log₂ 3`, and for `r ≤ r_H =
  0.6090897…` also `n ≥ j^(−1/6) · 2^((1−H(r))j)`. The threshold `1/log₂ 3` and the
  distinctness (injectivity) hypothesis are exactly the repository's own `1/α` and
  `injective_orbit` hypotheses.
* **Lemma 3.1: LBH implies every trajectory reaches 1.** So a conjecture of this shape is
  already known to be sufficient for the divergence half of Collatz.
* **Theorem 4.1: LBH implies explicit bounds** on total stopping time and maximum excursion,
  with the same `r_H` that `Curry2026` identifies with his `γ*`.

**Action taken.** `Rozier2017` is recorded as the closest prior art for the placement axis,
for the entropy exponent `H₂(1/α)`, and for the Global Occupation Conjecture itself. The
repository previously cited Rozier **nowhere**, mentioning him only second-hand through
Curry's identification of `γ*` with `r_H`. **The precise logical relation between LBH and
EOC's `O_c(m₀) = O(log m₀)` was not settled by this audit** and is recorded as an open
question, not as a claim of independence.

### 1.3 The 2-adic realizer formula is classical, and two closest sources were uncited

The repository cited `Terras1976`/`Everett1977`/`Lagarias1985` for the parity-vector
correspondence, but not:

* **`Bernstein1994`** — an explicit noniterative 2-adic formula: `Q = 2^{d_0} + 2^{d_1} + ⋯`
  and `N = (−1/3)2^{d_0} + (−1/9)2^{d_1} + (−1/27)2^{d_2} + ⋯` with `0 ≤ d_0 > d_1 > ⋯`.
  The exponent sequence is the repository's valuation word; the series is a closed-form
  realizer reconstruction.
* **`BernsteinLagarias1996`** — the 3x+1 conjugacy map `Φ` on `ℤ₂` with `Φ∘S∘Φ^{-1} = T`,
  and the cycle structure of the induced permutation `Φ_n` of `ℤ/2^nℤ`. This is the
  structural statement behind "a valuation word pins one residue class of its realizers".

**Action taken.** Both are now cited; the reconstruction formula is classified **CLASSICAL**,
with the Lean formalization as the contribution.

### 1.4 The harmonic-packing exclusion sits inside a stronger published result

Row W (`HarmonicPacking.lean`) excludes every eventual logarithmic drift floor
`R_k ≥ −B·log₂ k` for `B < 8/9`, for odd `M` with injective orbit, via the carry budget
`E_N ≤ (1/9)log₂ N + 7/(9 ln 2)`. The mechanism — orbit distinctness ⇒ control of
`Σ 1/m_k` ⇒ a lower bound — is the mechanism of Rozier's Theorem 2.6, and the repository's
own cited `Curry2026` already crosses the same barrier at `B < 1/β* ≈ 1.0359 > 1 > 8/9`.

**Action taken.** Row W keeps its Lean status, but its wording is scoped: it is an
independently formalized *weaker* threshold obtained by an elementary argument of a known
type, not a frontier result. This was already partly acknowledged for Curry; Rozier is now
added.

### 1.5 One citation gap and one unverifiable locator, both resolved

* **Rozier was named twice in the README and cited nowhere.** Fixed.
* **`Chang2026`** — the scratchpad flagged its identifier "SOURCE TO VERIFY". The paper is
  real: *A Structural Reduction of the Collatz Conjecture to One-Bit Orbit Mixing*,
  arXiv:2603.25753, DOI `10.48550/arXiv.2603.25753`, author string per arXiv metadata
  "Chang, Edward Y." (OpenAlex normalizes to "Edward Yi Chang"); a ResearchGate copy carries
  `10.13140/RG.2.2.28140.22403`. arXiv's own API does not return the record, which is why an
  earlier check could not confirm it; DataCite and OpenAlex both do.

---

## 2. Claim-by-claim novelty matrix

Categories: **CLASSICAL** · **KNOWN / REPARAMETERIZED** · **FORMALIZATION OF KNOWN RESULT** ·
**NEW DERIVATION OF KNOWN INGREDIENTS** · **APPARENTLY DISTINCT RESULT** · **NEGATIVE
RESULT** · **CONJECTURAL** · **UNCERTAIN — MORE SEARCH NEEDED**. Formal status uses the
repository's own labels plus **EXTERNAL THEOREM**.

| # | Claim / theorem | Location | Mathematical statement | Closest prior work | Relationship | Formal status | Novelty classification | Recommended wording | Keys |
|---|---|---|---|---|---|---|---|---|---|
| 1 | Accelerated map, valuation words | row A, `Basic.lean`, `ValuationWord.lean` | odd-to-odd map, `a(m)`, prefix sums | the accelerated/Syracuse map | identical | LEAN-PROVED | **CLASSICAL** | "the standard accelerated map" | `Terras1976`, `Everett1977`, `Lagarias1985` |
| 2 | Least-realizer congruence | row C, `Realizer.lean` | realizers of a length-`N` word form one class mod `2^(S_N+1)` | Terras' parity-vector theorem; Bernstein's 2-adic series; the conjugacy `Φ` | identical up to the accelerated encoding and the extra oddness bit | LEAN-PROVED | **FORMALIZATION OF KNOWN RESULT** | "the classical parity-vector congruence, formalized; the extra bit enforces terminal oddness" | `Terras1976`, `Bernstein1994`, `BernsteinLagarias1996` |
| 3 | Carry identities, exact finite-word realization | row B, `Carry.lean` | carry recursion `q`, closed form `C`, `q_eq_C` | Bernstein's closed form; Terras | equivalent under notation change | LEAN-PROVED | **FORMALIZATION OF KNOWN RESULT** | "an exact reconstruction of a known 2-adic formula" | `Bernstein1994`, `Terras1976` |
| 4 | Exact drift identity with `E_N` | README §core map | `log₂(m_N/m₀) = Nα + E_N − S_N` | Rozier Lemma 2.5, generalizing Eliahou's cycle formula | **equivalent under notation change** (log of the product form) | PROVED MATHEMATICALLY | **CLASSICAL** | "the logarithmic form of a known product identity" | `Eliahou1993`, `Rozier2017` |
| 5 | Valuation-shell counting | row Y, `CompositionCounting.lean` | `#{compositions of s into N positive parts} = C(s−1, N−1)` | elementary composition count | identical | LEAN-PROVED | **CLASSICAL** | "textbook stars-and-bars, formalized" | — |
| 6 | Chord rotation | row Z, `ChordRotation.lean` | some cyclic rotation keeps prefix sums under the endpoint chord | the cycle lemma | identical in content | LEAN-PROVED | **CLASSICAL** | "a cycle-lemma argument of Dvoretzky–Motzkin type" (already stated) | `DvoretzkyMotzkin1947` |
| 7 | Baseline exceptional exponent `H₂(1/α) ≈ 0.949956` | `ExceptionalPowerBound.lean` | counting bound on confined-word seeds | Terras–Everett counting; Rozier's entropy exponent at `ρ^{-1}`, `r_H` | same entropy mechanism and the same `1/log₂3` threshold | LEAN-PROVED | **NEW DERIVATION OF KNOWN INGREDIENTS** | "a Terras–Everett-type entropy count; the threshold `1/α` and the entropy exponent both appear in Rozier" | `Terras1976`, `Everett1977`, `Rozier2017` |
| 8 | Periodic-sector realizer escape | row F, `Periodic*.lean` | eventually-periodic confined word ⇒ `leastRealizer → ∞` | fixed rational 2-adic anchors | elementary consequence of the classical correspondence | LEAN-PROVED | **NEW DERIVATION OF KNOWN INGREDIENTS** | "elementary, from the classical 2-adic picture" | `BernsteinLagarias1996`, `Terras1976` |
| 9 | Bounded two-sided drift escape | row G, `BoundedDrift*.lean` | two-sided bounded drift ⇒ `leastRealizer → ∞` | Rozier Thm 2.6 mechanism (distinctness + harmonic control) | analogous; different hypothesis (drift bound vs. ones-ratio) | LEAN-PROVED | **NEW DERIVATION OF KNOWN INGREDIENTS** | "a pigeonhole argument in the same family as known distinctness bounds" | `Rozier2017`, `Eliahou1993` |
| 10 | Finite-prefix injective drift-depth bound | row V, `FinitePrefixPacking.lean` | injectivity through `2^L` + uniform drift floor ⇒ depth bound | Rozier Thm 2.6 | same mechanism, weaker conclusion | LEAN-PROVED | **NEW DERIVATION OF KNOWN INGREDIENTS** | "elementary packing under injectivity; cf. the stronger published bound" | `Rozier2017` |
| 11 | Coprime-six harmonic packing, `B < 8/9` floor exclusion | row W, `HarmonicPacking.lean` | for odd `M` with injective orbit, `R_k ≥ −B log₂ k` fails i.o. for `B < 8/9` | `Curry2026` (`B < 1/β* ≈ 1.0359`); Rozier Thm 2.6 | **weaker** than both, by the same mechanism | LEAN-PROVED | **NEW DERIVATION OF KNOWN INGREDIENTS** | "an elementary, independently formalized threshold, weaker than the published `1/β*`" | `Curry2026`, `Rozier2017` |
| 12 | Curry's windowed sparsity, `β*`, `1/β*` floor exclusion | README manuscript highlights | `#(A ∩ [a,a+X)) ≤ C_β X^β log 2X` for collision-free `A`; floor exclusion `B < 1/β*` | Curry's own theorem, on the García–Tal mechanism | **external dependency**, not repository mathematics | EXTERNAL THEOREM (not formalized) | **CLASSICAL / EXTERNAL** | already correctly separated from García–Tal; keep | `Curry2026`, `GarciaTal1999` |
| 13 | Banach-density-zero context | README §divergent orbits | qualitative density-zero for orbit representative sets | García–Tal | prerequisite for 12; no exponent stated there | EXTERNAL THEOREM | **CLASSICAL / EXTERNAL** | already correct; DOI now recorded | `GarciaTal1999` |
| 14 | Tao mixing interface | row L/M, `TaoLike/TaoInterface.lean` | `TaoMixingHypothesis` quoting Tao's Prop. 1.9 | Tao's theorem | **external hypothesis**; Tao's analytic proof is *not* formalized | CONDITIONAL FORMAL RESULT | **CLASSICAL / EXTERNAL** | "conditional on an external theorem, quoted not reproved" (already stated) | `Tao2022` |
| 15 | Tao triangle geometry `U(a,b)` | `TriangleArray`, `MaxTriangle`, `TriangleHop` | recurrences, propagation, merging; sharp distinct-triangle hop | Tao's triangle picture | follows Tao's construction; the hop theorem is the repository's own sharpening | LEAN-PROVED | **NEW DERIVATION OF KNOWN INGREDIENTS** | "exact geometry of Tao's triangles; the hop bound is ours" | `Tao2022` |
| 16 | `R_max(L) = o(L)` via the p-adic Subspace Theorem | `MaxTriangle` + Schlickewei | ineffective sublinearity of maximal triangle size | Schlickewei's p-adic subspace theorem; Ridout; Mahler analogy | **external dependency**; the reduction is the repository's | LEAN-PROVED reduction + EXTERNAL THEOREM | **NEW DERIVATION OF KNOWN INGREDIENTS** | "our reduction plus a classical Diophantine theorem; ineffective" | `Schlickewei1976`, `Ridout1958`, `Mahler1957`, `EvertseSchlickewei2002` |
| 17 | Unconditional `ShapeTail` for all even `j ≥ 300` | `ShapeUnconditional.lean` | badly shaped confined words are an exponentially small share, rate `2·2^{−j/300}` | no equivalent found | layered-kernel + explicit super-eigenvector certificate | LEAN-PROVED | **UNCERTAIN — MORE SEARCH NEEDED**, leaning APPARENTLY DISTINCT | "no equivalent statement was identified in the literature reviewed" | — |
| 18 | Super-eigenvector certificate `h(l,x) = 2^{σ−x}` | `ShapeCertificate.lean` | Collatz–Wielandt-style relaxation replacing a spectral computation | Collatz–Wielandt theory (standard) | standard technique, specific certificate | LEAN-PROVED | **NEW DERIVATION OF KNOWN INGREDIENTS** | "a standard Collatz–Wielandt relaxation with an explicit witness" | — |
| 19 | `CriticalWhiteCount ⇒ LowFreqDecay ⇒ WeightedFourier ⇒ exceptional bound` | `WhiteContraction`, `DecayInterface`, `WeightedChain` | chain of implications | Tao's Fourier strategy on a different ensemble | analogous strategy, different ensemble | LEAN-PROVED (implications only) | **NEW DERIVATION OF KNOWN INGREDIENTS** | "the same broad Fourier strategy on confined words; the first hypothesis is unproved" | `Tao2022` |
| 20 | `PowerOfTwoDangerousWindowSparsity` | `ArithmeticFrontier.lean` | ternary digit patterns of powers of 2 along confined paths | classical digit questions for `2^n mod 3^b`; Mahler | analogous family; not equivalent to any named conjecture (repo already says so) | OPEN | **CONJECTURAL** | keep the existing careful wording | `Mahler1957`, `Ridout1958` |
| 21 | Rényi-2 / prefix-sharing barrier | `RenyiBarrier.lean` | a collision-rate obstruction to uniform-in-frequency decay | second-moment/collision arguments (standard) | standard technique, specific obstruction | LEAN-PROVED | **NEGATIVE RESULT** | "a barrier internal to our approach" | — |
| 22 | iid `Geom(2)` persistence Chernoff bound | row N, `PersistenceModel.lean` | exponential-rate bound on the abstract iid persistence event | Lagarias–Weiss / Kontorovich–Lagarias stochastic models; standard Chernoff | standard large-deviation computation in a model of a known type | LEAN-PROVED (abstract model) | **CLASSICAL** (technique) | "a Chernoff bound in a standard iid model; not transferred to real orbits" | `LagariasWeiss1992`, `KontorovichLagarias2010` |
| 23 | Finite Chang-history realizability | row I, `ChangHistory.lean` | every finite binary Chang history is realized by some odd seed | Chang's one-bit mixing framework | **inspired terminology + borrowed observable**; the theorem is the repository's | LEAN-PROVED | **NEW DERIVATION OF KNOWN INGREDIENTS** | "our finite realizability theorem for an observable defined by Chang" | `Chang2026` |
| 24 | Mechanical/Sturmian word confinement | README §critical Sturmian boundary | `d*_j = ⌊α(j+1)⌋ − ⌊αj⌋` stays below the critical line; least realizers unbounded | López–Stoll, 3x+1 conjugacy over a Sturmian word | **UNCERTAIN**: same map and word class; the question asked may differ | PROVED MATHEMATICALLY (corollary of row G) | **UNCERTAIN — MORE SEARCH NEEDED** | "elementary; cf. prior work on the 3x+1 conjugacy over Sturmian words" | `LopezStoll2009` |
| 25 | Global Occupation Conjecture, `O_c(m₀) = O(log m₀)` | README §EOC | occupation count at drift level `c` is logarithmic in the seed | **Rozier's LBH** (`Rozier2017`, Hyp. 2.3) | same map, same placement question, same entropy mechanism; logical relation unsettled | OPEN / CONJECTURE | **CONJECTURAL**, with `Rozier2017` as closest prior conjecture | "our occupation formulation of a placement conjecture whose closest published relative is Rozier's Lower Bound Hypothesis; neither is known to imply the other" | `Rozier2017`, `Curry2026` |
| 26 | `CriticalCrossing`, finite occupation | README §EOC | weaker qualitative escape statements | Rozier Lemma 3.1 (LBH ⇒ trajectories reach 1) | weaker than what LBH would give | OPEN | **CONJECTURAL** | keep | `Rozier2017` |

## 3. Provenance of the Lean development

The brief's four categories, applied to the 90 tracked modules:

**A. Mathematically new theorem formalized in Lean.** No module qualifies unambiguously.
The best candidates are `ShapeUnconditional.shapeTail_allEven_rate` (row 17) and
`TriangleHop`'s sharp distinct-triangle bound (row 15), both of which are internal
statements about ensembles this repository defines, so "new" is not a meaningful claim
against the external literature. Recommended wording for both: *no equivalent statement was
identified in the literature reviewed.*

**B. Known mathematical theorem newly formalized.** `Realizer.lean` (row 2), `Carry.lean`
(row 3), `CompositionCounting.lean` (row 5), `ChordRotation.lean` (row 6). These are the
repository's clearest contribution *as formalization*: the parity-vector congruence, the
2-adic reconstruction, the composition count and the cycle lemma are all classical, and to
the extent of this review none had a Lean/Mathlib formalization before. That is a real
contribution and should be stated as a formalization contribution, not a mathematical one.

**C. Internal supporting lemma.** The bulk: `Confinement`, `FiniteValuationWord`,
`LiftDigits`, `ShapeBridge`, `ShapeCertificate`, `WhiteContraction`, `DecayInterface`,
`WeightedChain`, `PrefixPartition`, `RestartLawAlignment`, and the rest of the chain
plumbing.

**D. Computationally derived statement encoded formally.** `ArithmeticFrontier`'s certified
rates, the kernel-checked finite arithmetic inside the ShapeTail chain, and the
kernel-checked hop witness `(160,5) → (154,6)`. These are exact within their tested range
and must not read as unconditional theorems beyond it.

**The existence of a Lean proof does not make a theorem mathematically new**, and a known
result formalized is still a contribution. Both directions are now stated in the README.

## 4. Attribution audit

| checked | finding |
|---|---|
| García–Tal vs. Curry | **already correct and carefully separated**, in both the README context section and the manuscript-highlights section. No change needed; the missing DOI `10.4064/aa-90-3-245-250` is now recorded |
| Rozier | **named twice, cited nowhere** — fixed; `Rozier2017` added with DOI `10.7169/facm/1583` |
| Eliahou | **not cited at all**, though the product identity behind the drift identity is his — fixed |
| Bernstein; Bernstein–Lagarias | **not cited at all** — fixed |
| Chang | locator flagged "SOURCE TO VERIFY" — **verified**, DOI `10.48550/arXiv.2603.25753`; author string "Chang, Edward Y." per arXiv metadata |
| Mahler vs. Ridout | the Mahler citation and DOI in `LITERATURE_SUBSPACE_TRIANGLES.md` are **correct**; Ridout was named without a locator — `10.1112/S0025579300001339` now recorded |
| Schlickewei 1976 attribution | the subspace-theorem attribution to Schlickewei (1976) is **correct**; DOI `10.1515/crll.1976.288.86` now recorded. The Crossref record carries no author field for that volume |
| Korec | cited only via Tao's abstract, metadata unverified — **still unverified**: Mathematica Slovaca volumes of that period are not in Crossref. Flagged in `references.bib` |
| surveys used in place of primary sources | `Lagarias2010overview` is used for the Terras–Everett equidistribution statement. Primary sources `Terras1976`/`Everett1977` are also cited, so this is acceptable; the overview is orientation, not substitute |
| Tao attribution | correct throughout; density notion (logarithmic, not natural) correctly stated |

No Lean theorem identifier was renamed. `ChangHistory` keeps its name: the observable is
genuinely Chang's, and the module docstring already scopes what is and is not claimed.

## 5. Claim-strength audit

| phrase | occurrences | verdict |
|---|---|---|
| "novel" | 1 | it is the disclaimer *"It is not a novelty claim"* — correct as is |
| "proved here" | 1 | in a negative construction (*"is **not** proved here"*) — correct |
| "first" | 14 | all are *first-passage*, *first crossing*, *first-reducing*, *first terms* — technical, none is a priority claim |
| "new" | 12 | mostly *"new lower bounds"* in cited titles and *"nothing new is claimed"*; one instance (*"**D** would need a genuinely new invariant or theorem"*) is a target, not a claim |
| "exact" | 61 | used in the precise sense (exact identity, exact enumeration, exact congruence). Row 4 is the one place where "exact … derived by hand" implied origination; corrected |
| "sharp" | 4 | `TriangleHop`'s sharp hop bound and the alignment-style bounds are sharp **within the stated problem** — acceptable, scope is stated |
| "unconditional" | 35 | consistently means *without `TaoMixingHypothesis`*, which the legend defines. Acceptable, but every occurrence still sits inside an OPEN chain, and the README says so |
| "optimal" | 0 | — |
| "for the first time" | 0 | — |

**Net: the repository's claim strength was already well calibrated.** The single wording
correction required is row 4 (the drift identity), plus the added citations. This is unusual
and worth recording: the pre-existing `LITERATURE_CONTEXT.md` disclaimer — *"No systematic
priority search has been carried out, so nothing below asserts that any construction here is
new"* — is precisely the wording this kind of audit is meant to produce.

## 6. Labelling consistency

The repository's legend (FORMALLY VERIFIED / CONDITIONAL FORMAL RESULT / PROVED
MATHEMATICALLY / COMPUTATION / OPEN, plus `RESEARCH_STATUS.md`'s PROVED (LEAN), PROVED
(MATH), EXTERNAL THEOREM, COMPUTATIONAL, HEURISTIC, CONJECTURAL, REFUTED, OPEN) already
covers the distinctions the brief asks for. Two observations:

* **Row 4 was mislabelled by provenance, not by strength.** "PROVED MATHEMATICALLY" is
  accurate as to rigour; it was the absence of a citation that implied origination.
* **Computational enumerations are correctly bounded** — the 1230-environment scan, the
  worst certified rate 0.09124, and the `N ≤ 1000` mechanical-word computation are all
  labelled COMPUTATIONAL with their ranges stated.

## 7. Unresolved novelty questions

1. **Does Rozier's LBH imply EOC, or conversely?** Both are entropy-governed placement
   statements for the same map. Not settled here. This is the most important open
   provenance question in the repository.
2. **`LopezStoll2009` vs. the mechanical-word section.** Same map, same word class; full
   text not compared. Read before any Sturmian novelty claim.
3. **Is `ShapeTail` (row 17) genuinely without precedent?** It is a statement about an
   ensemble this repository defines, so the question may not be well posed against the
   external literature.
4. **`Korec1994`** remains bibliographically unverified.
5. **Row 7's `H₂(1/α)`** — whether the specific confined-word entropy count appears in the
   literature. `LITERATURE_CONTEXT.md` §4 already asks for this; Rozier is the nearest hit
   found, and it is close.
