# Literature context for the EOC / ShapeTail program

This document helps contributors place the repository relative to established work on the 3x+1 (Collatz)
problem. It says which ingredients are standard and which are specific to this repository. **It is not a novelty
claim.** No systematic priority search has been carried out, so nothing below asserts that any construction here is
new.

Literature for the Tao-triangle / p-adic Subspace rounds is documented separately, with its limits, in
[`LITERATURE_SUBSPACE_TRIANGLES.md`](LITERATURE_SUBSPACE_TRIANGLES.md). Labels follow
[`RESEARCH_STATUS.md`](RESEARCH_STATUS.md).

A Zotero-assisted provenance and novelty audit (September 2026) extended this document. Its claim-by-claim matrix is
in [`NOVELTY_AND_PROVENANCE.md`](NOVELTY_AND_PROVENANCE.md), and the machine-verified bibliography is
[`../references.bib`](../references.bib). That audit found four sources bearing directly on this repository's core
claims that were previously uncited — Eliahou, Rozier, Bernstein, and Bernstein–Lagarias — and they are incorporated
below.

**Scope of this document.** It records literature that is part of the repository's **provenance**: work that a claim
here uses, depends on, formalizes, or must be compared against as closest prior art. Papers merely *read during
exploration* are deliberately **not** listed, because listing them would imply a dependency that does not exist.

**How the references were checked (2026-09-16, extended 2026-09-18).**

* Bibliographic data for [Te76], [Ev77], [La85], [Ta22], [LW92], [KL03] and [DM47] was read from Crossref DOI
  records. [LW92]'s page range comes from its Project Euclid record.
* [UC10] was checked against its Crossref record (AMS, DOI 10.1090/mbk/078).
* arXiv identifiers and journal references were read from arXiv abstract pages.
* The descriptions of results rely on the published abstracts ([Ev77], [LW92], [KL03], [Ta22]) and on Lagarias's
  overview [La10].
* [Ko94] is included only because Tao's abstract cites its result. Its metadata comes from secondary citations and
  was **not** checked against the journal. This remains true after the September 2026 audit: Mathematica Slovaca
  volumes of that period are not deposited with Crossref.
* Entries added in the September 2026 audit ([El93], [Be94], [BL96], [Ro17], [LS09], [Cr78], [Ga81], [Te79],
  [AL95a], [AL95b], [AL95c], [Ri58], [Sc76], [ES02], [Ch26], [GT99], [Cu26]) were obtained by DOI content
  negotiation against publisher or registry metadata, or via the Crossref transform endpoint. [Ro17]'s full text was
  read from the openly available arXiv version (1510.01610), because its claims required direct comparison.

## 1. Stopping times, parity vectors and density one

Terras [Te76] and, independently, Everett [Ev77] studied the accelerated map T(n) = n/2 (n even), (3n+1)/2 (n odd).

* Everett's abstract states that almost every m has an iterate f^k(m) < m. This is the prototype of "almost all
  orbits descend" results.
* Lagarias's overview [La10] credits both authors with the key structural observation: the parity pattern of the
  first n iterates is equidistributed over residues mod 2^n. In this sense the initial iterates behave like
  independent fair coin flips.

### The 2-adic realizer formula and the conjugacy map

Two further classical sources bear directly on the repository's realizer arithmetic, and were **not cited before the
September 2026 audit**.

* **Bernstein [Be94]** gives a noniterative 2-adic formula for the 3N+1 conjugacy: `Q = 2^{d_0} + 2^{d_1} + …` and
  `N = (−1/3)2^{d_0} + (−1/9)2^{d_1} + (−1/27)2^{d_2} + …` with `0 ≤ d_0 > d_1 > …`. The exponent sequence is this
  repository's valuation word, and the series is a closed-form realizer reconstruction. The repository's `Carry`
  closed form and `Realizer` congruence are the same object in different notation.
* **Bernstein–Lagarias [BL96]** construct the conjugacy `Φ` on `ℤ₂` with `Φ∘S∘Φ⁻¹ = T` and determine the cycle
  structure of the induced permutation `Φ_n` of `ℤ/2ⁿℤ`. This is the structural statement behind "a valuation word
  pins exactly one residue class of its realizers", and it is more general than what is needed here.

So the reconstruction direction is **classical**, and the repository's contribution on this axis is the Lean
formalization, not the formula.

**In this repository.** The exact correspondence between valuation words and residue classes of their realizers is
formalized and sharpened in `ValuationWord`, `FiniteValuationWord`, `Realizer`, `LiftDigits` and related modules.
The confinement condition S_i ≤ ⌊iα + c⌋ (α = log₂ 3) packages the "orbit has not yet risen" event as a lattice-path
constraint on prefix sums. The unconditional baseline exceptional exponent H₂(1/α) (`ExceptionalPowerBound`) is a
counting statement of this Terras–Everett type. These parts are standard in spirit; the Lean formalization and the
exact confined-word bookkeeping are this repository's contribution.

## 1a. Rozier's Lower Bound Hypothesis and the Eliahou product identity — closest prior art

This section records the most consequential finding of the September 2026 audit. Both results were previously
uncited, and both bear on statements the repository treats as its own.

### The product identity behind the drift identity

Eliahou [El93] proved lower bounds on nontrivial cycle lengths using an exact product relation between an orbit's
endpoints and its odd terms. Rozier [Ro17, Lemma 2.5] states the generalization to arbitrary finite segments:

    T^(j)(n)/n = 2^(−j) · Π_{k<q} (3 + 1/m_k)

with `m_0, …, m_{q−1}` the odd terms among `n, T(n), …, T^(j−1)(n)`. Taking base-2 logarithms and separating the
`3^q` factor gives

    log₂(T^(j)(n)/n) = −j + q·log₂3 + Σ_{k<q} log₂(1 + 1/(3m_k))

which, with `q` the number of odd steps and `j` the total number of halvings, is **exactly** the repository's drift
identity `log₂(m_N/m₀) = N·α + E_N − S_N` with `E_N = Σ log₂(1 + 1/(3m_n))`, term for term. The identity is therefore
**classical**; what belongs to this repository is the logarithmic drift bookkeeping (`R_N`), the confinement framing,
and the Lean packaging — not the identity.

### The Lower Bound Hypothesis

Rozier [Ro17, Hypothesis 2.3] conjectures that there is a constant `C ≥ 0` with

    n ≥ j^(−C) · 2^((1 − H(q/j))·j)

for all positive `j, n` (not both 1), where `q` is the number of odd terms in `n, T(n), …, T^(j−1)(n)` and `H` is the
binary entropy function. This is a conjectural **entropy-governed lower bound on the least integer realizing a
prescribed parity-pattern statistic** — the same question as this repository's residue/arithmetic-placement axis, at
coarser `(j, q)` resolution rather than per valuation word.

Three facts make this the closest prior art to the repository's conjectural layer:

* **Theorem 2.6 proves the inequality unconditionally** when the ones-ratio satisfies `r = q/j ≤ 1/log₂3 = 0.630…`
  and the orbit terms `n, T(n), …, T^(j)(n)` are all **distinct**, in the forms `n ≥ j^(−1/6)·2^((1−ρr)j)` with
  `ρ = log₂3`, and for `r ≤ r_H = 0.6090897…` also `n ≥ j^(−1/6)·2^((1−H(r))j)`. Both the threshold `1/α` and the
  distinctness hypothesis coincide with this repository's `1/α` and its `injective_orbit` hypotheses (rows V, W).
* **Lemma 3.1: LBH implies every trajectory reaches 1.** A conjecture of this shape is already known to suffice for
  the divergence half of the problem.
* **Theorem 4.1: LBH implies explicit bounds** on total stopping time and maximum excursion, with the same `r_H` that
  Curry identifies with his `γ*` — which is how Rozier entered this repository's documentation second-hand, before
  being cited directly.

**Consequences for this repository.**

* The entropy-governed least-realizer lower bound must not be described as specific to this programme.
* The harmonic-packing exclusion (`HarmonicPacking.lean`, `B < 8/9`) uses the mechanism of Theorem 2.6 — distinctness
  gives control of `Σ 1/m_k`, which gives a lower bound — and reaches a **weaker** threshold than both Rozier's
  theorem in its regime and Curry's published `B < 1/β* ≈ 1.0359`. It remains a genuine Lean formalization of an
  elementary argument; it is not a frontier result.
* The **Global Occupation Conjecture's closest published relative is LBH.** Whether either implies the other was
  **not** settled by this audit, and no independence is claimed. This is recorded as the repository's principal open
  provenance question in [`NOVELTY_AND_PROVENANCE.md`](NOVELTY_AND_PROVENANCE.md) §7.

### Sturmian words

López–Stoll [LS09] study the 3x+1 conjugacy map over a Sturmian word — the same map and the same word class as the
repository's "critical Sturmian boundary" discussion and the manuscript's Sturmian/Christoffel material. Only the
bibliographic record and title were verified in the audit; the full text was not compared claim by claim, so this is
flagged **UNCERTAIN — MORE SEARCH NEEDED** and should be read before any Sturmian-related novelty claim.

## 2. Surveys and structural perspective

Lagarias's survey [La85] and the volume he edited [UC10], including the overview [La10] and the annotated
bibliographies [LaB1], [LaB2], are the standard entry points. They organize the problem around:

* the parity-vector (2-adic) encoding;
* density results;
* cycles;
* stochastic models;
* generalizations.

Contributors should consult them before treating any intermediate statement here as unexplored.

## 3. Almost-all and probabilistic results

* **Density bounds.** Tao's abstract [Ta22] cites Korec [Ko94]: Col_min(N) ≤ N^θ for almost all N (natural density)
  for every θ > log 3 / log 4. Krasikov–Lagarias [KL03] use difference inequalities to show that at least x^0.84 of
  the integers below x have 1 in their forward orbit (computer-assisted, per their arXiv abstract).
* **Tao's theorem.** [Ta22]: for any f with f(N) → ∞, Col_min(N) ≤ f(N) for almost all N in the sense of
  logarithmic density. By its abstract, the proof establishes an approximate transport property for a first-passage
  random variable of the Syracuse iteration. That property comes from estimating the characteristic function of a
  skew random walk on a 3-adic cyclic group at high frequencies, by studying how a two-dimensional renewal process
  meets a union of triangles attached to the frequency.

**In this repository.** Tao's result is not formalized. Where the `TaoLike` modules use Tao-style mixing, it enters
only as the explicit hypothesis `TaoMixingHypothesis` (see the README). The "Tao triangles" U(a,b) = (2^{−a} mod 3^b)/3^b
and their exact geometry (`TriangleArray`, `MaxTriangle`, `TriangleHop`) follow the triangle picture of [Ta22].

## 4. Stochastic models, large deviations, entropy

* **Stochastic models.** Lagarias–Weiss [LW92] introduce two stochastic models: a random walk imitating
  T (mod 2^j), and branching random walks imitating T^{−1} (mod 3^j). For both they prove analogues of the conjecture
  that limsup σ_∞(n)/log n is a finite constant, obtaining γ₀ ≈ 41.677647 in both models. Kontorovich–Lagarias [KL10]
  survey stochastic models for the 3x+1 and 5x+1 problems. These works are the natural reference for heuristics of
  the "iid geometric digits" type.
* **Binomial / entropy counting.** The confined-word counts here are lattice-path counts. The lower bound
  C(σ−1, j−1) ≤ j·|shell| rests on a chord-rotation argument of cycle-lemma type (`ChordRotation`,
  `CapacityBounds.shell_choose_le_mul_card`), a classical tool of Dvoretzky–Motzkin type [DM47]. The entropy bound
  C(n,k) ≥ 2^{nH(k/n)}/(n+1) (`BinomialEntropy`) is textbook material. We have **not** verified a specific Collatz
  paper that uses exactly this entropy/large-deviation formulation for **confined** words. The nearest hit found by
  the September 2026 audit is Rozier [Ro17], whose exponent `1 − H(r)` and threshold `r ≤ 1/α` are the same entropy
  mechanism at the level of `(length, odd-count)` pairs rather than confined words — close enough that the
  repository's `H₂(1/α)` baseline should be presented as a Terras–Everett-type count in the Rozier family rather than
  as an independent discovery. Contributors aware of a closer source are encouraged to add it with verified metadata.

## 5. Fourier techniques

Modern almost-all arguments control characteristic functions of 3-adic distributions of Syracuse-type random
variables [Ta22]. This repository follows the same broad strategy on a different ensemble: exponential sums over
**confined** valuation words, organized by prefix shells. The chain

`CriticalWhiteCount ⇒ LowFreqDecay ⇒ WeightedFourier ⇒ exceptional-set bound`

is PROVED (LEAN) as a sequence of implications (`WhiteContraction`, `DecayInterface`, `WeightedChain`). Its first
hypothesis is not proved. Known obstructions are recorded in `RESEARCH_STATUS.md` §12: uniform-in-frequency decay
fails at criticality, and there is a Rényi-2 barrier.

## 6. How the present repository differs

The present repository combines these ingredients in the following formal architecture.

* **Exact confined-word dynamic programming.** The ensemble is the finite shell of valuation words confined below the
  Collatz barrier with prescribed total. It is analysed through exact class decompositions (even prefix sums) and
  layered transfer kernels, not through an iid model. Probabilistic models enter only as heuristics or explicit
  hypotheses.
* **ShapeTail as a layered-kernel statement.** The shape side of the white-count problem, i.e. how many digit-pair
  blocks offer a usable interval of choices, reduces through `ShapeTail → TightTail → tilted class sum` to a pinned
  layered kernel (`ShapeBridge.class_sum_le_ker`). Classes inject into kernel paths, so no characterization of
  realizable classes is needed.
* **An explicit super-eigenvector certificate.** h(l,x) = 2^{σ−x} with tilt u = 3 and constant M = 3/2
  (`ShapeCertificate.blockW_superEigen`). This is a Collatz–Wielandt-style relaxation: one explicit positive vector
  replaces any spectral computation.
* **Lean formalization with kernel-checked arithmetic.** For every even j ≥ 300 the whole ShapeTail chain is
  PROVED (LEAN) (`ShapeUnconditional.shapeTail_allEven_rate`, rate ρ₁ ≤ 2·2^{−j/300}; see
  [`SHAPETAIL_UNCONDITIONAL.md`](SHAPETAIL_UNCONDITIONAL.md)). All finite arithmetic is checked by the Lean kernel.
* **The unresolved pressure problem.** `OddBlack.OddDarkPressure` asks for an exponential-moment bound on the number
  of dark odd cells a confined word carries in its own shape-good blocks. It is OPEN for the true environment. It is
  a 3-adic digit-pattern problem for powers of 2 sampled along confined paths. The incomplete exponential sums
  involved lie outside the ranges of standard short-sum estimates (`RESEARCH_STATUS.md` §10).

Nothing here proves the Collatz conjecture, and the exceptional-set exponent of the repository remains H₂(1/α).

## References

* **[AL95a]** D. Applegate and J. C. Lagarias, "Density bounds for the 3x+1 problem. I. Tree-search method",
  *Mathematics of Computation* **64** (1995), no. 209, 411–426. DOI:
  [10.1090/S0025-5718-1995-1270612-0](https://doi.org/10.1090/S0025-5718-1995-1270612-0).
* **[AL95b]** D. Applegate and J. C. Lagarias, "Density bounds for the 3x+1 problem. II. Krasikov inequalities",
  *Mathematics of Computation* **64** (1995), no. 209, 427–438. DOI:
  [10.1090/S0025-5718-1995-1270613-2](https://doi.org/10.1090/S0025-5718-1995-1270613-2).
* **[AL95c]** D. Applegate and J. C. Lagarias, "The distribution of 3x+1 trees", *Experimental Mathematics* **4**
  (1995), no. 3, 193–209. DOI: [10.1080/10586458.1995.10504321](https://doi.org/10.1080/10586458.1995.10504321).
* **[Be94]** D. J. Bernstein, "A noniterative 2-adic statement of the 3N+1 conjecture", *Proceedings of the American
  Mathematical Society* **121** (1994), no. 2, 405–408. DOI:
  [10.1090/S0002-9939-1994-1186982-9](https://doi.org/10.1090/S0002-9939-1994-1186982-9).
* **[BL96]** D. J. Bernstein and J. C. Lagarias, "The 3x+1 conjugacy map", *Canadian Journal of Mathematics* **48**
  (1996), no. 6, 1154–1169. DOI: [10.4153/CJM-1996-060-x](https://doi.org/10.4153/CJM-1996-060-x).
* **[Ch26]** E. Y. Chang, "A Structural Reduction of the Collatz Conjecture to One-Bit Orbit Mixing", arXiv:
  [2603.25753](https://arxiv.org/abs/2603.25753) (2026). DOI:
  [10.48550/arXiv.2603.25753](https://doi.org/10.48550/arXiv.2603.25753). A copy also carries
  [10.13140/RG.2.2.28140.22403](https://doi.org/10.13140/RG.2.2.28140.22403). Author string as given by the arXiv
  metadata; OpenAlex normalizes it to "Edward Yi Chang". Verified 2026-09-18 via DataCite and OpenAlex; note that
  arXiv's own API does not return this record.
* **[Cr78]** R. E. Crandall, "On the '3x+1' problem", *Mathematics of Computation* **32** (1978), no. 144, 1281–1292.
  DOI: [10.2307/2006353](https://doi.org/10.2307/2006353).
* **[Cu26]** M. J. Curry, "An Explicit Windowed Sparsity Bound for Divergent 3x+1 Orbits, with Logarithmic-Floor
  Exclusion beyond the Harmonic Barrier", Zenodo, 2026. DOI:
  [10.5281/zenodo.22087163](https://doi.org/10.5281/zenodo.22087163).
* **[DM47]** A. Dvoretzky and Th. Motzkin, "A problem of arrangements", *Duke Mathematical Journal* **14** (1947),
  no. 2. DOI: [10.1215/S0012-7094-47-01423-3](https://doi.org/10.1215/S0012-7094-47-01423-3). (Page range not
  recorded in the Crossref record; not re-checked.)
* **[El93]** S. Eliahou, "The 3x+1 problem: new lower bounds on nontrivial cycle lengths", *Discrete Mathematics*
  **118** (1993), no. 1–3, 45–56. DOI:
  [10.1016/0012-365X(93)90052-U](https://doi.org/10.1016/0012-365X(93)90052-U).
* **[Ev77]** C. J. Everett, "Iteration of the number-theoretic function f(2n) = n, f(2n + 1) = 3n + 2", *Advances in
  Mathematics* **25** (1977), no. 1, 42–45. DOI:
  [10.1016/0001-8708(77)90087-1](https://doi.org/10.1016/0001-8708(77)90087-1).
* **[Ga81]** L. E. Garner, "On the Collatz 3n+1 algorithm", *Proceedings of the American Mathematical Society* **82**
  (1981), no. 1, 19–22. DOI:
  [10.1090/S0002-9939-1981-0603593-2](https://doi.org/10.1090/S0002-9939-1981-0603593-2).
* **[GT99]** M. V. P. Garcia and F. A. Tal, "A note on the generalized 3n+1 problem", *Acta Arithmetica* **90**
  (1999), no. 3, 245–250. DOI: [10.4064/aa-90-3-245-250](https://doi.org/10.4064/aa-90-3-245-250). (The DOI was not
  recorded in this repository before the September 2026 audit.)
* **[KL03]** I. Krasikov and J. C. Lagarias, "Bounds for the 3x+1 problem using difference inequalities", *Acta
  Arithmetica* **109** (2003), no. 3, 237–258. DOI: [10.4064/aa109-3-4](https://doi.org/10.4064/aa109-3-4).
  arXiv: [math/0205002](https://arxiv.org/abs/math/0205002).
* **[KL10]** A. V. Kontorovich and J. C. Lagarias, "Stochastic models for the 3x+1 and 5x+1 problems", in [UC10],
  pp. 131–188. arXiv: [0910.1944](https://arxiv.org/abs/0910.1944).
* **[Ko94]** I. Korec, "A density estimate for the 3x+1 problem", *Mathematica Slovaca* **44** (1994), no. 1, 85–89.
  (Cited in [Ta22]; metadata from secondary citations, not checked against the journal.)
* **[La85]** J. C. Lagarias, "The 3x + 1 problem and its generalizations", *The American Mathematical Monthly*
  **92** (1985), no. 1, 3–23. DOI:
  [10.1080/00029890.1985.11971528](https://doi.org/10.1080/00029890.1985.11971528). Reprinted with corrections in
  [UC10].
* **[La10]** J. C. Lagarias, "The 3x+1 problem: an overview", in [UC10], pp. 3–29. arXiv:
  [2111.02635](https://arxiv.org/abs/2111.02635).
* **[LaB1]** J. C. Lagarias, "The 3x+1 problem: an annotated bibliography (1963–1999)". arXiv:
  [math/0309224](https://arxiv.org/abs/math/0309224).
* **[LaB2]** J. C. Lagarias, "The 3x+1 problem: an annotated bibliography, II (2000–2009)". arXiv:
  [math/0608208](https://arxiv.org/abs/math/0608208).
* **[LS09]** J. López and P. Stoll, "The 3x+1 conjugacy map over a Sturmian word", *Integers* **9** (2009), article
  A13. DOI: [10.1515/integ.2009.014](https://doi.org/10.1515/integ.2009.014).
* **[LW92]** J. C. Lagarias and A. Weiss, "The 3x + 1 problem: two stochastic models", *The Annals of Applied
  Probability* **2** (1992), no. 1, 229–261. DOI: [10.1214/aoap/1177005779](https://doi.org/10.1214/aoap/1177005779).
* **[Ri58]** D. Ridout, "The p-adic generalization of the Thue–Siegel–Roth theorem", *Mathematika* **5** (1958),
  no. 1, 40–48. DOI: [10.1112/S0025579300001339](https://doi.org/10.1112/S0025579300001339). (Cited by name in
  [`LITERATURE_SUBSPACE_TRIANGLES.md`](LITERATURE_SUBSPACE_TRIANGLES.md); the locator was added by the September 2026
  audit.)
* **[Ro17]** O. Rozier, "The 3x+1 problem: a lower bound hypothesis", *Functiones et Approximatio Commentarii
  Mathematici* **56** (2017), no. 1, 7–23. DOI: [10.7169/facm/1583](https://doi.org/10.7169/facm/1583). arXiv:
  [1510.01610](https://arxiv.org/abs/1510.01610). Full text read from the openly available arXiv version; see §1a.
* **[Sc76]** H. P. Schlickewei, "Die p-adische Verallgemeinerung des Satzes von Thue–Siegel–Roth–Schmidt", *Journal
  für die reine und angewandte Mathematik* **1976** (1976), no. 288, 86–105. DOI:
  [10.1515/crll.1976.288.86](https://doi.org/10.1515/crll.1976.288.86). (The Crossref record carries no author field
  for this volume; the attribution is the standard one and matches
  [`LITERATURE_SUBSPACE_TRIANGLES.md`](LITERATURE_SUBSPACE_TRIANGLES.md).)
* **[Ta22]** T. Tao, "Almost all orbits of the Collatz map attain almost bounded values", *Forum of Mathematics,
  Pi* **10** (2022), e12. DOI: [10.1017/fmp.2022.8](https://doi.org/10.1017/fmp.2022.8). arXiv:
  [1909.03562](https://arxiv.org/abs/1909.03562).
* **[Te76]** R. Terras, "A stopping time problem on the positive integers", *Acta Arithmetica* **30** (1976), no. 3,
  241–252. DOI: [10.4064/aa-30-3-241-252](https://doi.org/10.4064/aa-30-3-241-252).
* **[Te79]** R. Terras, "On the existence of a density", *Acta Arithmetica* **35** (1979), no. 1, 101–102. DOI:
  [10.4064/aa-35-1-101-102](https://doi.org/10.4064/aa-35-1-101-102).
* **[UC10]** J. C. Lagarias (ed.), *The Ultimate Challenge: The 3x+1 Problem*, American Mathematical Society,
  Providence, RI, 2010. ISBN 978-0-8218-4940-8. DOI: [10.1090/mbk/078](https://doi.org/10.1090/mbk/078).

---

Machine-readable versions of all of the above, plus the Diophantine entries of
[`LITERATURE_SUBSPACE_TRIANGLES.md`](LITERATURE_SUBSPACE_TRIANGLES.md), are in
[`../references.bib`](../references.bib). Provenance per claim is in
[`NOVELTY_AND_PROVENANCE.md`](NOVELTY_AND_PROVENANCE.md).
