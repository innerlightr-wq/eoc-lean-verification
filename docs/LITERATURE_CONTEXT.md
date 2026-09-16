# Literature context for the EOC / ShapeTail program

This document helps contributors place the repository relative to established work on the 3x+1 (Collatz)
problem. It says which ingredients are standard and which are specific to this repository. **It is not a novelty
claim.** No systematic priority search has been carried out, so nothing below asserts that any construction here is
new.

Literature for the Tao-triangle / p-adic Subspace rounds is documented separately, with its limits, in
[`LITERATURE_SUBSPACE_TRIANGLES.md`](LITERATURE_SUBSPACE_TRIANGLES.md). Labels follow
[`RESEARCH_STATUS.md`](RESEARCH_STATUS.md).

**How the references were checked (2026-09-16).**

* Bibliographic data for [Te76], [Ev77], [La85], [Ta22], [LW92], [KL03] and [DM47] was read from Crossref DOI
  records. [LW92]'s page range comes from its Project Euclid record.
* [UC10] was checked against its Crossref record (AMS, DOI 10.1090/mbk/078).
* arXiv identifiers and journal references were read from arXiv abstract pages.
* The descriptions of results rely on the published abstracts ([Ev77], [LW92], [KL03], [Ta22]) and on Lagarias's
  overview [La10].
* [Ko94] is included only because Tao's abstract cites its result. Its metadata comes from secondary citations and
  was **not** checked against the journal.

## 1. Stopping times, parity vectors and density one

Terras [Te76] and, independently, Everett [Ev77] studied the accelerated map T(n) = n/2 (n even), (3n+1)/2 (n odd).

* Everett's abstract states that almost every m has an iterate f^k(m) < m. This is the prototype of "almost all
  orbits descend" results.
* Lagarias's overview [La10] credits both authors with the key structural observation: the parity pattern of the
  first n iterates is equidistributed over residues mod 2^n. In this sense the initial iterates behave like
  independent fair coin flips.

**In this repository.** The exact correspondence between valuation words and residue classes of their realizers is
formalized and sharpened in `ValuationWord`, `FiniteValuationWord`, `Realizer`, `LiftDigits` and related modules.
The confinement condition S_i ≤ ⌊iα + c⌋ (α = log₂ 3) packages the "orbit has not yet risen" event as a lattice-path
constraint on prefix sums. The unconditional baseline exceptional exponent H₂(1/α) (`ExceptionalPowerBound`) is a
counting statement of this Terras–Everett type. These parts are standard in spirit; the Lean formalization and the
exact confined-word bookkeeping are this repository's contribution.

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
  paper that uses exactly this entropy/large-deviation formulation for confined words. Contributors aware of one are
  encouraged to add it here with verified metadata.

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

* **[DM47]** A. Dvoretzky and Th. Motzkin, "A problem of arrangements", *Duke Mathematical Journal* **14** (1947),
  no. 2. DOI: [10.1215/S0012-7094-47-01423-3](https://doi.org/10.1215/S0012-7094-47-01423-3). (Page range not
  recorded in the Crossref record; not re-checked.)
* **[Ev77]** C. J. Everett, "Iteration of the number-theoretic function f(2n) = n, f(2n + 1) = 3n + 2", *Advances in
  Mathematics* **25** (1977), no. 1, 42–45. DOI:
  [10.1016/0001-8708(77)90087-1](https://doi.org/10.1016/0001-8708(77)90087-1).
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
* **[LW92]** J. C. Lagarias and A. Weiss, "The 3x + 1 problem: two stochastic models", *The Annals of Applied
  Probability* **2** (1992), no. 1, 229–261. DOI: [10.1214/aoap/1177005779](https://doi.org/10.1214/aoap/1177005779).
* **[Ta22]** T. Tao, "Almost all orbits of the Collatz map attain almost bounded values", *Forum of Mathematics,
  Pi* **10** (2022), e12. DOI: [10.1017/fmp.2022.8](https://doi.org/10.1017/fmp.2022.8). arXiv:
  [1909.03562](https://arxiv.org/abs/1909.03562).
* **[Te76]** R. Terras, "A stopping time problem on the positive integers", *Acta Arithmetica* **30** (1976), no. 3,
  241–252. DOI: [10.4064/aa-30-3-241-252](https://doi.org/10.4064/aa-30-3-241-252).
* **[UC10]** J. C. Lagarias (ed.), *The Ultimate Challenge: The 3x+1 Problem*, American Mathematical Society,
  Providence, RI, 2010. ISBN 978-0-8218-4940-8. DOI: [10.1090/mbk/078](https://doi.org/10.1090/mbk/078).
