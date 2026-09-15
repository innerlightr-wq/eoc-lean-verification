# Literature for the triangle / Subspace rounds (2026-09)

This file lists only literature that was actually read or verified for the results in
[`RESEARCH_STATUS.md`](RESEARCH_STATUS.md). Each entry says how it was checked, which statement is used, and what its
limits are. Entries in the last section are cited in older round notes, but their precise statements were **not**
re-verified; nothing in this repository depends on them.

Third-party texts downloaded for reading (lecture-note PDFs, arXiv source files) are **not** redistributed in this
repository. Use the URLs below.

## 1. The p-adic Subspace Theorem (Schlickewei), via Evertse's lecture notes — EXTERNAL THEOREM, used

* **Source.** J.-H. Evertse, lecture notes on Diophantine approximation (Leiden), Chapter 8 "The p-adic Subspace
  Theorem". <https://pub.math.leidenuniv.nl/~evertsejh/dio19-8.pdf>. The norm convention is in Chapter 7:
  <https://pub.math.leidenuniv.nl/~evertsejh/dio19-7.pdf>.
* **How checked.** The PDF text was read directly (Theorem 8.7 statement, p. 162, and the remark following it; the
  definition ‖x‖ = max|xᵢ| in Chapter 7).
* **Statement used (Theorem 8.7, attributed there to Schlickewei, 1976).** Let n ≥ 2, ε > 0, C > 0, K a number field,
  p₁, …, p_s distinct primes. For each p ∈ {∞, p₁, …, p_s} let L_{1,p}, …, L_{n,p} be linearly independent linear
  forms in X₁, …, X_n with coefficients in K. Then the solutions x ∈ ℤⁿ of
  ∏_{p ∈ {∞,p₁,…,p_s}} |L_{1,p}(x) ⋯ L_{n,p}(x)|_p ≤ C·‖x‖^{−ε}
  lie in finitely many proper linear subspaces of ℚⁿ. The p-adic absolute values are normalized by |p|_p = 1/p.
* **Instance used.** n = 2, K = ℚ, primes 2 and 3, forms X − Y, Y at ∞ and X, Y at 2 and 3, C = 1, ε = δ. In Lean this
  instance is the hypothesis `EOC.MaxTriangle.SubspaceInstance δ`.
* **Relevance.** Gives, with the repository's reduction, R_max(L) = o(L) (`sublinearMaxTriangle_of_subspace`).
* **Limitations.** The theorem is **ineffective**: the remark after Theorem 8.7 states that the only available proofs
  do not determine the subspaces. So no rate for R_max and no computable L₀(ε) follow. The n = 2 case used here is the
  Ridout-type (p-adic Roth) case; Theorem 8.6 of the same notes is the p-adic Roth theorem.

## 2. Mahler: fractional parts of powers of rational numbers — analogy only

* **Source.** K. Mahler, "On the fractional parts of the powers of a rational number (II)", *Mathematika* **4** (1957),
  122–124. DOI: [10.1112/S0025579300001170](https://doi.org/10.1112/S0025579300001170).
* **How checked.** The statement was verified from secondary sources found by web search (e.g. the introduction of
  [arXiv:math/0611622](https://arxiv.org/abs/math/0611622)); the original paper was not read in this session.
* **Statement.** For coprime integers p > q ≥ 2 and every ε > 0, ‖(p/q)ⁿ‖ < e^{−εn} holds for only finitely many n
  (‖·‖ = distance to the nearest integer), proved via Ridout's theorem; ineffective.
* **Relevance.** Same mechanism as §4 of the status file. Writing 3ⁿ = qₙ2ⁿ + rₙ, the Ridout/Subspace bound on the
  {2,3}-free part gives |qₙ||rₙ| ≥ 3^{n(1−ε)}. The repository's case is a 3-adic analogue (small-height 3-adic
  approximations y of 2^{−a}) with two varying cofactors.
* **Limitations.** The EOC / Tao-triangle statement does **not** appear in Mahler's work. Only the mechanism is
  analogous.

## 3. Quantitative Subspace Theorem — NOT USED / REQUIRES RECHECK

A literature audit in the 2026-09-15 hop round (a sub-agent reading author preprints) located the following works and
reported explicit upper bounds, polynomial in 1/δ, for the **number** of exceptional subspaces, with ineffective
**location** (bibliographic data below as reported by that audit; check against the journal versions before citing):

* J.-H. Evertse, "An improvement of the quantitative Subspace theorem", *Compositio Math.* **101** (1996), 225–311.
  Preprint: <https://pub.math.leidenuniv.nl/~evertsejh/95-subspace.pdf>.
* J.-H. Evertse and H. P. Schlickewei, "A quantitative version of the Absolute Subspace Theorem", *J. reine angew.
  Math.* **548** (2002), 21–127. Preprint: <https://pub.math.leidenuniv.nl/~evertsejh/00-abssub.pdf>.
* J.-H. Evertse and R. G. Ferretti, "A further improvement of the Quantitative Subspace Theorem", *Ann. of Math.*
  **177** (2013), 513–590. [arXiv:1008.2340](https://arxiv.org/abs/1008.2340).
* J.-H. Evertse, "On the Quantitative Subspace Theorem", *J. Math. Sci.* **171** (2010), 824–837 (survey). Preprint:
  <https://pub.math.leidenuniv.nl/~evertsejh/08-subspace.pdf>.

**The specific exponents and constants reported by that audit have not been independently re-verified. They are NOT
USED anywhere in this repository (REQUIRES RECHECK).** The only use of these works is qualitative: if a verified bound
N(δ) on the number of exceptional lines holds, then the number of triangles with s ≥ log(2η) + δ·(a log 2 + b log 3)
is at most N(δ). This would make the finite count in `EOC.TriangleHop.largeApexes_finite` effective (the locations
would stay ineffective). Any bound polynomial in 1/δ is polynomial in L/R at scale δ ≈ R/L, and is therefore useless
for occupation at fixed or logarithmic R.

## 4. Tao, "Almost all orbits of the Collatz map attain almost bounded values" — conceptual input

* **Source.** T. Tao, *Forum of Mathematics, Pi* **10** (2022), e12. [arXiv:1909.03562](https://arxiv.org/abs/1909.03562).
* **How checked.** The arXiv source was read in the 2026-09-15 Tao round. Section and line references are recorded in
  `scratch/tao_2026-09-15/REPORT.md`. The source files are not redistributed here.
* **Parts used conceptually.**
  - The decay of Fourier coefficients of the Syracuse random variables (Prop. "f-decay", §7).
  - The triangle geometry of the black set: black/white points; the black set as a union of separated triangles.
  - The cancellation at white points.
  - The renewal / stopping-time architecture and the white-count estimate.
* **Limitations.** Tao's decay estimate is uniform in the frequency and polynomial in strength. Its large-triangle case
  uses a supercritical slope. The repository's law is **critical and confined**, and there uniform decay fails
  numerically (small integer ξ give |Φ_ξ/P| ≈ const; `scratch/tao_2026-09-15/XIUNIT.txt`). **Tao's uniform result
  does not transfer directly to the critical confined law**, and no part of it is formalized here. (The separate
  interface `TaoMixingHypothesis`, quoting Tao's Proposition 1.9, is documented in the README.)

## 5. Cited in round notes; statements NOT re-verified — not used

* C. L. Stewart, "On the representation of an integer in two different bases", *J. reine angew. Math.* **319** (1980),
  63–72. <https://eudml.org/doc/152278>. Bibliographic data verified; the precise lower bound on the number of nonzero
  digits (of order log n / log log n, as quoted in the Tao-round notes) was **not** re-verified from the source.
* Senge and Straus (early 1970s), on the number of nonzero digits of integers in two multiplicatively independent bases
  tending to infinity. Cited in the Tao-round notes. The reference and statement were **not** re-verified.
* **Relevance and limits.** These are the classical results on ternary digits of powers of 2 (digit counts tending to
  infinity at a logarithmic-type rate). Triangle size is the length of a run of equal 3-adic digits of 2^{−a}, so they
  concern the same kind of object. They give only o(L)-type information and **do not** prove the triangle-occupation
  bound needed in `RESEARCH_STATUS.md` §10.
