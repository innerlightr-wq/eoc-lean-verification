## Revision 5 Update — September 2026

Revision 5 substantially reorganizes the EOC program around two distinct
axes of the accelerated Collatz problem:

1. **The drift / Archimedean axis** — what can be proved about the growth,
   sparsity, and drift behavior of a hypothetical divergent orbit.

2. **The residue / arithmetic-placement axis** — how small the exact
   positive integer realizing a prescribed valuation word can be.

The second remains the central unresolved component of the Effective
Occupation Conjecture (EOC).

### 1. Garcia–Tal / Curry divergent-orbit sparsity

Revision 5 incorporates the collision-free orbit-sparsity mechanism of
Garcia and Tal (1999), together with the explicit quantitative sharpening
developed by M. J. Curry (2026).

Garcia and Tal established qualitative zero-Banach-density behavior for
infinite aperiodic generalized 3n+1 orbits. Curry supplied an explicit
windowed sparsity estimate of the form

\[
\#(\mathcal O\cap[a,a+X))
\le C_\beta X^\beta\log(2X),
\qquad \beta>\beta_*,
\]

where

\[
\beta_*\approx0.9653844.
\]

Applied to the accelerated Collatz orbit, this yields:

- reciprocal summability along every hypothetical divergent orbit,
  \[
  \sum_{n\ge0}\frac1{m_n}<\infty;
  \]

- bounded accumulated correction term
  \[
  E_n=\sum_{j<n}\log_2\left(1+\frac1{3m_j}\right);
  \]

- exclusion of every eventual logarithmic drift floor
  \[
  R_n\ge-B\log_2 n+O(1)
  \]
  for
  \[
  B<\frac1{\beta_*}\approx1.0358567.
  \]

This crosses the harmonic threshold \(B=1\) and is substantially stronger
than the elementary \(B<8/9\) exclusion developed internally in the EOC
framework.

This result concerns hypothetical divergent orbits only. It does **not**
prove EOC, exclude nontrivial cycles, or resolve the arithmetic placement
of exact realizers.

### 2. Corrected exact realizer congruence

Revision 5 uses the corrected exact realizer modulus

\[
2^{S_N+1},
\]

rather than \(2^{S_N}\).

For a valuation word

\[
D=(d_0,\ldots,d_{N-1}),
\]

with

\[
C_N(D)=\sum_{j=0}^{N-1}3^{N-1-j}2^{s_j},
\qquad
S_N=\sum_{j<N}d_j,
\]

the exact realizers form one residue class modulo \(2^{S_N+1}\):

\[
r(D)\equiv
\bigl(2^{S_N}-C_N(D)\bigr)3^{-N}
\pmod{2^{S_N+1}}.
\]

The extra bit enforces terminal oddness and therefore exact realization of
the final valuation digit.

This provides the arithmetic foundation for the residue-axis formulation
of EOC.

### 3. Fixed anchors and the moving-anchor problem

For periodic and eventually periodic valuation words, the relevant coarse
realizers arise as truncations of a fixed rational 2-adic anchor. Binary
periodicity of that anchor yields exponential lower bounds for the least
positive realizer outside the explicitly identified periodic exceptions.

A first-defect result also survives: for words of the form

\[
X^a E X^b,
\]

the realizer retains an exponential lower bound determined by the periodic
run \(X^a\) preceding the first defect.

The analogous recovery claim after a defect was retracted. Later periodic
runs do not restore the lost global anchor precision.

For genuinely irregular words, the relevant 2-adic anchor changes with the
word itself. This **moving-anchor anti-concentration problem** is now
identified as the central unresolved residue-axis problem of EOC.

### 4. Finite Chang-history realizability

Revision 5 adds a new application of the exact realizer machinery to a
mod-32 return observable related to Edward Y. Chang's one-bit Collatz
framework.

Chang isolates a burst-ending distinction between the classes

\[
9\pmod{32}
\qquad\text{and}\qquad
25\pmod{32}.
\]

In valuation-word language, the present work derives

\[
m_j\equiv9\pmod{16}
\iff
(d_j,d_{j+1})=(2,1),
\]

and, at such an event,

\[
m_j\equiv9\pmod{32}\iff d_{j+2}=1,
\]

\[
m_j\equiv25\pmod{32}\iff d_{j+2}\ge2.
\]

For an arbitrary binary history

\[
y=(y_0,\ldots,y_{K-1}),
\]

define canonical blocks

\[
0\mapsto(2,1,1),
\qquad
1\mapsto(2,1,2).
\]

Concatenating these blocks produces a valuation word of length \(3K\).
The exact realizer theorem then gives a genuine positive odd Collatz seed
whose prescribed events occur consecutively at

\[
0,3,6,\ldots,3(K-1),
\]

with exactly the chosen mod-32 labels.

Hence:

> **Every nonempty finite binary Chang history is realizable as a
> consecutive finite history of genuine accelerated Collatz events.**

For the canonical word,

\[
1\le r(D(y))
<
2^{4K+\#\{t:y_t=1\}+1}.
\]

The event status is completely controlled through index \(3K-2\); the
first event position not determined by the canonical word is \(3K-1\).

### 5. What finite universality does not imply

The finite-history theorem does **not** establish:

- realization of every infinite binary history by one orbit;
- a full binary shift;
- independence or Bernoulli behavior;
- asymptotic frequency \(1/2\);
- Chang's sufficient pointwise balance condition;
- an implication from Chang return balance to EOC;
- an arbitrary irregular-word realizer floor;
- EOC or the Collatz conjecture.

Instead, the theorem rules out a class of finite-obstruction strategies:
there are no forbidden finite binary histories, no universal finite bound
on biased runs, and no local exclusion of either label.

Any asymptotic balance theorem must therefore use genuinely long-range
information along a single orbit.

### 6. Lean 4 formal verification

The finite Chang-history construction has been formalized in Lean 4 /
Mathlib.

Main module:

```text
EOC/ChangHistory.lean

## September 2026 Update: Bounded-Drift Realizer Escape

The repository now includes a second formally verified infinite sector of the
accelerated Collatz / EOC program: **bounded-drift realizer escape**.

New modules:

- `EOC/BoundedDriftCore.lean`
- `EOC/BoundedDrift.lean`

Both modules have been integrated into the project, and the full repository
build completes successfully.

### Main result

For an infinite valuation word \(d\), let

\[
S_N=\sum_{j<N} d_j,
\qquad
R_N=S_N-N\log_2 3,
\]

and let \(r_N(d)\) denote the least positive integer realizing the first
\(N\) valuations exactly.

The new formalization establishes the qualitative implication

\[
\boxed{
-G\le R_N(d)\le c\quad\text{for every }N
\quad\Longrightarrow\quad
r_N(d)\to\infty.
}
\]

Equivalently, an infinite valuation word whose drift remains in a fixed
vertical band cannot have a bounded sequence of least positive exact
realizers.

### Proof architecture

The proof separates the hypothetical realizing orbit into two cases.

If the least realizers were bounded, their monotonicity forces eventual
stabilization at a single positive integer \(m\). That integer then realizes
every finite prefix and therefore the entire infinite valuation word.

For the resulting accelerated orbit:

1. **Non-injective case.**  
   A repeated state gives an eventually periodic orbit. The previously
   formalized periodic-sector result implies positive drift per repeated
   block, forcing \(R_N\) to become unbounded above. This contradicts the
   assumed upper drift bound.

2. **Injective case.**  
   `BoundedDriftCore.lean` supplies a new elementary discrete packing
   argument. A fixed lower drift bound restricts the growth of all orbit
   states, while injectivity requires increasingly many distinct positive
   integers. A dyadic product estimate makes these two requirements
   incompatible.

Thus neither a periodic nor an injective positive orbit can realize an
infinite word whose drift remains bounded both above and below while keeping
its least realizers bounded.

### Mathlib-free arithmetic core

A substantial part of the new argument is isolated in
`EOC/BoundedDriftCore.lean`.

The core proves an integer-arithmetic obstruction of the form

\[
\text{injective accelerated orbit}
\quad\Longrightarrow\quad
\inf_N R_N=-\infty,
\]

expressed internally through an equivalent power inequality rather than
real logarithms.

The proof uses:

- filtered finite products and counting;
- injective-state pigeonhole estimates;
- dyadic decomposition;
- an exact accelerated-orbit product identity;
- a uniform bound on all states through a finite time horizon; and
- a final finite counting contradiction.

The dyadic argument intentionally favors formal simplicity over the sharper
analytic constant available in the accompanying mathematical work. Its
growth exponent is

\[
\log_2(3/2)\approx0.585<1,
\]

which is already sufficient for the qualitative pigeonhole contradiction.

### Relation to the periodic sector

The repository now contains two complementary formally verified mechanisms:

\[
\boxed{
\text{eventually periodic confined word}
\Longrightarrow
r_N\to\infty
}
\]

and

\[
\boxed{
\text{two-sided bounded drift}
\Longrightarrow
r_N\to\infty.
}
\]

The second result removes the entire bounded-drift (equivalently, for a
confined word, bounded-slack) sector from the possible bounded-realizer
regime.

Consequently, any still-unresolved bounded-realizer candidate among
\(c\)-confined words must have drift that makes arbitrarily deep negative
excursions:

\[
\inf_N R_N=-\infty.
\]

This does **not** prove EOC or the Collatz conjecture. The general
moving-anchor problem for irregular confined words with sufficiently deep
negative drift remains open.

### Formal verification status

The new modules were checked with the repository's pinned Lean toolchain and
then integrated into the complete project.

The full build completed successfully:

```text
Build completed successfully (2031 jobs).

## September 2026 Update — Periodic-Sector Formalization

The Lean formalization has been extended to cover the eventually periodic
valuation-word sector of the accelerated Collatz system.

The new modules `PeriodicCore.lean` and `Periodic.lean` formally establish,
among other supporting results, that a positive integer orbit with an
eventually periodic valuation word cannot remain permanently confined above
a fixed drift barrier.

The argument derives the strict block inequality

\[
3^L < 2^{S_B},
\]

for a repeated valuation block of length \(L\) and valuation sum \(S_B\).
Equivalently,

\[
S_B - L\log_2 3 > 0,
\]

so repetition of the block produces positive cumulative drift and eventually
violates any fixed upper confinement bound.

The implementation has been verified with the repository's pinned Lean/Mathlib
environment, and the full project currently builds successfully.

**Scope.** This result settles the eventually periodic sector only. It does
not establish the corresponding escape statement for arbitrary aperiodic
confined valuation words, which remains the principal open sector.


# EOC Lean Verification

```text
Verified release: v1.0.0
Lean: 4.34.0-rc1
Formalized scope: through Proposition 5.9
```

Lean 4 / Mathlib formalization of selected results from the Pillar 3 (residue-axis) section of:

> Elias De Jesús. *A Global Occupation Conjecture for the Accelerated 3x + 1 Map: Drift-Axis Progress, the Corrected Residue-Axis Reformulation, and the Least-Realizer Floor.* Zenodo, 2026. [doi:10.5281/zenodo.21895060](https://doi.org/10.5281/zenodo.21895060) (all-versions DOI: [10.5281/zenodo.20569293](https://doi.org/10.5281/zenodo.20569293))

This repository is a companion artifact to that paper, not a standalone claim. Every theorem below compiles against a pinned Mathlib revision with `lake build`; nothing here is asserted without a corresponding kernel-checked proof.

## What this repository is — and is not

This project formalizes the **exact realizer congruence** (Proposition 5.2), the **confinement/record-chronology apparatus** (Definition 5.5), and the **record-chronology, monotonicity, and single-window equivalence** results (Propositions 5.7–5.9) from the paper's Pillar 3.

It does **not** formalize or claim:

- The Effective Occupation Conjecture (EOC) itself, at any tier (Conjectures 3.1–3.4) — these are open, exactly as the paper states.
- The Collatz conjecture.
- **Proposition 5.10.** Deliberately out of scope. Its forward implication is conditional on the open Conjecture 3.1 and would additionally require formalizing the multi-window occupation functional $O_c$. Its strictness discussion relies on specific externally computed orbit witnesses. Neither component is needed for the kernel-checked single-window theory through Proposition 5.9, so this repository stops at that natural boundary.
- Pillars 1, 2, and 4 of the paper (occupation-tier logic, the unconditional drift-axis floor-exclusion theorem, and the periodic/eventually-periodic realizer floors) — untouched by this repository.

## Verification status

| File | Status |
|---|---|
| `EOC/Basic.lean` | VERIFIED |
| `EOC/ValuationWord.lean` | VERIFIED |
| `EOC/Carry.lean` | VERIFIED |
| `EOC/Realizer.lean` | VERIFIED — **frozen** (see below) |
| `EOC/Confinement.lean` | VERIFIED through Proposition 5.9 |

`Realizer.lean` was verified first and then deliberately frozen: every later file (`Confinement.lean`) imports it read-only and reproves anything it needs locally from public lemmas rather than editing it further. This keeps the dependency graph auditable — a change anywhere in `Confinement.lean` can never silently alter an already-checked result upstream.

### Results formalized, by paper reference

| Paper result | Key Lean theorem(s) | File |
|---|---|---|
| Lemma 3.10 (affine closure) | `affineClosure_val`, `affineClosure_T` | `Basic.lean` |
| Definition 5.1 (word, realizes) | `Realizes`, `realizes_iff_iter_valuation` | `ValuationWord.lean` |
| Carry recursion, closed form | `q_eq_C`, `iter_carry_eq` | `Carry.lean` |
| Proposition 5.2 (exact realizer congruence) | `realizerCongruence` | `Realizer.lean` |
| Remark 5.4 (coarse anchor, two-lift, inequality) | `coarseAnchor_unique`, `leastRealizer_eq_or_eq_add`, `coarseAnchor_le_realizer` | `Realizer.lean` |
| Lemma 5.6 (residue pinning) | `residue_pinning` | `Realizer.lean` |
| Definition 5.5 (confinement, $r_{\min}$) | `Confined`, `rmin` | `Confinement.lean` |
| Proposition 5.7 (record-chronology inversion) | `record_chronology` | `Confinement.lean` |
| Proposition 5.8 (monotonicity) | `rmin_mono` | `Confinement.lean` |
| Proposition 5.9 (single-window equivalence) | `single_window_equiv_log`, `single_window_equiv` | `Confinement.lean` |

## A note on Definition 5.5's `L`

`Confinement.lean` defines `L c m` (the paper's $L_c(m)$) via `sSup`, for notational fidelity — but the file says explicitly, in-line, that this is **not certified**: it matches the paper's intended finite maximum only when the relevant confined-prefix set is bounded above, which the paper justifies via Lemma 4.2 (Pillar 2, unformalized here). Establishing that boundedness ultimately relies on global orbit behavior that is not known unconditionally and lies in Collatz-level territory. Every theorem in this repository that needs $L_c$'s behavior (Propositions 5.7–5.9) sidesteps this by working directly with the `Confined` predicate instead, which is fully well-defined regardless. If you see `L` used anywhere as though its value were established, that is a bug — please open an issue.

## Audit findings worth knowing about

A handful of hypotheses in the formalized statements turned out to be unused by the actual Lean proofs, even though they are retained (per the paper's stated hypotheses) rather than silently dropped:

- `odd_T`'s `Odd m` hypothesis: the proof establishes `Odd (T m)` for *all* `m : ℕ`, not only odd `m`.
- `single_window_equiv_log` / `single_window_equiv`'s `hc : 0 < c` and `hε_pos : 0 < ε`: retained to match the paper's literal "fix $c>0$" and $\varepsilon>0$ hypotheses, though the specific proof strategy used may not need either.

These are recorded here as genuine findings about the formalization, not treated as license to weaken the paper's stated hypotheses.

## Toolchain

- **Lean**: `4.34.0-rc1`
- **Mathlib**: pinned at revision `de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11`

The exact pin is in `lake-manifest.json`; do not `lake update` without expecting to re-verify.

## Reproducing the build

```bash
git clone https://github.com/innerlightr-wq/eoc-lean-verification
cd eoc-lean-verification
lake exe cache get   # downloads prebuilt Mathlib .olean files
lake build
```

A successful run ends with `Build completed successfully`. Everything else printed during the build (module-doc-string style lints, a couple of unused-variable warnings, a `push_neg`-deprecation notice) is a linter warning, not an error — the audit findings above account for the substantive ones.

To check a single file in isolation:

```bash
lake env lean EOC/Confinement.lean
```

## License

- The **paper** (linked above) is CC BY 4.0, per its Zenodo record.
- The **Lean source in this repository** is released under [Apache License 2.0](LICENSE), matching Mathlib's own license, to keep reuse terms consistent with the library this project builds on.

## Citing

If you use this formalization, please cite the paper (DOI above). If you want to cite the formalization itself, cite this repository together with the specific release tag (`v1.0.0`) you built against, given the pinned-Mathlib nature of the build.

## Acknowledgments

Portions of this formalization — proof strategy drafting, Mathlib API verification, and iterative debugging against compiler output — were produced with AI assistance (Anthropic's Claude). All mathematical judgment, the decision of what to formalize and what to explicitly leave out of scope, and responsibility for the correctness of what is claimed here rest with the repository author.
