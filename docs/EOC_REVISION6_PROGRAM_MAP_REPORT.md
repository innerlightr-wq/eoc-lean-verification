# EOC Revision 6 — program map revision report

## A. Starting state

| item | value |
|---|---|
| base commit | `e1aee371026fe0501793d7d84dced169c8f64fc5` (`Record commit hash and push status in the audit report`, tip of `time-axis-drift-exit-impossibility-audit`) |
| verified how | `git fetch origin`, then `git rev-parse` against the remote ref |
| ordinary checkout | **dirty** (53 entries). Not touched. |
| worktree | isolated, `scratchpad/eoc-r6`, `.lake/packages` symlinked |
| branch | `eoc-program-map-revision6` |
| `main` | untouched. No PR. |

### A.1 A blocking finding: there is no Revision-5 LaTeX source

The brief instructed me to "locate the actual LaTeX source in the repository". **It does not
exist.** I checked:

- every `.tex` tracked on every remote branch of `eoc-lean-verification` — the only hit is
  `scratch/tao_2026-09-15/src/collatz.tex`, which is Tao's paper, not this one;
- every `.tex` under `/home/elias` to depth 4 — hits are other projects' manuscripts only;
- `~/Downloads`: six files `EOC_latestRev*.pdf`, all byte-identical
  (`73adc35e628b5fbcf8c74557e0ef4b797008f1e58baebff3fdc18c4fe5368fa8`), 25 pages.

Revision 5 exists **only as a PDF**. This is the same hazard recorded for an earlier paper of this
author's (a deposited v1 with no source, whose v2 had to be a labelled reconstruction). I raised it
rather than silently reconstructing, and the chosen course was to **author Revision 6 fresh**: a
new LaTeX document whose content is drawn from the Revision-5 PDF text plus the later audits.

**Consequence for provenance, stated in the paper itself.** Revision 6 is not a diff against
Revision 5's source. Statements carried over are transcribed from the Revision-5 PDF and
re-checked; the paper's claim-status convention marks them `[Revision 5]`. Nothing is asserted to
be verbatim.

## B. Revision-5 architecture

25 pages; abstract + non-claims; nine sections and three appendices:

1 Introduction · 2 Preliminaries · 3 Layer I: EOC and its logical status (four tiers, Thm 3.6
reduction, Cor 3.9 explicit instance, Thm 3.11 Rozier shadow) · 4 Layer II: unconditional
drift-axis progress (Lem 4.2 terminal/cyclic drift, Thm 4.5 the 8/9 bound, Thm 4.8 Garcia–Tal/Curry,
Prop 4.9 reciprocal summability, Thm 4.11 the `1/β*` threshold) · 5 Layer III: residue-axis
reformulation (Prop 5.2 exact congruence, Prop 5.6 record chronology, Prop 5.7 single-window
equivalence, Thms 5.8–5.10 proved sectors, §5.4 Chang finite universality) · 6 Computational
calibration · 7 Relation to prior work · 8 Open problems A–G · 9 Conclusion · Appendices A band
rigidity, B status summary, C Chang clarifications.

Organizing thesis: *divergent-orbit sparsity is well understood; the pointwise residue-axis core —
placement of exact realizers of irregular confined words — is untouched, and the moving-anchor
problem is the central obstacle.*

## C. Why Revision 6 was needed

Ten audits postdating Revision 5, all read for this revision:

| audit | bearing on the paper |
|---|---|
| Curry divergence part 2; Curry realizer window interface | fixed the Curry interface and its limits |
| Realizer lift-digit / positivity | lift digits are realizer bits; eventual-zero tail ⟺ positive realization |
| Normalized carry terminal zero gap | the gap is `⌈E⌉`, a target not a mechanism |
| Transport regeneration realizer bridge | transport budget is exact bookkeeping; the `o(H)` envelope is insufficient |
| Super-budget cancellation / external arithmetic | matching precision collapses to seed bits; external `p`-adic machinery does not apply |
| Intrinsic–extrinsic constraint independence | `B_N = 2^{S_N} m_N`; the two norms are one identity |
| Global single-orbit nonlocal separation | finite-cylinder barrier; word-shadow cardinality barrier |
| Positive-orbit confinement lifetime | the corridor is automatic; `U_all` ⟺ `O(log n)` stopping time |
| Time-axis drift exit / divergence impossibility | integral corridor; drift exit ⟺ no divergence; self-financing recovery |

Three of these materially contradict or supersede Revision-5 text (§P, §H, §Z below). The rest
change the architecture rather than the theorems.

## D. New programme map

Four axes replace three layers: **occupation** (`O_c`), **residue** (`r_min`, `r(D)`), **time**
(`L_c`, `τ_c`), **divergence** (`R_n`, value set). The paper's Figure 1 shows the bridges; every
arrow is referenced to a numbered result. Two chains:

```
EOC → single-window lifetime ⟷ least-realizer frontier ⟷ arithmetic placement
                              (separated returns branch off, uncontrolled)

divergent orbit → R_n → −∞ → last global max → infinite zero-corridor tail → τ₀(m*) = ∞
```

**Every arrow was audited.** One arrow in the brief's proposed diagram was *not* correct as drawn
and was changed: the brief placed "record chronology" below a single-window/separated-returns
split as though both fed into it. Record chronology inverts `L_c` only; separated returns do not
enter it. The figure reflects that.

## E. Exact residue–time duality

Already Propositions 5.6 and 5.7 of Revision 5. **Not new.** What Revision 6 does:

1. promotes them from technical observations inside the residue section to the organizing
   principle of the paper (§6.2);
2. generalizes the exponential case to a transfer principle at arbitrary scale
   (Prop. `prop:transfer`, §R below) — **this is new and is proved here**;
3. records that no unconditional lifetime bound can exist short of excluding divergence, so the
   graded table grades a programme every entry of which is open.

## F. Qualitative time axis

New material in the paper, reclassified rather than newly proved:

- `τ_c(m) = inf{n ≥ 1 : R_n > c}`, with the **integral** characterisation
  `R_n ≤ 0 ⟺ 2^{S_n} ≤ 3^n`. The entire time axis needs no real analysis.
- `(DE)`: every odd `m` has some `n ≥ 1` with `3^n < 2^{S_n}`.
- **Theorem: `(DE)` ⟺ no divergent positive orbit**, compatible with nontrivial cycles, hence
  strictly weaker than Collatz.

**Provenance, stated in the paper.** The forward direction is the companion Curry foundation's
zero-corridor tail theorem (already proved and formalized there). The reverse direction is
Revision 5's own Lemma 4.2 (terminal and cyclic drift). The *statement* `(DE)` is, negated, the
frontier already posed in the companion work. Revision 6's contribution is the reclassification and
the exact placement in the hierarchy — nothing more, and the paper says so twice.

## G. Ordinary stopping comparison

`m_n < m_0 ⟺ R_n > E_n`, so `τ₀ ≤ σ` with `σ` Terras's stopping time. Strictness holds **exactly
at cycle minima** (`m = 1`: `R_n = E_n` identically, `τ₀ = 1`, `σ = ∞`). Off cycle minima,
strictness at depth `n` requires `r_min(n,0) ≤ 0.4809 n/(1 − {αn})`, polynomial in `n`, so any
superpolynomial realizer floor forces `τ₀ = σ`. The inequality is proved; the accompanying
exhaustive search is labelled a computational diagnostic.

## H. Launch-renormalization update

Retained as a valid structural reduction, with the exact scales
(`t₁ ≤ εN + O(1)`, `L ≥ (1−ε)N − O(1)`, `log₂ m* ≤ αεN + O(log N)`, `A ≤ c + (α−1)εN + O(1)`) and
renormalization stability.

**Corrected reading of the closing hypothesis.** The corridor-uniform hypothesis
`L ≤ K(log₂ m + A)` appears to be a mild corridor statement. It is not: the corridor is
*automatic*, `R_n ≤ log₂ m₀ + E_n`, with equality once the orbit reaches 1. Instantiating there
gives `L ≤ K(2log₂ m + E)` with `E = O(log L)`, which bounds `L` — so the hypothesis implies no
orbit is injective forever, i.e. **it implies the absence of divergent orbits**, and with the
converse it is equivalent to an `O(log m)` accelerated stopping-time bound. It is *noncircular*
with respect to Open Problem C but *substantially stronger than Collatz*, and the paper no longer
presents it as a plausibly easier closing hypothesis. The half-strength variant's exemption fired
on 0 of 29,999 tested orbits — recorded as a computation only.

## I. Self-financing recovery

New negative result in the paper. One step achieves drift exit when `2^d m₀ > 3 m_n`; the available
valuation is capped by `2^{d_n} ≤ 3m_n + 1`. The cap exceeds the requirement by a factor ≈ `m₀`.
Underlying reason: `log₂ m_n = log₂ m₀ − R_n + E_n`, so sustained negative drift creates exactly
the ordinary height that permits the recovery valuations repaying it.

**What it rules out**, stated as scope: any argument of the form "a sufficiently deep drift
excursion cannot recover because the required valuation exceeds what the current iterate supplies".
The measured margin (+1.83 minimum) is labelled a diagnostic; the inequality is proved.

## J. Residue-axis updates

Retained: exact realizer congruence mod `2^{S_N+1}`; coarse anchor vs. exact lift and the
unconditional `r(D) ≥ a_{S_N}(D)`; record-chronology inversion; periodic, eventually periodic and
bulk-defect floors; the retraction of the false "long periodic recovery restores precision" claim;
the moving-anchor remark.

Updated: the irregular sector is no longer framed only as "moving anchor". §O below.

## K. Coordinate-collapse ledger

New table in the paper. Normalized carry → same anchor information; lift digits → binary blocks of
the realizer; eventually-zero lift tail → eventual realizer constancy → positive realization;
terminal zero gap → `⌈E⌉`; transport `F/M/H` → exact bookkeeping, with genuine-orbit matching
precision equal to the zero-run of the *seed's* binary expansion; cumulative excess regeneration →
disjoint seed-bit intervals, total `≤ ⌊log₂ m₀⌋ + 1`; `B_N = C_N + 3^N χ = 2^{S_N} m_N`, hence
`v₂(B_N) = S_N` exactly and `log₂|B_N| − v₂(B_N) = log₂ m_N`.

The last row is the reason the product-formula / `p`-adic-versus-Archimedean intersection produced
nothing: there was only ever one condition.

## L. Symbolic / full-shift update

Revision 5 had finite Chang-history universality. Revision 6 strengthens the *symbolic* conclusion
to an infinite zero-corridor full shift (machine-checked), and states the sharper lesson: even
substantial **infinite** symbolic freedom coexists with zero confinement, so the missing
restriction is not local symbolic dynamics. Positive-integer realization of such words remains open
and, by §M, cannot be decided at word level at all.

## M. Word-shadow cardinality barrier

New central boundary theorem. Family indexed by `b ⊆ ℕ`:
`w_b(i) = 2` if `i ≡ 2 (mod 3)` and `⌊i/3⌋ ∈ b`, else `1`. Every member is zero-confined (integral
form `2^{S_n} ≤ 3^n`, from `S_n ≤ n + ⌊n/3⌋` and `16 ≤ 27` after cubing), has
`R_n ≤ (4/3 − α)n → −∞` linearly, `Σ2^{R_n} < ∞`, and `#{n : R_n ≥ −G} = O(G)`. The map is
injective; one positive integer realizes at most one infinite word; Cantor gives **all but countably
many members unrealizable**.

**Scope, stated in the paper**: no collection of word-level global properties can *characterize*
positive realization. It does **not** preclude word-level information yielding quantitative realizer
bounds.

## N. Finite-cylinder barrier

Every odd class mod `2^k` contains arbitrarily large positive odd integers, so every exact-realizer
cylinder is nonempty and unbounded, and no finite-precision property of integers is equivalent to
positivity. Displayed as the quantifier distinction `∀N ∃m_N` (free) versus `∃m ∀N` (the problem).
Scope stated: this concerns *deciding* infinite realization, not proving finite quantitative bounds.

## O. Height / closure reinterpretation

Revision 5: periodic versus irregular. Revision 6: the separating invariant is
`ρ_N = log₂ H / S_N`, the height of the word-generated divisibility relation over the divisor
exponent. Periodic, eventually periodic and one-defect words amortize a fixed height over
unboundedly many repetitions (`ρ_N → 0`); arbitrary words supply only `(C_N, 3^N)` with
`ρ_N ≥ 1`. **Complexity is not the controlling invariant**: the Sturmian zero-corridor word, of
minimal aperiodic complexity, already fails amortization while its periodic approximants do not.
Labelled a structural interpretation, not a theorem about all words.

## P. Frontier-defect correction

Revision 5's Open Problem E asked whether `E(D) ≤ H₂(ρ_c)S + Φ(N)` is genuinely easier than an
exponential floor and recorded that as open. **Corrected.** With `g = ⌈E⌉` and `E ≤ g < E+1`, the
defect target is equivalent up to an additive 1 to a gap bound, and under confinement that is an
exponential floor with `ε = I_Collatz + o(1)`. Open Problem E is the **sharp-leading form of Open
Problem C**, not an independent weaker route. Revision 5's wording is not preserved.

## Q. Occupation versus single-window hierarchy

Retained and promoted: `O_c ≥ L_c` strictly, witnessed by `m₀ = 285175` with `L₁ = 14` but
`O₁ = 97`. A complete single-window theory does not yield EOC. For merely excluding divergence,
however, only the absence of one infinite *final* episode is needed — a much weaker requirement.

## R. Graded lifetime / frontier transfer

New proposition and table:

| lifetime hypothesis | frontier obtained | character |
|---|---|---|
| `L_c(m) ≤ K log₂ m` | `log₂ r_min ≥ N/K` | exponential (Open Problem C) |
| `L_c(m) ≤ K(log₂ m)^p` | `log₂ r_min ≥ (N/K)^{1/p}` | stretched exponential |
| `L_c(m) ≤ K m^θ` | `r_min ≥ (N/K)^{1/θ}` | polynomial |
| `L_c(m) ≤ K m` | `r_min ≥ N/K` | linear |

This is the most constructive output of the recent audits: EOC's residue axis becomes a **graded**
programme. Accompanied by the honest caveat that no unconditional entry is known and none can be
proved without excluding divergence.

## S. Closed-route map

Thirteen rows in the paper, each tagged **T** (formal result), **C** (computational diagnostic) or
**I** (interpretive closure): fixed-modulus packing (terminal at 8/9); bulk entropy; shell
injectivity; moving-anchor collision law; Chang finite *and* infinite symbolic freedom; lift digits;
terminal zero gap; normalized carry; transport budget; external `p`-adic arithmetic; global word
shadows; corridor-uniform lifetime; deep-drift recovery impossibility.

## T. Revised open problems: old → new

| Revision 5 | Revision 6 | change |
|---|---|---|
| A effective constants | A | unchanged |
| B cycle exclusion | B | unchanged |
| C arbitrary-word floor | **C** (merged) | stated in both residue and time form |
| D moving-anchor anti-concentration | **merged into C** | Revision 5 itself said C and D are "the same question at two levels of precision" |
| E frontier defect | **folded into C** | corrected: it is C's sharp-leading form (§P) |
| — | **D intermediate time-axis bounds** | new; any unconditional `L_c` bound |
| — | **E universal drift exit** | new slot; reclassified, explicitly not newly invented |
| — | **F separated returns** | new; the part single-window theory misses |
| F density-one EOC | G | unchanged |
| G pointwise Chang balance | H | demoted to auxiliary |

## U. Abstract changes

Rewritten. No longer ends with "the moving-anchor problem remains the central obstacle". Now
communicates: the four axes; residue–time duality and the graded transfer; Curry's dual
quantitative/qualitative role; the drift-exit ⟺ no-divergence equivalence and its strict weakness
relative to Collatz; the finite-cylinder and cardinality barriers; the coordinate-collapse
identity; launch renormalization's corrected closing hypothesis; self-financing recovery; the
separated-returns gap; and that neither EOC nor Collatz is proved.

## V. Introduction changes

Rewritten around the architecture, not chronology. Answers: what EOC is; why occupation rather than
stopping time; the four axes; which bridges are exact; where unconditional progress exists; what has
been ruled out; what remains. A "what this revision adds" list separates synthesis from new results.

## W. Title recommendation

**Changed**, to:

> A Global Occupation Conjecture for the Accelerated 3x+1 Map: Residue–Time Duality,
> Divergent-Orbit Sparsity, and the Pointwise Realizer Problem

Reason: the Revision-5 subtitle names "the Moving-Anchor Problem" as the terminal object, and §O
shows moving-anchor framing is not the controlling distinction. "Residue–Time Duality" names the
organizing result; "Pointwise Realizer Problem" names the target without over-committing to a
mechanism. The stem is unchanged, preserving bibliographic continuity.

## X. Bibliography audit

22 entries. **Added** relative to Revision 5: Bernstein 1994 and Bernstein–Lagarias 1996 (the
2-adic conjugacy underlying the realizer correspondence, used throughout and previously uncited in
the visible text); the launch-renormalization and transport-deficit companion notes.
**Retained**: Eliahou, Rozier, Terras, Everett, Garcia–Tal, Curry, Lagarias–Weiss,
Kontorovich–Lagarias, Tao, Steiner, Simons–de Weger, Hercher, Bařina, Lothaire, the two earlier
De Jesús notes, Chang ×2. **Removed**: none. Every entry supports text actually retained.

Bařina's entry now carries both the 2021 and 2025 papers, matching the verification limit quoted.

## Y. Formal verification status

Twelve modules cited in the paper, all present on this branch, all building, with no real `sorry`
or `admit` (the only matches are docstring lines asserting their absence):
`CurryFoundation`, `ChangHistory`, `ChangFullShift`, `ZCRERealizerGrowth`, `RealizerLiftDigit`,
`TerminalZeroGap`, `TransportRegeneration`, `SuperBudgetCancellation`, `ConstraintHeight`,
`GlobalSeparation`, `OrbitLifetime`, `DriftExit`.

The paper states explicitly what is **not** formalized: the Garcia–Tal/Curry input, reciprocal
summability, the proved-sector floors (companion note), and every conjecture.

## Z. Computational claims audit

| claim | Revision 6 status |
|---|---|
| frontier record table | retained, diagnostic |
| identity verifications (Eliahou–Rozier, aggregate, integral corridor, `B_N = 2^{S_N}m_N`) | retained, described as verification of exact statements |
| self-financing margin `+1.83` | retained, explicitly a diagnostic |
| `τ₀ = σ` off cycle minima | retained, diagnostic |
| `U_half` exemption 0/29,999 | retained, explicitly "computation only" |
| **any claim that a normalized stopping/lifetime ratio saturates** | **removed** — a limited scan had suggested a trend that published record tables contradict |
| large scans re-run for bigger samples | not performed |

A methodological remark in the paper records the units hazard: `σ∞` counts even steps (`= S_L`),
`L` counts odd accelerated steps; the two must not be compared without conversion.

## AA. Claim-status audit

The paper carries an explicit convention (Appendix C) and tags substantive statements:
`[Revision 5]`, `[proved]`, `[companion work]`, `[external, cited]`, `[formalized]`,
`[computational diagnostic]`, `[structural interpretation]`, `[reclassification]`,
`[correction to Revision 5]`.

**Newly proved in this paper**: the transfer principle; the integral corridor characterisation; the
divergence equivalence (assembled from two cited ingredients); the automatic-corridor proposition
and its `U_all` corollary; the self-financing inequality; the cardinality barrier; the
finite-cylinder barrier.
**Reclassified, not new**: residue–time duality; the last-maximum reduction; `(DE)` itself; the
future-minimum theorem (a consequence of Revision 5's Lemma 2.2).
**Corrected**: Open Problem E's status; the reading of the corridor-uniform hypothesis.

## AB. Files changed

```
paper/eoc_rev6.tex                            (new)
paper/eoc_rev6.pdf                            (new, build product)
docs/EOC_REVISION6_PROGRAM_MAP_REPORT.md      (new)
```

No Lean module was added or modified: every bridge the paper needed was already formalized on the
preceding branches.

## AC. Build

```
latexmk -pdf -interaction=nonstopmode eoc_rev6.tex    (3 passes)
  → exit 0, 22 pages
  → 0 undefined citations, 0 undefined references
  → 0 overfull boxes
lake build EOC.CurryFoundation EOC.ChangHistory EOC.ChangFullShift EOC.ZCRERealizerGrowth
           EOC.RealizerLiftDigit EOC.TerminalZeroGap EOC.TransportRegeneration
           EOC.SuperBudgetCancellation EOC.ConstraintHeight EOC.GlobalSeparation
           EOC.OrbitLifetime EOC.DriftExit
  → Build completed successfully (2272 jobs)
```

### AC.1 Verification details

`git diff --check`: clean. Real `sorry`/`admit` scan across all twelve cited modules (excluding
docstring lines that assert their absence): **none**. The LaTeX build required three passes for
the hand-rolled `thebibliography`; the first pass also surfaced a missing `xcolor` dependency for
the `hyperref` link colours, now declared.

Paper statistics: 22 pages, 1,300 source lines, 13 sections plus 3 appendices, 22 bibliography
entries, 5 tables, 1 figure.

## AD. Commits

*(filled at commit time)*

## AE. Push status

*(filled at push time)*

## AF. Final Revision-6 thesis

EOC is best viewed as a programme with an exact residue–time duality and a strictly stronger global
occupation layer. The residue axis is solved for finite realizability and several fixed-anchor
sectors and remains open at the arbitrary-word frontier. The time axis separates into a qualitative
drift-exit problem — equivalent, under the current divergence theory, to excluding divergent orbits,
and strictly weaker than Collatz because it tolerates cycles — and quantitative lifetime bounds that
invert directly to realizer floors on a graded scale. Garcia–Tal/Curry supplies strong unconditional
divergence-side sparsity and the last-maximum reduction, but not drift exit. Later structural audits
show that finite cylinders, invertible realizer coordinates, transport budgets and even strong
global valuation-word shadows cannot supply the missing positive-orbit information by themselves.
Launch renormalization validly reaches actual positive-orbit dynamics, but its original
corridor-uniform closure is essentially an `O(log n)` stopping-time conjecture, while deep negative
drift is self-financing with respect to recovery valuations. Full EOC additionally requires control
of separated returns. The surviving frontier is therefore actual positive-orbit arithmetic:
qualitative exclusion of an infinite zero-corridor tail, quantitative control of single-window
lifetime at any scale, and recurrence control sufficient for total occupation.
