# Revision 7: release review

*Bounded finalization pass. Branch `rev7-finalization`, base `43c10b0` (verified as the latest
correction tip, not assumed). Revision 6, `main` and the ordinary checkout untouched.*

## Provenance at the start of this pass

| | |
|---|---|
| Start commit | `43c10b057b5e96611be57d2628772afd65081ece` |
| Tracked PDF sha256 | `2f183d0c1cfaf9c100def9a53b1ef932ac6167d75cdbf5ce32f28bc7d9ede3fd` |
| Pages | 30 |
| Source correspondence | Rebuilt clean from the tracked `.tex`: **text layer identical**, byte differences confined to timestamp/ID |

## Corrections made in this pass

**Carry-budget appendix.** Verified line by line. `N ≥ 2` is required (at `N = 1`, `3N−5 < 0`) and
the two remaining cases are now handled explicitly: `E_0 = 0`, `E_1 ≤ log₂(4/3) < 0.416`. The
sharpness remark said the sequence "increases to 0.9728…, with maximum 1 at M=1", which is
self-contradictory; it now records that `A_M − ⅓ln M` equals 1 at `M=1`, **drops** to 0.9690 at
`M=2`, and increases from there — with no monotonicity theorem invented, and the whole remark
marked as a finite computation used nowhere.

**`prop:occstop` — a vacuous display removed.** The general form
`Occ_c ≤ T + #{n ≥ T : m_n ≥ m₀2^{−c}}` is true but **useless**: if any cycle value meets the
threshold the cycle repeats it forever, so the counting term is *infinite*, while actual occupation
is finite (corridor membership is a condition on `R_n`, which gains a fixed amount per period).
Restated as the two usable cases. **And the display was still being re-used one page later in
`rem:Uallscope`(i), cited to the proposition it had been removed from** — that passage is rewritten.

**Separated returns.** The surrogate total is now *defined*:
`Q := Σᵢ (1 + K(log₂m_{aᵢ} + cᵢ))`, with `Q ≥ P(log₂m₀ − c)` derived. The ratio bound uses only
proved estimates, names `e₀` explicitly rather than `O_c(1)`, and states that the `B`s cancel.
`prop:episodes` now carries the prefix-occupation conclusion `≤ e₀ + 2B` that its Lean counterpart
always had. Enlarging a seed *within its residue class* is distinguished from growth of the *least*
realizer. The obstruction is scoped to the single-window charge displayed, not to per-episode
methods generally.

**Cycles and (U).** Fifteen further consistency defects were found by sweeping the front matter and
summary tables against the corrected body, and all were fixed. The recurring one: the abstract,
conclusion and closed-route row 12 still carried the *withdrawn* reading that the corridor-uniform
hypothesis is "an `O(log n)` stopping-time conjecture" — it bounds the **injective initial
segment**, so it yields entry into *a* cycle, not arrival at 1. Also corrected: `cor:cycles` and the
abstract asserted "(DE) alone does not reach Collatz", the non-entailment `rem:strictlyweaker`
explicitly disclaims; §3.4 and `op:A` claimed Collatz without the accompanying cycle search; §1
credited Existence EOC with the effective consequence it does not supply; the programme diagram
labelled an arrow "strict"; §9.6's title asserted the withdrawn universal claim; the hierarchy and
`op:C` dropped `prop:window`'s necessary `m ≥ 3` / `r(D) ≥ 3`; `op:H` excluded word-level criteria
in general; `obs:height` asserted the unproved one-defect case; `prop:transfer`'s *nondecreasing*
hypothesis was missing in four summaries; two §14 status lines over-read; `Occ_c`'s domain was
`c > 0` while `c = 0` is used in substance.

**Bulk-defect.** Remains outside proved results, unused downstream, described as unproved **in the
sources audited**, with the "for `a` sufficiently large" qualifier and its scope preserved.

**Citations.** All five DOIs intact; Bařina correctly split as [13] (2021) / [14] (2025); the
`2^71` claim routes to [14]. No deposit DOI is invented for Revision 7 anywhere.

## Verification performed

* Latest tip verified by `git fetch` before branching; `43c10b0` confirmed as most recent.
* Tracked PDF confirmed to correspond to the tracked source.
* **Formal side unchanged this pass** (only `paper/` differs), so the build evidence carries over —
  and it was re-run on this tree: full default `lake build` clean; all 16 modules named in §14
  reachable from the library root; `#print axioms` on a sample spanning every new module returns
  only `propext, Classical.choice, Quot.sound`.
* LaTeX: no undefined references, no undefined citations, three overfull boxes all under 2.6pt and
  all inherited from Revision 6.
* **Visual inspection, not just exit code**: every page measured (rightmost text `544.7pt` against a
  540pt block and a 612pt page — nothing within 52pt of any edge); the programme diagram, hierarchy
  table, verification table and appendix rendered and read as images.

## Remaining limitations

**Mathematical open problems.** Universal drift exit `(DE)`; whether `(DE)` implies cycle-freeness
(no implication is established in either direction); EOC at every tier; `prop:bulkdefect`, unproved
in the sources audited; strictness of Level 4 over Level 3 at a fixed corridor; a bound on
`Σᵢ ℓᵢ` not factoring through per-episode single-window estimates.

**Unaudited dependencies.** Curry's Theorem 2.3 — audited on paper, **not formalized**, and the one
external input the divergence chain consumes. `thm:rozier` (Rozier's LBH) — source not held
locally, marked unaudited; not load-bearing. The analytic absorption inside `cor:Uall` — proved on
paper, not formalized. `thm:cardinality` items (b), (c), (d) — proved on paper, not formalized.
