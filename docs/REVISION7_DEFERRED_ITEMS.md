# Deferred items for Revision 7

Revision 6 is frozen (`eoc-program-map-revision6`, Zenodo
[10.5281/zenodo.22903860](https://doi.org/10.5281/zenodo.22903860)). The following are
corrections or additions identified after the freeze. None invalidates Revision 6; each would
improve it.

## 1. The ZCRE counterpoint to the cardinality barrier — §9.3

Revision 6 §9.3 states the barrier correctly but does not delimit it. One sentence would, and its
absence is what allowed an overbroad reading to propagate into three other files (corrected on
`closed-route-scope-audit`, see `docs/CLOSED_ROUTE_SCOPE_AUDIT.md`).

**Proposed addition** after Remark 9.4 (*What this does and does not establish*):

> The barrier is sharply delimited, and it is worth saying how. Since `leastRealizer` is a function
> of the valuation word alone, *bounded prefix realizers* is itself a global word-level property,
> and it characterizes positive realization exactly. It escapes Theorem 9.3 because it is not
> shared by the family: it holds for the countably many realizable members and fails for the rest.
> So the barrier does not say that word-level information is insufficient in principle; it says
> that the *divergent-orbit shadows* — the properties a hypothetical Type-II orbit's word is known
> to have — are too coarse, while the one word-level invariant sharp enough to decide the question
> is a restatement of realization rather than an independent handle.

**Status:** correction of scope, not of mathematics. Revision 6's own wording is already safe.

## 2. Two closed-route labels are stronger than their support — §11

From `docs/CLOSED_ROUTE_SCOPE_AUDIT.md`:

- **Row 1 (fixed-modulus terminality at 8/9).** The 8/9 bound is a theorem; *terminality at every
  other fixed modulus* rests on a structural argument plus a finite scan that the paper itself
  calls "consistent with, though not proving, this". The table row should read as
  *tested unsuccessfully*, not *proved*.
- **Row 10 (external `p`-adic arithmetic).** "Wrong complexity scale" compresses an applicability
  audit whose own scope note records that a systematic 2010–2026 literature sweep was not
  performed. Suggested wording: *no applicable uniform bound found; dimension grows with `N`*.

## 3. Transport row understates a positive result — §11

Row 9 lists the transport survival budget purely as a closure. The `O(log n₀)` bound on cumulative
excess regeneration along a genuine orbit is a *theorem* that came out of that route, and is worth
naming rather than filing under closed routes.

## 4. Open Problem F (separated returns) can now be stated quantitatively — §12

Revision 6's Open Problem F reads "Control the number of separated confined episodes… full EOC
requires both episode length and episode count." That is correct as written, and Revision 6 needs
no correction. But the qualitative phrasing leaves open a reading — a *uniformly bounded* episode
count — that is now **provably false**, and the problem can be sharpened accordingly.

From `docs/SEPARATED_RETURNS_CORRECTION_AUDIT.md`:

- the number of episodes is **not** uniformly bounded: for every `c` and every `B` there is an odd
  seed whose genuine orbit has more than `B` corridor episodes (formalized,
  `EOC/SeparatedReturns.lean`);
- episode counts `Ω(log m_0)` are *realized* — there are seeds with `B` episodes and
  `m_0 < 2^{6B+2e_0+3}` — so the target is `P_c(m_0) = O(\log m_0)`, not `O(1)`;
- at a re-entry the local threshold is pinned: `d_{a-1} = 1` and `0 ≤ c − R_a < α − 1`. This is a
  small, clean structural fact that Revision 6 does not state anywhere and that belongs near
  Remark `rem:LvsO`;
- episode count alone would still not suffice, because the per-episode single-window accounting is
  provably lossy by a factor `Ω(\log m_0)` on the prefix of an explicit family. The needed estimate
  is joint.

**Proposed for Revision 7:** restate Open Problem F as a bound `P_c(m) = O(\log m)` together with an
aggregate length estimate, and add the entry lemma as a numbered remark. **Status:** sharpening,
not correction.

## 5. §7.1 — (U) implies EOC outright

Revision 6 treats the corridor-uniform hypothesis (U) as controlling single-window lifetime. It in
fact implies full Existence EOC: occupation ends at arrival at `1`, so a total-stopping-time bound
bounds occupation --- `occupation_le_of_reaches_one` for `m_0 \ge 2^c`, and
`occupation_le_of_reaches_one_general` for every seed, the post-arrival tail contributing at most
`3 \cdot 2^c`. Worth one sentence, with two caveats: this is a relocation rather than a reduction,
since (U) implies Collatz; and the step from (U) to the stopping-time bound is imported from the
lifetime audit and is *not* formalized, so the chain is a proved bridge on an unformalized layer.

## 6. Proposition `prop:lastmax` — the status label over-claims

Revision 6's Proposition `prop:lastmax` (the restart at the last global drift maximum) carries
`\status{companion work; already formalized in the repository}`. At the time of the freeze what was
formalized was `CurryFoundation.zero_corridor_tail`, the corridor inequality in **shifted-index form
on the original seed's word**. The seed-level statement the divergence equivalence actually
consumes --- *there is an actual positive odd integer `m*` with `R_k(m^*) < 0` for all `k \ge 1`* ---
was **not** formalized.

It is now: `EOC/ZeroConfinedSeed.lean` (`exists_neg_drift_seed`, `exists_zero_confined_seed`,
`exists_zero_corridor_seed`, `exists_zero_confined_seed_tendsto`), assembled on branch
`divergence-exclusion-survey` from `Periodic.orbit_add`, `SeparatedReturns.sum_concat`,
`Confinement.odd_orbit` and `CurryFoundation.exists_last_atBot_max`.

**Proposed for Revision 7:** keep the label but make it accurate, e.g.
`\status{companion work; formalized (EOC/ZeroConfinedSeed.lean)}`. **Status:** label correction; the
mathematics of Revision 6 is unaffected.

## 7. Two repository defects found while checking that chain

Both are recorded in `docs/DIVERGENCE_EXCLUSION_SURVEY.md` and fixed or corrected on
`divergence-exclusion-survey`; neither affects the manuscript.

- `EOC/BoundedDrift.lean` carried a banner "NOT COMPILED IN THE AUDIT ENVIRONMENT". It compiles, and
  its three main theorems audit to standard axioms. Banner corrected.
- `EOC/CurryDivergenceProfile.deficit_tendsto_atTop` has a docstring claiming to combine
  `\Delta_k \ge 0` with `\Delta_k \to \infty` "past the last global drift maximum", but is proved by
  `refine \<0, ?_\>` --- at `n_0 = 0`, where the companion `deficit_nonneg` need not hold. The
  statement is true (bare `\exists`) but is not that combination. The two are now available at the
  same seed via `exists_zero_confined_seed_tendsto`. The docstring should be corrected in place.

## 8. Curry's input: cite the audited version, and separate the two roles

Revision 6 cites Curry's note. An independent audit from the source text is now on file
(`docs/CURRY_INDEPENDENT_AUDIT.md`; PDF archived at `docs/sources/Curry_WindowedSparsity.pdf`,
sha256 `67daa37d...`, dated 24 August 2026). The proof is correct; two local defects were found and
repaired in the audit (a typo in Thm 2.3's light case, and a missing integrality/ceiling step in
Thm 4.2). Neither affects Proposition 3.1.

**Proposed for Revision 7.**

- Cite the version and date explicitly, and record that the note is unrefereed as far as anything in
  it or in this repository shows --- the repository's own provenance note already says so.
- Keep Curry's two roles apart in the text: Proposition 3.1 (reciprocal summability) is the *only*
  input the divergence-to-zero-confined-seed reduction consumes; Theorem 4.1 / Corollary 4.3 (the
  logarithmic-floor exclusion, reaching `B < 1/\beta^* = 1.0358567`) sit beside the chain and sharpen
  what a divergent orbit must look like, superseding the manuscript's 8/9 threshold for that purpose.
- Note that `\beta^* < 1` is the load-bearing numerical fact.

**Status:** citation precision and role separation; no mathematics of Revision 6 changes.

## 9. Do not assert a drift rate for divergent orbits

Any wording suggesting a divergent orbit has linear (or any specific) negative drift should be
avoided. What is established is `R_n \to -\infty`, together with Curry's *limsup* bound
`limsup g_n / \log_2 n \ge 1/\beta^*`. Logarithmic, sublinear and linear regimes are all open ---
see `docs/DIVERGENCE_SURVEY_SCOPE_NOTE.md` A. **Status:** scope wording.

## 10. The Curry dependency is now one theorem, and it is named

After `EOC/PowerSavingSummable.lean`, the divergence-to-zero-confined-seed chain depends on exactly
one unformalized external statement: **Curry's Theorem 2.3** (windowed sparsity), interfaced as
`CurryInterface.WindowedSparsity`. Proposition 3.1 is no longer a separate input --- it is derived
from Theorem 2.3 inside Lean by the dyadic summation.

**Proposed for Revision 7:** where the manuscript cites Curry for reciprocal summability, cite
Theorem 2.3 as the input and note that the passage to summability is formalized. **Status:**
dependency precision; no mathematics changes. This strengthens verification and is **not** a new
exclusion mechanism.
