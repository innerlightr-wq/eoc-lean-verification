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
- `Θ(log m₀)` episodes actually occur, so the target is `P_c(m₀) = O(log m₀)`, not `O(1)`;
- at a re-entry the local threshold is pinned: `d_{a-1} = 1` and `0 ≤ c − R_a < α − 1`. This is a
  small, clean structural fact that Revision 6 does not state anywhere and that belongs near
  Remark `rem:LvsO`;
- episode count alone would still not suffice, because the per-episode single-window accounting is
  lossy by a factor `Θ(log m₀)` on an explicit family. The needed estimate is joint.

**Proposed for Revision 7:** restate Open Problem F as a bound `P_c(m) = O(\log m)` together with an
aggregate length estimate, and add the entry lemma as a numbered remark. **Status:** sharpening,
not correction.

## 5. §7.1 — (U) implies EOC outright

Revision 6 treats the corridor-uniform hypothesis (U) as controlling single-window lifetime. It in
fact implies full Existence EOC directly: occupation ends at arrival at `1` (for `m_0 \ge 2^c`), so
a total-stopping-time bound bounds occupation (`occupation_le_of_reaches_one`). Worth one sentence,
with the caveat that this is a relocation rather than a reduction, since (U) implies Collatz.
