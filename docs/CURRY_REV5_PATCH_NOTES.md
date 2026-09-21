# Recommended manuscript changes: EOC Revision 5 vs. the audited Curry chain

*Recommendations only. The manuscript PDF/source is not edited by this document or by this
branch. Each item is CURRENT / ISSUE / PROPOSED / STATUS.*

Scope reviewed: manuscript §4.2 (Theorem 4.8–4.11, Remarks 4.12–4.13), the surrounding
occupation/floor-exclusion material, and every place the manuscript's abstract or introduction
summarizes what Curry gives it. Compared against `docs/CURRY_FOUNDATION.md` and
`EOC/CurryFoundation.lean`.

---

### Patch 1 — Theorem 4.8 (window sparsity), attribution and status

```
CURRENT:
"Theorem 4.8 (Garcia–Tal [5]; explicit form, Curry [6])." Stated, not reproduced ("We do not
reproduce Curry's proof...").
ISSUE:
None. This is accurate and appropriately scoped — already marked "external theorem, not
formalized" in the repository's own provenance audit (`docs/NOVELTY_AND_PROVENANCE.md` row 12).
The independent audit in this branch corroborates the theorem's correctness but changes nothing
about how it should be cited.
PROPOSED:
Optionally add a footnote or citation to the fact that this theorem has now been independently
audited by this project (not merely cited), pointing to `docs/CURRY_FOUNDATION.md` §8.1, with
the same "audited, not peer-reviewed, not community-accepted" caveat repeated verbatim.
STATUS: OPTIONAL — strengthens confidence disclosure, changes no mathematical content.
```

### Patch 2 — Proposition 4.9 (reciprocal summability), understated uniformity

```
CURRENT:
States "∑ x∈O 1/x < ∞" per orbit; the carry-budget remark says "EN is bounded along every
divergent orbit, rather than of size (1/9) log2 N".
ISSUE:
UNDERSTATED. Tracing Curry's own proof (not just his stated Proposition 3.1) shows the bound is
uniform across every divergent orbit of every seed: a single constant K(β), depending only on
β, with ∑ 1/m_n ≤ K(β) for all such orbits simultaneously — not merely "finite, orbit by
orbit." See `docs/CURRY_FOUNDATION.md` §8.3.
PROPOSED:
Add a remark after Proposition 4.9 noting the stronger, uniform form, with the one-line
derivation (sum the *raw*, orbit-blind form of Theorem 4.8 over dyadic blocks; the bound never
mentions O). Optional — does not change any later theorem, since only finiteness (not the
specific constant) is used downstream.
STATUS: RECOMMENDED, low priority.
```

### Patch 3 — Theorem 4.11 (occupation bound), constant-dependency wording

```
CURRENT:
"There are constants c1, c2, depending on β and on the orbit through m0, Q∞."
ISSUE:
None — this is exactly correct, and is a place where Rev. 5 already gets the universal-vs-
orbit-dependent distinction right (§E of the Curry Verification Audit found no misuse anywhere
in the manuscript). No change needed. Recorded here only so the patch-note review is visibly
complete on this point, per the governing instruction not to silently skip sections.
PROPOSED:
None.
STATUS: NO CHANGE — confirmed correct as written.
```

### Patch 4 — missing chain: `R_n → -∞`, `Σ 2^{R_n} < ∞`, zero-corridor, deficit

```
CURRENT:
§4.2 stops at Theorem 4.11 / Corollary (the B < 1/β* floor exclusion) and Remark 4.13's scope
note. Nothing in the current manuscript states R_n → -∞ explicitly, the summability of 2^{R_n},
the last-global-maximum reduction, or the zero-corridor/deficit theorems.
ISSUE:
GAP (omission, not an error). These are short, fully checked consequences of what §4.2 already
establishes (Level B/C in `docs/CURRY_FOUNDATION.md`), now formalized unconditionally in
`EOC/CurryFoundation.lean` behind the single external hypothesis `ReciprocalSummable`. They are
not currently in the manuscript at all.
PROPOSED:
Add a new subsection (e.g. §4.3, "The zero-corridor tail") stating, with the Level B/C labeling
preserved:
  (i)   R_n → -∞ (CURRY + ELEMENTARY CONSEQUENCE);
  (ii)  Σ 2^{R_n} < ∞;
  (iii) existence of a last global drift maximum n0 (generic real-sequence fact);
  (iv)  the Zero-Corridor Tail Theorem, S'_k ≤ ⌊kα⌋ for k ≥ 1 — noting explicitly that this
        step needs only the floor's definition, not irrationality of α (a correction to how an
        earlier informal draft of this audit phrased it — see `docs/CURRY_FOUNDATION.md` §8.5);
  (v)   the deficit Δ_k = ⌊kα⌋ - S'_k → ∞ and its recurrence Δ_{k+1} = Δ_k + b_{k+1} - d_k.
Then state the precise necessary-condition corollary (§8.7 of `docs/CURRY_FOUNDATION.md`) and
the explicit non-claims list (§8.8), matching Remark 4.13's existing discipline.
STATUS: RECOMMENDED — the most substantive addition in this patch set. Not applied to the
manuscript by this branch; drafted content is available verbatim in `docs/CURRY_FOUNDATION.md`
§8.4–§8.7 for the author to adapt.
```

### Patch 5 — "unconditional" / "strongest unconditional result" language

```
CURRENT:
Searched for "unconditional" near Curry-dependent material (Theorem 4.10, 4.11, Remark 4.12).
Theorem 4.10/4.11's own statements are correctly NOT labeled "unconditional" — they are
downstream of an external, audited-but-unformalized theorem, and the manuscript's Lean
companion (`EOC/LogCorridor.lean`) correctly gates them behind the explicit hypothesis
`LogFloorExclusion`, never claiming them as proved internally.
ISSUE:
None found. The word "unconditional" is reserved in the manuscript for genuinely
Lean-proved, external-theorem-free results (e.g. the 8/9 harmonic-packing bound, Theorem 4.5),
and that reservation is honored around the Curry material.
PROPOSED:
None.
STATUS: NO CHANGE — confirmed correct as written.
```

### Patch 6 — Rozier `r_H` provenance and the `γ* = r_H` identification

```
CURRENT:
"The exponent β* = γ* log2 3 coincides with Rozier's critical ones-ratio rH [2]" (§4.2, echoing
Curry's own Remark 2.4).
ISSUE:
None. Independently re-verified in this audit: rH and γ* solve the identical entropy-crossing
equation H(γ) = γλ (not merely the same decimal value), confirmed both numerically (50-digit
precision) and by inspecting Rozier's Theorem 2.6 regime split as recorded in the repository's
own `docs/LITERATURE_CONTEXT.md`.
PROPOSED:
None.
STATUS: NO CHANGE — confirmed correct as written.
```

### Patch 7 — Curry attribution vs. Garcia–Tal (repeat check)

```
CURRENT:
§4.2 opening paragraph attributes Banach-density-zero (qualitative) to Garcia–Tal 1999 and the
explicit quantitative form/exponent/threshold to Curry.
ISSUE:
None — already correct, and independently reconfirmed by this audit (`docs/
CURRY_FOUNDATION.md` §G in the original Curry Verification Audit; Curry's own paper is
self-contained and does not depend on trusting Garcia–Tal's proof, only their qualitative
idea, which Curry re-derives from Terras–Everett + elementary pigeonhole).
PROPOSED:
None.
STATUS: NO CHANGE — confirmed correct as written; this is the second independent confirmation
of the same attribution (see `docs/NOVELTY_AND_PROVENANCE.md` §4, "already correct and
carefully separated").
```

---

## Summary

Of seven items reviewed, **one substantive addition is recommended** (Patch 4 — the missing
`R_n → -∞` through zero-corridor/deficit chain, now available and Lean-checked), **one minor
strengthening is optional** (Patch 2 — the uniform reciprocal-summability bound), and **five
are confirmations that the current manuscript text is already accurate** and need no change.
No instance of overstatement was found anywhere in the reviewed material — Revision 5's
existing discipline about what is external, what is orbit-dependent, and what remains open
(Remark 4.13) held up under this independent check.
