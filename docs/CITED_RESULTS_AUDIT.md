# Audit of the cited results carrying essential implications

*Revision 7 presents a number of results as proved and attributes them to Revision 5 or to
companion notes. This audit checks those attributions against the sources. Branch
`rev7-cited-results-audit`, base `c24053e`.*

## 0. Sources, located and hashed

| Cited as | File | sha256 | Pages |
|---|---|---|---|
| Revision 5 | `docs/sources/EOC_Revision5.pdf` | `73adc35e628b5fbc…` | 25 |
| \cite{DJperiodic} | `docs/sources/DJ_PeriodicRealizerFloors.pdf` | `f0ed3dd663c98611…` | 12 |
| \cite{DJlaunch} | `docs/sources/DJ_LaunchRenormalization.pdf` | `5e9048db7d1f7b95…` | 20 |
| \cite{Curry} | `docs/sources/Curry_WindowedSparsity.pdf` | `67daa37d9b1b1b3e…` | 5 |

Curry's note was audited separately and in full (`docs/CURRY_INDEPENDENT_AUDIT.md`): correct, with
two local repairable defects.

---

## 1. Revision 5 attributions: **7 of 8 faithful, 1 altered**

| Rev 7 label | Rev 5 item | Verdict |
|---|---|---|
| `prop:inversion` | Prop. 5.6 | **Faithful**, numbering correct |
| `prop:window` | Prop. 5.7 | **Faithful**, numbering correct |
| `thm:reduction` | Thm. 3.6 | **Faithful**, all four parts word for word |
| `cor:explicit` | Cor. 3.9 | **Faithful on the claim**; the wrong witness *originates in Revision 5* |
| `thm:89` | Thm. 4.5 | **Faithful**, character for character |
| `lem:wedge` | Lem. 2.3 | **Faithful**, including the "in particular" clause |
| `lem:cycledrift` | Lem. 4.2 | **Faithful**; Rev 7 promotes one sentence from the proof body to the statement, and discloses it |
| `thm:band` | Thm. A.1 | **ALTERED** — see §2 |

### Independently re-verified here, not merely matched

* **`prop:inversion`** — the minimum over `c`-confined words of the least realizer equals the direct
  seed search, for `N = 1…12` and `c = 0,1`: **24/24 agree**.
* **`prop:window`** — both directions re-derived from `prop:inversion`, and the `m₀ ≥ 3` side
  condition shown **necessary**: at `m₀ = 1`, `L_c(1) = 0, 2, 4` for `c = 0,1,2` against
  `ε⁻¹log₂1 = 0`.
* **`cor:explicit`** — `m*(13,100,1) = 90` confirmed *least* (89 fails). The witness "longest:
  m = 27, 41 steps" is wrong, and the previous round of this audit had already corrected it to
  `m = 73` at 42 steps. **New information: the error originates in Revision 5**, so Revision 7 is not
  the source of it — which the status label now records.

---

## 2. `thm:band` was a paraphrase labelled a retention

Revision 5, Theorem A.1 (verbatim):

> Let `θ = α − 1`. If a word's drift path satisfies `β ≤ R_j < β + 1` for all `j ≤ ℓ` and some
> `β ∈ ℝ`, then every letter is in `{1, 2}`, and (writing `b_i = d_i − 1`) the word is a length-`ℓ`
> factor of the Sturmian system of slope `θ`; conversely every such factor arises, and there are
> exactly `ℓ + 1` admissible words for each `ℓ`.

Revision 7 rendered this as "the valuation letters … are determined up to the Beatty structure of
`θ`: the admissible letters are confined to `{1,2}` and their placement follows the Beatty gap
sequence of **`α`**", with `\status{Revision 5, retained}`. Four defects:

1. **The slope is wrong at the point of use.** It is `θ`, not `α`. Verified directly: with
   `d_i ∈ {1,2}` and `b_i = d_i − 1`,
   `R_j = Σ(b_i+1) − jα = Σb_i − j(α−1) = Σb_i − jθ`,
   so the band condition is the Beatty condition **at slope `θ`**, on the binary word `b`. Checked
   on 2000 random `{1,2}`-words: 0 failures. Revision 5 is consistent; Revision 7's "of `α`" is
   wrong.
2. **The substitution `b_i = d_i − 1` is dropped** — and it is exactly what converts the letters into
   the slope-`θ` alphabet, i.e. the step that makes the slope come out as `θ`.
3. **The converse is dropped** ("conversely every such factor arises").
4. **The exact count is dropped** ("exactly `ℓ + 1` admissible words"), and the quantifier is
   loosened from "for all `j ≤ ℓ` and some `β ∈ ℝ`" to "for all `j` in a window".

All four move toward vagueness rather than overclaim — but the label "retained" was inaccurate: this
was a paraphrase. **Fixed**: Revision 5's statement is restored verbatim, with a remark recording
the algebra and the correction.

Note the irony worth recording: the dropped clauses (factor characterisation, count `ℓ+1`) are
precisely the ones Revision 5 leans on an external reference for (Morse–Hedlund, via Lothaire).

---

## 3. Provenance precision: three cited items are *sketches* in Revision 5

Revision 7's `\status{Revision 5}` reads as "proved there". For three items it is not quite that:

| Item | Revision 5 status | Consequence |
|---|---|---|
| `prop:window` (Prop. 5.7) | **proof sketch** — complete in substance | Both directions re-derived here, so nothing rests on the label |
| `lem:carrybudget` (Lem. 4.3) | **proof sketch** | **`thm:89` rests on it**, so the `8/9` exclusion inherits a sketched lemma |
| `thm:band` (Thm. A.1) | **proof sketch**, key step cited to Morse–Hedlund | Not load-bearing for the main chain |

The labels now disclose this. The one that matters is `lem:carrybudget`: `thm:89` is fully proved in
Revision 5 *given* it, and `thm:89` feeds `cor:injocc`, which `thm:reduction`(i) uses. I re-derived
the `E_N ≤ (1/9)log₂N` bound independently in the previous audit round and it is correct, so the
mathematics holds; but the chain's formal provenance passes through a sketch, and Revision 7 should
say so rather than imply a full proof.

**None of the eight Revision 5 items defers to a companion note.** Revision 5's own companion-note
deferrals (Thm. 5.8, Thm. 5.9 → `\cite{DJperiodic}`) are correctly carried across as such in
Revision 7.

---

## 4. Companion notes: 4 of 5 faithful, **1 citation-integrity failure**

| Rev 7 item | Source | Verdict |
|---|---|---|
| `thm:periodic` | \cite{DJperiodic} Thm. 6.2 | **Faithful**, proved unconditionally |
| `thm:evperiodic` | \cite{DJperiodic} Thm. 9.1 | **Faithful in substance**; two hypotheses were dropped |
| `prop:bulkdefect` | *nowhere in \cite{DJperiodic}* | **NOT IN THE CITED SOURCE** — see below |
| `thm:launch` | \cite{DJlaunch} Thm. 5.4 | **Faithful**, essentially word for word, proved unconditionally |
| the four `ε`-dangerous bounds | \cite{DJlaunch} Prop. 6.3 | **Numerically faithful**; one hypothesis dropped |

### 4.1 `prop:bulkdefect` was listed under "Proved sectors" and is not proved anywhere

Verified by reading the source directly. `DJ_PeriodicRealizerFloors.pdf` contains **no** statement
about defect words `X^a E X^b`. Its epistemic ledger (§15, p. 10) reads:

> Finite-defect words | **Open, major** | natural next step

and §16 (p. 11), of exactly this class:

> "The natural next frontier is a periodic background with finitely many defects… The open
> question is whether such defects preserve a single fixed anchor, force a transition between
> finitely many fixed anchors, or destroy the fixed-anchor property altogether… **This note does
> not attempt to resolve this question.**"

The same page warns: *"this note does not establish `r(D) ≥ 2^{S(D)−O(1)}` for arbitrary confined
words, and **no such claim should be inferred from the results proved here**."*

The actual origin is **Revision 5, Prop. 5.10**, which states it with a one-paragraph mechanism and
**no proof** — and carries the qualifier *"for `a` sufficiently large"* that Revision 7 had dropped.

**Not a contradiction, but not proved either.** 5.10's content concerns the coarse anchor at depth
`aS_X`, fixed by the `X^a` prefix alone, and its floor is exponential in `a` only, not in `|D|`. So
it is *weaker* than what the note calls open. Weaker-and-unproved is still unproved.

**Fixed**: the statement is retained as a recorded Revision 5 claim, relabelled "stated, not
proved", the dropped qualifier restored, and the subsection renamed. `thm:periodic` and
`thm:evperiodic` are unaffected — both are proved unconditionally in the note.

### 4.2 Hypotheses dropped from `thm:evperiodic` and the `ε`-dangerous bounds

* `thm:evperiodic` lost the largeness condition (`S_Y + nS_X ≥ P_{X,Y} + B_{X,Y}`) and the fact
  that "the same exceptional case" is **not literally the same**: `ξ_X ≠ 0` holds for every block,
  whereas `ξ_{X,Y} ≠ 0` is proved only for `b_X > 1`, with `b_X = 1` checked case by case.
* The **launch-size bound** holds in \cite{DJlaunch} Prop. 6.3(d) only *"if the orbit segment
  `r(D_N) = m_0,…,m_{t_1}` is injective"*. Revision 7 stated it flatly.

That hypothesis is the material one, because the note is explicit that it cannot be discharged.
Remark 8.3 (p. 10), verbatim:

> "An earlier draft of this note claimed that existing cycle exclusions render a hypothetical
> nontrivial-cycle tail 'incompatible with danger at any fixed ε once N is large.' **That claim was
> incorrect**, with the asymptotics running in the wrong direction, and **is retracted**. … the
> cycle branch is closed unconditionally (and sharply, by Theorem 8.2) for the trivial cycle, and
> **open for hypothetical nontrivial cycles at large N**. **Rather than assume nonexistence
> silently**, the conditional theorem of §11 carries the hypothesis explicitly."

Revision 7 did exactly what the note declines to do. **Fixed**: the hypothesis is restored, along
with `r(D) ≥ 3` in the definition of `ε`-dangerous, and the renormalization-stability sentence now
inherits `N > N_c`, the period cap `q₀`, and `ε < (2−α)/(2+α) ≈ 0.1158`.

**Neither note contains an unproved assumption that damages `thm:periodic`, `thm:evperiodic` or
`thm:launch`** — all three are proved outright in their sources, and \cite{DJlaunch} states plainly
that its own closing hypotheses `U_all`/`U_half` "remain unproved", which Revision 7 already
reflects.

`thm:rozier` (Rozier's LBH ⟹ `conj:sharp`) is cited to an external paper not held locally, and is
not load-bearing — it positions EOC rather than supporting it. It remains cited-not-verified.

`thm:rozier` (Rozier's LBH ⟹ `conj:sharp`) is cited to an external paper not held locally, and is
not load-bearing for the main chain — it positions EOC rather than supporting it.

---

## 5. Closing assessment, corrected

An earlier summary of this work said *"not one was an error in the underlying mathematics."* That
is too flattering and is withdrawn. The evidence supports something narrower and more useful:

> **Several checked source results remain sound, while transcription errors, unsupported claims,
> and incorrect statements entered the manuscript.**

Three distinctions the earlier phrasing blurred:

* **Some failures were mathematical errors in the statements as written**, not mistranscriptions.
  `prop:futuremin` ("if `R_n ≤ 0` then `m_n > m_0`") is *false* at `n = 0`. `cor:explicit`'s
  witness was a *false* numerical claim. `thm:band` named the *wrong slope*. These are wrong
  statements, whatever their provenance.
* **An unproved proposition is not thereby false — its correctness is unsettled.**
  `prop:bulkdefect` has no proof on file anywhere; that makes it an open claim, not a refuted one,
  and the paper now says exactly that.
* **What the audits do support** is that the *checked source results* — Curry's Thm 2.3 and
  Prop 3.1, \cite{DJperiodic} Thms 6.2 and 9.1, \cite{DJlaunch} Thm 5.4, and the Revision 5 items
  re-derived here — are sound as stated in their sources.

## 6. Final dependency check

Run after the corrections, to confirm no argument still relies on a withdrawn status:

| Check | Result |
|---|---|
| Is `prop:bulkdefect` used as an input anywhere? | **No.** Its only cross-reference is its own correction remark |
| Does the programme map still list it under "strongest proved"? | **No.** Moved to the open-target column, pointing at §\ref{sec:bulkdefect} |
| Does "Proved sectors" still contain it? | **No.** That subsection now contains exactly `thm:periodic` and `thm:evperiodic`, both proved unconditionally in the source |
| Is the launch-size bound used anywhere without injectivity? | **No.** It appears only in its own passage, immediately followed by `rem:launchhyp` stating the hypothesis |
| Does any downstream argument cite `thm:launch` or the dangerous-word bounds? | **No** — 0 references; that material is self-contained |
| Is the carry-budget proof reachable? | **Yes** — Appendix `app:carrybudget`, referenced from `lem:carrybudget` |

## 7. Presentation changes made

* **`prop:bulkdefect` moved out of the proved sectors** into its own subsection,
  "The finite-defect sector: an unproved claim inherited from Revision 5", which opens by saying
  nothing in the paper depends on it and that it is retained only because Revision 5 recorded it.
  It is not omitted because a reader of Revision 5 will look for it.
* **The carry-budget bound now has a complete proof** (Appendix `app:carrybudget`), with every step
  elementary and the constant explicit: `E_N ≤ (1/9)log₂(3N−5) + 2/(3ln2) ≤ (1/9)log₂N + 1.138`.
  The one step Revision 5 left implicit — that the `j`-th integer coprime to 6 is at least `3j−2` —
  is proved by the residue count, using that `3j−3 ≡ 0` or `3 (mod 6)` so the awkward cases do not
  arise. Sharpness is flagged as a computational observation, not folded into the theorem.
* **`thm:rozier` remains marked unaudited**: its source is not held locally and it is not
  load-bearing.
