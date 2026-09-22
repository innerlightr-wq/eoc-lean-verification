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

## 4. Still open in this audit

The companion notes `\cite{DJperiodic}` (for `thm:periodic`, `thm:evperiodic`, `prop:bulkdefect`)
and `\cite{DJlaunch}` (for `thm:launch` and the four `ε`-dangerous bounds) are **archived and
hashed but not yet audited**. Those results are presented in Revision 7 as proved, and the audit is
in progress; until it reports, they should be treated as cited-not-verified.

`thm:rozier` (Rozier's LBH ⟹ `conj:sharp`) is cited to an external paper not held locally, and is
not load-bearing for the main chain — it positions EOC rather than supporting it.
