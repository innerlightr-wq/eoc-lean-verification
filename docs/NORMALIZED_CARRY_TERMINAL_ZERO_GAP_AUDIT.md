# Normalized-carry terminal zero-gap audit

Follow-up to [`docs/REALIZER_LIFT_DIGIT_POSITIVITY_AUDIT.md`](REALIZER_LIFT_DIGIT_POSITIVITY_AUDIT.md),
which identified the positivity coordinate but found no constraint on it.

**Question.** Does the sparse-unit form `Z_N = −Σ_{j<N} 3^{−(j+1)} 2^{S_j}` impose any
*nontautological* restriction on the length of the high-order zero gap, for zero-confined
irregular words?

**Answer: no. Every candidate mechanism closes, and all six of Gate 35's stop conditions hold.**

| mechanism | outcome |
|---|---|
| exact binary carry/borrow propagation | depends on the **complete lower block** — no finite closure (§M, §N) |
| mixed Archimedean / 2-adic approximation | **vacuous**: the error `3^N r_N` exceeds the unit `2^S` even at `r_N = 1` (§Q, §R) |
| irregularity → gap restriction | **none found**: large-gap words retain full symbolic freedom (§S, §T, §U) |

The audit's positive content is that the **correct integer target is now exact and formalized**,
and that one claim from the previous round needed correcting: `E(D)` is *not* an integer zero-run.

---

## A. Starting state

| | |
|---|---|
| branch point | `realizer-lift-digit-positivity-audit` = `bb4f6c907878c005e36f2e0fb0a297e43213fa7b`, **fetched and verified**, not taken from prose |
| new branch | `normalized-carry-zero-gap-audit` |
| worktree | isolated; Mathlib shared by read-only symlink |

Ordinary checkout on `research-sparse-visits-2026-09-16`, 53 dirty files, untouched. `main`
(`1c4d6700`) unmodified.

## B. Source inventory

| | source |
|---|---|
| **CAAP** | `~/Downloads/confinementAbundanceArithmeticPlacement (4).pdf` — *From Confinement Abundance to Arithmetic Placement*, sha256 `391a60d9a2e8…`. The three copies in `~/Downloads` are **byte-identical**. Read: §5–6, §8, App. A–C, and **Remark B.2** and **Open Problem B.1** in full. |
| **PL** | `~/Downloads/peeling_theorem_ledger.md`, sha256 `54a6d958286a793e…` |
| **HC** | `~/Downloads/halfcylinderv2.pdf`, sha256 `9dde423a50e5fbf9…` |
| repo | `EOC/Carry.lean` (`q`, `C`, `q_eq_C`), `EOC/Realizer.lean`, `EOC/ZCRERealizerGrowth.lean`, `EOC/RealizerLiftDigit.lean`, `EOC/ArithmeticFrontier.lean` |
| **P1** | EOC Rev 5 — Prop 5.2, §6 (`E(D)`), §8 Open Problems C/D/E |

### Prior art that must not be rediscovered

CAAP already contains, and this audit does **not** claim:

- nested least realizers and monotonicity `r_min(N+1,c) ≥ r_min(N,c)` (Prop 5.1);
- bounded ⟺ eventually constant;
- **Open Problem B.1, Qualitative Realizer Escape** — `r_N → ∞`, equivalent to `r_{N+1} > r_N`
  infinitely often;
- **the jump `k_N`**, defined by `r_{N+1} = r_N + k_N 2^{S_N+1}`, with the exact criterion
  `k_N = 0 ⟺ v₂(3μ_N+1) = d_{N+1}` where `μ_N = T^N(r_N)` (Remark B.2);
- the stabilization obstruction, counting barriers, and closure-versus-separation tests.

> **Attribution correction owed to the previous round.** `RealizerLiftDigit.liftDigit` is CAAP's
> jump `k_N`. The previous report presented it as a new definition; it is not, and CAAP was not
> available to that round. The new module records the attribution in its header.

CAAP Remark B.2 also states, in advance, the conclusion this audit reaches independently:
*"qualitative realizer escape, carry forcing, fixed-realizer contradiction, and plateau-exhaustion
arguments do not by themselves bypass the irregular-word moving-anchor obstruction: in the
orbit-tracking case they reduce to the original question."* §AE and §AF confirm that for the
carry-gap route specifically.

## C. Existing zero-gap/depth notation

Searched the repository for `E(D)`, `endpointDepth`, `zero run`, `floorLog`, `log2 r`,
`Nat.log`, `Nat.size`, moving anchor, `PowerOfTwoDangerousWindowSparsity`.

**No discrete version of `S − ⌊log₂ r⌋` exists.** `Nat.log 2` is available and already used
(`EOC/ShellDecomposition.lean`). `E(D) = S − log₂ r(D)` appears only in P1 §6 prose, not in Lean.
So `discreteGap` is new and duplicates nothing.

## D. Discrete high-bit gap

```
discreteGap S r  :=  S − Nat.log 2 r
```

For `1 ≤ r < 2^{S+1}` this is the number of zero bits strictly above the top bit of `r` inside the
`(S+1)`-bit window. Formalized with `log_le_of_lt` guaranteeing `⌊log₂ r⌋ ≤ S`, so the truncated
subtraction is honest.

## E. Correction to `E(D)` interpretation

**The previous round overstated this and it is corrected here.**
`docs/REALIZER_LIFT_DIGIT_POSITIVITY_AUDIT.md` §Z said `E(D) = S − log₂ r` "is exactly the terminal
zero-run length". It is not: `E` is real-valued.

With `h = ⌊log₂ r⌋` and `g = S − h`:

```
E = S − log₂ r = g − frac(log₂ r),        so        g − 1 < E ≤ g,   i.e.   g = ⌈E⌉.
```

Equality `E = g` holds only when `log₂ r ∈ ℤ`, i.e. `r = 1` (realizers are odd).

Verified on **4399** zero-confined words (`N = 3…11`): **0 violations** of `g − 1 < E ≤ g` and of
`g = ⌈E⌉`; **0** cases of `E = g` (no `r = 1` in the sample). `g` is the integer variable; `E` is
not.

## F. Carry-side equivalence

From the verified identity `r_N = (Z_N + 2^{S}) mod 2^{S+1}` (previous round §H), in the
small-realizer regime:

```
r_N < 2^S   ⟹   z_N := Z_N mod 2^{S+1} = 2^S + r_N.
```

Verified on **871** small-realizer zero-confined words: **0 mismatches**. Formalized as
`carry_residue_of_small_realizer`.

So a gap of length `g` reads on the carry side as: **bit `S` of `z_N` is set, then `g − 1`
consecutive zero bits, then the top bit of `r_N`.** That is the exact carry-side formulation.

## G. Dangerous-gap event

```
Gap_G(D)  :⟺  G ≤ discreteGap S r(D)  ⟺  r(D) < 2^{S−G+1}
```

Formalized as `discreteGap_ge_iff` (hypotheses `0 < r`, `G ≤ S`, `r < 2^{S+1}`), with no real
logarithms. Also `discreteGap_eq_zero_iff : g = 0 ↔ 2^S ≤ r`.

Relation to `E`: `Gap_G(D) ⟺ g ≥ G ⟺ E > G − 1` (by §E), so "`E ≥ G + O(1)`" is only correct up
to the `<1` rounding term — which §X takes care to keep.

## H. Anti-tautology boundary

`Gap_G(D)` and `r(D) < 2^{S−G+1}` are the **same statement**, by `discreteGap_ge_iff`. Likewise
the carry-side form of §F. **None of these translations is progress**, and this audit does not
count them as such.

A useful theorem must derive the impossibility of a long gap from an *independent* property of the
sparse sum `Σ 3^{−(j+1)} 2^{S_j}`. §I–§T test every available candidate.

## I. Sparse-unit bit dependencies

Each summand is `3^{−(j+1)}·2^{S_j}`: an **odd 2-adic unit** times `2^{S_j}`. An odd unit has bit 0
equal to 1 and generically nonzero bits at every higher position, so term `j` contributes to
**every** bit `b ≥ S_j`.

Computed for `D = (1,2,1,1,2,1,2)`, `S = 10`, each term's residue mod `2^{11}`:

```
j=0  S_j= 0   01010101011
j=1  S_j= 1   10001110010
j=2  S_j= 3   00010011000
j=3  S_j= 4   01100010000
j=4  S_j= 5   11101100000
j=5  S_j= 7   10010000000
j=6  S_j= 8   01100000000
```

Every term with `S_j ≤ b` has support at bit `b`. **There is no locality**: the high frontier
depends on the entire history, not on a bounded suffix. This was not assumed — it is forced by the
units being odd.

## J. Prefix/suffix decomposition

Exact, and formalized as `C_split`:

```
C_{k+n} = 3^n · C_k + 2^{S_k} · C'          (C' the suffix carry)
```

equivalently `Z_N = Z_k + 2^{S_k} U_{k,N}` with `U_{k,N} = −3^{−(k+1)}·V(suffix)`.

The suffix enters only through `2^{S_k}` times its own carry. **But the prefix enters at full final
precision:** to know `C_N mod 2^{S_N+1}` one needs `C_k mod 2^{S_N+1}`, not `C_k mod 2^{S_k+1}`.

That is exactly the frontier-erosion / access-cost phenomenon (PL T6: any auxiliary state enabling
exact reconstruction needs `n − w − O(1)` bits; no sublinear middle regime). The inherited-prefix
precision required is linear in the final depth.

## K. Peeling directionality

PL T3: the visible data is recoverable from `Z_n mod 2^Q` **iff** `Q ≥ S_{n−1}+1`, with silent
truncation below.

> **Lemma (directionality).** Peeling is a decoding of the word *from* low-order 2-adic digits. The
> gap is a property of the high-order digits of `Z_N mod 2^{S_N+1}`. Peeling therefore supplies no
> bound on the gap: given the word, the high bits are *computed*, and given the high bits, peeling
> adds nothing the word did not already determine.

This is the same structural point as the previous round's §N (an encoding cannot restrict what it
encodes), now located precisely: **peeling is perfectly informative in the wrong direction.**

## L. High-bit nonlocality

Measured on the `(N,S) = (13,20)` shell (8045 words):

- fixing an **11-letter prefix** and varying only the last two letters moves `g` by up to **12**
  (out of `S = 20`), across 2652 prefix classes;
- fixing a **4-letter suffix** and varying the prefix moves `g` by up to **12**, across 170 suffix
  classes.

So a late one-letter change alters the gap by `O(S)`, and identical suffix data is compatible with
widely varying gaps. **The high-gap event is neither prefix-local nor suffix-local**, confirming §I
computationally. (§AC, §AD record the two directions separately as the brief asks.)

## M. Borrow propagation

`Z_{N+1} = Z_N − 3^{−(N+1)}2^{S_N}`. The subtrahend is `2^{S_N}` times an odd unit, so it has a `1`
at bit `S_N` and arbitrary bits above. Maintaining a zero run at positions `S_N−G … S_N` across the
subtraction requires a borrow arriving from below with a prescribed parity at every one of those
positions.

The borrow into bit `b` is determined by the **entire block of bits below `b`** of both operands —
and by §I both operands' low blocks depend on the whole history. So the borrow condition is not a
bounded-state condition.

This reproduces, in the present setting, the complete-lower-block dependence HC already found in a
related cross-level problem; it is **not** claimed as new (§N).

## N. Borrow-chain closure

**No finite closure.** The state needed to propagate the zero-gap condition across `G` positions is
the full lower block (§M), whose size grows with `S_N`. Per Gate 10's instruction, no automaton was
forced.

Recorded as: **NO FINITE BORROW CLOSURE**, with attribution to HC for the analogous prior finding.

## O. Modular interval formulation

From `r ≡ 2^S − C_N 3^{−N} (mod 2^{S+1})`, the event `r < 2^{S−G+1}` is

```
C_N · 3^{−N}  mod 2^{S+1}   ∈   ( 2^S − 2^{S−G+1},  2^S − 1 ]
```

— an interval of length `2^{S−G+1}` inside `ℤ/2^{S+1}`, i.e. **relative density `2^{−G}`**.

Note the multiplication by `3^{−N}` is a bijection of `ℤ/2^{S+1}` that does **not** preserve
intervals, so the corresponding set for `C_N` itself is a dilated interval, not an interval. The
clean statement is the one above, for the anchor.

This is precisely arithmetic placement: *does the structured integer `C_N 3^{−N}` avoid a
prescribed interval of density `2^{−G}`?* — i.e. **Open Problem D**. No new content.

## P. Integer/orbit identity formulation

`3^N r_N + C_N = 2^S m_N` with `m_N` odd. A gap `g ≥ G` gives

```
0 < 2^S m_N − C_N = 3^N r_N < 3^N 2^{S−G+1}.
```

So `C_N` sits just below the multiple `2^S m_N`. **But `m_N` is *defined* by this equation**, so the
"approximation" is automatic for every exact realizer — the Gate 13 tautology warning applies, and
this subroute is closed on those grounds alone. §Q adds an independent, quantitative kill.

## Q. Mixed real/2-adic approximation

For a legitimate Diophantine interface the Archimedean side must be **independently** small. It is
not:

| `N` | `S` | `log₂ 3^N` | `log₂ 2^S` | `log₂(3^N r_min)` | nontrivial? |
|---|---|---|---|---|---|
| 6 | 9 | 9.51 | 9.00 | 14.26 | no |
| 9 | 14 | 14.26 | 14.00 | 19.02 | no |
| 12 | 19 | 19.02 | 19.00 | 23.77 | no |
| 15 | 23 | 23.77 | 23.00 | 28.53 | no |

Because `S = ⌊αN⌋ ≤ αN = log₂ 3^N`, we have `3^N ≥ 2^S`, hence

```
error = 3^N r_N ≥ 2^S · r_N ≥ 2^S       for every r_N ≥ 1.
```

**The approximation error always exceeds the unit `2^S` being approximated.** The statement
"`C_N` is close to a multiple of `2^S`" is vacuous — it is satisfied with room to spare by every
word, small realizer or not.

**Verdict for this gate: MIXED REAL/2-ADIC APPROXIMATION IS TAUTOLOGICAL**, on both grounds
(§P's free `m_N`, and the size obstruction here).

## R. Carry-size obstruction

§Q *is* the carry-dominance check. The same obstruction that killed the earlier Pell/continued-
fraction attempts kills this one, and for the same reason: `3^N` and `2^{S}` are the same size to
within `O(1)` under zero confinement, so the carry term has no room to be a small correction.

No Pell or continued-fraction work was reopened.

## S. Irregularity interface

Periodic and eventually periodic confined words already have fixed-anchor realizer floors
(P1 Thm 5.8/5.9), so a new theorem must exploit something separating irregular words. The
repository's available notions are eventual periodicity, first-defect structure, and repeated-block
structure — no new "irregularity score" was invented.

**No mechanism was found linking any of them to the gap.** §T shows why: a long gap does not force
repeated structure.

## T. Long gap versus symbolic rigidity

On the `(N,S) = (14,21)` shell, 17637 words:

| `g ≥` | 1 | 2 | 3 | 4 | max `g` |
|---|---|---|---|---|---|
| count | 8770 | 4399 | 2199 | 1114 | 15 |

The 2199 words with `g ≥ 3` have **188 distinct 4-letter suffixes**. Large-gap words do **not**
collapse onto few suffixes, near-periodic patterns, or a bounded-complexity family.

**A long zero gap does not force symbolic rigidity.** The route from irregularity to a gap
restriction has no visible entry point.

## U. Same-gap fibers

| `N` | `S` | words | `g≥1` | `g≥2` | `g≥3` | `g≥4` | max `g` | distinct 4-suffixes at `g≥3` |
|---|---|---|---|---|---|---|---|---|
| 12 | 18 | 2652 | 1296 | 612 | 311 | 149 | 11 | 97 |
| 13 | 20 | 8045 | 4032 | 2043 | 1013 | 527 | 12 | 167 |
| 14 | 21 | 17637 | 8770 | 4399 | 2199 | 1114 | 15 | 188 |

All comparisons are conditioned on fixed `(N,S)` as §21 of the brief requires — shell mixing would
confound terminal valuation depth with the gap.

## V. Same-shell null comparison

Density of `g ≥ G` against the random-injective prediction `2^{−G}`:

| `N` | `S` | `g≥1` | `g≥2` | `g≥3` | `g≥4` | `g≥5` |
|---|---|---|---|---|---|---|
| 13 | 20 | 0.5012 | 0.2539 | 0.1259 | 0.0655 | 0.0287 |
| 14 | 21 | 0.4973 | 0.2494 | 0.1247 | 0.0632 | 0.0310 |
| **null `2^{−G}`** | | 0.5000 | 0.2500 | 0.1250 | 0.0625 | 0.0312 |

Agreement is close at every level. **No extra arithmetic suppression or enhancement of the gap is
visible**, consistent with CAAP's finding that confined realizer placement matches random injective
placement at population scale. Diagnostic only (§33): this is a population statement and cannot
close the frontier either way.

## W. Record-frontier gap calibration

| seed | `N` | `S` | `r_N` | `g` | `E` | `g = ⌈E⌉`? |
|---|---|---|---|---|---|---|
| 27 | 8 | 11 | 27 | 7 | 6.245 | ✓ |
| 27 | 12 | 16 | 27 | 12 | 11.245 | ✓ |
| 703 | 12 | 14 | 703 | 5 | 4.543 | ✓ |
| 26623 | 12 | 13 | 10239 | 0 | −0.322 | ✓ |
| 626331 | 12 | 15 | 36507 | 0 | −0.156 | ✓ |

Seed 27 is the clean illustration: once `2^{S+1} > 27` the realizer stops moving and the gap grows
one bit per unit of valuation. Note `E` can be **negative** when `r > 2^S`, while `g = 0` — another
reason `g`, not `E`, is the right variable. No new record search was run.

## X. Open Problem E translation

P1 Open Problem E: `E(D) ≤ H₂(ρ_c)·S + Φ(N)` with `Φ(N) = o(N)`.

Using `g − 1 < E ≤ g` (§E), the exact integer form is

```
E ≤ H₂(ρ_c)S + Φ(N)      ⟸      g ≤ H₂(ρ_c)S + Φ(N),
E ≤ H₂(ρ_c)S + Φ(N)      ⟹      g ≤ H₂(ρ_c)S + Φ(N) + 1.
```

So E and the integer gap bound are equivalent **up to an additive 1**, not exactly equivalent —
the rounding correction the brief insisted on. With `H₂(1/α) = 0.949956` and `S ≈ αN`, the
statement is `g ≲ 1.5056 N`, against the trivial ceiling `g ≤ S ≈ 1.585 N`.

## Y. Open Problem C translation

`r(D) ≥ 2^{εN}` translates, by `discreteGap_ge_iff`, to

```
g(D) ≤ S_N − εN,     and under zero confinement S_N ≤ ⌊αN⌋ ≤ αN + c,
g(D) ≤ (α − ε)N + c.
```

> **The realizer-floor problem is exactly the problem of preventing a linear high-bit zero gap.**

That is the sharpest statement this audit produces, and it is a translation (§H), not a mechanism.

## Z. Qualitative Escape hierarchy

The brief's warning is correct and worth stating precisely. Writing `h_N = ⌊log₂ r_N⌋`:

| statement | meaning in gap coordinates | strength |
|---|---|---|
| infinitely many lift jumps `k_N ≠ 0` | `r_N` changes infinitely often | weakest |
| **qualitative escape** `r_N → ∞` (CAAP OP B.1) | `h_N → ∞` | weak |
| sublinear gap | `g_N = o(N)` | intermediate |
| **linear gap exclusion** | `g_N ≤ (α − ε)N` | = OP C |
| exponential floor `r_N ≥ 2^{εN}` | same as above | = OP C |

**Crucially, qualitative escape does not bound `g_N`.** If `r_N → ∞` slowly — say `h_N ~ log N` —
then `g_N = S_N − h_N ~ αN`, a *linear* gap. So CAAP's Open Problem B.1, even if proved, leaves the
gap unbounded. The hierarchy has a genuine gap between "escape" and "sublinear gap" that no
existing result spans.

## AA. Negative-integer calibration

| `x` | word | `g_N` for `N = 2…8` |
|---|---|---|
| `−1` | `(1,1,1,1,…)` | 0,0,0,0,0,0,0 |
| `−5` | `(1,2,1,2,…)` | 0,0,0,0,0,0,0 |

Their realizers have the **top bit set** (`r ≈ 2^{S+1}`), so `g = 0` throughout — no zero gap at
all. Combined with the previous round's finding that both words are zero-confined:

> **Long zero gaps are a small-realizer phenomenon, not a generic consequence of zero
> confinement.** The negative examples occupy the opposite extreme of the gap variable.

Used as a sanity check only, not as part of any positive-realizer claim.

## AB. Chang stress test

Using the machine-checked `ChangFullShift.changSeq`:

| history | `g_N` for `N = 4…12` |
|---|---|
| all-true | 0,2,0,0,0,1,2,3,0 |
| all-false | 0,2,0,1,2,3,0,0,0 |
| alternating | 0,2,0,0,0,1,2,3,0 |
| period-3 | 0,2,0,0,0,1,2,3,0 |

Arbitrary symbolic complexity coexists with both small and large gaps, and different histories give
nearly identical gap profiles. **Chang complexity is not the variable controlling the gap.** No
Chang route reopened.

## AC. Prefix perturbation

Same 11-letter prefix, last two letters varying, `(N,S) = (13,20)`: **max spread in `g` is 12**,
over 2652 prefix classes. A late one-letter change can move the gap by more than half the window.

## AD. Suffix perturbation

Same 4-letter suffix, prefix varying: **max spread in `g` is 12**, over 170 suffix classes. This
interfaces with the W=2 round's finding that complete suffix fibres balance while the prefix
selector breaks balance — here, identical suffix data is compatible with a 12-bit range of gaps, so
**no suffix-local theorem can control it.**

## AE. Deterministic invariant search

Exact quantities available at depth `N`: `N`, `S_N`, `R_N`, `C_N`, `Z_N`, `r_N`, `m_N`, `Δ_N`, and
suffix data. Does any relation among all of them **except `r_N`** bound `g`?

| candidate | verdict |
|---|---|
| `N, S_N, Δ_N, R_N` | word-level only; §AA shows two words with the same `Δ_N → ∞` behaviour and `g ≡ 0` |
| `C_N`, `Z_N` | determine `r_N` exactly (§F), so any bound through them is a bound through `r_N` — circular |
| `m_N` | defined by the orbit identity from `r_N` (§P) — circular |
| suffix data | §AD: 12-bit gap spread at fixed suffix — no bound |

**Every candidate bound either requires inserting `r_N` itself or fails outright.** This is the
independence test, and nothing survives it — matching CAAP Remark B.2's advance warning.

## AF. Weakest genuinely new missing lemma

The natural candidate,

> *zero-confined irregular words cannot produce a carry gap of length `≥ θ S_N`,*

is **Open Problem C verbatim** by §Y, so it is not an intermediate lemma.

A legitimate intermediate would need independent hypotheses and a proof route *through carry
structure*. The audit found no such route: §M/§N show the borrow condition has no finite closure,
§Q shows the Diophantine side is vacuous, and §T shows irregularity gives no purchase.

**NONE found.**

## AG. Lean formalization

**New module `EOC/TerminalZeroGap.lean`**, 5 theorems + 1 definition, no
`sorry`/`admit`/`axiom`/`opaque`.

| declaration | statement |
|---|---|
| `discreteGap S r` | `S − Nat.log 2 r` |
| `log_le_of_lt` | `0 < r → r < 2^{S+1} → Nat.log 2 r ≤ S` |
| `discreteGap_ge_iff` | `0 < r → G ≤ S → r < 2^{S+1} → (G ≤ discreteGap S r ↔ r < 2^{S−G+1})` |
| `discreteGap_eq_zero_iff` | `g = 0 ↔ 2^S ≤ r` |
| `carry_residue_of_small_realizer` | `r = (Z + 2^S) % 2^{S+1} → r < 2^S → Z < 2^{S+1} → Z = r + 2^S` |
| `C_split` | `∃ C', C d (k+n) = 3^n · C d k + 2^{s d k} · C'` |

Reuses the repository's `C`, `q`, `q_eq_C` (`EOC/Carry.lean`) and `s_mono'`
(`EOC/FirstDivergence.lean`) rather than re-deriving them. **Nothing speculative was formalized**:
no Diophantine claim, no borrow automaton, no gap bound.

The header records the §E correction and the CAAP `k_N` attribution so a future reader meets both
at the source.

## AH. Computational checks

`scratch/terminal_zero_gap.py`, standard library only, deterministic. Key results already cited:
`g = ⌈E⌉` **0/4399** violations; `z_N = 2^S + r_N` **0/871** mismatches; carry-dominance table;
term-by-term bit supports; shell fibers and the `2^{−G}` null; prefix/suffix spreads of 12;
negative and Chang calibrations; record-frontier values.

All population figures are diagnostics (§33 of the brief); none is offered as an endpoint.

## AI. Tests/build

| command | result |
|---|---|
| `lake build EOC.TerminalZeroGap` | **success, 2258 jobs, 0 errors** |
| `lake build EOC.Carry` | success, 1134 jobs |
| `lake build EOC.ZCRERealizerGrowth` | success, 2049 jobs |
| `lake build EOC.RealizerLiftDigit` | success, 2050 jobs (no regression) |
| `python3 scratch/terminal_zero_gap.py` | exit 0 |
| forbidden-token grep | clean |

## AJ. Axiom audit

```
discreteGap_ge_iff                : [propext, Classical.choice, Quot.sound]
discreteGap_eq_zero_iff           : [propext, Classical.choice, Quot.sound]
carry_residue_of_small_realizer   : [propext, Quot.sound]
C_split                           : [propext, Classical.choice, Quot.sound]
log_le_of_lt                      : [propext, Classical.choice, Quot.sound]
```

Standard Mathlib axioms only.

## AK. Files changed

```
new:  EOC/TerminalZeroGap.lean                             5 theorems + 1 definition
new:  scratch/terminal_zero_gap.py                         reproducible checks
new:  docs/NORMALIZED_CARRY_TERMINAL_ZERO_GAP_AUDIT.md     this report
```

No existing Lean file modified; no theorem statement changed; no source document edited.

## AL. Commits

Branch `normalized-carry-zero-gap-audit`, from `bb4f6c9`.

| commit | contents |
|---|---|
| `539b59d` | `EOC/TerminalZeroGap.lean` + `scratch/terminal_zero_gap.py` |
| (this file) | this report |

## AM. Push status

Branch pushed to `origin/normalized-carry-zero-gap-audit`. **No pull request opened.** `main`
unmodified; dirty ordinary checkout untouched.

## AN. Research verdict

**`TERMINAL ZERO GAP IS A TARGET, NOT A MECHANISM`**

All six of Gate 35's stop conditions hold, and this verdict is the one that states the outcome
rather than a single symptom of it.

It is chosen over four neighbours that are individually true but partial.
`ZERO GAP IS EXACTLY THE REALIZER-PLACEMENT TARGET` is proved (§G, §Y, formalized) and is the
positive half, but says nothing about whether a mechanism exists.
`PEELING CONTROLS THE WRONG END OF THE BIT STRING` (§K), `BORROW PROPAGATION DOES NOT CLOSE`
(§M, §N) and `MIXED REAL/2-ADIC APPROXIMATION IS TAUTOLOGICAL` (§P, §Q) are each established, but
each closes only one of the three candidate mechanisms; the chosen verdict is their conjunction
plus §T's absence of an irregularity route. `NO IRREGULARITY-TO-GAP MECHANISM FOUND` is also true
(§S, §T) but understates how thoroughly the other two routes closed.

**The decisive distinction the brief asked for.** "The gap means `r` is small" is proved and
formalized. "The carry structure independently prevents such a gap" is **not** established by
anything found here:

- the sparse-unit sum has **no locality** — every term reaches every high bit (§I), so there is no
  bounded-state object to reason about;
- the borrow condition depends on the **complete lower block** (§M), reproducing HC's prior
  negative finding rather than escaping it;
- the Archimedean side is **vacuous** because `3^N ≥ 2^S` under zero confinement, so the error
  term exceeds the unit even for `r_N = 1` (§Q) — the same carry dominance that closed the Pell
  route;
- gap statistics match random-injective placement to three decimals (§V), and large-gap words keep
  full symbolic freedom (§T).

**What the audit delivers.** The exact integer target, formalized: *prevent `g(D) ≤ (α − ε)N` from
failing* — Open Problem C is precisely the exclusion of a **linear** high-bit zero gap (§Y), and
Open Problem E is the same statement with constant `H₂(1/α)` up to an additive 1 (§X). Plus two
corrections that keep the record straight: `E(D)` is not an integer zero-run (`g = ⌈E⌉`, §E), and
the previous round's `liftDigit` is CAAP's jump `k_N` (§B).

And one hierarchy clarification that matters for choosing the next target: **qualitative realizer
escape does not bound the gap** (§Z). Proving `r_N → ∞` would leave `g_N` linear. Any future
mechanism must control the *rate*, not merely the fact, of escape.
