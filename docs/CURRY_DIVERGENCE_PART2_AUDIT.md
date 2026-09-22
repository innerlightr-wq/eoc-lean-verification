# Divergent side — Part 2: cross-paper audit of the injective/divergent profile

A theorem-status map, not a proof attempt. Three manuscripts are read against each other and
against the Lean library to determine the strongest rigorously supportable completion of

> *If a Type-II / injective / divergent accelerated Collatz orbit exists, then it must satisfy ____.*

**Headline answer to the Part 2 target.** The compression of Curry's paper to `R_n → −∞` discards
three separable things, and they are lost at two different stages:

1. The **quantitative occupation bound** `#{n : g_n ≤ G} ≤ c₁2^{βG}(G+c₂)` — a power saving of
   `2^{−(1−β_*)G}`, `1−β_* = 0.0346…`, over what mere distinctness of the states already gives.
   This is proved in both source papers and is **not** in the Lean reduction.
2. The **window-uniformity in `a`** — the entire content of "Banach density zero". This is
   discarded **by the source papers themselves**: every downstream consequence uses Theorem 2.3
   only at `a = 1`. Formalizing the occupation bound would not recover it.
3. The **universality of `C_β`** over collision-free sets, which the papers half-use and the Lean
   interface drops entirely.

And one structural finding that bounds how much any of it can help: every Curry consequence is
conditional on the orbit *existing*, whereas ZCRE asks *whether* a realizer exists. A conditional
description cannot serve as a hypothesis in that existence question. §U states the one interface
that survives this objection and the exact reason it is currently circular.

---

## A. Starting state

| | |
|---|---|
| repository | `~/GitHub/eoc-lean-verification` |
| branch point | `dynamic-deficit-feedback` = `1d087e20b72faaf7a4d13ee03c44b0858990f238` ✓ matches brief |
| new branch | `curry-divergence-part2` |
| worktree | isolated; Mathlib shared by read-only symlink |

Ancestry verified against the brief, all three confirmed ancestors of the tip:

| branch | commit | relation |
|---|---|---|
| `curry-foundation-zero-corridor` | `5db34a58` | ancestor |
| `zcre-realizer-growth` | `9435bca0` | ancestor |
| `dynamic-deficit-feedback` | `1d087e20` | the tip itself |

The two named ancestor branches exist only as **remote** refs (`refs/heads/...` on `origin`), not
as local branches; ancestry was confirmed against those. The ordinary checkout was on
`research-sparse-visits-2026-09-16` with **53 dirty files** and was not touched, per the brief.
`main` (`1c4d6700`) is unmodified.

## B. Source papers

All three located as files and read; none was taken from a prior prompt's summary.

| | paper | file | sha256 (first 16) |
|---|---|---|---|
| **P1** | De Jesús, *A Global Occupation Conjecture for the Accelerated 3x+1 Map: Divergent-Orbit Sparsity, Exact Realizers, and the Moving-Anchor Problem*, **Revision 5, 2026** | `EOC_latestRev (4).pdf` | `73adc35e628b5fbc…` |
| **P2** | Curry, *An Explicit Windowed Sparsity Bound for Divergent 3x+1 Orbits, with Logarithmic-Floor Exclusion beyond the Harmonic Barrier*, **24 August 2026** | `occupation_note_clean.pdf` | `67daa37d9b1b1b3e…` |
| **P3** | De Jesús, *Valuation-Mean Classification for the Accelerated Collatz Map: A Conditional Lyapunov Criterion, the Critical Boundary log₂3, and the Cycle Window*, **July 2026** (Version 5 per its §1) | `Lyapunov_Collatz_revision (1) (3).pdf` | `4f5bbd64d168fe93…` |

Filename note: the brief expects `EOC_latestRev (4)(2).pdf` and `occupation_note_clean(1).pdf`.
The five `EOC_latestRev*.pdf` copies in `~/Downloads` are **byte-identical** (all
`73adc35e628b5fbc…`), and only one `occupation_note_clean.pdf` exists, so the numbering is a
download artifact and there is no ambiguity about which file was read.

P2 is 5 pages and was read in full, line by line, as the brief requires. Its conclusions were
**not** taken from P1's paraphrase — though §E records that P1's paraphrase turns out to be
faithful.

## C. Notation crosswalk

Verified numerically on the orbits of `m₀ = 7, 27, 703` (§Z): every identity below was checked to
`10⁻⁹` at each step, including the product identity and both sign conventions.

| object | P1 / repo / this audit | P2 (Curry) | P3 (valuation-mean) |
|---|---|---|---|
| accelerated map | `T(m) = (3m+1)/2^{d(m)}` | `U(y) = (3y+1)/2^{ν₂(3y+1)}` | `T(m)`, same |
| state | `m_n` | `y_n` | `m_k` |
| valuation | `d_n = ν₂(3m_n+1)` | `a_n = ν₂(3y_n+1)` | `D_k = ν₂(3m_k+1)` |
| prefix sum | `S_N = Σ_{n<N} d_n` | `A_N = a₀+…+a_{N−1}` | `S_N = Σ_{k<N} D_k` |
| `log₂3` | `α` | `λ` | `α` |
| drift | `R_N = S_N − αN` | `R_n = A_n − nλ` (states `R_n = −g_n`) | `R_N = S_N − Nα` |
| **anti-drift** | `−R_N` | **`g_n = nλ − A_n`** | — |
| mean | `S_N/N` | — | **`D_N = S_N/N`** |
| carry sum | `E_N = Σ_{n<N} log₂(1+1/(3m_n))` | `E_N`, same | `E_N`, same; `ϵ_N = E_N/N` |
| carry product | `Q_N = ∏_{j<N}(1+1/(3m_j))` | `Q_n`, same | same |
| deficit | `Δ_k = ⌊αk⌋ − S_k` | — | — |

Bridging identities, all verified:

```
R_N  = −g_N                            (Curry's sign convention, P2 §1)
R_N  = N(D_N − α)                      (P3 Definition 2.4)
g_N  = N(α − D_N)
Q_N  = 2^{E_N}                         (hence "carry sum" and "carry product" are the same datum)
R_N  = log₂(m₀/m_N) + E_N              (P3 (7); Eliahou–Rozier in drift form)
m_N  = m₀ · Q_N · 2^{−R_N} = m₀ Q_N 2^{g_N}      (P1 Lemma 2.2; P2 (1))
R_k  = −Δ_k − {αk}                     (exact, no error term)
```

### ⚠ Notation collision — the one trap in this audit

**P3's Proposition 5.1 defines `g_N := (1/N)·log₂(m_N/m₀)`**, the mean exponential *growth rate*.
**P2's `g_n := nλ − A_n`** is the unnormalized *anti-drift*. These are different objects sharing a
symbol, and they differ by both a factor of `N` and an additive carry term:

```
g_N^{P3}  =  g_N^{P2}/N  +  ϵ_N ,        ϵ_N = E_N/N
```

Throughout this audit **`g` means Curry's `g` (= `−R`)**, matching the brief. P3's quantity is
written `ĝ_N` where it is needed. A reader who conflates them would read P3's
`D_N = α − g_N + ϵ_N` as contradicting `R_N = N(D_N−α)`; it does not.

## D. Orbit-type vocabulary

The brief asks that "divergent" never be used ambiguously. Four distinct notions:

| term | meaning |
|---|---|
| **unbounded** | `sup_n m_n = ∞` |
| **tends to infinity** | `m_n → ∞` |
| **injective** | `m_i ≠ m_j` for `i ≠ j` (P1 Def 4.1; P3 Def 2.5) |
| **infinite aperiodic** | not eventually periodic (P2's hypothesis class) |

**In the positive-integer accelerated setting these collapse.** The implications, with sources:

1. **repeated state ⟹ eventually periodic.** `T` is a function, so `m_i = m_j` with `i<j` forces
   period `j−i` from step `i`. (P3 Def 2.5; P1 Lemma 4.2.)
2. **injective ⟹ `m_n → ∞`.** Only finitely many positive odd integers lie below any bound, so
   an injective sequence of them escapes every bound permanently. Stated and proved in **P3
   Definition 2.5**. Note this is genuinely stronger than *unbounded* and the proof is what
   supplies the upgrade.
3. **`m_n → ∞` ⟹ injective** is *false* in general for sequences but holds here because a
   repeat forces periodicity (1), which forces boundedness.
4. **aperiodic ⟹ collision-free.** P2 §2: a collision `T^j(u₁)=T^j(u₂)` between two orbit points
   forces eventual periodicity, hence boundedness. Attributed by Curry to Garcia–Tal.

So for orbits of the positive accelerated map: **injective ⟺ `m_n → ∞` ⟺ infinite aperiodic ⟺
unbounded ⟺ "Type-II divergent"**, and the trichotomy of P3 Def 2.5 (terminating / nontrivial
cycle / injective) is exhaustive and exclusive. Below, *divergent* always means this class.

One caveat worth stating: Curry's Proposition 3.1 is about the **raw** map `T₀(n) = n/2, (3n+1)/2`
and its full value set `O` (even values included); the accelerated odd iterates `{m_n}` are a
*subset*. Sub-sums of convergent positive series converge, so the odd-only conclusion follows —
but it is strictly weaker than what Curry proves. §T records this as discarded information.

## E. Curry theorem extraction

Read from P2 directly. Exact statements and quantifiers.

**Lemma 2.1 (Terras–Everett).** The parity prefix `(T^j(n) mod 2)_{j<N}` depends only on
`n mod 2^N`, and `n mod 2^N ↦ prefix` is a bijection `Z/2^N → {0,1}^N`. Consequently for every
`r ≥ 0`: `T^N(n + r2^N) = T^N(n) + r·3^{m_N(n)}`.

**Lemma 2.2.** For all `n, N ≥ 1`: `T^N(n) < 3^{m_N(n)}(2^{−N}n + 1)`.

**Definition.** `A ⊂ ℕ` is **collision-free** if distinct `u₁,u₂ ∈ A` never satisfy
`T^j(u₁) = T^j(u₂)` for any `j ≥ 0`.

**Theorem 2.3 (windowed sparsity).** Let `A` be collision-free, `γ ∈ (1/2, 1/λ)`. Then **for all
integers `a ≥ 1`, `X ≥ 2`**:

```
#(A ∩ [a, a+X))  ≤  6(⌊log₂X⌋ + 1)(X^{H(γ)} + X^{γλ})
```

and with `β_* = γ_*λ = H(γ_*)`, `γ_*` the unique root of `H(γ) = γλ` on `(1/2, 1/λ)`: for every
`β > β_*` there is a constant `C_β` with `#(A ∩ [a,a+X)) ≤ C_β X^β log(2X)` **uniformly in `a`**.

Verified numerically (§Z): `γ_* = 0.6090897679`, `β_* = 0.9653844417 = H(γ_*)`,
`1/β_* = 1.0358567600`, and `γ_* ∈ (0.5, 1/λ = 0.6309…)`. All match the paper's digits.

**Proposition 3.1 (reciprocal summability).** `O` the value set of a divergent orbit of `T` ⟹
`Σ_{x∈O} 1/x < ∞`; equivalently `Σ_{k≥0} 1/T^k(N₀) < ∞` and, for the odd iterates,
`Σ_{n≥0} 1/y_n < ∞`.

**Identity (1).** `y_n = y₀ 2^{g_n} Q_n`, `Q_n = ∏_{j<n}(1+1/(3y_j))` nondecreasing. **(2)**:
`y₀2^{g_n} ≤ y_n ≤ y₀Q_∞2^{g_n}`.

**Theorem 4.1 (floor exclusion, harmonic barrier).** No divergent orbit satisfies
`g_n ≤ B log₂n + K` for all large `n`, with constants `B ≤ 1`, `K ≥ 0`.

**Theorem 4.2 (occupation).** `(y_n)` the odd iterates of a divergent orbit, `β ∈ (β_*,1)` fixed.
There are constants `c₁, c₂` **depending on `β` and on the orbit (through `y₀` and `Q_∞`)** with

```
#{n ≥ 0 : g_n ≤ G}  ≤  c₁ 2^{βG}(G + c₂)      for all G ≥ 1.
```

**Corollary 4.3.** No divergent orbit satisfies `g_n ≤ B log₂n + K` for all large `n` with
`B < 1/β_* = 1.0358567…`. **The endpoint `B = 1/β_*` is not excluded.**

**§5 Limitations, quoted in substance.** `β_*` is a genuine barrier *for the argument of Theorem
2.3*: it balances the entropy of heavy parity prefixes against the contraction of light ones, and
"both sides are sharp **for the hypothesis class**". Improving `1/β_*` requires either deeper
iteration than `N ≈ log₂X` (which breaks Lemma 2.1's modulus bookkeeping) or an input beyond
parity counting. Nothing constrains nontrivial cycles (periodic ⟹ not aperiodic ⟹ outside every
hypothesis). Nothing bears on the sub-critical occupation of *convergent* orbits, "which is the
open core of the Effective Occupation Conjecture".

**Fidelity of P1's import.** P1 Rev 5 already carries the whole chain, translated to `R`:
Theorem 4.8 = Curry Thm 2.3, Proposition 4.9 = Curry Prop 3.1, Theorem 4.10 = Curry Thm 4.1,
Theorem 4.11 = Curry Thm 4.2 + Cor 4.3. Statements, constants and quantifiers agree. **No
discrepancy found** between P2 and P1's rendering of it — including the honest retention of
"the endpoint `B = 1/β_*` is not excluded by this argument".

## F. Uniformity audit

The brief flags this as a main reason to read P2 directly. Resolved item by item.

| item | uniform over divergent orbits? | dependence |
|---|---|---|
| **A. `C_β` (Thm 2.3)** | **YES — universal** | on `β` only |
| **B. Prop 3.1** | conclusion is per-orbit; the *rate* is universal | the bound on `Σ1/x` depends only on `β` |
| **C. `c₁, c₂` (Thm 4.2)** | **NO** | `β`, and the orbit through `y₀` and `Q_∞` |
| **D. Cor 4.3 threshold `1/β_*`** | **YES** | a pure constant |
| **E. `R_N → −∞`** | qualitative, so vacuously uniform | none |

**A is the finding worth stating plainly.** The explicit bound
`6(⌊log₂X⌋+1)(X^{H(γ)}+X^{γλ})` contains **no reference to `A` whatsoever** — not its seed, not
its density, nothing. So `C_β` is universal over *all* collision-free sets once `β` is fixed, not
merely over all orbits. This is stronger than the brief's cautious phrasing anticipated, and it
is visible only from P2's own proof.

**C is genuinely orbit-dependent, and the dependence is exactly located.** From the proof, the
bound is `C_β(y₀Q_∞)^β 2^{βG} log(2y₀Q_∞2^G)`, so `c₁ ≍ C_β(y₀Q_∞)^β` and
`c₂ ≍ log₂(2y₀Q_∞)`. Since `C_β` is universal, **the sole orbit-dependence in the whole package
is the single scalar `y₀Q_∞`.** Nothing else about the orbit enters.

**Does the zero-corridor reduction require uniformity?** **No.** The reduction needs only
`R_N → −∞` for the one hypothetical orbit under discussion, which is a per-orbit statement. A
proof by contradiction fixes one orbit; uniformity is never invoked. This resolves the earlier
internal worry: it was unnecessary.

**Would EOC-style uniformity require substantially more?** **Yes, and §U explains why it is the
crux.** EOC (P1 Conj 3.1–3.4) wants `O_c(m₀) ≤ K log₂m₀ + C` for *all* seeds with explicit
constants. Curry gives nothing of this kind: his bound is on the *anti*-occupation of one
divergent orbit, with a constant growing like `(y₀Q_∞)^β`. Because `c₁` **grows** with `y₀`, a
word with a large realizer gets a *weaker* constraint — which is precisely the wrong direction for
extracting a realizer lower bound (§U).

## G. Reciprocal summability chain

From window sparsity to `Q`/`E` convergence, with the exact dependency at each step.

```
Thm 2.3 (collision-free windowed sparsity)
   │  [divergent ⟹ aperiodic ⟹ collision-free]                     — §D.4
   ▼
Prop 3.1  Σ_{x∈O} 1/x < ∞   ⟹  Σ_n 1/m_n < ∞                       — sub-sum
   │  log(1+x) ≤ x
   ▼
log Q_n ≤ (1/3)Σ_j 1/m_j < ∞ ⟹ Q_n ↑ Q_∞ < ∞ ⟹ E_n ↑ E_∞ < ∞      — Q_n = 2^{E_n}
```

**Only `a = 1` is needed.** Curry's proof of Prop 3.1 sums Theorem 2.3 over dyadic blocks
`[2^i, 2^{i+1})`, i.e. at `a = 2^i`. That use of general `a` is **removable**: writing
`N(X) = #(O ∩ [1,X))` for the initial-segment count,

```
Σ_{x∈O} 1/x  =  Σ_i Σ_{x∈O∩[2^i,2^{i+1})} 1/x
             ≤  Σ_i 2^{−i} N(2^{i+1})
             ≤  Σ_i 2^{−i} C_β 2^{(i+1)β} log(2^{i+2})
             =  C_β 2^β log2 · Σ_i (i+2) 2^{−i(1−β)}  <  ∞   for β < 1.
```

So the entire chain runs on initial-segment counts alone. This is the substitute proof referred
to in §T, and it is what makes the window-uniformity claim in §T checkable rather than rhetorical.

**Where `β < 1` is spent.** Convergence needs `2^{−i(1−β)}` summable, i.e. `β < 1`; available
because `β_* = 0.9654… < 1`. The margin `1 − β_* = 0.0346…` is small but is the whole reason the
chain closes, and it reappears in §M as the power saving.

## H. Drift-to-minus-infinity

Both routes in the brief are valid. They differ in inputs, and the brief's framing of which is
cheaper needs one correction.

**Route A (via Theorem 4.2).** For each fixed `G`, `#{n : g_n ≤ G} ≤ c₁2^{βG}(G+c₂) < ∞`. Finitely
many `n` below each level ⟹ for every `G` there is `N` with `g_n > G` for `n ≥ N` ⟹ `g_n → +∞`
⟹ `R_n → −∞`. **Valid.** Inputs: Thm 2.3, Prop 3.1, identity (2), and the counting argument of
Thm 4.2.

**Route B (via the product identity).** `Σ1/m_n < ∞` ⟹ terms `→ 0` ⟹ `m_n → ∞` (no separate
appeal to injectivity needed); `Q_n ↑ Q_∞ < ∞`; then `2^{g_n} = m_n/(m₀Q_n) → ∞`, so `g_n → ∞`.
**Valid.** Inputs: Thm 2.3, Prop 3.1, identity (1).

**Route B requires strictly fewer inputs** — it never invokes Theorem 4.2's counting. Equivalently
and most cleanly, from P3's form of the identity:

```
R_N = log₂(m₀/m_N) + E_N ,   E_N ≤ E_∞ < ∞ ,   m_N → ∞   ⟹   R_N → −∞.
```

Route A's extra cost buys a *rate*, which Route B does not give; but for the qualitative
conclusion Route B is cheaper. Note also that Route B's derivation of `m_n → ∞` from summability
alone is what lets the Lean interface avoid threading a separate injectivity hypothesis — the
`CurryFoundation` header makes exactly this observation.

**Represented in Lean:** yes, as Route B. `R_tendsto_atBot` is proved from `orbit_tendsto_atTop`
(itself from `ReciprocalSummable` via `Summable.tendsto_atTop_zero`) and `carryU_tendsto`, through
`orbit_mul_two_rpow_R`. Route A is **not** in Lean, because Theorem 4.2 is not.

## I. Valuation-mean consequences

**What P3 proves unconditionally (Theorem 4.3).** For an injective orbit, for *every* `N ≥ 1`:

```
D_N ≤ α + (log₂m₀ + (1/6)log₂N + 1/(3 ln 2))/N ,     hence  limsup D_N ≤ α.
```

Equivalently `R_N ≤ log₂m₀ + E_N = O(log N)`. Note this is a genuine finite-`N` bound, not merely
an asymptotic statement — but the correction term is **positive**, so P3 alone does **not**
exclude `D_N > α` at any finite `N`, and `limsup` permits `D_N = α` along a subsequence.

**What Curry adds.** Precisely an upgrade of the carry bound:

```
P3 / P1 harmonic packing:   E_N = O(log N)         (distinctness of states)
Curry Prop 3.1:             E_N ≤ E_∞ < ∞          (windowed sparsity)
```

Everything else follows from that one substitution. In particular `R_N ≤ log₂m₀ + E_∞` is now
**bounded above by a constant**, not `O(log N)`.

**Is `D_N < α` eventually, rigorously?** **Yes.** `g_N → ∞` gives `g_N > 0` for large `N`, and for
`N ≥ 1`, `g_N > 0 ⟺ D_N < α` since `g_N = N(α − D_N)`.

**Classification (the brief asks for this explicitly):**

- **not** explicitly stated in any of the three papers in this form;
- an **immediate cross-paper corollary**, one line from `g_N → ∞`;
- **now formalized** — `valuationMean_lt_alpha_eventually`, §W;
- **and a reformulation, not new information.** `D_N < α eventually` is *logically equivalent* to
  `R_N < 0 eventually`, which is an immediate weakening of `R_N → −∞`. It imposes nothing that
  the drift statement did not. P3's own **Remark 5.2** says this in advance: "for a divergent
  orbit the valuation mean and the growth rate are the same quantity in different units — so
  there is no independent 'profile' to exclude". The novelty is presentational.

**What Curry does NOT imply.** `g_N → ∞` says nothing about the *rate*, so it does not decide:

| possibility | compatible with all three papers? |
|---|---|
| `lim D_N = α` (i.e. `g_N/N → 0`) | **yes** — `g_N → ∞` sublinearly |
| `lim D_N = α − c`, `c > 0` (i.e. `g_N ≍ cN`) | **yes** by these theorems; see the caveat below |
| `limsup D_N = α` with `liminf D_N < α` | **yes** |
| `limsup D_N < α` | **yes** by these theorems; same caveat |
| `limsup D_N > α` | **NO** — P3 Thm 4.3 |
| `D_N > α` for infinitely many `N` | **NO** for large `N` — Curry, §I above |

**Caveat on the linear cases.** P3 Theorem 4.3's finite-`N` bound gives
`D_N ≤ α + O(log N / N)`, hence `g_N ≥ −log₂m₀ − (1/6)log₂N − 1/(3ln2)`, i.e. an upper bound on
`R_N` only. It does not bound `g_N` above, so linear `g_N` is not excluded by the drift theorems.
Whether a *divergent* orbit can really sustain `g_N ≍ cN` is a separate question about growth
rates (`m_N ≈ m₀Q_∞2^{cN}`, doubly exponential in nothing — merely exponential growth, which is
what divergence means); nothing in these three papers rules it out. §R records it as allowed.

## J. Zero-corridor restart

`R_N → −∞` ⟹ `R` attains a **last** global maximum: the sequence exceeds any level only finitely
often, so the set of global maximizers is nonempty and finite. Let `n₀` be the last one and
restart at `m_{n₀}`.

For every `k ≥ 1`, `R_{n₀+k} < R_{n₀}` — *strictly*, because `n₀` is the **last** maximizer, so no
later index attains the maximum. Hence with `S'_k := S_{n₀+k} − S_{n₀}`:

```
R_{n₀+k} − R_{n₀} = S'_k − kα < 0     ⟹     S'_k < kα.
```

`S'_k` is an **integer**, so `S'_k < kα` gives `S'_k ≤ ⌊kα⌋` directly by the definition of the
floor (`Int.le_floor`).

**A precision point the Lean file records and the informal audit got slightly wrong.**
`docs/CURRY_FOUNDATION.md` §8.5 says this step "uses irrationality of `α`". It does not: the
integrality of `S'_k` plus `S'_k < kα` suffices, with no rationality hypothesis at all.
Irrationality of `α` *is* needed elsewhere — for the Beatty gap `b_k ∈ {1,2}` in the deficit
recurrence — and `alpha_smul_not_int` is retained and used there. The brief's Gate 5 phrasing
("because `αk` is irrational") should be read as applying to the Beatty-gap step, not to the
corridor step. This correction is already in the Lean source comment; it is restated here because
the brief asked for the argument to be verified rigorously rather than inherited.

So a divergent orbit, after restart, satisfies the **exact zero corridor** `S'_k ≤ ⌊αk⌋` for all
`k ≥ 1`.

## K. Deficit profile

`Δ_k := ⌊αk⌋ − S'_k ≥ 0` on the corridor tail. The identity is exact:

```
R'_k = S'_k − kα = −Δ_k − {αk},        {αk} ∈ [0,1),
```

so `−Δ_k − 1 < R'_k ≤ −Δ_k`: the drift and the deficit are the same datum up to a bounded
fractional correction, and therefore

```
R'_k → −∞   ⟺   Δ_k → ∞ .
```

Deficit dynamics: `Δ_{k+1} = Δ_k + b_{k+1} − d_k` with `b_{k+1} = ⌊(k+1)α⌋ − ⌊kα⌋ ∈ {1,2}` (the
Beatty gap, needing `1 < α < 2` and irrationality). Since `d_k ≥ 1`, `Δ` increases by at most 1
per step (`deficit_succ_le`), so the deficit **cannot jump** — it climbs to infinity one unit at a
time, which is what makes the corridor a genuine constraint rather than a bookkeeping identity.

## L. State-scale profile

On the corridor tail, `−R_N = Δ_N + {αN}`, so the Eliahou–Rozier identity gives **exactly**

```
m_N = m₀ · Q_N · 2^{Δ_N + {αN}} .
```

With `1 ≤ Q_N ≤ Q_∞ < ∞` and `1 ≤ 2^{{αN}} < 2`, explicit valid constants:

```
m₀ · 2^{Δ_N}   ≤   m_N   <   2 m₀ Q_∞ · 2^{Δ_N} .
```

Both are attainable up to the stated factors; the multiplicative gap is `2Q_∞`, a single
orbit-dependent scalar. So `m_N = Θ(2^{Δ_N})` with an absolute implied constant once `Q_∞` is
fixed.

**Does this give a new constraint?** **No — it is a change of coordinates**, and this audit
confirms the `dynamic-deficit-feedback` verdict against the three papers rather than inheriting
it. The reasons, now sourced:

1. `Δ_k` determines the word: `Δ_k = ⌊αk⌋ − S_k` gives `S_k`, and `d_k = S_{k+1} − S_k`. So the
   deficit profile and the valuation word are **interchangeable data**, not independent.
2. The word plus `m₀` determines every `m_N` (P1 Prop 5.2's recursion `2^{s_j}m_j = 3^jm₀ + q_j`).
   So `m_N` carries no information beyond `(word, m₀)`.
3. The bracket above is therefore a *consequence* of the identity, not an additional restriction:
   it says the state scale is the deficit in different units. **P3 Remark 5.2 states precisely
   this** ("the same quantity in different units — so there is no independent 'profile' to
   exclude"), and P3's abstract calls the whole classification "a change of coordinates on the
   orbit trichotomy".

Passing the brief's discipline gate: does `m_N ≍ 2^{Δ_N}` impose information not already
determined by the valuation word and the orbit recurrence? **No.** **Reformulation.**

## M. Occupation comparison

This is where the two programs are easiest to conflate, and they count **opposite sides of drift
space**.

| | Curry (P2 Thm 4.2; P1 Thm 4.11) | EOC (P1 Conj 3.1; P3 §7) |
|---|---|---|
| functional | `#{n : g_n ≤ G}` = `#{n : R_n ≥ −G}` | `O_c(m₀) = #{n : R_n ≤ c}` |
| side of `0` | drift **above** a negative floor `−G` | drift **below** a positive ceiling `c` |
| claim for a divergent orbit | **finite**, `≤ c₁2^{βG}(G+c₂)` | **infinite** — and of density one |
| quantifier | one orbit, constants via `y₀Q_∞` | all seeds, `K log₂m₀ + C`, explicit |
| status | proved (given Thm 2.3) | conjectural |

For a divergent orbit both hold simultaneously and are consistent: the drift eventually sits below
every negative level (Curry), hence a fortiori below every positive level (EOC's `O_c = ∞`).

**Why Curry does not prove EOC.** Three independent reasons:

1. **Opposite side.** Curry bounds how often the drift is *shallow* (near or above `0`); EOC
   bounds how often it is *below* `c`. Finiteness of the former says nothing about the latter.
2. **Wrong orbit class.** Curry's hypothesis is divergence, hence aperiodicity. EOC's open core is
   the occupation of orbits that **do** converge — P2 §5 says so explicitly ("nothing here bears
   on the sub-critical occupation of convergent orbits, which is the open core"), and P1
   Remark 4.13 and Open Problem F agree. A terminating orbit is not collision-free (its points all
   merge at 1), so Theorem 2.3 does not apply to it at all.
3. **No uniformity.** EOC needs all seeds with explicit constants; Curry's constants grow with
   `y₀Q_∞` (§F).

**Do they combine into a two-sided description?** Yes, and it is worth having, but it is a
description. For a divergent orbit after restart:

```
                 ⌊ upper: R_N ≤ log₂m₀ + E_∞              (constant ceiling; Curry-upgraded P3 Thm 4.3)
 R_N  confined   ⌊ lower: no eventual floor B log₂N, B < 1/β_*   (Cor 4.3)
                 ⌊ rate:  #{N : R_N ≥ −G} ≤ c₁2^{βG}(G+c₂)       (Thm 4.2)
```

P3 **Remark 7.5** already describes this shape for injective orbits ("its drift profile is
confined between an explicit ceiling and an explicit recurrence"); Curry tightens the ceiling from
`O(log N)` to `O(1)` and replaces the density-one recurrence with `R_N → −∞`.

**The quantitative content, isolated.** How much does Theorem 4.2 beat what distinctness alone
gives? If `R_n ≥ −G` then `m_n ≤ m₀Q_∞2^G` by §L, and the `m_n` are **distinct positive odd
integers**, so trivially

```
#{n : R_n ≥ −G}  ≤  (m₀Q_∞2^G + 1)/2  =  O(2^G).
```

Curry gives `O(2^{βG}G)` with `β > β_*`. **The entire gain is the power saving
`2^{−(1−β)G}`, with `1 − β_* = 0.0346155…`** — and that is exactly what carries the floor
threshold from `B ≤ 1` (Thm 4.1, which needs only summability) past the harmonic barrier to
`B < 1/β_* = 1.0359…` (Cor 4.3). This number is the precise measure of "beyond the harmonic
barrier" in the paper's title.

## N. `β_*` barrier

`β_* = γ_*λ = H(γ_*)` where `γ_*` is the unique root of `H(γ) = γλ` on `(1/2, 1/λ)`. In the proof,
the two cases balance at `γ_*`:

- **heavy** (`m ≥ γN`): entropy count of parity prefixes with `≥ γN` ones, `≤ 2^{NH(γ)} ≈ X^{H(γ)}`.
  `H` is strictly **decreasing** on `(1/2,1)`.
- **light** (`m < γN`): Lemma 2.2 contraction forces `T^N(B₁)` into `< 3X^{γλ}` integers, so
  collision-freeness caps `#B₁ ≤ 3X^{γλ}`. `γλ` is strictly **increasing**.

`max(H(γ), γλ)` is therefore minimized exactly at the crossing, giving `β_*`. `γ_* = r_H` is
Rozier's critical ones-ratio because `H(γ) = γλ` divided by `γ` is his defining equation — the
same entropy-versus-contraction tradeoff.

**Why it cannot be crossed by this method (P2 §5).** Both bounds are sharp *for the hypothesis
class*, so no optimization inside the argument improves `β_*`. Improvement needs either deeper
iteration than `N ≈ log₂X` — which breaks Lemma 2.1, since the bijection `n mod 2^N ↦ prefix`
is exactly `N`-deep and the window `[a, a+X)` only sees `X ≈ 2^N` residues — or an input beyond
parity counting.

**The load-bearing phrase is "for the hypothesis class."** Theorem 2.3 quantifies over **arbitrary
collision-free sets `A`**. An actual accelerated Collatz orbit is vastly more special: its
elements satisfy `2^{s_j}m_j = 3^jm₀ + q_j` and lie in one residue class mod `2^{S_N+1}`
(P1 Prop 5.2). So `β_*`'s sharpness is sharpness against a much larger class than the one we care
about, and it does **not** show `β_*` is the truth for orbits. That is the interface, and it is
where §T.4 and §U live.

**Candidate new inputs, classified** (identifying the interface only, per the brief — no route is
started):

| candidate | assessment |
|---|---|
| **longer-window dependence** (`N ≫ log₂X`) | named by P2 §5 as the first option; blocked by Lemma 2.1's modulus bookkeeping. Would need a replacement for the prefix bijection at depth `N` with only `2^{N}` ≫ `X` residues visible. |
| **actual orbit arithmetic rather than arbitrary collision-free sets** | **the most promising interface.** Uses P1 Prop 5.2's exact congruence, which Theorem 2.3 never touches. §U. |
| **2-adic / 3-adic information** | `3^j` units mod `2^k` already appear in Prop 5.2 and in Lemma 2.1's `r·3^{m_N}`; a genuine 3-adic input (beyond `3` being a unit) is not used by either paper. Unknown. |
| **residue-realizer constraints** | this is P1 Open Problem C/D territory; see §S, §U. Not supplied by Curry. |
| **parity-counting refinements** (mod 3 etc.) | P1 App. D/E prove `8/9` **terminal** for fixed-modulus congruence packing, and Rem 4.12 records that Curry's windowed mechanism is different in kind. So this direction is closed for the packing method. |

## O. Current `CurryFoundation.lean` coverage

Read as source. The file's own header is explicit and accurate: **Curry's Theorem 2.3 is not
formalized**; it "enters here only through the single external interface `ReciprocalSummable`, at
the weakest point that makes it usable".

**The chain does begin in the middle.** Precisely:

```
Thm 2.3  ──────────── NOT FORMALIZED (external, audited-not-cited) ────────────┐
Prop 3.1 ──────────── NOT FORMALIZED; its CONCLUSION is the interface ─────────┤
                                                                               ▼
ReciprocalSummable M := Summable (fun n => 1/(orbit M n))        ◀── entry point (a hypothesis,
   │                                                                  not an axiom)
   ├─► orbit_tendsto_atTop      m_n → ∞
   ├─► carryE_monotone/bddAbove/carryE_tendsto   E_n ↑ E_∞ < ∞
   ├─► carryU_tendsto           Q_n ↑ Q_∞ < ∞
   ├─► two_rpow_R_eq            2^{R_n} = M·Q_n/m_n          (Eliahou–Rozier, reused)
   ├─► R_tendsto_atBot          R_n → −∞                     (Route B of §H)
   ├─► summable_two_rpow_R      Σ 2^{R_n} < ∞
   ├─► exists_last_atBot_max    generic: f → −∞ has a last global max
   ├─► alpha_smul_not_int       kα ∉ ℤ for k ≥ 1             (proved, not assumed)
   ├─► zero_corridor_tail       S'_k ≤ ⌊kα⌋ for all k ≥ 1
   ├─► deficit_nonneg           Δ_k ≥ 0
   ├─► deficit_tendsto_atTop_iff   R'_k → −∞ ⟺ Δ_k → ∞      (bridging iff)
   ├─► beatty_gap_mem           b_k ∈ {1,2}
   └─► deficit_succ / _le       Δ_{k+1} = Δ_k + b − d ; Δ_{k+1} ≤ Δ_k + 1
```

Theorem-by-theorem map (`M` odd, `hrs : ReciprocalSummable M` throughout):

| Lean declaration | statement | assumption is… | source | downstream use |
|---|---|---|---|---|
| `ReciprocalSummable` | `Summable (1/orbit M n)` | **abstracts Curry** (Prop 3.1 conclusion) | P2 Prop 3.1 = P1 Prop 4.9 | everything |
| `orbit_pos` | `0 < m_n` | proved (oddness) | — | positivity side-conditions |
| `orbit_tendsto_atTop` | `m_n → ∞` | proved from `hrs` | §D.2 / Route B | `R_tendsto_atBot` |
| `carryE_monotone` | `E` monotone | proved | P3 Def 2.3 | `carryE_tendsto` |
| `carryE_bddAbove` | `E` bounded above | proved from `hrs` | P2 §3 | `carryE_tendsto` |
| `carryE_tendsto` | `E_n → E_∞` | proved | P2 §3 | `carryU_tendsto` |
| `carryU_tendsto` | `Q_n → Q_∞` | proved | P2 (1) | `R_tendsto_atBot` |
| `two_rpow_R_eq` | `2^{R_n} = M·Q_n/m_n` | proved (reuses `orbit_mul_two_rpow_R`) | P1 Lem 2.2 | `R_tendsto_atBot` |
| `R_tendsto_atBot` | `R_n → −∞` | proved from `hrs` | **not in Curry**; elementary consequence | corridor |
| `summable_two_rpow_R` | `Σ2^{R_n} < ∞` | proved | — | (not used downstream here) |
| `exists_last_atBot_max` | generic last-max | proved, Collatz-independent | §J | corridor |
| `alpha_smul_not_int` | `kα ∉ ℤ` | **proved**, not assumed | — | `beatty_gap_mem` |
| `alpha_lt_two` | `α < 2` | proved | — | `beatty_gap_mem` |
| `zero_corridor_tail` | `∃n₀ ∀k≥1, S'_k ≤ ⌊kα⌋` | proved from `hrs` | §J | `deficit_nonneg` |
| `deficit` | `Δ_k = ⌊kα⌋ − S_k` | definition | §K | — |
| `deficit_nonneg` | `Δ_k ≥ 0` | proved from `hrs` | §K | — |
| `deficit_tendsto_atTop_iff` | `R'→−∞ ⟺ Δ→∞`, **given `hR`** | proved; `hR` must be supplied | §K | — |
| `beatty_gap_mem` | `b_k ∈ {1,2}` | proved | §K | `deficit_succ_le` |
| `deficit_succ` | `Δ_{k+1} = Δ_k + b_{k+1} − d_k` | proved; docstring notes "pure algebra" | §K | closed route |
| `deficit_succ_le` | `Δ_{k+1} ≤ Δ_k + 1` | proved | §K | §K |

**Gap found: `Δ_k → ∞` was not concluded for the actual orbit.** The file proves `Δ_k ≥ 0` and the
equivalence `deficit_tendsto_atTop_iff`, but the `iff` carries a hypothesis `hR` that is never
discharged against the real orbit, so no declaration states `Δ_k → ∞`. Every ingredient was
present. Closed in §W as `deficit_tendsto_atTop`.

**Not formalized, and correctly not claimed:** Theorem 2.3, Proposition 3.1 itself, Theorem 4.1,
Theorem 4.2, Corollary 4.3, `β_*`, and every quantitative rate. The file says so; this audit
confirms it and adds that **no declaration anywhere in the repository mentions `β_*` or the
occupation bound** (§T).

One presentational note: the header cites the interface as "Curry's Proposition 3.1 (manuscript
Proposition 4.9)". Both numbers are right — Prop 3.1 in P2, Prop 4.9 in P1 — but the phrase reads
as if one document had both numberings. Not an error; flagged in §X only as a legibility point.

## P. Current `ZCRERealizerGrowth.lean` coverage

Established equivalence, for a word `d : ℕ → ℕ` with all digits `≥ 1`:

```
bounded prefix realizers  ⟺  positive-integer realizable  ⟺  least realizer eventually constant
```

`boundedPrefixRealizers_iff_positiveRealizer`, plus
`leastRealizer_eventually_constant_of_bounded`, `leastRealizer_eq_mod_of_realizes`
(`leastRealizer d N = m₀ mod 2^{S_N+1}`), `leastRealizer_le_of_realizes`,
`exists_positiveRealizer_of_bounded`. The file's header states it depends on **neither the Curry
foundation nor the zero-corridor sector**, which the source confirms: its only hypothesis is
digit positivity.

**Does the reconstructed Curry profile add any hypothesis ZCRE does not already use?** Candidates
from the brief, each checked:

| candidate | adds independent arithmetic information to realizability? |
|---|---|
| reciprocal summability `Σ1/m_n < ∞` | **no** — a property of the orbit of a realizer that already exists |
| finite `Q_∞` | **no** — same, and `Q_∞ = 2^{E_∞}` is not new data |
| quantitative Curry occupation bound | **no, as currently stated** — its constant `c₁ ≍ C_β(m₀Q_∞)^β` depends on the realizer; see §U |
| `β_*` | **no** — a constant in an external counting argument |
| `D_N < α` eventually | **no** — equivalent to `R_N < 0` eventually (§I) |
| `Δ_N → ∞` | **no** — equivalent to `R_N → −∞` (§K); and `Δ` ⟺ word (§L.1) |
| state scale `m_N ≍ 2^{Δ_N}` | **no** — equivalent to the identity (§L) |

**None of them adds independent arithmetic information, and there is a structural reason, not just
seven separate coincidences.** ZCRE is a question of the form *does there exist a realizer for
this word?* Every item above is of the form *if a divergent orbit exists, then it has property P*.
A statement conditional on the realizer existing cannot be used as a hypothesis to decide whether
it exists — the quantifiers are in the wrong order. This is the sharpest form of the discipline
gate in this audit, and it applies uniformly to the whole Curry package.

## Q. Consolidated divergent-orbit profile

**CONDITIONAL PROFILE.** *Assume Curry's Theorem 2.3 as proved in P2 (audited, not formalized).
Let `(m_n)` be the accelerated orbit of an odd `m₀ > 1` that does not reach `1` and does not
enter a nontrivial cycle. Then:*

| # | property | provenance |
|---|---|---|
| 1 | states pairwise distinct (injective) | P3 Def 2.5 / P1 Lem 4.2 — **proved, trichotomy** |
| 2 | `m_n → ∞` (not merely unbounded) | P3 Def 2.5 — **proved**; Lean `orbit_tendsto_atTop` |
| 3 | value set collision-free | P2 §2 (Garcia–Tal) — **proved** |
| 4 | `Σ_{x∈O} 1/x < ∞`, hence `Σ_n 1/m_n < ∞` | P2 Prop 3.1 = P1 Prop 4.9 — **imported, not formalized** |
| 5 | `Q_n ↑ Q_∞ < ∞` and `E_n ↑ E_∞ < ∞` | P2 (1)+§3 — **proved from 4**; Lean `carryU_tendsto`, `carryE_tendsto` |
| 6 | `R_n → −∞`, i.e. `g_n → +∞` | **new-in-Lean elementary consequence** of 2+5 (§H Route B); Lean `R_tendsto_atBot` |
| 7 | `R_N ≤ log₂m₀ + E_∞` — a **constant** ceiling | Curry-upgraded P3 Thm 4.3 — **cross-paper corollary** |
| 8 | `D_N < α` for all large `N`, strictly | **immediate cross-paper corollary** (§I); Lean `valuationMean_lt_alpha_eventually` |
| 9 | no eventual floor `g_n ≤ B log₂n + O(1)` for any `B < 1/β_* = 1.0359…` | P2 Cor 4.3 = P1 Thm 4.11 — **imported, not formalized**. Endpoint `B = 1/β_*` **not** excluded |
| 10 | `#{n : g_n ≤ G} ≤ c₁2^{βG}(G+c₂)`, `β > β_*`, `c₁,c₂` via `m₀,Q_∞` | P2 Thm 4.2 = P1 Thm 4.11 — **imported, not formalized** |
| 11 | *after restart at the last drift maximum `n₀`:* `S'_k ≤ ⌊αk⌋` for every `k ≥ 1` | **proved & formalized**, `zero_corridor_tail` |
| 12 | `Δ_k ≥ 0` and `Δ_k → ∞` | **proved & formalized**, `deficit_nonneg`, `deficit_tendsto_atTop` (new, §W) |
| 13 | `Δ_{k+1} ≤ Δ_k + 1` — the deficit cannot jump | **proved & formalized**, `deficit_succ_le` |
| 14 | `m₀2^{Δ_k} ≤ m_k < 2m₀Q_∞2^{Δ_k}` | **proved**, §L; explicit constants; *reformulation* |
| 15 | `O_c(m₀) = ∞` for every `c > 0`, on a set of density one | P3 Prop 7.1 (failure of (3)), via P1 Cor 8.16 — **proved**. Subsumed by 6 for divergent orbits |
| 16 | prefix least realizers are **bounded** and eventually constant at `m₀` | **proved & formalized**, `boundedPrefixRealizers_iff_positiveRealizer` |

Properties deliberately **excluded** from this list despite sounding plausible: any statement that
`g_N/N` has a limit; any positive lower bound on `α − D_N`; any uniform-over-seeds constant; any
claim about cycles (P2 §5, P1 Rem 4.13 — outside every hypothesis); any claim about convergent
orbits' occupation (P2 §5: "the open core").

## R. Surviving Type-II behaviors

| | behavior | status |
|---|---|---|
| **A** | `g_N → ∞` extremely slowly but above the excluded floors | **allowed** — the target class. Must eventually exceed `B log₂N` for every `B < 1/β_*` |
| **B** | `g_N ≍ c log₂N` with `c ≥ 1/β_*` | **allowed**; `c = 1/β_*` exactly is the **unexcluded endpoint** (P2 Cor 4.3) |
| **B′** | `g_N ≍ c log₂N` with `c < 1/β_*` | **ruled out** — P2 Cor 4.3 |
| **C** | sublinear power growth, `g_N ≍ N^θ`, `0<θ<1` | **allowed** — no theorem here touches it |
| **D** | linear growth `g_N ≍ cN`, i.e. `D_N → α − c` | **allowed by these theorems** (§I caveat) |
| **E** | `D_N → α` from below (`g_N/N → 0`) | **allowed** — and is the natural shape of A/B/C |
| **F** | `D_N → α − c`, `c > 0` | **allowed**; same as D |
| **G** | highly irregular valuation sequences | **allowed, and barely constrained.** Only `Δ_{k+1} ≤ Δ_k+1` (§K) and `Δ_k ≥ 0` restrict the shape. P1 Rem 5.12 records arbitrary irregular confined words as **open** |
| **H** | recovery-free deficit escape (`Δ` monotone from `n₀`) | **allowed**; not forced. `Δ` may dip, subject to `Δ ≥ 0` |
| **I** | arbitrarily large temporary deficit recoveries | **partially constrained.** A recovery to `Δ ≤ G` can happen at most `c₁2^{βG}(G+c₂)` times in total (P2 Thm 4.2), so recoveries to any fixed depth are finite in number — but their *size* is unbounded and their timing unconstrained |
| — | `limsup D_N > α` | **ruled out** — P3 Thm 4.3 |
| — | `D_N > α` infinitely often | **ruled out** for large `N` (§I) |
| — | `R_N` bounded below | **ruled out** — §H |
| — | eventually periodic valuation word | **ruled out** for a divergent orbit — P1 Thm 5.8/5.9 give realizer floors for periodic and eventually periodic words; also directly, periodicity of the word with `S'_k ≤ ⌊αk⌋` forces linear `Δ` growth with a rational mean, excluded by P1 Thm 5.8's excluded-case analysis |

**Shape of the frontier.** The surviving class is: a divergent orbit whose deficit `Δ_k` climbs to
infinity, by steps of at most `+1`, faster than `(1/β_*)log₂k` but otherwise arbitrarily
irregularly, visiting each depth `G` at most `O(2^{βG}G)` times, with states pinned at
`Θ(2^{Δ_k})`. Nothing in the three papers constrains the irregularity further — which is exactly
P1's Open Problem D ("arbitrary irregular confined words") restated in deficit coordinates.

## S. Weakest missing Type-II exclusion lemma

The brief's candidate **X**, stated precisely:

> **(X)** For every positive odd `m`, some prefix of its valuation word satisfies `S_k > αk`.

Equivalently, in zero-corridor form:

> **(X′)** No positive odd integer realizes an infinite valuation word with `S_k ≤ ⌊αk⌋` for
> every `k ≥ 1`.

**(X) ⟹ no Type-II divergence**, given the three-paper package: a divergent orbit restarted at its
last drift maximum realizes an infinite corridor word (§J, profile item 11), contradicting (X′).
The implication uses Curry only through `R_n → −∞`; nothing quantitative is needed.

**Relation to the repository's existing notions** — equivalences stated only where proved:

| statement | relation to (X′) | proved? |
|---|---|---|
| **ZCRE** (no positive-integer realizer for any infinite corridor word) | **literally (X′)** | definitional |
| **unbounded least prefix realizers** for every corridor word | **equivalent to (X′)** | **proved** — `boundedPrefixRealizers_iff_positiveRealizer`. This is the UPR ⟺ ZCRE collapse |
| **eventual realizer stabilization** fails for every corridor word | **equivalent to (X′)** | **proved** — `leastRealizer_eventually_constant_of_bounded` |
| **P1 Open Problem C** (`r(D) ≥ 2^{εN} − O(1)` for all relevant `c`-confined words) | **strictly stronger than (X′)**: an exponential floor implies unboundedness, not conversely | open; implication is elementary |
| **P1 Open Problem D** (moving-anchor anti-concentration) | P1 calls C–D "in substance the same question at two levels of precision" | open |
| **P1 Open Problem E** (frontier-defect control, `E(D) ≤ H₂(ρ_c)S + Φ(N)`, `Φ = o(N)`) | **relation to C is itself open** — P1 says so explicitly | open |

**On the labels.** The brief asks whether "Open Problem C/E" exist "in this repo revision". They
**do exist in P1 Rev 5** (§15, Open Problems A–G). They do **not** appear in the repository's
`docs/` at commit `1d087e2` — a `grep` for them returns nothing. So the correct statement is: they
are manuscript labels, not repository labels. (An earlier internal round recorded them as
non-existent; that finding was about the repo, and is now refined.)

**So the weakest clean addition is (X′) = ZCRE itself**, and the honest reading is that the
three-paper package reduces Type-II exclusion to a statement the repository had already isolated
as its frontier. Curry does not shrink the gap between (X′) and what is proved; it removes the
*analytic* obstructions (harmonic thinness, the `8/9` barrier) and leaves the *arithmetic* one
(realizer size for irregular confined words) untouched.

## T. Information discarded by the current Curry reduction

**Mandatory section, and the core of Part 2.** The current reduction compresses Curry to
`R_n → −∞` (plus `Q_∞ < ∞`). What is lost, in order of significance:

### T.1 — The quantitative occupation bound (lost at the Lean boundary)

`#{n : g_n ≤ G} ≤ c₁2^{βG}(G+c₂)` with `β > β_*`. Proved in **both** source papers (P2 Thm 4.2,
P1 Thm 4.11) and **absent from the repository entirely** — no declaration mentions `β_*`, the
exponent, or any occupation count. What is lost is exactly the **power saving
`2^{−(1−β_*)G}`, `1−β_* = 0.0346155…`**, over the trivial distinctness count `O(2^G)` (§M). Since
that saving is the sole reason the floor threshold passes `B = 1` to `1/β_* = 1.0359…`, dropping it
discards the paper's headline improvement and keeps only its qualitative shadow.

**Status: genuinely unused.** `R_n → −∞` implies `#{n : g_n ≤ G} < ∞` for each `G`
(now Lean: `occupation_above_finite`) but gives **no rate at all**.

### T.2 — Window-uniformity in `a` (lost in the source papers, one level earlier)

This is the finding the Part 2 target was aiming at, and the answer is not the expected one.

Theorem 2.3's strength is the count in **every** window `[a, a+X)`, uniformly in `a` — that
uniformity *is* Banach density zero. But:

- **Theorem 4.2 uses it only at `a = 1`.** P1 Thm 4.11's proof says so verbatim: "apply
  Theorem 4.8 with `a = 1`, `X = m₀Q_∞2^G`".
- **Proposition 3.1 appears to use general `a`** (dyadic blocks `[2^i,2^{i+1})`), but **does not
  need to**: §G gives a substitute proof using only initial-segment counts `N(X) = #(O∩[1,X))`,
  with the same conclusion.

So **every downstream consequence in both papers factors through the single-parameter function
`N(X)`**, and the uniformity in `a` is never used by anything. It is discarded before the Lean
reduction is even reached, and formalizing T.1 would not recover it.

**Status: genuinely unused — and unused by the papers, not only by us.** This reframes the Part 2
question: the compression to `R_n → −∞` is not where the spatial information is lost.

### T.3 — Universality of `C_β` over collision-free sets

`C_β` depends on `β` alone (§F.A). The papers exploit this only implicitly; the Lean interface
drops it completely, since `ReciprocalSummable` is a bare per-orbit hypothesis with no constant.
**Status: unused**, and the one piece of latent uniformity actually available in the package.

### T.4 — The hypothesis class is far larger than needed

Theorem 2.3 holds for **arbitrary collision-free sets**. We apply it only to orbits, which satisfy
P1 Prop 5.2's exact congruence. P2 §5's sharpness claim is sharpness against the larger class, so
`β_*` is not known to be sharp for orbits (§N). **Status: unused, and the most promising
interface** — it is the only item here that could in principle improve `β_*` rather than merely
be re-imported.

**A refinement of Theorem 2.3 that follows from reading its proof.** Collision-freeness is used
**only once**, in the light case, and **only at `j = N = ⌊log₂X⌋`**: two elements of `B₁` sharing
`T^N(s₁) = T^N(s₂)` are converted to a collision in `A`. The heavy case is a pure entropy count
using no collision hypothesis. Therefore, for each fixed `X`:

> **Theorem 2.3 holds with "collision-free" weakened to "`T^{⌊log₂X⌋}` is injective on `A`".**

For the statement uniform over all `X` this is equivalent to collision-freeness (injectivity of
`T^N` for every `N` *is* collision-freeness), so it is not a strengthening of the uniform theorem.
But **per `X` it is strictly weaker**, and that matters: it lets the bound apply to **finite orbit
segments of orbits not known to be aperiodic**, provided the segment does not merge within
`≈ log₂X` further steps. A terminating orbit's points all merge at `1`, which is why the theorem
is unavailable for them as stated; the refinement makes it available up to the merge. **Status:
genuinely new observation, elementary, not stated in P2.** Its use is discussed in §U.

### T.5 — Collision-freeness of the raw orbit, and the even values

Curry's Prop 3.1 bounds `Σ_{x∈O} 1/x` over the **full** `T`-orbit including even values; the
reduction uses only the odd subsequence `Σ_n 1/m_n`, a sub-sum. The even values roughly double the
point count and are the ones Lemma 2.1's parity prefixes actually track. **Status: unused**;
likely genuinely redundant for drift purposes, since `E_N` is defined on odd iterates only.

### T.6 — The explicit finite form

`6(⌊log₂X⌋+1)(X^{H(γ)} + X^{γλ})`, valid for every `γ ∈ (1/2,1/λ)` with explicit constant `6`.
Only the asymptotic `C_βX^βlog(2X)` shadow is used. **Status: unused**, and the reason the
constants in T.1/T.3 are effective at all.

### Interaction classification (the brief's categories)

| discarded item | can it interact with positive-integer realizability / ZCRE? |
|---|---|
| T.1 occupation rate | **promising interface, currently circular** — §U |
| T.2 window-uniformity in `a` | **obviously redundant** for drift; and already unused by the papers. For realizability: see §U's negative argument |
| T.3 `C_β` universality | **genuinely unused**; would matter only if T.1 were de-circularized |
| T.4 larger hypothesis class / the `j=N` refinement | **promising interface** — the only route to improving `β_*` rather than re-importing it |
| T.5 raw-orbit/even values | **obviously redundant** for the drift chain |
| T.6 explicit constants | **already exploited** in substance (effectivity), unused in form |

## U. Spatial-sparsity / realizer interface

**Is there one? A partial one, and the exact obstruction is identifiable.**

### The negative argument first

Curry's theorem constrains **how many** states lie in a window. Realizability constrains **how
small** the least realizer `r(D)` of a word can be (P1 Prop 5.2:
`r(D) ≡ 2^{S_N} − C_N(D)3^{−N} (mod 2^{S_N+1})`). A sparsity bound cannot lower-bound `r(D)`
directly: sparsity limits cardinality in a window, and `m₀` is a single point, of which there is
always exactly one. No counting bound forbids one point from being small.

Worse, the dependence runs the wrong way. In Theorem 4.2, `c₁ ≍ C_β(m₀Q_∞)^β` **grows** with
`m₀`. So Curry's constraint is *strongest* for small realizers and *weakest* for large ones — the
opposite of what an exclusion argument needs, which is a contradiction from `m₀` being small.

### The one interface that survives

Combining §L and Theorem 4.2 does give a realizer **lower** bound. If a corridor word's deficit
stays shallow for a long time — say `#{n < K : Δ_n ≤ G} = K` — then every such state satisfies
`m_n ≤ 2m₀Q_∞2^G`, and all are distinct, so Theorem 2.3 at `a = 1`, `X = 2m₀Q_∞2^G` gives

```
K  ≤  C_β (2m₀Q_∞)^β 2^{βG} log(2 · 2m₀Q_∞2^G)
```

and therefore, solving for the seed,

```
m₀  ≳  ( K / (C_β Q_∞^β 2^{βG}(G + O(1))) )^{1/β} .
```

**This is a realizer lower bound of exactly the shape Open Problem C asks for** — a word whose
deficit lingers low must have a large realizer. It is derived, not conjectured.

**Why it is currently circular.** Theorem 2.3 requires `A` collision-free, which for an orbit
means aperiodic, which is the divergence we are trying to exclude. Applied to a hypothetical
divergent orbit, the bound constrains an object already assumed to exist; it cannot be used to
show the object does not exist.

**Why T.4 is the plausible way out, stated as an exact interface.** By the refinement in §T.4, the
bound needs only `T^{⌊log₂X⌋}` injective on the state set — not full collision-freeness. For a
**finite** `c`-confined prefix `D` of length `K` with a realizer `m₀` and states bounded by `X`,
this is a *checkable, finite* condition: no two of the `K` states merge within `⌈log₂X⌉` steps.
So the interface to write is:

> **Interface (finite-prefix sparsity ⟹ realizer floor).** Let `D` be a `c`-confined word of
> length `K`, `m₀ = r(D)`, states `m_0..m_{K−1} ≤ X := 2m₀Q_K2^{G}` where
> `G := max_{n<K} Δ_n`. If `T^{⌈log₂X⌉}` is injective on `{m_n}_{n<K}`, then
> `K ≤ 6(⌈log₂X⌉+1)(X^{H(γ)} + X^{γλ})` for every `γ ∈ (1/2,1/λ)`, and hence
> `m₀ ≳ (K/(2^{β G}(G+O(1))))^{1/β}` up to the constants of §F.

Every symbol here exists in the repository: `Confined` (`EOC/Confinement.lean`), `r(D)`/
`leastRealizer` and `realizerCongruence` (`EOC/Realizer.lean`), `s`/`R` (`EOC/ValuationWord.lean`,
`EOC/Confinement.lean`), `deficit` (`EOC/CurryFoundation.lean`). **No declaration currently
consumes a spatial-window bound on actual states** — verified by search; the repository has no
window/interval-count predicate at all. So the interface is writable but unwritten.

**Honest assessment of its prospects, and one caution.** The non-merging hypothesis is not free:
for a confined word whose realizer's orbit terminates, merging is exactly what happens, and the
hypothesis fails precisely in the cases we would want to exclude. Whether "does not merge within
`log₂X` steps" is easier to establish for confined words than ZCRE itself is **unknown**, and it
could easily be equivalent. Classified: **promising interface, unknown whether it is a
reformulation.** It is *not* claimed as a bridge.

### The brief's independence question

*Could two hypothetical accelerated tails have the same `R`/`Δ` profile but radically different
spatial-window behavior?* **No, not radically.** `Δ` determines the word (§L.1), the word plus
`m₀` determines every state, and changing the realizer rescales all states by roughly `m₀′/m₀`,
which translates window behaviour to another scale rather than changing its shape. So spatial
sparsity is **not** independent information beyond `(Δ-profile, m₀)` — which is why T.2 ranks as
redundant and T.1/T.4 (the *rate* and the *hypothesis class*) are where the residual value sits.

## V. New consequences found

Four items, all elementary, each classified against the discipline gate. **No new mathematics of
consequence; no mechanism that excludes divergence.**

1. **`D_N < α` strictly and eventually** (§I). Not stated in any of the three papers.
   **Classification: reformulation** — logically equivalent to `R_N < 0` eventually. P3 Remark 5.2
   predicts exactly this. Formalized (§W).
2. **`R_N ≤ log₂m₀ + E_∞`, a constant drift ceiling** (§I, profile item 7). P3 Thm 4.3 gives
   `O(log N)`; substituting Curry's bounded `E_N` makes it `O(1)`. **Classification: immediate
   cross-paper corollary, reformulation** — it is P3's proof with Curry's input.
3. **Theorem 2.3 needs collision-freeness only at `j = ⌊log₂X⌋`** (§T.4). Not stated in P2; it
   follows from reading the proof, since the heavy case uses no collision hypothesis.
   **Classification: genuinely new observation about the source argument**, elementary, and the
   only item here that is not a coordinate change. Its value is that it widens the hypothesis
   class to finite segments (§U); whether that is usable is unknown.
4. **The whole downstream chain factors through `N(X) = #(O∩[1,X))`** (§G, §T.2), with a substitute
   proof of Prop 3.1 that avoids general `a`. **Classification: genuinely new observation about
   the source argument** — it identifies what the papers actually use, and it is what makes T.2's
   "unused" claim verifiable rather than asserted.

Items 3 and 4 are observations about the *papers*, not about Collatz. Items 1 and 2 are
reformulations. **Nothing found imposes information not already determined by the valuation word
and the orbit recurrence.**

## W. Lean opportunities

| level | content |
|---|---|
| **LEVEL 1 — already formalized** | the whole `ReciprocalSummable → R→−∞ → last max → corridor → Δ≥0` chain; `deficit_succ`, `deficit_succ_le`, `beatty_gap_mem`, `alpha_smul_not_int`; ZCRE's three-way equivalence (§O, §P) |
| **LEVEL 2 — elementary; four items implemented this round** | `deficit_tendsto_atTop`, `valuationMean_lt_alpha_eventually`, `occupation_above_finite`, `eventually_R_lt` — see below |
| **LEVEL 3 — Curry analytic theorem, not formalized** | Theorem 2.3; Prop 3.1 as an implication; Theorems 4.1/4.2, Cor 4.3 and the `β_*` exponent. Thm 4.2 is the one whose *statement* could be added as a second interface without its proof, if the quantitative rate is ever wanted downstream (§T.1) |
| **LEVEL 4 — genuinely difficult** | the parity-prefix/window combinatorics of Thm 2.3 (entropy tail counts, Terras–Everett bijection at depth `N`, the light/heavy split); and the §U interface, which additionally needs a window-count predicate that does not yet exist |
| **inappropriate** | anything asserting a rate from `R_tendsto_atBot`; any uniform-over-seeds constant; anything about cycles or convergent-orbit occupation |

**Implemented: `EOC/CurryDivergenceProfile.lean`** (new, 4 theorems, no `sorry`/`admit`/`axiom`/
`opaque`; axiom check shows only `propext`, `Classical.choice`, `Quot.sound`):

- `deficit_tendsto_atTop` — `∃ n₀, Δ_k → ∞`. Closes the §O gap by discharging
  `deficit_tendsto_atTop_iff`'s hypothesis against the real orbit.
- `valuationMean_lt_alpha_eventually` — `∀ᶠ N, S_N/N < α`. The §I cross-paper corollary.
- `occupation_above_finite` — `{n | −G ≤ R_n}.Finite` for every `G`. The *qualitative* shadow of
  Thm 4.2; its docstring records explicitly that the quantitative `2^{βG}` rate is **not** implied.
- `eventually_R_lt` — `∀ᶠ n, R_n < −G`, the form Route A of §H uses.

None duplicates an existing declaration (verified by search before writing). All are conditional
on `ReciprocalSummable`, exactly as `CurryFoundation` is — **no new interface or axiom was
introduced**, and none of them is a step toward excluding divergence.

**A wiring observation, deliberately not acted on.** `EOC.lean` does not import
`EOC.CurryFoundation` or `EOC.ZCRERealizerGrowth`, so the Curry sector sits outside the aggregate
module at this commit. The new file follows that existing convention rather than changing unrelated
wiring; it is built and verified directly. (A separate branch has already addressed the
index-coverage consequences of this pattern.)

## X. Paper inconsistencies or notation issues

Four items. **None is a mathematical error.**

1. **`g` collides across P2 and P3** — P2's `g_n = nλ − A_n` (unnormalized anti-drift) versus P3
   Prop 5.1's `ĝ_N = (1/N)log₂(m_N/m₀)` (mean growth rate), related by
   `ĝ_N = g_N^{P2}/N + ϵ_N`. **The single most dangerous item in this audit**; §C fixes the
   convention. Recommend P3 rename its quantity (e.g. `ρ_N`) if the two papers are ever read
   together in print.
2. **Cross-numbering of the same result.** Reciprocal summability is Curry's **Prop 3.1**, P1's
   **Prop 4.9**, and the Lean header's "Curry's Proposition 3.1 (manuscript Proposition 4.9)".
   All correct; the parenthetical reads as though one document carried both numbers. Legibility
   only.
3. **`docs/CURRY_FOUNDATION.md` §8.5 attributes the corridor step to irrationality of `α`.**
   Imprecise: integrality of `S'_k` suffices (§J). Already corrected in the Lean source comment;
   the prose doc still carries the older phrasing. *This is a repo-doc issue, not a paper issue.*
4. **"Open Problem C/E" are manuscript labels, not repository labels** (§S). P1 Rev 5 §15 defines
   A–G; the repo `docs/` at `1d087e2` mentions none of them.

No sign errors, no constant mismatches, and no disagreement between P2 and P1's import of P2 were
found. `β_*`, `γ_*`, `1/β_*` and `τ_M` all reproduce to the digits printed (§Z).

## Y. Files changed

```
new:  EOC/CurryDivergenceProfile.lean          4 theorems (Level 2), builds clean
new:  docs/CURRY_DIVERGENCE_PART2_AUDIT.md     this report
```

No existing Lean file was modified; `EOC.lean` was left untouched (§W). **No theorem statement was
changed, no paper or manuscript source was edited** (Gate 20), and no PDF was touched.

## Z. Build/test status

| command | result |
|---|---|
| `lake build EOC.CurryFoundation EOC.ZCRERealizerGrowth` | success, 2051 jobs (baseline, before changes) |
| `lake build EOC.CurryDivergenceProfile` | **success, 2038 jobs, 0 errors, 0 warnings from the new file** |
| `lake build EOC` | success, 8803 jobs |
| `#print axioms` on all 4 new theorems | `[propext, Classical.choice, Quot.sound]` only — no custom axiom |
| grep for `sorry`/`admit`/`axiom`/`opaque` in the new file | none (only the header's prose disclaimer) |

Numerical verification (stdlib Python, no dependencies added; §C, §E):

| quantity | computed | paper |
|---|---|---|
| `λ = log₂3` | 1.5849625007 | — |
| `γ_* = r_H` | 0.6090897679 | 0.6090897 ✓ |
| `β_* = γ_*λ` | 0.9653844417 | 0.9653844 ✓ |
| `H(γ_*)` | 0.9653844417 | `= β_*` ✓ (crossing verified) |
| `1/β_*` | 1.0358567600 | 1.0358567 ✓ |
| `1 − β_*` | 0.0346155583 | the §M power saving |
| `γ_* ∈ (1/2, 1/λ = 0.6309…)` | true | ✓ |

Sign conventions and identities verified step-by-step on the orbits of `m₀ = 7, 27, 703` (to
`10⁻⁹` at every step): `R_n = −g_n`, `R_n = n(D_n − α)`, `m_n = m₀Q_n2^{−R_n}`, `Q_n = 2^{E_n}`.
Per the brief, **no finite trajectory was used as evidence about infinite divergence** — these
checks confirm notation only.

## AA. Commits

Branch `curry-divergence-part2`, from `1d087e2`.

| commit | contents |
|---|---|
| `3492fcc` | `EOC/CurryDivergenceProfile.lean` — the four Level-2 theorems |
| (this file) | this audit report |

## AB. Push status

Branch pushed to `origin/curry-divergence-part2` and tracking. **No pull request opened.** `main`
unmodified; the dirty ordinary checkout on `research-sparse-visits-2026-09-16` left exactly as
found.

## AC. Research verdict

**`CURRY PROFILE COMPLETE; QUANTITATIVE INFORMATION CURRENTLY UNUSED`**

The profile is complete in the sense that matters: §Q lists sixteen properties of a hypothetical
divergent orbit with provenance for each, the chain from Curry's interface to
`Δ_k → ∞` is fully formalized, and this round closed the one place where the Lean library stopped
short of a consequence it had already proved all the ingredients for (`Δ_k → ∞` itself, §O). No
source-level issue was found: P2 is internally sound, P1 imports it faithfully, and the only real
hazard is the `g`-notation collision of §X.1, which is a presentation matter.

The verdict turns on §T.1: **Curry's quantitative content — the occupation bound, its `β_*`
exponent, and the `2^{−0.0346G}` power saving over mere distinctness — is proved in both
manuscripts and used nowhere in the repository.** That saving is the entire reason the floor
exclusion passes the harmonic barrier, so discarding it discards the paper's headline and retains
only its qualitative shadow.

Two findings temper any enthusiasm about recovering it, and they are why the verdict is not
`NEW CROSS-PAPER CONSEQUENCE FOUND`:

- **The window-uniformity was never the prize.** §T.2 shows the source papers themselves use
  Theorem 2.3 only at `a = 1`; §G supplies the substitute proof that makes this checkable. The
  Part 2 hypothesis — that compressing to `R_n → −∞` is where the spatial information is lost — is
  **false as posed**: the spatial content is lost one level earlier, inside Curry's own §3–4, and
  formalizing the occupation bound would not recover it.
- **A conditional description cannot answer an existence question.** §P: every Curry consequence
  has the form *if a divergent orbit exists, then P*, while ZCRE asks *whether* a realizer exists.
  The quantifiers are in the wrong order, which is a structural reason — not seven coincidences —
  that none of the seven candidate hypotheses adds anything to realizability.

What remains genuinely open as an interface is narrower and better-defined than when this audit
started: §T.4's observation that Theorem 2.3 uses collision-freeness **only at `j = ⌊log₂X⌋`**,
which widens its hypothesis class to finite orbit segments and yields the §U realizer floor
`m₀ ≳ (K/2^{βG}G)^{1/β}` — a bound of exactly Open Problem C's shape, currently circular, with the
precise non-merging hypothesis needed to de-circularize it written out. Whether that hypothesis is
easier than ZCRE itself is **unknown**, and it may be equivalent. It is recorded as an interface,
not a route, and no work on it was started.
