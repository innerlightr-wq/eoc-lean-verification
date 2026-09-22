# Curry–realizer window interface

Follow-up to [`docs/CURRY_DIVERGENCE_PART2_AUDIT.md`](CURRY_DIVERGENCE_PART2_AUDIT.md), which found
that the current reduction consumes only the qualitative shadow `R_n → −∞` of Curry's windowed
sparsity theorem, and identified a possible finite interface through the theorem's non-merging
hypothesis.

**Question.** Can Curry's power-saving window count be transferred to finite families of exact
realizers of zero-confined valuation words?

**Answer: no, and the obstruction is upstream of non-merging.**

The first gate settles it. Curry's proof splits on the raw odd-step density `γ`: a **heavy**
branch (entropy count over parity prefixes, no collision hypothesis) and a **light** branch (the
only place collision-freeness is used, and the only source of the spatial power saving). Zero
confinement forces odd-step density `≥ ρ = 1/log₂3 = 0.6309…`, while the crossing sits at
`γ_* = 0.6090…`. So:

> **Zero-corridor words are strictly heavy at every raw depth.** The light branch never engages,
> so the mechanism that produces Curry's power saving never runs, and the surviving bound has
> exponent `H₂(ρ) = 0.949955527…` — which is exactly `1 − I₀/α`, the constant
> `EOC/ExceptionalPowerBound.lean` already proves unconditionally, with explicit constants, and
> without needing collision-freeness at all.

Non-merging turns out to hold automatically on shells (census below, and already proved in P1 §6)
and to be **irrelevant**, because the branch that would use it is never taken. Two further
independent obstructions (§P population-vs-pointwise, §R circularity) block the interface even if
the density inequality had gone the other way.

---

## A. Starting state

| | |
|---|---|
| repository | `~/GitHub/eoc-lean-verification` |
| branch point | `curry-divergence-part2` = `0d7e3edc70708723b87a915396b3edfe6e79ad36` (fetched and verified, not taken from the prompt) |
| new branch | `curry-realizer-window-interface` |
| worktree | isolated; Mathlib shared by read-only symlink |

Ancestry verified — all four required branches are ancestors of the tip:

| branch | commit | relation |
|---|---|---|
| `curry-foundation-zero-corridor` | `5db34a58` | ancestor |
| `zcre-realizer-growth` | `9435bca0` | ancestor |
| `dynamic-deficit-feedback` | `1d087e20` | ancestor |
| `curry-divergence-part2` | `0d7e3edc` | the tip itself |

The ordinary checkout was on `research-sparse-visits-2026-09-16` with **53 dirty files** and was
not touched. `main` (`1c4d6700`) unmodified.

## B. Source basis

**PDFs** (same three files, hashes as recorded in the Part 2 audit §B):

- **P1** De Jesús, *A Global Occupation Conjecture…*, Revision 5, 2026 — §4.2 (Curry import),
  §5.1–5.3 (realizer congruence, single-window equivalence, proved sectors), §6 (computational
  calibration), §8 (Open Problems A–G).
- **P2** Curry, *An Explicit Windowed Sparsity Bound…*, 24 Aug 2026 — Lemmas 2.1–2.2 and the full
  proof of Theorem 2.3, read line by line for §J.
- **P3** De Jesús, *Valuation-Mean Classification…*, July 2026 — Def 2.4, Prop 3.2.

**Repository files read as source:** `EOC/CurryFoundation.lean`, `EOC/CurryDivergenceProfile.lean`,
`EOC/ZCRERealizerGrowth.lean`, `EOC/Realizer.lean`, `EOC/PrefixCollision.lean`,
`EOC/Confinement.lean`, `EOC/ValuationWord.lean`, **`EOC/ExceptionalPowerBound.lean`** (decisive
for §G), `EOC/SurvivorDensity.lean`, `EOC/EntropyBounds.lean`, `EOC/ShellDecomposition.lean`, plus
`docs/CURRY_FOUNDATION.md`, `docs/ZCRE_REALIZER_GROWTH_AUDIT.md`,
`docs/DYNAMIC_DEFICIT_FEEDBACK_AUDIT.md`, `docs/CURRY_DIVERGENCE_PART2_AUDIT.md`.

No new literature search was run (Gate 19).

## C. Raw/accelerated dictionary

| object | raw map `T₀(n) = n/2` (even), `(3n+1)/2` (odd) | accelerated `U(m) = (3m+1)/2^{d(m)}` |
|---|---|---|
| step count | `J` raw steps | `k` accelerated steps |
| relation | `J = S_k` | `S_k = d_0 + … + d_{k−1}` |
| odd steps among the first `S_k` | exactly `k` | one per accelerated step |
| parity word | `1 0^{d_0−1} · 1 0^{d_1−1} · … · 1 0^{d_{k−1}−1}` | `(d_0,…,d_{k−1})` |
| odd-step density | `k / S_k` | — |

Convention: `1` = odd step, `0` = even step. One accelerated step `m ↦ (3m+1)/2^d` is one odd raw
step `m ↦ (3m+1)/2` followed by `d−1` even raw steps, so it contributes the block `1 0^{d−1}` and
exactly one odd iterate, namely `m` itself.

**Verified exactly** (§O): for `m₀ ∈ {7, 27, 703, 26623}` the predicted block concatenation equals
the directly-iterated raw parity word, the length equals `S_k`, and the odd count equals `k`.

**Position bookkeeping, needed in §H.** The odd iterates `m_0, m_1, …, m_j` sit at raw positions
`S_0 = 0, S_1, …, S_j`. Hence for `S_j < J ≤ S_{j+1}` the number of odd iterates among
`n, T₀n, …, T₀^{J−1}n` is exactly `j+1`. This is Curry's `m_N(n)`.

## D. Natural realizer scale

P1 Proposition 5.2: the exact realizers of a word `D` of total valuation `S = S_N(D)` form a
single residue class **mod `2^{S+1}`**, not `2^S`:

```
r(D) ≡ (2^S − C_N(D)·3^{−N})   (mod 2^{S+1}),     C_N(D) = Σ_{j<N} 3^{N−1−j} 2^{s_j}.
```

So the least positive realizer satisfies `r(D) < 2^{S+1}`, and the natural Archimedean window for
a family of such realizers is `[1, X)` with

```
X = 2^{S+1},     J = ⌊log₂ X⌋ = S + 1.
```

Curry's window proof sets `J = ⌊log₂X⌋`, so at the realizer scale **`J = S+1`, one raw step beyond
the accelerated boundary `S`** — not `J = S`. The `+1` is not cosmetic: it changes which iterate is
the last one counted, and §H shows it changes the odd count from `k` to `k+1`. Getting that wrong
manufactures a spurious exceptional range, which is exactly the error §H records.

If instead one takes `X = 2^S` (the coarse anchor modulus, P1 Def 5.4), then `J = S` and the
boundary is aligned. Both cases are covered below, and both are heavy.

## E. Critical density comparison

```
α  = log₂3 = 1.584962500721…
ρ  = 1/α   = log_3 2 = 0.630929753571…
γ_* = 0.609089767924…      the unique root of H₂(γ) = αγ on (1/2, 1/α)
β_* = αγ_* = 0.965384441732…
```

**`γ_* < ρ`, with margin `ρ − γ_* = 0.021839985648`.** Proved without decimals:

- At `γ = ρ` the light exponent is `αρ = α·(1/α) = 1` **exactly**.
- The heavy exponent there is `H₂(ρ) = 0.949955527188… < 1`, because `H₂(p) < 1` for every
  `p ≠ 1/2` and `ρ ≠ 1/2`.
- So `H₂(ρ) − αρ < 0`.
- On `(1/2, 1/α)`, `H₂` is strictly decreasing and `αγ` strictly increasing, so `H₂(γ) − αγ` is
  strictly decreasing; it vanishes at `γ_*` and is negative at `ρ`. Hence **`γ_* < ρ`**.

The certificate `H₂(ρ) < 1` needs no new analysis in this repository: `1 − I₀/α = H₂(1/α)`
(`ExceptionalPowerBound.one_sub_I0_div_alpha_eq`) together with `I₀ > 0`
(`ExceptionalPowerBound.I0_pos'`) gives it in one line. Formalized in §V as
`binEntropy_inv_alpha_lt_one`, so `γ_*` never has to be defined in Lean.

## F. Zero-corridor heavy-regime test

**Proved, and in a stronger form than Gate 17 proposed.**

> **ZERO-CORRIDOR HEAVY-REGIME LEMMA.** Let `D` be a zero-confined accelerated word, i.e.
> `S_j ≤ ⌊αj⌋` for every `j ≥ 1`. Then the raw parity prefix has odd-step density
>
> ```
>       (#odd steps among the first J) / J   ≥   ρ = 1/α   >   γ_*
> ```
>
> **for every raw depth `J ≥ 1`** — not merely at accelerated boundaries — and also at the `+1`
> realizer-modulus depth `J = S_k + 1`. There is **no finite exceptional range**.

*Proof.* Fix `J` and let `j` be the block containing it, `S_j < J ≤ S_{j+1}`. By §C the odd count
is exactly `j+1`, so the density is `(j+1)/J`, which is **decreasing in `J`** across the block and
therefore minimized at the right endpoint `J = S_{j+1}`:

```
density(J)  ≥  (j+1)/S_{j+1}  ≥  (j+1)/(α(j+1))  =  1/α  =  ρ,
```

using zero confinement `S_{j+1} ≤ ⌊α(j+1)⌋ ≤ α(j+1)`. For `J = S_k + 1` see §H. With `γ_* < ρ`
from §E, the density is strictly above the crossing at every depth. ∎

The key structural point is the monotonicity: **a long run of even steps lowers the running
density, but it can only lower it down to the value at the next accelerated boundary**, which
confinement already pins above `ρ`. This is what closes Gate 6 completely (§I).

**Consequence.** Curry's light branch — the only branch using collision-freeness, and the only
source of the `X^{αγ}` power saving — is never the binding branch for a zero-corridor word at any
raw depth. The mechanism cannot be transplanted, because it never runs.

**Scope, stated precisely.** This is a statement about transplanting Curry's *proof* to the
zero-corridor realizer family. Curry's Theorem 2.3 and its `β_*` conclusion continue to apply
unchanged to actual divergent orbits; nothing here weakens them. The divergent-orbit application
is heavy-only too, but there the heavy count is applied to *states* in a window, which is a
different and genuinely useful statement (Part 2 audit §M).

## G. Heavy-branch entropy consequence

Isolating the heavy branch from P2's proof (`m ≥ γJ` case): the elements occupy residue classes
mod `2^J` whose parity prefix has at least `γJ` ones; there are at most
`Σ_{i≥γJ} C(J,i) ≤ 2^{J H₂(γ)}` such classes, and each meets `[1,X]` in at most `X/2^J + 1 ≤ 3`
points. With `J = ⌊log₂X⌋` and the outer factors:

```
#W  ≤  6(⌊log₂X⌋ + 1) · X^{H₂(γ)}.
```

At the density a zero-corridor word actually has we may take `γ = p = k/S ≥ ρ`, and since `H₂` is
decreasing on `(1/2,1)` the exponent is `H₂(p) ≤ H₂(ρ)`. In accelerated units, with `S ≈ αk`:

```
raw-length units:          2^{H₂(ρ) S}
accelerated-depth units:   2^{α H₂(ρ) k},     α H₂(ρ) = 1.505643887946…
entropy deficit:           I_Collatz = α(1 − H₂(ρ)) = 0.079318612775…,  1/I = 12.6073813575…
```

**This is not a new bound. It is the repository's existing constant.**

| source | exponent |
|---|---|
| Curry heavy branch at density `ρ` (this audit) | `H₂(ρ) = 0.949955527188…` |
| `EOC/ExceptionalPowerBound.lean`, title line: *"the baseline power bound `C_U·X^{H₂(1/α)}` for confined seeds"* | `1 − I₀/α = H₂(1/α) = 0.949955527188…` |
| P1 Remark 3.10, "predicted asymptotic slope `1/I(α)`" | `12.6074` vs computed `12.60738136` |

`one_sub_I0_div_alpha_eq : 1 − I₀/α = binEntropy α⁻¹ / log 2` is already a Lean theorem, and
`survivor_count_le_rpow` already proves that odd seeds `μ < X` confined for `⌊log₂X/α⌋` steps
number at most `C_c · X^{1−I₀/α}`.

So the answer to Gate 3 is the third-from-last option, sharpened: **algebraically identical to
existing entropy/shell counting — the same exponent, already formalized.** Worse for the interface,
the repository's version is *stronger in three respects*: it is unconditional (needs no
collision-freeness at all), it has explicit constants, and it applies directly to confined seeds
rather than to an abstract collision-free set.

Nothing is "slightly different" and nothing is genuinely stronger.

## H. `+1` modulus endpoint

At `J = S_k + 1` the raw orbit has passed raw positions `0,…,S_k`. Position `S_k` holds the
terminal accelerated state `m_k`, which is **odd** (P1 Prop 5.2(d), terminal parity). So the odd
count is `k+1`, not `k`, and the density is

```
(k+1)/(S_k+1)  ≥  (k+1)/(αk+1)  >  1/α  =  ρ ,
```

the last step because `α(k+1) = αk + α > αk + 1` for `α > 1`. **This holds for every `k ≥ 0`, with
no exceptional range.** Formalized as `oddDensity_succ_ge_inv_alpha` (§V).

### An error this audit made and corrected

An intermediate step computed `k/(⌊αk⌋+1)` — counting `k` odd steps at raw depth `S_k+1` — and
reported a finite exceptional set `k ∈ {1,2,3,4,6,7,9,12,14}` with the inequality holding only for
`k ≥ 15`, plus a crude closed-form threshold `k > γ_*/(1−β_*) = 17.5958`. **That was wrong**: it
undercounts the odd steps by one, because `m_k` at position `S_k` is itself odd. With the correct
count `k+1` the inequality is strict for all `k`, and the exceptional set is empty. Direct
iteration confirms it (§O): the minimum density over all zero-confined words with `k ≤ 12` and all
raw depths `J = 1,…,S_k+1` is `0.631578947368 ≥ ρ = 0.630929753571`, with **zero** depths at or
below `γ_*`. The brief asked that this endpoint not be handwaved; the first attempt at it was
wrong in exactly the direction that would have invented a false exception.

## I. Non-aligned raw depths

**Zero-corridor words never enter the light regime at any raw depth.** This answers Gate 6's five
questions, but the answers are degenerate because the premise fails.

1. *How large must `d_k` be?* No `d_k` is large enough. Within block `j` the density
   `(j+1)/J` decreases as the even-run proceeds, but its infimum over the block is the value at
   the block's right endpoint, `(j+1)/S_{j+1} ≥ ρ`. A longer even run means a larger `d_j`, which
   raises `S_{j+1}` — and confinement caps `S_{j+1} ≤ ⌊α(j+1)⌋`, so the cap moves with it.
2. *In terms of `Δ_k` and the partial even-run length `t`:* at `J = S_j + 1 + t`,
   `density = (j+1)/(S_j+1+t)`, and `t ≤ d_j − 1`. Light would need
   `S_j + 1 + t > (j+1)/γ_*`, i.e. `J > (j+1)/γ_*`; but `J ≤ S_{j+1} ≤ α(j+1) = (j+1)/ρ < (j+1)/γ_*`.
   The condition is **unreachable under confinement**, for every `Δ_k` and every `t`.
3. *Is entering the light regime equivalent to a large local recovery in `Δ`?* Moot — it cannot be
   entered. Structurally, entering it would require `S_J > J/ρ`, i.e. drift above the corridor,
   which is the negation of zero confinement. So "light" and "zero-confined" are mutually
   exclusive by definition, not by estimate.
4. *Does it reduce to the high-valuation/recovery-block analysis?* No, and it does not need to:
   the exclusion is immediate from the corridor, with no recovery analysis.
5. *Can a light interval persist for more than `O(d_k)` raw steps?* It cannot exist at all.

**Classification: no new information.** The non-aligned analysis produces a strictly stronger
version of the same lemma rather than a new mechanism.

## J. Exact finite Curry hypothesis

Read from P2's proof of Theorem 2.3. Collision-freeness is used **exactly once**, in the light
case, and **only at the single iterate depth `J = ⌊log₂X⌋`**. The heavy case uses no collision
hypothesis whatsoever (it is a pure entropy count over residue classes mod `2^J`).

The light case argues: `T₀^J` maps `B₁` into fewer than `3X^{γα}` integers; if `#B₁` exceeded that,
two distinct `s₁, s₂ ∈ B₁` share `T₀^J(s₁) = T₀^J(s₂)`; since they also share the odd count `m`,
Lemma 2.1 gives `T₀^J(s_i + z'2^J) = T₀^J(s_i) + z'3^m`, so the two corresponding elements of `A`
collide.

**Weakest exact hypothesis.** `B₁` is, by construction, the elements of the window lying in one
common odd-count class, translated by `z'2^J`. By Lemma 2.1 the parity prefix — hence the odd count
`m_J` — depends only on the residue mod `2^J`, so `m_J(y − z'2^J) = m_J(y)`. The needed hypothesis
is therefore:

> **(H_J)** For each `m`, the map `T₀^J` is injective on
> `A ∩ [a, a+X) ∩ {y : m_J(y) = m}`.

That is: *no two window points with the same odd count merge by time `J`.* This is weaker than
injectivity of `T₀^J` on the whole window (which is weaker still than infinite collision-freeness),
and it is the exact condition — the brief asked not to broaden it, and the odd-count restriction is
the part that is easy to broaden away by accident.

For the statement uniform over all `X`, quantifying `(H_J)` over every `J` recovers full
collision-freeness, so this is not a strengthening of the uniform theorem; **per `X` it is strictly
weaker**, which is what a finite application needs.

## K. Bounded multiplicity generalization

Replace injectivity by bounded fibers. Suppose every fiber of `T₀^J` on the relevant set has at
most `M` points. The light case then gives `#B₁ ≤ M · 3X^{γα}` instead of `3X^{γα}`; the heavy case
is untouched. Carrying P2's outer factors (`#B ≥ #W/2` from the two-translate choice, and
`#B₁ ≥ #B/(J+1)` from the odd-count pigeonhole) through unchanged:

```
#W  ≤  6(⌊log₂X⌋ + 1) ( X^{H₂(γ)}  +  M · X^{αγ} )         for every γ ∈ (1/2, 1/α).
```

This is derived from the proof, not assumed; it matches the shape the brief anticipated, with the
constant `C(J) = 6(J+1)` made explicit.

With `M = X^δ` the light exponent becomes `αγ + δ`, and the optimal crossover solves
`H₂(γ) = αγ + δ`, giving exponent `β_*(δ) = H₂(γ_δ)`:

| `δ` | `γ_δ` | `β_*(δ)` | power saving? |
|---|---|---|---|
| 0 | 0.60908977 | **0.96538444** | yes |
| 0.01 | 0.60456713 | 0.96821622 | yes |
| 0.05 | 0.58588741 | 0.97860957 | yes |
| 0.10 | 0.56103750 | 0.98922340 | yes |
| 0.20 | 0.50470353 | 0.99993617 | yes |
| 0.2076 | — | ≥ 1 | **no** |

**Exact threshold.** The crossing leaves `(1/2, 1/α)` when `γ_δ = 1/2`, where `H₂(1/2) = 1`, giving

```
δ_max  =  1 − α/2  =  1 − (log₂3)/2  =  0.2075187496… .
```

So a nontrivial power saving survives **iff `δ < 1 − α/2`**. Regimes:

| `M` | `δ` | exponent |
|---|---|---|
| `O(1)` | 0 | `β_* = 0.9653844` — unchanged |
| `poly(J)` | 0 | `β_*` unchanged (absorbed into the `log` factor) |
| `2^{o(J)}` | 0 | `β_*` unchanged |
| `X^δ`, `δ < 0.2075` | `δ` | `β_*(δ) < 1`, still a saving |
| `X^δ`, `δ ≥ 0.2075` | `δ` | no saving; bound is trivial |

This is a genuinely weaker interface than complete non-merging, and it is generous: multiplicity
may grow like `X^{0.2}` and still leave a power saving. **It does not help here**, because §F puts
zero-corridor words in the heavy branch, where `M` does not appear in the bound at all.

## L. Fixed-word family

**Family A** — all positive integers in the realizer class of one fixed word `D`, total `S`.

By P1 Prop 5.2 this is a single arithmetic progression with modulus `2^{S+1}`. In a window of
length `X` it has exactly `⌊X/2^{S+1}⌋` or that `+1` elements. At the natural scale `X = 2^{S+1}`
that is **1**.

Curry's bound at the same scale gives `6(S+2)·X^{H₂(ρ)} ≈ 2^{0.95(S+1)}·6(S+2)`, which is larger
than the exact count by a factor `≈ 2^{0.05S}`. So Curry's theorem is **enormously weaker than
trivial AP counting** for this family, and it needs a hypothesis (`(H_J)`) that AP counting does
not.

They also share the same raw parity prefix through depth `S`, so `T₀^S` is injective on the family
exactly when the progression's terms have distinct `T₀^S` images — which holds, since
`T₀^S(r + t·2^{S+1}) = T₀^S(r) + t·2·3^k` by Lemma 2.1, an injective affine map in `t`. Terminal
separation is `2·3^k`, so non-merging is free here too, and still useless.

**Closed: trivially sparse, Curry strictly weaker than the exact count.**

## M. Fixed-shell family

**Family B** — one least realizer for each admissible word of accelerated length `k` and total
valuation `S`. This was expected to be the most relevant family. It is also already settled in the
source paper.

**P1 §6 proves shell injectivity** (quoted verbatim):

> *Shell injectivity.* For fixed `(N,S)`, the map `D ↦ ξ_N(D) mod 2^S` is injective across all
> `C(S−1, N−1)` compositions of `S` into `N` parts (a corollary of the collision law of
> Remark 5.12). The shell therefore contains exactly `C(S−1, N−1)` distinct residues among `2^S`
> available positions — **ordinary counting, no collision-driven reduction.**

So:

| quantity | value |
|---|---|
| number of words in the shell | `C(S−1, k−1)` (compositions), fewer under confinement |
| number of distinct seeds | exactly the same — shell injectivity |
| natural `X` | `2^{S+1}` |
| raw length | `S` |
| common odd count | `k` (every word in the shell has the same `k`) |
| fiber multiplicity of `T₀^S` | **1** — see below |
| can two shell words merge to the same terminal state? | **no** |

**Terminal merging (Gate 10).** For `D ≠ D'` with the same `k` and `S`, the carry identity
`2^S m_k = 3^k m_0 + C(D)` gives

```
m_k = m'_k   ⟺   3^k (m_0 − m'_0) = C(D') − C(D).
```

And `T₀^S(r(D)) = m_k` exactly, since `S` raw steps from an odd realizer land on the terminal
accelerated state (§C). So the fibers of `T₀^S` on the shell *are* the terminal-state fibers, and
shell injectivity of the residues plus distinctness of the least representatives makes them
singletons. The census (§O) confirms multiplicity 1 across all 52 shells with `k ≤ 12` — and P1 §6
had already tested this to `S ≤ 30` with shells up to `3.5×10⁷`, far beyond this replication.

**So `M = 1` for free on a shell: the non-merging hypothesis of §J is automatically satisfied.**
And it does not matter, because §F routes the shell into the heavy branch where `M` is absent.
Asymptotically the heavy bound `2^{H₂(k/S)S}` and the exact composition count `C(S−1,k−1)` agree to
leading exponential order — they are the same binomial — so Curry reproduces the count it was
supposed to improve.

## N. Zero-confined family

**Family C** — least realizers of all zero-confined words through depth `k`.

| `k` | `K` = #words | `log₂K / k` | Curry budget `log₂[6(S+2)X^{H₂(ρ)}]` | slack (bits) |
|---|---|---|---|---|
| 8 | 173 | 0.9293 | 18.742 | 11.307 |
| 10 | 961 | 0.9908 | 21.872 | 11.963 |
| 12 | 8045 | 1.0812 | 25.976 | 13.003 |
| 14 | 51033 | 1.1171 | 29.019 | 13.380 |
| 15 | 108950 | 1.1156 | 30.028 | 13.294 |

The budget rate is `α·H₂(ρ) = 1.505644` bits per accelerated step; the observed confined-word
growth at `k = 15` is `1.1156` bits per step. **The family is exponentially smaller than the window
budget**, with the absolute slack growing (11.3 → 13.3 bits over `k = 8…15`).

Two reasons, both structural: the corridor constraint `S_j ≤ ⌊αj⌋` is a ballot-type restriction
that cuts the composition count well below its unconstrained value, and shell injectivity (§M)
means the residues are placed without any collision-driven excess to exploit.

**Consequence: the population bound is satisfied with exponential room, so it cannot yield a
contradiction for this family — even before §P's quantifier objection.** Mixing shells adds
nothing: the union over `S` of shells is still bounded by the same entropy budget, and the observed
total is what the table reports.

## O. Computational collision census

`scratch/curry_window_census.py` — standard library only, deterministic, reproduces every number
quoted in this report.

| section | parameters | result |
|---|---|---|
| raw/accelerated dictionary | `m₀ ∈ {7, 27, 703, 26623}` | predicted `1 0^{d−1}` blocks equal the directly-iterated raw parity word; length `= S_k`; odd count `= k`. All 4 exact |
| realizer congruence sanity | all 313 zero-confined words with `k ≤ 8` | `r(D)` realizes `D` by direct iteration, and `(3^k r + C(D))/2^S = m_k`. **0 mismatches** |
| density at every raw depth | all zero-confined words `k ≤ 12`, depths `J = 1…S_k+1` | min density `0.631578947368`, attained at `k=12, S=19, J=19`; `≥ ρ = 0.630929753571`; **0 depths `≤ γ_*`** |
| shell census | all `(k,S)` shells with `k ≤ 12` — **52 shells**, up to 2652 words | max terminal fiber **1**; max `T₀^S` fiber **1**; shells with a repeated least realizer **0** |
| population slack | `k = 6…15` | table in §N |
| multiplicity exponents | `δ = 0…0.25` | table in §K; `δ_max = 0.2075187496` |

Distribution of fiber multiplicities is degenerate: every fiber is a singleton, so there is nothing
to correlate against periodic words, small realizers, carry gcd structure, or deficit profile. The
"large fiber" conjectures the brief wanted killed early are killed: **no fiber of size `> 1` exists
in this range**, which is consistent with P1 §6's already-proved shell injectivity rather than
evidence for anything new.

**Finite data is used here only to check identities, notation, and already-proved statements. No
inference about infinite behaviour is drawn from it.**

## P. Pointwise-versus-counting barrier

**Mandatory gate, and an independent obstruction.**

Suppose, contrary to §F, that Curry's full bound `K(X) ≪ X^β log X` with `β < 1` did apply to a
family of `K` confined-word realizers all lying below `X`. Inverting:

```
K ≤ C_β X^β log(2X)     ⟹     X ≳ (K / (C_β log 2X))^{1/β}.
```

Since all `K` realizers lie below `X`, this says **some realizer in the family must be large** —
i.e. `max_D r(D)` is large. It says nothing about the minimum.

EOC's single-window form is about the **minimum**. P1 Proposition 5.7 is explicit: `(i) r(D) ≥ 2^{εN}`
**for every** `c`-confined `D`, equivalently `r_min(N,c) ≥ 2^{εN} − O(1)`. A counting bound is a
statement about a population; a realizer floor is a statement about every member. `max` large does
not imply `min` large, and with `K` members below `X` the bound is consistent with one member equal
to `3` and the rest spread out.

Concretely in this setting: §N shows the confined family is *already* exponentially below the
budget, so the inversion yields `X ≳ 2^{1.12k/0.95}` against the actual `X = 2^{S+1} ≈ 2^{1.58k}`
— satisfied, no information extracted, let alone a pointwise floor.

**Can the interface ever become pointwise?** Only by building a separate family around each target
word, so that the target's own realizer being small forces a whole large family into a short
interval. §Q tests every construction available in the repository, and all of them fail. Therefore:

> **CURRY GIVES POPULATION SPARSITY, NOT A POINTWISE REALIZER FLOOR.**

This holds independently of §F. Even if zero-corridor words had been light, this gate would block
the bridge.

## Q. Target-local family attempts

For a fixed target zero-confined word `W` with least realizer `r(W)`, we need a family that is
(1) forced into a short interval by `r(W)` being small, (2) structured enough for `(H_J)`, and
(3) large enough that a power saving contradicts.

| construction | outcome |
|---|---|
| **suffix variations** `W' = W·v` | leaves the shell: `S` grows, so `X = 2^{S+1}` grows with the family. The family is large but the interval grows with it, so (1) fails — no contradiction |
| **prefix-preserving extensions** | same failure, and `PrefixCollision.mem_split` shows confinement couples prefix and suffix only through `σ`, so extensions are unconstrained by `W` itself |
| **shell neighbours** (same `(k,S)`, different word) | (1) fails: by shell injectivity (§M) their residues are spread over `2^S` positions independently of `r(W)`. A small `r(W)` implies nothing about neighbours' realizers |
| **digit flips** `d_i ± 1` | changes `S`, hence the modulus and the interval. Also generically destroys zero confinement — a flip `d_i → d_i − 1` raises all later `S_j`, and near-critical words have no slack |
| **affine-cylinder translations** `r + t·2^{S+1}` | this is Family A (§L): exactly `⌊X/2^{S+1}⌋` points in a window, trivially sparse, and (3) fails since the family has one point at the natural scale |
| **residue lifts** (deeper modulus `2^{S+j}`) | the lifts of one class are an AP with a larger modulus, so the family shrinks as the modulus grows. (3) fails |

Every construction fails at (1) or (3): **either the family is large and the interval grows with
it, or the interval is fixed and the family is a single point.** That trade-off is not accidental —
it is the realizer congruence itself. The family of realizers below `2^{S+1}` for words of total
valuation `S` *is* the shell, whose size is exactly the composition count, and §N shows that count
sits below the entropy budget. There is no room to localize.

No construction was found that keeps the interval fixed while growing the family, so **no
target-local bridge survives.**

## R. Anti-circularity audit

For each candidate bridge: what guarantees `(H_J)` or bounded multiplicity?

| bridge | source of non-merging / multiplicity control | verdict |
|---|---|---|
| Apply Curry to the states of a hypothetical divergent orbit | "these points lie on a divergent orbit" (aperiodic ⟹ collision-free) | **circular** for excluding divergence — this is the Part 2 audit's finding, restated |
| Apply Curry to Family A (fixed word) | Lemma 2.1: `T₀^S(r + t2^{S+1}) = T₀^S(r) + 2t·3^k`, injective in `t` | **non-circular** but useless (§L) |
| Apply Curry to Family B (fixed shell) | **P1 §6 shell injectivity**, a proved finite theorem about `ξ_N(D) mod 2^S` | **non-circular** — derived from independent finite arithmetic (the carry identity), exactly what Gate 14 requires. But the heavy/light routing makes it idle (§F, §M) |
| Apply Curry to Family C (all confined words) | same shell injectivity, shell by shell | **non-circular**, and idle for the same reason; also blocked by §N slack and §P |
| Derive a realizer floor from the inversion | needs "the target word has no small positive realizer" to localize the family | **circular** — assumes the conclusion (§P, §Q) |
| Bounded-multiplicity variant with `M = X^δ` | would need a finite theorem bounding `T₀^J` fibers on the family | **non-circular in principle**; `M = 1` is available free (§M), so the hypothesis is satisfied and still idle |

**The honest summary is unusual and worth stating plainly: the non-merging hypothesis is available
non-circularly, from a proved finite theorem, and it does not help.** The circularity that killed
the Part 2 interface is not the binding obstruction here. The binding obstruction is the
heavy/light routing of §F, with §N and §P as independent backstops.

## S. Open Problem C comparison

P1 Open Problem C, read from Rev. 5 §8 rather than from a repo summary:

> **Open Problem C (Arbitrary-word exponential realizer floor).** Find `ε > 0` with
> `r(D) ≥ 2^{εN} − O(1)` for all genuinely relevant `c`-confined words, not merely periodic,
> eventually periodic, or first-defect words. This is the residue-axis core of EOC
> (Proposition 5.7).

| aspect | Open Problem C | what any finite Curry bound gives here |
|---|---|---|
| quantifier | **every** relevant confined `D` | **some** member of a family is large |
| object | `r(D)`, the least realizer of the target | `max` over a population below `X` |
| shape | exponential in `N` (accelerated length) | power of `X` with exponent `< 1` |
| hypotheses | none beyond confinement | `(H_J)` plus a family construction |

**Relation: no direct implication, in either direction.** Curry's content here is strictly
population-only (§P), and C is pointwise. The inversion

```
m₀  ≳  ( K / (2^{βG}·G) )^{1/β}
```

does appear — §N/§P derive it — but its hypotheses are: a family of `K` distinct realizers, all
below `X = 2m₀Q_∞2^G`, satisfying `(H_J)`, with `β > β_*`. Its conclusion bounds the **largest**
realizer in that family. **It is therefore not a realizer floor**, and calling it one would be the
central error this gate exists to prevent. Additionally §F makes `β` here `H₂(ρ)` rather than
`β_*`, and §N shows `K` is too small for the inversion to bind at all.

## T. Open Problem E comparison

> **Open Problem E (Frontier-defect control).** A weaker target than Open Problem D, suggested but
> not established by §6: `E(D) ≤ H₂(ρ_c)S + Φ(N)` for every `c`-confined `D`, with `Φ(N) = o(N)`.
> Even `Φ(N) = O(log N)` would be valuable. Whether this is a genuinely easier target than Open
> Problem C, or logically equivalent to it, is itself open.

Here `E(D) = S − log₂ r(D)` is the endpoint depth (P1 §6).

**E is already phrased with the same entropy constant `H₂(ρ_c)` that Curry's heavy branch
produces.** That is the sharpest available statement of the relation: Curry's heavy-regime bound is
another expression of the very entropy-depth structure E is about, not an advance on it.

Where Curry falls short of E, precisely:

1. **Quantifier.** E demands the bound for **every** confined `D`; Curry's heavy count bounds a
   population. This is §P again, and it is the whole gap.
2. **The error term.** E's content is entirely in `Φ(N) = o(N)` — the leading term `H₂(ρ_c)S` is
   already what entropy counting predicts. Curry's heavy branch supplies the leading term and a
   `log` factor, i.e. it supplies exactly the part E takes for granted and nothing of the part E
   asks for.
3. **P1 §6 already measured this.** It reports that "the extremal gap `H₂(ρ)S − max_D E(D)` stayed
   bounded rather than growing", across shells to `S = 30`, and concludes: *"bulk entropy, shell
   counting, confinement, and ordinary extreme-value statistics are all consistent with the
   admissible residues behaving like a random injective placement at the population size entropy
   predicts; none of these mechanisms shows evidence of a second exponential rate. **Any successful
   pointwise argument must detect arithmetic information finer than all four.***"

Curry's heavy branch **is** bulk entropy plus shell counting. So P1 §6 had already predicted,
computationally and at larger scale than §O's replication, that it cannot settle E or C.

## U. New theorem/observation

Three items. One is a genuine, elementary, apparently-new cross-paper observation; two are
corrections or derivations.

**1. The zero-corridor heavy-regime lemma (§F).** For every zero-confined accelerated prefix, the
raw odd-step density is `≥ ρ = 1/log₂3 > γ_*` at **every** raw depth, including the `+1`
realizer-modulus depth, with no exceptional range. Hence zero-corridor words lie strictly in
Curry's entropy-heavy regime and the collision/light branch never engages.

Status, against the brief's four options:

- **not** explicit in any of the three papers — P2 never considers confined words, and P1/P3 never
  translate confinement into raw parity density;
- implicit at most in the coincidence that both `β_*` and `I₀` descend from the same entropy
  equation, which P2 §1 notes ("the same entropy equation as his constant, which is reassuring
  rather than surprising") without drawing this consequence;
- **elementary and apparently new as a cross-paper observation**;
- **not** encoded anywhere in the repository before this round — no file mentions `γ_*`, and the
  raw-parity-density view of confinement does not appear.

Its consequence is the useful part: *the branch generating Curry's spatial power saving is not the
mechanism controlling aligned near-critical zero-corridor prefixes.* This is a statement about
transplanting the proof, not about Curry's theorem, which stands.

**2. The bounded-multiplicity window bound and its exact threshold (§K).** Derived from P2's proof:
`#W ≤ 6(⌊log₂X⌋+1)(X^{H₂(γ)} + M·X^{αγ})`, with a nontrivial power saving iff `M = X^δ` for
`δ < δ_max = 1 − α/2 = 0.2075187496`. Not in P2 (which states only the `M = 1` case). A correct
generalization; idle here for the reason in item 1, but it is the reusable form if the light branch
is ever reached in another setting.

**3. The weakest exact finite hypothesis (§J).** `(H_J)`: for each `m`, `T₀^J` is injective on
`A ∩ [a,a+X) ∩ {m_J = m}`. The Part 2 audit stated a broader version (injectivity on the window);
the odd-count restriction is the exact one, and it is strictly weaker.

**Not new, and explicitly credited elsewhere:** shell injectivity and the multiplicity-1 census
(§M, §O) — proved in P1 §6 and tested there at larger scale; the `H₂(1/α)` exponent (§G) — already
`EOC/ExceptionalPowerBound.lean`; the circularity of the divergent-orbit application (§R) — the
Part 2 audit.

## V. Lean formalization

**New file `EOC/CurryHeavyRegime.lean`**, 4 theorems, builds clean, no `sorry`/`admit`/`axiom`/
`opaque`; `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for all four.

| theorem | statement | assumptions |
|---|---|---|
| `oddDensity_ge_inv_alpha` | `0 < S → S ≤ α·k → α⁻¹ ≤ k/S` | zero confinement in real form |
| `oddDensity_succ_ge_inv_alpha` | `0 < S → S ≤ α·k → α⁻¹ < (k+1)/(S+1)` | the `+1` depth, **strict**, no exceptional range (§H) |
| `binEntropy_inv_alpha_lt_one` | `H₂(α⁻¹)/log 2 < 1` | from `one_sub_I0_div_alpha_eq` + `I0_pos'` |
| `heavy_binds_at_inv_alpha` | `H₂(α⁻¹)/log 2 < α·α⁻¹` | the assembled heavy-side comparison |

Design choices, both following the brief's instruction not to introduce analytic machinery for one
audit:

- **`γ_*` is never defined.** The heavy-side certificate is `H₂(ρ) < 1 = αρ`, which follows in one
  line from the repository's own `I₀ > 0` — no intermediate-value theorem, no strict-monotonicity
  development, no root extraction. The step from that certificate to `γ_* < ρ` is the elementary
  monotonicity argument of §E, left in prose because formalizing it would require defining `γ_*`.
- **The density lemmas are stated on reals with `S ≤ α·k`**, not on the raw map. Formalizing "raw
  odd-step density" would require introducing `T₀` and a parity-count function, which the
  repository does not have; the arithmetic content of §F is the inequality, and the raw/accelerated
  dictionary (§C) that turns `k/S` into a density is verified computationally (§O) rather than
  formalized. This is recorded as a limitation, not hidden.

**Deliberately not formalized:** `rho_gt_gammaStar` as such (would need `γ_*`, excluded above);
`finiteCurryLightBound_of_fiberMultiplicity` (§K) — the finite theorem is correct but **idle** by
§F, and the brief says to formalize only genuinely useful results; the shell terminal collision
identity — already proved in P1 §6 and it would duplicate `PrefixCollision` machinery. No
exploratory conjecture was formalized.

`EOC.lean` was left untouched: the Curry sector (`CurryFoundation`, `ZCRERealizerGrowth`,
`CurryDivergenceProfile`) sits outside the aggregate imports at this commit, and the new file
follows that existing convention rather than changing unrelated wiring.

## W. Files changed

```
new:  EOC/CurryHeavyRegime.lean                    4 theorems (heavy-regime lemma + certificate)
new:  scratch/curry_window_census.py               reproducible census, stdlib only
new:  docs/CURRY_REALIZER_WINDOW_INTERFACE.md      this report
```

No existing Lean file modified. No theorem statement changed. No PDF or manuscript source edited.

## X. Tests

| command | result |
|---|---|
| `lake build EOC.CurryHeavyRegime` | **success, 2257 jobs, 0 errors** |
| `lake build EOC.CurryDivergenceProfile EOC.ZCRERealizerGrowth` | success, 2052 jobs (no regression) |
| `#print axioms` × 4 new theorems | `[propext, Classical.choice, Quot.sound]` — no custom axiom |
| grep `sorry`/`admit`/`axiom`/`opaque` in new file | none (header prose aside) |
| `python3 scratch/curry_window_census.py` | exit 0; reproduces every number in §E, §G, §K, §N, §O |

Numerical verification (stdlib only, no dependency added):

| quantity | computed | cross-check |
|---|---|---|
| `α = log₂3` | 1.584962500721 | — |
| `ρ = 1/α` | 0.630929753571 | brief states 0.63092975 ✓ |
| `γ_*` | 0.609089767924 | P2 states 0.6090897 ✓ |
| `β_* = αγ_*` | 0.965384441732 | P2 states 0.9653844 ✓ |
| `ρ − γ_*` | **0.021839985648** | `> 0`, the decisive margin |
| `H₂(ρ)` | 0.949955527188 | `= 1 − I₀/α`, repo constant ✓ |
| `α·H₂(ρ)` | 1.505643887946 | budget rate, bits/step |
| `I₀ = α(1−H₂(ρ))` | 0.079318612775 | — |
| `1/I₀` | 12.6073813575 | P1 Rem 3.10 prints 12.6074 ✓ |
| `δ_max = 1 − α/2` | 0.2075187496 | §K threshold |
| min density, all `k ≤ 12`, all raw depths | 0.631578947368 | `≥ ρ` ✓, 0 depths `≤ γ_*` |
| max terminal fiber, 52 shells | 1 | matches P1 §6 shell injectivity ✓ |

## Y. Commits

Branch `curry-realizer-window-interface`, from `0d7e3ed`.

| commit | contents |
|---|---|
| `2d3704a` | `EOC/CurryHeavyRegime.lean` + `scratch/curry_window_census.py` |
| (this file) | this audit report |

## Z. Push status

Branch pushed to `origin/curry-realizer-window-interface` and tracking. **No pull request opened.**
`main` unmodified; the dirty ordinary checkout on `research-sparse-visits-2026-09-16` left exactly
as found.

## AA. Research verdict

**`CURRY LIGHT BRANCH DOES NOT TOUCH ZERO-CORRIDOR REALIZERS`**

The brief's stated success condition is answered in the affirmative, and it is the decisive fact:
`ρ = 1/log₂3 = 0.6309…` exceeds `γ_* = 0.6091…`, so zero confinement `S_j ≤ ⌊αj⌋` puts the entire
near-critical realizer sector strictly on Curry's entropy-heavy side — at **every** raw depth, not
only at aligned accelerated boundaries, and including the `+1` realizer-modulus depth with no finite
exceptional range (§F, §H, §I). The light branch is the only place collision-freeness is used and
the only source of the spatial power saving, so the mechanism cannot be transplanted because it
never runs.

This explains structurally what the Part 2 audit observed empirically: Curry's theorem dramatically
improves divergent-orbit **drift** control while leaving the moving-anchor/pointwise **realizer**
problem untouched. The two applications land in different branches of the same proof. Against
states of a divergent orbit the window bound is applied at a density that is not pinned by
confinement; against realizers of confined words the density is pinned above `ρ`, and the bound
degenerates to entropy counting.

The surviving heavy bound is not merely "like" existing work: its exponent is `H₂(ρ) = 1 − I₀/α`,
**the same constant `EOC/ExceptionalPowerBound.lean` already proves** — unconditionally, with
explicit constants, and needing no collision-freeness (§G). So `EQUIVALENT TO EXISTING
ENTROPY/REALIZER BARRIER` is also true and is the immediate corollary; the light-branch verdict is
chosen because it names the mechanism and implies the equivalence.

Two further obstructions hold independently, so the route would fail even if the density inequality
had gone the other way:

- **§P, population versus pointwise.** Any window count bounds a population, hence the *largest*
  realizer in a family; Open Problems C and E are about the *least* realizer of a *given* word. And
  §N shows the confined family is exponentially below the entropy budget (1.12 vs 1.51 bits per
  accelerated step, slack growing), so the inversion does not even bind.
- **§Q, no localization.** Every target-local construction available in the repository either grows
  the interval with the family or shrinks the family to a point — a trade-off that is the realizer
  congruence itself, not an accident of the constructions tried.

One finding cuts against the expected narrative and is worth recording: **non-merging is not the
obstruction.** It holds automatically on shells with multiplicity exactly 1 (§M, §O), it is
available non-circularly from P1 §6's proved shell injectivity, and the bounded-multiplicity
generalization (§K) is generous enough to tolerate `M = X^{0.2}`. All of that is idle. The Part 2
audit nominated non-merging as the interface to watch; this round finds the hypothesis satisfiable
and the interface closed one gate earlier.

Finally, P1 §6 had already reached the same conclusion computationally at larger scale, and stated
the requirement this round confirms: *"any successful pointwise argument must detect arithmetic
information finer than"* bulk entropy, shell counting, confinement, and extreme-value statistics.
Curry's heavy branch is the first two of those four.
