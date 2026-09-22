# Positive-orbit confinement lifetime audit

Actual integer dynamics, launch renormalization, and corridor-uniform escape.

## A. Starting state

| item | value |
|---|---|
| base commit | `171995cb5cc21f1d9ea174f877a38051a4657753` (`Record commit hash and push status in the audit report`) |
| verified how | `git fetch origin`, then `git rev-parse origin/global-single-orbit-nonlocal-separation-audit` |
| ordinary checkout | **dirty** (53 entries). Not touched. |
| worktree | isolated, `scratchpad/eoc-lt`, `.lake/packages` symlinked |
| branch | `positive-orbit-confinement-lifetime-audit` |
| `main` | untouched. No PR. |

## B. Launch-renormalization source

`~/Downloads/launchRenormalization.pdf` (two byte-identical copies), sha256
`5e9048db7d1f7b951460f89995bbaaed0062a4be7fa39ce73767e3409a4582a6`; extracted text `LR.txt`,
1044 lines, sha256 `277008cff006aefc7caf3728613a1e33dcf10fa3f763449fd0eed76cc0065f26`. Read in full.

Imported exactly (quantifiers as stated in the note):

| result | content |
|---|---|
| Thm 5.3 | `F_N = F_{t1} + Q_N`, `Q_N = S_N − S_{t1}`, and `0 < F_{t1} < d_{t1}` when `τ_N ≥ 1` |
| Thm 5.4 | `T_j = −m*_j 3^{−j}` for `2^{S_j} > r(D)`, with `m*_j = (3^j r(D) + C_j)/2^{S_j}` the **genuine** `j`-th accelerated iterate; the letters after `j` are exactly the accelerated valuation word of `m*_j` |
| Prop 6.3(a) | `ε`-danger forces `β_N = 1`, so `r(D) = χ_N` |
| Prop 6.3(b) | `t_1 ≤ εN + 1`, `Q_N > S_N − εN − d_{t1}` |
| Prop 6.3(c) | `R_{t1} ≥ (1−α)t_1 > −(α−1)(εN+1)` |
| Prop 6.3(d) | `log₂ m*_{t1} ≤ αεN + 19log₂N + O(1)` — leading coefficient `αε`, **not** `ε` |
| Prop 9.1, Cor 9.4 | renormalization stability; finite structural enumeration cannot close the program |
| Prop 11.1 | `c' = c − R_{t1} ≤ c + (α−1)(εN+1) = Θ(εN)`; relative `c'/L ≤ (α−1)ε/(1−ε) + o(1)` |
| Def 11.2 | `U_all(K)`: for every odd `m ≥ 3` and every `A ≥ 1`, every injective initial orbit segment of `m` with `R_i(m) ≤ A` for `0 ≤ i ≤ L` has `L ≤ K(log₂ m + A)`. `U_half(K,q₀)`: the same, assumed only for segments whose exact terminal repetitions of period `≤ q₀` (with `≥ 3` repeats) each cover at most half the segment |
| Prop 11.3 | `U_all(K)` ⟹ no `ε`-dangerous `c`-confined word of length `N ≥ N₁`, for every `ε < ε₀(K) = 1/(1+(2α−1)K)`; `2α−1 = 2.1699…`; at `K ≈ 12.61`, `ε₀ ≈ 0.0353` |
| Remark 11.4, 9.5 | the residual problem is *at least as demanding* as the fixed-corridor original |

## C. Current lifetime definition (Gate 0)

For odd `m ≥ 3`, the accelerated orbit is `m_0 = m`, `2^{d_{i+1}}m_{i+1} = 3m_i + 1`,
`S_i = Σ_{j≤i}d_j`, `R_i = S_i − iα`, `α = log₂3`. Note `R_0 = 0`: the drift in Def 11.2 is
measured **from the launch point**, so for the renormalized daughter problem the corridor is the
*relative* one. `L(m,A)` is the largest `L` such that `m_0,…,m_L` are distinct and `R_i ≤ A` for
`0 ≤ i ≤ L`.

Absolute versus relative matters exactly once, in Prop 11.1: the parent's fixed corridor `c`
becomes the daughter's `c' = c − R_{t1}`, which is `Θ(εN)`. All statements below use the relative
normalization of Def 11.2.

## D. Dangerous-word to lifetime bridge (Gate 1)

Reproved against the current repo conventions (which agree with the note's):

```
ε-dangerous c-confined D_N   ⟹   β_N = 1, r(D) = χ_N            (Prop 6.3a)
                             ⟹   t₁ ≤ εN + 1                     (Prop 6.3b)
                             ⟹   log₂ m*_{t1} ≤ αεN + 19log₂N + O(1)   (Prop 6.3d)
                             ⟹   L ≥ (1−ε)N − 1                  (suffix length)
                             ⟹   A = c' ≤ c + (α−1)(εN+1)        (Prop 11.1)
```

The ratio the hypothesis must beat is therefore

```
L / (log₂ m* + A)  ≥  (1−ε)N / ((2α−1)εN + O(log N))  →  (1−ε)/((2α−1)ε).
```

At `ε = 0.0353` this is `0.9647/(2.1699·0.0353) = 12.6`, which is exactly the paper's `K ≈ 12.61`.

**A sharper framing: the whole route turns on one classical constant.** Eliminating `A` via
Prop 6.3(d) and the suffix length, danger requires

```
L / log₂ m*  ≥  (1 − ε)/(α ε)          ( = 1.369·K at ε = ε₀(K) ).
```

So writing `S := sup { L / log₂ m : injective accelerated segment }`, the contrapositive is

> **If `L ≤ S·log₂ m` for every injective accelerated orbit segment, then no `ε`-dangerous
> `c`-confined word exists for `ε < 1/(1 + αS)` — an exponential realizer floor with that `ε`.**

| `S` | resulting `ε` |
|---|---|
| 13.77 | 0.0438 |
| 15.42 | 0.0393 |
| 17.59 | 0.0346 |
| 25 | 0.0246 |

**Any finite `S` gives a nonvacuous `ε`** — there is no threshold to beat, only the correspondence
`S ↦ ε = 1/(1+αS)`. (An earlier draft of this section wrongly presented `S ≤ 17.26` as a threshold;
it is merely the `S` whose image is the paper's `ε₀(12.61) = 0.0353`.)

**`S` is a classical quantity, and the record table converts exactly.** Lagarias's total stopping
time `σ∞(n)` counts *even* steps, i.e. `σ∞ = S_L` in this audit's notation, while `L` counts *odd*
steps; `γ(n) = σ∞(n)/ln n` (natural log). Since `S_L = αL + R_L` and `R_L = log₂m + E` (§AA),

```
S = L/log₂ m  =  (γ·ln2 − 1 − E/log₂m)/α .
```

Checked against the verified record table (§AS):

| `n` | `σ∞` | `γ` | ⇒ `L` | ⇒ `S = L/log₂m` |
|---|---|---|---|---|
| 27 | 70 | 21.2389 | 41.2 | 8.66 |
| 63,728,127 | 592 | 32.9435 | 357.2 | **13.78** |
| 1.049·10¹⁷ | 1404 | 35.8238 | 850.2 | 15.04 |
| 7.219·10²¹ | 1848 | 36.7169 | 1120.1 | **15.43** |

The conversion reproduces this audit's own computed `L = 357` at `n = 63{,}728{,}127` exactly, which
cross-validates both.

## E. General sufficient lifetime scale (Gate 2)

Substituting `log₂m = Θ(αεN)`, `A = Θ((α−1)εN)`, `L = Ω((1−ε)N)`:

| `F(x,A)` | contradiction? |
|---|---|
| A. `K(x+A)` | **yes**, for `ε < 1/(1+(2α−1)K)` — the paper's case |
| B. `Kx + K_A A` | **yes**, for `ε < 1/(1 + (Kα + K_A(α−1))ε)`-type threshold; same shape |
| C. `o(x+A)` | **yes**, trivially — but no such statement is remotely plausible (§AI) |
| D. `(x+A)log(x+A)` | **no** — gives `L ≲ εN·log N`, which exceeds `(1−ε)N` for large `N` |
| E. `(x+A)^θ`, `θ>1` | **no** — `(εN)^θ ≫ N` |
| F. `Kx + o(A)` | **yes** — `A`'s linear term is what costs; killing it lowers the threshold to `ε < 1/(1+αK)` |

So only bounds **linear or sublinear in `x+A`** are useful. Anything with an extra `log` factor
already fails. This is a narrow target.

## F. Anti-tautology test (Gate 3)

Is `U_all` at fixed `A` a repackaging of the least-realizer floor? **No** — and §AA shows it is
something quite different, and independently identifiable. That is the one genuinely good news in
this audit: the launch route does *not* close a circle.

But §AA also shows the hypothesis is far stronger than a corridor statement, which is the bad news.

## G. Trivial injectivity bounds (Gate 4)

Injectivity alone gives: if all `m_i ∈ [1,M]` then `L ≤ (M+1)/2` (distinct odd values). Confinement
does **not** bound `m_i` above — see §H. The exact relation available is the aggregate identity

```
2^{S_i}·m_i = 3^i·m_0 + C_i          (Lean: aggregate_identity, verified 29,999 seeds)
```

equivalently `m_i 2^{R_i} = m_0 Q_i` with `Q_i = Π_{j<i}(1 + 1/(3m_j)) ≥ 1`.

## H. One-sided corridor issue (Gate 5) — stated early as instructed

The confinement condition is `R_i ≤ A` only. `R_i` may dive arbitrarily negative, and one step can
lower it by at most `α−1 = 0.58496` (since `d ≥ 1`), so deep dives are permitted and merely cost
time. Since `log₂ m_i = log₂ m − R_i + E_i`, a deep negative excursion of `R` corresponds to
ordinary values growing **exponentially**, entirely inside the corridor.

> **Ordinary orbit size is essentially unrestricted by a one-sided corridor.**

The problem is *not* silently replaced by `|R_i| ≤ A` anywhere in this audit.

## I. Orbit-floor consequences (Gate 6)

Writing `E_i = log₂ Q_i ≥ 0`:

```
log₂ m_i = log₂ m − R_i + E_i          (verified, 0 violations over 29,999 seeds)
```

Under `R_i ≤ A` this gives only `log₂ m_i ≥ log₂ m − A`: a **lower** bound. No upper bound on `m_i`
follows, because `E_i ≥ 0` and `R_i` is unbounded below. This is exactly why injectivity counting
cannot work, and it is the precise form of §H.

## J. Curry finite-window interface (Gate 7, 8)

Curry's statements apply to an actual divergent positive orbit. Of the consequences available:

| statement | usable for a finite injective segment? |
|---|---|
| `Σ1/m_n < ∞` | asymptotic, for full divergent orbits; a finite-segment version gives only `Σ_{i≤L}1/m_i ≤ L/m_0` (wrong direction, §P) |
| `Q_n → Q_∞ < ∞` | needs the infinite orbit |
| occupation `#{n : R_n ≥ −G} ≪ 2^{βG}G` | a statement about *drift levels*, i.e. a word shadow (previous branch) |
| orbit-set Banach density zero (Garcia–Tal) | spatial, qualitative |

The one shape that would matter is a **uniform finite-window spatial bound** —
`#{orbit values in [x, x+X)} ≤ C X^β log 2X` valid for *any* collision-free segment. §K measures
what such a bound would buy even if granted.

## K. Spatial sparsity to max-state growth (Gate 9)

Grant the strongest plausible form: `L` distinct orbit values below `X` forces
`L ≤ C X^β log X`, hence `X ≳ (L/(C log L))^{1/β}` — **polynomial in `L`**.

Combined with the orbit-floor identity, a large `max m_i` means a deep negative `R` excursion, not
a violation of `R_i ≤ A`. So sparsity forces the orbit *upward*, which the one-sided corridor
permits. §T does the numbers.

## L. Large-excursion escape hatch (Gate 10) — this is what kills the route

```
R_i dives negative  →  m_i grows exponentially  →  spatial sparsity satisfied  →  no contradiction.
```

The corridor constrains only the ceiling; the orbit escapes through the floor. Returning from depth
`−G` to near the ceiling costs no more than **one** step, because `d` is unbounded above (§N).

## M. Drift excursion cost (Gate 11, 12)

Exact asymmetry, both directions:

- **Downward is bounded per step**: `ΔR_i = d_i − α ≥ 1 − α = −0.58496`, so reaching depth `G`
  below the start requires at least `G/(α−1) = 1.7095·G` accelerated steps.
- **Upward is unbounded per step**: `d` has no fixed upper bound, so recovery can occur in one step.

**But the asymmetry points the wrong way.** `G/(α−1)` is a *lower* bound on the number of steps —
it says a deep excursion takes time, which *lengthens* the lifetime. It cannot be used to bound `L`
above. Recorded because it is easy to mistake for leverage.

## N. Large-valuation recovery (Gate 13)

The one genuinely orbit-level inequality: from `2^{d_i}m_{i+1} = 3m_i + 1` and `m_{i+1} ≥ 1`,

```
2^{d_i} ≤ 3m_i + 1          (Lean: valuation_le; verified, 0 violations)
```

so `d_i ≤ log₂(3m_i+1)`. A symbolic word has no such constraint — this passes Gate 44.

Its consequence is §AA: `ΔR_i ≤ log₂(3m_i+1) − α ≈ log₂ m_i`, and substituting the orbit-floor
identity gives `R_{i+1} ≤ log₂ m + E_i`. That is the automatic corridor.

## O. Amortized orbit potential (Gate 14)

Attempted: a potential in `log₂ m_i`, `R_i`, `E_i`, `log(3m_i+1)`. Every combination tried collapses
to the orbit-floor identity `log₂ m_i + R_i − E_i = log₂ m`, which is an identity, not a potential.
The previously closed transport `H` potential was not reused.

**Closed immediately, per the gate's own instruction.** No potential survives that is not the
identity in disguise.

## P. Reciprocal mass (Gate 15, 16)

`m_i = m 2^{−R_i}Q_i` with `Q_i ≥ 1` gives `1/m_i ≤ 2^{R_i}/m` — an **upper** bound on reciprocal
mass. A lower bound needs an upper bound on `Q_i`, i.e. on `E_i`; for an injective orbit the values
are distinct odd integers so `Σ_{j<i}1/m_j ≤ Σ_{k<i}1/(m_0+2k) = O(log i)`, giving
`E_i = O(log i)` with the small constant `1/(6ln2) = 0.2404`. Measured: `max E ≤ 0.27` across all
29,999 seeds tested.

So `1/m_i ≥ 2^{R_i}/(m·2^{E_i})` with `E_i` tiny — but `R_i` can be very negative, so the terms are
tiny and no useful lower bound on `W_L = Σ_{i≤L}1/m_i` follows. **No lower estimate on reciprocal
mass exists here.**

## Q. Near-ceiling occupation (Gate 17)

Nothing in the confinement condition forces returns toward `A`. A segment may spend all its time at
very negative `R`. The abstract words illustrating this are exactly the previous branch's
uncountable family, and §AG confirms that no argument in this audit would distinguish them.

## R. Monotone deep-drift possibility (Gate 18)

`R_i ≈ −γi` for long stretches gives `m_i ≈ m 2^{γi}Q_i`, ordinary exponential growth. Fully
compatible with the growth envelope of §S as long as `γ ≤ α−1`. **No known result excludes it**, and
this is exactly what a hypothetical Type-II orbit would do.

## S. Maximal forward ordinary growth (Gate 19, 20)

Exact, and proved:

```
2^n (m_n + 1) ≤ 3^n (m_0 + 1)          (Lean: growth_envelope; verified, 0 violations)
```

i.e. `m_n ≤ (3/2)^n(m_0+1) − 1`, `log₂ m_n ≤ log₂(m_0+1) + n(α−1)`. The per-step rate ceiling is
`α − 1 = 0.584963`.

## T. Curry exponent versus growth rate (Gate 21, 53) — the stop test fires

| `L` | sparsity forces `X ≳` | growth allows `X ≤` |
|---|---|---|
| 100 | `10^{2.1}` | `10^{18}` |
| 1,000 | `10^{3.1}` | `10^{176}` |
| 10,000 | `10^{4.1}` | `10^{1761}` |

(`β = 0.9654`; `β = 0.99` gives the same picture.) Polynomial lower bound against exponential upper
bound, with the margin **widening** with `L`.

Gate 53's clean stop test: a spatial-sparsity argument would have to force ordinary growth at a
per-step log₂ rate exceeding `α−1 = 0.585`. Sparsity forces rate `(1/β)·log₂L/L → 0`. It is not
close, and cannot be made close.

## U. Dyadic shell decomposition (Gate 22, 23)

Shell membership `m_i ∈ [2^k,2^{k+1})` translates to `−R_i + E_i ∈ [k − log₂m, k+1 − log₂m)`. Since
`E_i` is tiny, shells correspond to drift levels. But `R_i` is not monotone — `Δlog₂m_i = α − d_i`
and a single large `d_i` collapses `m_i` by an arbitrary factor — so shells are revisited freely.
No constrained crossing order exists. **Closed.**

## V. Record maxima / minima (Gate 24, 25, 35, 36)

Measured over 29,999 seeds: **the orbit minimum is at the final index in 29,999 of 29,999 cases.**
Every convergent orbit ends at `m = 1`, which is its minimum, so Gate 36's position `h` equals `L`
and **branch B always holds**: there is no tail after the minimum.

Consequently the "restart at the daughter's internal minimum" mechanism (Gate 35) is **vacuous for
every actual orbit** and is meaningful only for a hypothetical divergent orbit, where it cannot be
computed. This was the gate flagged as potentially highest-value; it is empty.

## W. Escape-or-recurrence dichotomy (Gate 26)

The dichotomy can be stated — a long injective confined segment either recurs in a bounded ordinary
window or makes a large excursion — but branch 2 is not obstructed (§L, §T), so the dichotomy does
not close. It is not presented as a result.

## X. Large-excursion branch (Gate 27)

`m_j ≥ m2^G` gives `−R_j ≥ G − E_j`: a large ordinary excursion *is* a deep negative drift. The
suffix after such a point is a new launch-renormalized problem with a corridor widened by `G`. So
this branch reproduces the note's renormalization stability (Prop 9.1, Cor 9.4) exactly, and adds
nothing.

## Y. Iterated launch renormalization (Gate 28)

Candidate decreasing resources across `(m^{(k)}, A_k, L_k)`: `m` itself, bit length, minimum orbit
value, count of states below the original launch value. **None decreases monotonically.** The note's
§10 already proves the envelope is non-contracting and that parameter contraction is impossible;
this audit adds only §V's observation that the minimum-reset route is empty.

## Z. Launch integer descent (Gate 29)

Checked against the exact statement. Prop 6.3(d) gives `log₂ m*_{t1} ≤ αεN + 19log₂N + O(1)`, i.e.
`m*` is small **relative to `N`** — it is bounded by roughly `2^{αεN}` while the remaining suffix has
length `≥ (1−ε)N`. It is **not** claimed, and does not follow, that `m* < r(D)`: `r(D) < 2^{εN}`
while `m*` may be as large as `2^{αεN}`, and `α > 1`. **So the launch integer can be larger than the
realizer.** Any descent argument must not assume otherwise.

## AA. Type-II minimum normalization (Gate 31, 32) — mandatory gate

For an orbit restarted at its minimum, `m_i ≥ m_0`, so the orbit-floor identity gives `R_i ≤ E_i`
with `E_i = O(log i)`. But the audit found something stronger and unconditional:

> **The corridor bound is automatic for *every* positive orbit, minimum-normalized or not.**

From `m_i ≥ 1` alone and the aggregate identity,

```
2^{S_i} ≤ 3^i·m_0 + C_i        (Lean: corridor_automatic)
```

i.e. `R_i ≤ log₂ m_0 + E_i`. And it is **attained**: as soon as the orbit reaches `1`, the
inequality is an equality (`corridor_attained`). Measured across 29,999 seeds, the least valid
corridor width satisfies

```
A  =  log₂ m + E      exactly     (mean, max and min of (log₂m + E) − A all 0.000000).
```

## AB. Minimum-seed corridor: known or new? (Gate 33)

The repository contains carry bounds and floor-exclusion results but no statement of the automatic
corridor in this form; the launch note treats `A` as a hypothesis parameter throughout. The
underlying ingredients (`m_i ≥ 1`, the aggregate identity) are entirely standard, so the
*observation* is elementary — but its consequence, §AK, does not appear anywhere in the repository
or the note, and it changes how `U_all` should be read.

## AC. Daughter internal minimum (Gate 34, 35)

Empty, by §V: the daughter orbit's minimum is at its end. No corridor improvement from `Θ(εN)` to
`O(log L)` is available.

## AD. Minimum-location dichotomy (Gate 36)

Branch A (`h ≤ ηL`) is empty for actual orbits. Branch B (`h > ηL`) always holds. No constraint on
branch B was derived from injectivity, size, or drift.

## AE. Post-minimum tail (Gate 37, 38)

Vacuous for the same reason. And the gate's own warning applies: the bound `R_i ≤ E_i` obtained by
minimum normalization is **automatic**, so restating it supplies no lifetime restriction.

## AF. Curry after minimum normalization (Gate 41, 42)

Translating ordinary windows `[m_0, 2^G m_0]` into `−R_i + E_i ≤ G` turns Curry's spatial sparsity
into a drift-occupation statement — which is a **word shadow**, defeated by the previous branch's
cardinality construction. No new interaction.

## AG. Actual-orbit versus word-shadow check (Gate 44) — mandatory

| ingredient used | valid for a symbolic word? |
|---|---|
| `R_i ≤ A`, drift asymmetry, occupation | **yes** — word shadow, inert |
| `2^{d_i} ≤ 3m_i + 1` (§N) | **no** — genuinely orbit-level |
| growth envelope `2^n(m_n+1) ≤ 3^n(m_0+1)` (§S) | **no** — orbit-level |
| `m_i ≥ 1` ⟹ automatic corridor (§AA) | **no** — orbit-level |
| minimum location (§V) | **no** — orbit-level |

The three orbit-level ingredients are real, and they are exactly what produced §AA and §AK. They
do **not** produce a lifetime bound: §L and §T show why.

## AH. Targeted computations (Gate 45)

Over odd `m < 60001` (29,999 seeds), all with **0 violations**: orbit-floor identity; automatic
corridor in both real and exact integer form; growth envelope in integer form; `2^{d_i} ≤ 3m_i+1`.
Plus `A = log₂m + E` exactly, and minimum-at-final-index in 29,999/29,999 cases.

## AI. Adversarial worst-lifetime seeds (Gate 46)

Record `L/(log₂ m + A)` by range:

| range | argmax `m` | `L` | `L/log₂m` | `L/(log₂m+A)` | `E` |
|---|---|---|---|---|---|
| `[3,10³)` | 27 | 41 | 8.62 | **4.196** | 0.262 |
| `[10³,10⁴)` | 6171 | 96 | 7.62 | 3.774 | 0.252 |
| `[10⁴,10⁵)` | 52527 | 125 | 7.97 | 3.961 | 0.199 |
| `[10⁵,10⁶)` | 837799 | 195 | 9.91 | 4.923 | 0.256 |
| `[10⁶,3·10⁶)` | 1723519 | 207 | 9.99 | **4.972** | 0.196 |

Extended to large long-trajectory seeds (ratios computed directly, so provenance is irrelevant),
the **running maximum** of `L/(log₂m + A)` is:

| `m` | `log₂ m` | running max |
|---|---|---|
| 27 | 4.8 | 4.196 |
| 230631 | 17.8 | 4.571 |
| 626331 | 19.3 | 4.884 |
| 837799 | 19.7 | 4.923 |
| 1723519 | 20.7 | 4.972 |
| 5649499 | 22.4 | 5.060 |
| 6649279 | 22.7 | 5.439 |
| 8400511 | 23.0 | 5.535 |
| 63728127 | 25.9 | **6.853** |

**Correction to an earlier draft of this section.** Over this audit's own range (to `6.4·10⁷`) the
ratio rises monotonically, and I initially wrote that it "is still increasing … with no sign of
saturation". That range is far too small to support any trend claim. The verified record table
(§AS) covers `n` up to `7·10²¹` and shows the opposite picture: `γ` sits at `21.24` from `n = 27`
until `n = 230{,}631` (factor `8500`), jumps to `32.94` at `63{,}728{,}127` and is then **flat until
`3.74·10¹²`**, and has been **stuck at `35.8238` across the whole exhaustively searched range from
`1.05·10¹⁷` to `4.65·10¹⁹`** — a factor of `440` with no improvement. Increments are shrinking
(`6.0, 4.4, 1.8, 0.65, 0.06, 0.71, 0.12`) while `n` grows by orders of magnitude.

So the honest statement is: **the records creep upward very slowly, with long plateaus and shrinking
increments, consistent with saturation but not proving it.** In this audit's normalization the
largest verified value is `S = 15.43` at `n = 7.219·10²¹`. Mechanism of the worst
cases: long stretches of `d = 1` (deep negative drift, ordinary growth at the maximal rate)
punctuated by large-`d` collapses — exactly the escape hatch of §L.

## AJ. Strongest unconditional lifetime bound (Gate 47)

**There is none that is nontrivial.** The only unconditional statements proved here are the growth
envelope (§S) and the automatic corridor (§AA), neither of which bounds `L`. A bound of the form
`L ≤ F(m,A)` would in particular assert that every orbit terminates, which is the Collatz
conjecture. So no unconditional lifetime bound can exist short of Collatz.

## AK. Comparison with `U_all` / `U_half` (Gate 48) — the audit's main finding

Because the corridor is automatic and exactly `log₂m + E` (§AA), `U_all(K)` can be instantiated at
that `A`:

```
L ≤ K(log₂m + A) = K(2log₂m + E)          (Lean: Uall_gives_stopping_bound)
```

and since `E = O(log L)` with constant `0.2404`, this is `L ≤ 2K log₂m + O(K log log m)`. Conversely
a total-stopping-time bound `L ≤ K'log₂m` gives back `U_all(K')` for every `A ≥ 0`
(`stopping_bound_gives_Uall`). Therefore:

> **`U_all(K)` is equivalent, up to a factor 2 in the constant, to: every accelerated Collatz orbit
> reaches `1` within `O(log₂ m)` steps.**

**And the divergence exclusion is immediate.** For an injective segment the iterates are distinct
odd positive integers, so
`E_L ≤ (1/(3 ln 2))·Σ_{j<L}1/m_j ≤ 0.2404·ln L + 0.48` — measured `max E ≤ 0.27` throughout §AH.
Since that grows slower than `L`, the inequality `L ≤ K(2log₂m + E_L)` **bounds `L`**. Hence

> `U_all(K)` implies **no accelerated orbit is injective forever**: there are no divergent Collatz
> orbits.

(Lean: `no_unbounded_injective` formalizes the endpoint where the Archimedean property enters; the
absorption of the `log L` term is elementary and is not formalized.) `U_all(K)` therefore implies
the hard half of the Collatz conjecture outright, and with the no-nontrivial-cycle assumption the
note already makes in Prop 11.3, the full conjecture with an `O(log n)` stopping-time bound.

| hypothesis | actual orbit input? | dep. on `m` | dep. on `A` | sufficient for OP C? | status | circularity |
|---|---|---|---|---|---|---|
| injectivity only | yes | — | — | no | proved | — |
| maximal forward growth (§S) | yes | `log m` | — | no | **proved here** | — |
| Curry spatial sparsity | yes | — | — | no (§T) | imported | — |
| Curry reciprocal summability | yes | — | — | no (§P) | imported | — |
| minimum-normalized carry bound | yes | — | `O(log i)` | no (§AE) | automatic | — |
| **automatic corridor `A = log₂m+E`** | yes | `log m` | — | no | **proved here** | — |
| `U_half(K,q₀)` | yes | `log m` | linear | yes, `ε<ε₀` | **open; = `U_all` in practice (§AL)** | not circular, but ⟹ Collatz |
| `U_all(K)` | yes | `log m` | linear | yes, `ε<ε₀` | **open; ⟺ `O(log n)` stopping time** | not circular, but ⟹ Collatz |

**Good news:** the launch route is *not* circular — `U_all` is not a repackaging of Open Problem C,
and it is independently identifiable as a classical question.
**Bad news:** it is strictly stronger than the Collatz conjecture, so Prop 11.3 derives a realizer
floor from something that already implies what the program is trying to prove.

## AL. Weakest sufficient launch-subclass hypothesis (Gate 49)

`U_half(K,q₀)` exempts segments majority-covered by a bounded-period terminal repetition. Measured
at `q₀ = 4` over 29,999 seeds: **0 of 29,999 orbits are exempted (0.00%)**. So `U_half` carries
essentially the same burden as `U_all` and inherits §AK.

*Caveat, stated precisely.* The measurement is over the **injective** segment, which ends when the
orbit first reaches `1`; the `1`-cycle's own `d ≡ 2` tail is therefore not part of the word. If one
rode the cycle the exemption would fire, but the segment would no longer be injective, so that case
is outside both hypotheses. The 0% figure is the correct one for the hypotheses as stated.

The application, however, needs far less than either: only segments with `log₂m = Θ(αεN)`,
`A = Θ((α−1)εN)` and `L = Ω((1−ε)N)`. A hypothesis restricted to that regime would avoid the
`A = log₂m + E` instantiation of §AK and would **not** imply Collatz. That is the correct place to
weaken Definition 11.2, and §AM audits whether it can be done noncircularly.

## AM. Provenance audit (Gate 50) — mandatory

A subclass defined as "arises from an `ε`-dangerous realizer" is circular. Recognizable-from-the-orbit
alternatives, and their status:

| defining property | recognizable from the launch orbit alone? |
|---|---|
| injective | yes |
| no majority bounded-period terminal repetition | yes (this is `U_half`'s clause) |
| `log₂ m ≤ δL` for a fixed `δ` | **yes** — and this is the key one: it excludes the `A = log₂m+E` instantiation whenever `L ≫ log₂m` |
| relative corridor `A/L ≤ δ'` | **yes**, and it is what Prop 11.1(iii) actually supplies |
| internal-minimum location | yes, but vacuous (§V) |

So the honest weakening is: assume the lifetime bound **only for segments whose corridor and launch
size are both `O(δL)`**. Since the automatic corridor gives `A = log₂m + E`, a segment satisfying
both `log₂m ≤ δL` and `A ≤ δL` is one that has *not yet* descended to `1` — the hypothesis then no
longer implies Collatz. This is noncircular. It is also, as far as this audit can tell, entirely
unstudied.

## AN. Lifetime dichotomy (Gate 51)

Branches A (majority bounded-period tail) and the trivial-cycle part of B are handled by the note.
Branch C (a forced ordinary excursion `≥ F(L,m,A)`) is the one this audit tested, and §T shows the
only available `F` is polynomial in `L` against an exponential envelope. Branch D is empty by §V.
**No dichotomy survives as a useful statement.**

## AO. Required excursion rate (Gate 52, 53)

A useful excursion theorem must force `max m_i ≥ m·2^{cL}` with `c > α−1 = 0.584963`. Spatial
sparsity forces `c = (1/β)·log₂L/L → 0`. The gap is not a constant factor; it is a different
functional class. **Exact numeric target recorded for any future attempt: beat `0.584963` per
step.**

## AP. Deficit / ordinary-growth dictionary (Gate 54, 55)

With `Δ_n = ⌊αn⌋ − S_n` and `R_n = −Δ_n − {αn}`:

```
log₂ m_n = log₂ m_0 + Δ_n + {αn} + E_n           (exact)
```

So for a zero-confined actual orbit, the deficit is ordinary log-growth minus `E_n`. This is an
identity, not a mechanism — recorded as the dictionary and not used as leverage.

## AQ. Minimum normalization caveat (Gate 57) — important warning

For a minimum-normalized orbit, `m_n ≥ m_0` gives `Δ_n + {αn} + E_n ≥ 0` automatically, and
`R_n ≤ E_n = O(log n)`. Zero confinement asserts `R_n ≤ 0`. **The gap between the automatic bound
and the hypothesis is only `O(log n)`.**

> Minimum normalization very nearly trivializes zero confinement: it makes the corridor condition
> automatic up to a logarithmic term, erasing most of the feature the program is trying to exploit.

This is the precise reason the mandatory Gate 32 route, which looked highest-value, yields nothing.

## AR. Why `log m + A`? (Gate 58) — mandatory

**There is no independent reason, and the scale is not what it appears.** By §AK the hypothesis at
its own natural corridor is the `O(log n)` total-stopping-time statement. Evidence:

- **Empirical:** `S = L/log₂m` reaches `15.43` at `n = 7.219·10²¹` and has been flat at `15.04`
  across the entire exhaustively verified range `1.05·10¹⁷ … 4.65·10¹⁹` (§AI, §AS). The increments
  shrink; the picture is consistent with saturation but proves nothing.
- **Heuristic:** Roosendaal/Farin's Stirling/entropy computation predicts a completeness ceiling
  `0.6090897679…`, hence `γ_max = 41.677647656…`, i.e. `S_max ≈ 17.59` and `ε ≈ 0.0346`. This is a
  non-rigorous entropy heuristic and is presented as nothing more.
- **Heuristic:** the average accelerated stopping time is `Θ(log m)`, which is why the *shape* is
  natural — but averages say nothing about the pointwise supremum, which is the quantity `U_all`
  bounds.
- **Structural:** nothing in §M–§T supplies a mechanism at this scale; the one-sided corridor
  permits exactly the excursions that would be needed to violate it.

So `U_all` should be presented as **a sufficient hypothesis, not a naturally supported conjecture**
— and specifically as an instance of a classical open question rather than a new dynamical
principle.

The honest summary: the route needs **any** finite `sup L/log₂m`; no unconditional bound exists or
can exist short of Collatz; the verified maximum is `15.43` and the entropy heuristic suggests a
ceiling near `17.6`. If that heuristic is right the route yields `ε ≈ 0.035`. But it is a heuristic,
and the underlying question — is `γ` bounded? — is exactly the open problem.

## AS. Prior-art audit (Gate 59)

Verified from primary sources (Lagarias's two annotated bibliographies, his 2010 overview, Tao 2022,
Roosendaal's record tables, independently recomputed).

**Conventions, which matter and are easy to get wrong.** Lagarias (arXiv:math/0309224v13, §2, p. 2)
defines `σ∞(m) = inf{k : T^k(m) = 1}` for the *shortcut* map `T`, and `γ(m) := σ∞(m)/log m` with
**natural** log. `σ∞` counts the **even** steps; the ordinary Collatz delay is `h = σ∞ + d` where
`d` counts odd steps. **This audit's `L` is `d`, and `S_L` is `σ∞`.** The conversion is in §D.

| source | statement | quantifier |
|---|---|---|
| Lagarias, *The 3x+1 Problem: An Overview*, arXiv:2111.02635, §6.1 pp. 14–15 | the five "world records" (W1)–(W5) contain **no upper bound** on stopping time, total stopping time, or glide — only a lower bound (W3) and the largest known `γ` (W4) | — |
| Applegate & Lagarias, *Lower bounds for the total stopping time of 3x+1 iterates*, **Math. Comp. 72 (2003) 1035–1049** | infinitely many `n` with `σ∞(n) > 6.14316 log n`; `≫ x^{1/60}` of `n ≤ x` have `σ∞(n) > 5.9 log n` | pointwise, **lower** bound |
| Crandall / Shanks heuristic (via Lagarias 1985) | average order of `σ∞` is `≈ 6.95212 log n = (2/log(4/3))log n` | heuristic, average |
| Terras, Acta Arith. **30** (1976) 241–252 | integers with finite *stopping time* have natural density one | density 1 |
| Everett, Adv. Math. **25** (1977) 42–45 | same, independently | density 1 |
| Allouche (1979) | `Col_min(N) ≤ N^θ` for almost all `N`, any `θ > 0.869` | density 1, per fixed `θ` |
| Korec, Math. Slovaca **44** (1994) 85–89 | `{n : ∃k, T^k(n) < n^β}` has density one for every `β > log3/log4 = 0.7925` | density 1, per fixed `β` |
| Tao, **Forum of Math. Pi 10 (2022) e12**, Thm 1.3 | `Col_min(N) < f(N)` for almost all `N` in **logarithmic** density, for any `f → ∞` | logarithmic density; **no pointwise content** |
| Roosendaal, *3x+1 Completeness and Gamma Records* | record table; `γ = 35.823841` at `n = 104{,}899{,}295{,}810{,}901{,}231`, verified for all `n ≤ 46.5·10¹⁸`; largest known `γ = 36.716918` at `n = 7{,}219{,}136{,}416{,}377{,}236{,}271{,}195` (= Lagarias's W4) | computational |
| Roosendaal, Conjecture 3 / Farin entropy heuristic | completeness `C(N) < ln2/ln3 = 0.63093` always; conjectured ceiling `C_max = 0.6090897679…`, hence `γ_max = 41.677647656…` | conjecture + non-rigorous heuristic |

**The decisive negative, confirmed.** There is **no unconditional theorem bounding the number of
steps a Collatz orbit takes while staying above its starting value** — that quantity is Terras's
stopping time `σ(n)` (Roosendaal's *glide*), and its finiteness is itself open (Roosendaal's
"Conjecture 1b … obviously unproven as well"). A bound `σ(n) ≤ g(n)` would prove Collatz by strong
induction. And boundedness of `γ` implies Collatz trivially, since `γ(n) = +∞` for a divergent or
non-trivially-cyclic `n`; it is **strictly stronger** than Collatz, since Collatz alone gives
finiteness without uniformity. This confirms §AK independently.

*Scope caveat carried from the verification:* the negative claim rests on Lagarias's bibliographies
(comprehensive 1963–2009), his 2010 overview and Tao 2022; a systematic 2010–2026 sweep was not
performed. Such a theorem would be major news and would appear in Tao's introduction, where it does
not.

## AT. Almost-all limitation (Gate 60)

Every density-type result above (Terras, Everett, Allouche, Korec, Tao) is **almost-all**, and Open
Problem C is **pointwise**. The gap cannot be crossed without a distribution theorem for the launch
integers `m*_{t1}`, and no such theorem exists: the launch integers are produced by the pinning
construction from dangerous words, an exceptional set by hypothesis, so a statement holding off a
density-zero set says nothing about them.

Tao is explicit that his method has no pointwise version — Remark 1.4, p. 3: sharpening Theorem 1.3
to an absolute constant "is likely to be almost as hard to settle as the full Collatz conjecture,
and out of reach of the methods of this paper." His first-passage time `T_x(N)` is defined with the
convention `+∞` allowed and is **never bounded**; Proposition 1.9 controls Syracuse iterates only
"for almost all `N` and for times `n` up to `c log N`".

So: **almost-all results do not apply pointwise here**, and this is stated explicitly rather than
left implicit.

## AU. Weakest genuinely new missing lemma (Gate 61)

The `δ`-restricted lifetime hypothesis of §AM:

> **(U_δ)** There are `K < ∞` and `δ > 0` such that every injective accelerated orbit segment with
> `log₂ m ≤ δL` and `max_i R_i ≤ δL` has `L ≤ K(log₂ m + max_i R_i)`.

This is noncircular (§AM), does not imply Collatz (the excluded instantiation is exactly the one
that would), and still closes Prop 11.3 for `ε` small enough that the dangerous launch data satisfy
both `δ`-constraints. **No approach to it is known.**

## AV. Lean formalization

`EOC/OrbitLifetime.lean`, 9 declarations plus the `Orbit` structure.

| theorem | content |
|---|---|
| `aggregate_identity` | `2^{S_n}m_n = 3^n m_0 + C_n` from the step relation |
| `valuation_le` | `2^{d_i} ≤ 3m_i + 1` — orbit-level (§N) |
| `growth_step`, `growth_envelope` | `2^n(m_n+1) ≤ 3^n(m_0+1)` — the `α−1` rate ceiling (§S) |
| `corridor_automatic` | `2^{S_n} ≤ 3^n m_0 + C_n` — the corridor is not a hypothesis (§AA) |
| `corridor_attained` | equality once `m_n = 1` — so `A = log₂m + E` exactly |
| `Uall_gives_stopping_bound` | `U_all` at the automatic corridor gives `L ≤ K(2log₂m + E)` |
| `stopping_bound_gives_Uall` | the converse, so the two are equivalent up to a factor 2 (§AK) |
| `no_unbounded_injective` | an injective segment family bounded by one real is finite — where `U_all` ⟹ "no divergent orbit" lands |

No Curry or external theorem is formalized. Following the convention of preceding rounds the module
is not added to the `EOC.lean` aggregator.

## AW. Tests / build

```
lake build EOC.GlobalSeparation →  2262/2262, success
lake build EOC.OrbitLifetime    →  2263/2263, success
lake env lean EOC/OrbitLifetime.lean →  exit 0
```

Scripts: `scratch/lifetime.py`, `scratch/records.py`, `scratch/creep.py`.

## AX. Axiom audit

All eight declarations depend only on `propext`, `Classical.choice`, `Quot.sound`
(`aggregate_identity` and `corridor_attained` on `propext` alone; `valuation_le` and
`corridor_automatic` on `propext, Quot.sound`). No `sorry`, `admit`, `axiom`, `opaque`.

## AY. Files changed

```
EOC/OrbitLifetime.lean                                (new)
docs/POSITIVE_ORBIT_CONFINEMENT_LIFETIME_AUDIT.md     (new)
scratch/lifetime.py                                   (new)
scratch/records.py                                    (new)
scratch/creep.py                                      (new)
```

## AZ. Commits

*(filled at commit time)*

## BA. Push status

*(filled at push time)*

## BB. Research verdict

**`POSITIVE-ORBIT LIFETIME IS THE RIGHT LEVEL, BUT NO KNOWN DYNAMICAL MECHANISM BOUNDS IT AT THE
REQUIRED SCALE`**

Gate 62's stop conditions, checked individually: (1) confinement is one-sided and gives only a
lower bound on `m_i` (§H, §I) ✓; (2) spatial sparsity forces only polynomial excursions against an
exponential envelope (§T, §AO) ✓; (3) reciprocal summability yields no lower mass estimate (§P) ✓;
(4) minimum normalization gives an automatic corridor and no restriction — indeed it nearly
trivializes confinement (§AA, §AQ) ✓; (5) launch iteration is non-contracting with no decreasing
resource (§Y) ✓; (7) no actual-orbit theorem distinguishes the dangerous launch subclass (§AM) ✓.

Condition (6) needs a **correction to the brief's expectation**, and it is this audit's main
finding. Every `L(m,A)` bound strong enough for Open Problem C is *not* equivalent to the realizer
floor — the launch route is genuinely noncircular. It is instead **strictly stronger than the
Collatz conjecture**:

> Because `m_i ≥ 1` forces `2^{S_i} ≤ 3^i m_0 + C_i`, the corridor hypothesis `R_i ≤ A` is
> **automatic**, with `A = log₂ m + E` *exactly* (verified to the last digit on 29,999 seeds).
> Instantiating `U_all(K)` there gives `L ≤ K(2log₂m + E)`, and the converse holds, so
> **`U_all(K)` ⟺ "every accelerated orbit reaches 1 within `O(log₂ m)` steps"** — the `O(log n)`
> total-stopping-time conjecture, which implies Collatz.

`U_half` does not help: its exemption clause fires on **0 of 29,999** orbits tested.

**Why this verdict rather than the neighbours.** `ONE-SIDED CONFINEMENT PERMITS UNCONTROLLED DEEP
EXCURSIONS` (§H, §L) and `CURRY SPARSITY FORCES LARGE EXCURSIONS BUT NOT SHORT LIFETIME` (§K, §T)
are both established, but each is one mechanism; the chosen verdict is the conjunction they
support. `MINIMUM NORMALIZATION YIELDS A NEW LIFETIME RESTRICTION` is **refuted** (§AA, §AQ): it
yields an automatic bound that nearly trivializes confinement. `A WEAKER NONCIRCULAR LIFETIME
HYPOTHESIS SUFFICES` is not claimed — §AU states the candidate `(U_δ)` but nothing is known about
it. `AN ESCAPE-OR-RECURRENCE DICHOTOMY SURVIVES` fails because the escape branch is unobstructed.

**What is new here:**

1. The corridor width in `U_all` is **automatic and exactly `log₂ m + E`**, not a hypothesis
   (§AA, Lean `corridor_automatic` / `corridor_attained`).
2. Hence **`U_all(K)` is equivalent to the `O(log n)` total-stopping-time conjecture** (§AK), and
   in particular **implies that no Collatz orbit diverges** — the launch route is noncircular but
   assumes more than Collatz. This reclassifies Definition 11.2.
3. `U_half`'s exemption is empirically empty (0/29,999), so it inherits the same status (§AL).
4. The prior-art audit confirms §AK independently: no unconditional bound on stopping time exists
   or can exist short of Collatz, and boundedness of `γ` is strictly stronger than Collatz (§AS).
   In this audit's normalization the verified record is `S = L/log₂m = 15.43` at `n = 7.2·10²¹`,
   giving `ε = 0.0393` if it were a true bound; the entropy heuristic suggests `S ≈ 17.6`,
   `ε ≈ 0.0346`.
5. The Gate-32 minimum-normalization route, flagged as highest-value, is **empty**: the orbit
   minimum is at the final index in 29,999/29,999 cases (§V), and minimum normalization nearly
   trivializes zero confinement (§AQ).
6. The exact numeric target for any future excursion theorem: beat `α−1 = 0.584963` per step
   (§AO). Sparsity gives `→ 0`.
7. The noncircular weakening that does not imply Collatz: `(U_δ)` of §AU, restricting to segments
   with `log₂m` and `A` both `O(δL)`.

**Two corrections made during the audit**, recorded rather than silently fixed: (a) an earlier draft
presented `S ≤ 17.26` as a *threshold* to beat — it is only the `S` whose image under
`ε = 1/(1+αS)` is the paper's `ε₀(12.61)`; any finite `S` works. (b) An earlier draft claimed the
ratio is "still increasing with no sign of saturation" on the strength of this audit's own range
(`n < 6.4·10⁷`); the verified record table to `7·10²¹` shows long plateaus and shrinking increments
instead (§AI).
