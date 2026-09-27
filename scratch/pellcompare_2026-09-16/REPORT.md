# Does the Pell-spine mechanism transfer to EOC? (round of 2026-09-16, part 20)

Nothing committed or pushed in either repository.  The Pell repo was cloned read-only into the
session scratchpad (`.../scratchpad/pell`), never modified.  EOC-side data analysis is in
`scratch/spine_2026-09-16/`.

## 1–2. The exact Pell theorem and its mechanism (audited, then re-verified)

**Theorem 4.4 (manuscript).**  Order primitive Pythagorean triples by increasing hypotenuse `c` and
set `Δk = |b−a|/c`.  The record minima of `Δk` are attained **exactly** at the near-isosceles
("Pell spine") triples `|b−a| = 1`, i.e. `(3,4,5), (20,21,29), (119,120,169), …`, for which
`c·Δk ≡ 1`; the record sequence contracts with limiting ratio `3−2√2 = 0.17157…`.

The proof has exactly two ingredients:

* **Lemma 4.2 (arithmetic gap).**  In the shifted parametrization `s = m−n`, `|b−a| = |s²−2n²|` with
  `gcd(s,n) = 1`.  Any odd prime `p | d` gives `(s n^{-1})² ≡ 2 (mod p)`, so `2` is a QR mod `p`,
  so `p ≡ ±1 (mod 8)`; the least such prime is `7`.  Hence **`d = 1` or `d ≥ 7`** — nothing between.
* **Lemma 4.3 (spine growth).**  `c_{j+1} = 6c_j − c_{j−1}` ⇒ `c_{j+1}/c_j < 3+2√2 = 5.8284…`.

and the single comparison **`R = 3+2√2 < 7 = G`** closes it: for off-spine `T'` take the largest
spine `c_i ≤ c'`; then `c_i > c'/R > c'/G ≥ c'/d'`, so `Δk(T') = d'/c' > 1/c_i`, i.e. something at a
*no-larger scale* is strictly better, so `T'` is never a record.

**Verified in-session** (COMPUTATIONAL, exact integers, `c ≤ 10⁶`, 159 139 primitive triples):
records `= (3,4,5), (20,21,29), …, (137903,137904,195025)` are exactly the spine terms; all records
have `d = 1`; the observed leg differences are `1, 7, 17, 23, 31, 41, 47, 49, …` — **nothing in
`(1,7)`**; spine ratios `5.8, 5.8276, 5.8284, …` all `< 3+2√2`; and `verify_spine` confirms
`b−a = 1`, `a²+b² = c²`, `gcd = 1`, `u²−2c² = −1`, and both recurrences.

## 3. The abstract template — PROVED (MATH)

> **Spine–Record Lemma.**  Let `𝒯` carry a scale `c : 𝒯 → ℝ_{>0}` and a numerator `d : 𝒯 → ℝ_{>0}`;
> put `Δ = d/c`.  Let `S ⊆ 𝒯` with scales `c₁ < c₂ < …` unbounded.  Assume
> **(H1) gap:** `d ≡ 1` on `S` and `d ≥ G` off `S`;
> **(H2) growth:** `c_{j+1} ≤ R·c_j` for all `j`, with `R < G`;
> **(H3) base:** `c₁ ≤ c(T)` for every `T ∈ 𝒯`.
> Then the record minima of `Δ` in order of increasing `c` are **exactly** the elements of `S`.

*Proof.*  Off-spine `T'`: take `i` maximal with `c_i ≤ c'` (exists by (H3), unboundedness).  Then
`c' < c_{i+1} ≤ R c_i`, so `Δ(T') = d'/c' ≥ G/c' > R/c' > 1/c_i = Δ(S_i)` with `c_i ≤ c'`: not a
record.  On-spine `T = S_j`: any `T'` with `c' ≤ c_j` has `Δ(T') ≥ 1/c'` (if on-spine) or
`> 1/c_i ≥ 1/c_j` (if off-spine, same computation): a record. ∎

**Part XXI check:** with `G = 7`, `R = 3+2√2`, `c₁ = 5 ≤ c(T)` for every primitive triple, the lemma
returns Theorem 4.4 verbatim.  The abstraction is faithful.

## 4–6. EOC side: what plays each role, and where it breaks

### The right structural analogue exists — and is already in the literature
The Pell spine is the **convergent sequence of `√2`** (`s/n → √2`, `u/c → √2`).  The corresponding
object in Collatz/EOC is the convergent sequence of **`α = log₂3`**, which governs the barrier
`top[i] = ⌊iα⌋`, the barrier-riding ("greedy") word, and the periodic-barrier approximants used in
the ShapeTail work (`8/5, 19/12, 65/41, 485/306`).  It is not a new object:
`log₂3 = [1;1,1,2,2,3,1,5,2,23,2,2,1,1,55,…]` has convergents whose **numerators** include
`301994/190537`, `17087915/10781274`, `85137581/53715833` (computed here, exact) — and
`301994`, `17087915`, `85137581` are precisely the three coefficients in Eliahou's cycle-length
theorem (EXTERNAL THEOREM, Eliahou 1993: any nontrivial cycle has period
`301994A + 17087915B + 85137581C`; the statement is recalled from the literature survey of round 17,
not re-derived here, but the three integers are verified in-session to be `log₂3` convergent
numerators).  So "the arithmetic spine of Collatz" is the `log₂3`
convergent family, and it already carries the best known rigidity result in the field.

### But the mechanism does not transfer — two independent obstructions

**(a) No constant growth ratio `R`.**  `√2` is a *quadratic* irrational: its continued fraction is
periodic, the spine obeys a fixed linear recurrence, and `c_{j+1}/c_j → 3+2√2` is a **constant**
below `7`.  `log₂3` is not quadratic and its partial quotients are not bounded in the observed
range; the convergent-denominator growth ratios are

| step | 3 | 5 | 6 | 7 | **9** | 12 | **14** | 16 |
|---|---|---|---|---|---|---|---|---|
| `q_{k+1}/q_k` | 2.50 | 3.42 | 1.29 | 5.77 | **23.46** | 1.40 | **55.58** | 4.98 |

A Pell-type argument needs `R < G` with `R` a fixed constant; here `R` already spikes to `23.5` and
`55.6` inside the first fifteen convergents, and bounding it at all is equivalent to `log₂3` being
badly approximable — an **OPEN** Diophantine problem (known effective irrationality measures allow
polynomially growing partial quotients).  **REFUTED: hypothesis (H2) has no EOC instance with a
constant.**

**(b) No gap `G`.**  Equality analysis of the one exact EOC certificate now available
(`EOC.ShapeCertificate.blockW_superEigen`, `Σ_y blockW·h(l+1,y) ≤ (3/2)h(l,x)` with `h = 2^{σ−x}`):
writing `w = b(2l+1) − x` for the headroom, the row sum is `2^{σ−x}·S_w/2` with
`S_w = ∑_{k≥1} min(k,w)·tilt·2^{−k}`, and exactly

| `w` | 0 | **1** | 2 | 3 | 4 | 5 | … | ∞ |
|---|---|---|---|---|---|---|---|---|
| `S_w` | 0 | **3** | 5/2 | 11/4 | 23/8 | 47/16 | … | **3** |
| deficit `3−S_w` | 3 | **0** | 1/2 | 1/4 | 1/8 | 1/16 | `2^{−(w−3)}` | **0** |

So the certificate is saturated exactly at **`w = 1`, the barrier-hugging (contact) blocks** — the
same family the ShapeTail large deviation has to control — and again in the free limit `w → ∞`; the
slack is *maximal* in between (`w = 2`).  But the off-spine deficit is `2^{−(w−3)} → 0`:
**REFUTED — there is no uniform gap; off-spine configurations approach the extremal value
geometrically closely.**

### Why a gap is unlikely anywhere in the pressure world
Pell's gap comes from *integrality plus congruence*: `d` is a positive integer and quadratic
reciprocity forbids `d ∈ {3,5}`.  In EOC there are two regimes:

* **ShapeTail world** — the kernel weights are integers (`|B_r|`) times a rational tilt, so the
  observable *is* quantized; but as shown above the extremal value is approached, not isolated.
* **OddDarkPressure / CriticalWhiteCount world** — where the current contraction problem actually
  lives — the transfer weights carry `p = 1/α` and `q = 1−p`, *irrational*.  The pressure spectrum
  is not quantized at all, so **there is no candidate for `d` and hence none for `G`**.

## The two extremal families are structurally opposite (Parts XIV, XXII)

In Pell the spine is an **infinite recurrent** family: every spine element is a record, forever,
with scales growing by a constant factor.  In EOC the extremal windows are **transient**: at the
resolution where the observable is faithful (`K = 32`) the previous round measured the fraction of
supercritical windows lying on any cycle of the true-environment compatibility graph as

| `K` | 16 | 24 | **32** |
|---|---|---|---|
| fraction of bad windows that can recur at all | 0.9955 | 0.10 | **0.00** |
| longest run of consecutive bad windows (disjoint tiling) | 4 | 1 | **1** |

So EOC's high-pressure configurations are excursions *away from* the contracting bulk, never a
recurrent extremal backbone.  Under the Spine–Record Lemma this means there is no candidate `S` at
all: hypotheses (H2) and (H3) presuppose an infinite family whose scales one can index, and the
EOC extremizers do not form one.

## The `O(log R)` correction is generic, not Pell-like — COMPUTATIONAL, decisive

Parts XXIV–XXVI asked whether a geometrically spaced record family explains
`C(θ_max) ≈ 0.2–0.3·log₂R`.  It does not need to: that is exactly the **Karlin–Altschul /
Cramér** law for the maximal segment sum of a sequence with negative drift.  Testing it directly on
the 30-environment corpus (8 310 blocks):

* pooled `mean(w − θ) = −0.10021` (negative drift, as required);
* the Cramér exponent solving `E[e^{λ(w−θ)}] = 1` is **`λ* = 2.3948`** (`E[e^{λ*X}] = 1.000000`);
* the law predicts `C ≈ ln R / λ*`, i.e. a slope of **`ln2/λ* = 0.2894` bits per `log₂R`**;
* **measured** slope of `max C` over prefixes `R = 20 … 320`: **`0.209`**, and the previous round's
  independent estimate was **`0.20–0.30`**.

So the logarithmic surplus is produced by ordinary extreme-value fluctuation of a negative-drift
sum, with an exponent computable from the one-block weight distribution.  **No geometric record
family is needed, and none is evidenced** — the Pell reading of the `log R` term is REFUTED.

## Status

* PROVED (MATH): the Spine–Record Lemma; that it reproduces Theorem 4.4.
* COMPUTATIONAL (exact): the Pell reproduction; the `S_w` table; the `log₂3` convergent ratios.
* EXTERNAL THEOREM: Eliahou 1993 (cycle lengths from `log₂3` convergents); quadratic reciprocity
  second supplement (Lemma 4.2).
* REFUTED: hypothesis (H2) for EOC (no constant spine growth — `log₂3` is not a quadratic
  irrational, ratios spike to 55.6); hypothesis (H1) for the ShapeTail certificate (deficit
  `2^{−(w−3)}`, no uniform gap).
* OPEN: whether `log₂3` is badly approximable (this is exactly what (H2) would need).
