# Independent audit of Curry's windowed sparsity note

*Read from the source text, not from repository summaries. Branch
`curry-audit-and-scope-correction`, base `76afebb` (verified against `origin`).*

## 0. The source

| | |
|---|---|
| Title | *An Explicit Windowed Sparsity Bound for Divergent 3x+1 Orbits, with Logarithmic-Floor Exclusion beyond the Harmonic Barrier* |
| Author | Michael John Curry, London, Ontario, Canada |
| Date | **24 August 2026** |
| Length | 5 pages |
| Provenance | supplied by the user (`~/Downloads/occupation_note_clean.pdf`); three byte-identical copies |
| sha256 | `67daa37d9b1b1b3e3f96af3448fd710c7a683e17a00dc6f314f45a6c36288a76` |
| Archived | `docs/sources/Curry_WindowedSparsity.pdf` (same hash) |

The PDF's *metadata* Title field is truncated to "An Explicit Windowed Sparsity Bound for Divergent
3x+1 Orbits"; the **document body carries the full title** including the subtitle the repository
cites. No discrepancy.

No publication venue, DOI, or arXiv identifier appears in or on the note. **Nothing about its
status is inferred from citations**: the audit below is of the mathematics only.

**How to read the "independent check" column.** The verdicts rest on the *general proof arguments*,
which are reproduced in §3–§5. The exact computations **corroborate** those arguments — they confirm
identities, boundary cases and the numerical optimisation — and establish nothing on their own. A
finite check is never evidence for a universally quantified theorem.

## 1. Setting, and the two maps (brief item 2)

Curry works with **two** maps and keeps them apart correctly.

* `T(n) = n/2` (n even), `(3n+1)/2` (n odd) — the *shortcut* map, on all positive integers. All of
  §2 (the counting) is about `T`.
* `U(y) = (3y+1)/2^{v₂(3y+1)}` — the *accelerated (Syracuse)* map on odd integers, with
  `y_{n+1} = U(y_n)`, `a_n = v₂(3y_n+1)`, `A_n = a_0+⋯+a_{n-1}`, `λ = log₂3`, `g_n = nλ − A_n`.

In the repository's notation `R_n = A_n − nλ`, so **`g_n = −R_n`** — Curry says so explicitly. The
repository's `orbit` is `U`, matching Curry's `y_n`.

The passage between them (brief item 10) is in Proposition 3.1: the odd iterates `y_n` are a
**subsequence** of the `T`-orbit, so `Σ_n 1/y_n ≤ Σ_{x∈𝒪} 1/x`. That is the only step needed and it
is valid. The repository's `ReciprocalSummable M := Summable (fun n => 1/(orbit M n))` is exactly
Curry's odd-iterate conclusion, so the interface is the right one.

## 2. Theorem-by-theorem verdicts

| Result | Verdict | Independent check |
|---|---|---|
| Collision-free; value set of an infinite aperiodic orbit is collision-free | **Correct** | A collision `T^j(u₁)=T^j(u₂)` with `u₁≠u₂` in one orbit makes two distinct times share a value ⟹ eventually periodic. §3 below |
| **Lemma 2.1** (parity-prefix rigidity; bijection `ℤ/2^N → {0,1}^N`; `T^N(n+r2^N) = T^N(n) + r·3^{m_N(n)}`) | **Correct** | 26,334 exact identities (`N ≤ 10`, `n < 400`, `r < 6`), 0 failures; bijection + residue-dependence for `N ≤ 12`, 0 failures |
| **Lemma 2.2** (`T^N(n) < 3^{m_N(n)}(2^{-N}n+1)`) | **Correct** | 35,988 cases (`1 ≤ N ≤ 12`, `n < 3000`), 0 failures. Unrolling verified symbolically (§4) |
| **Theorem 2.3** (windowed count) | **Correct, one typo** | see §4 |
| — the covering of `[a,a+X)` by two shifts | **Correct** | 15,880,001 points (`X < 400`, `a < 200`), 0 failures |
| — residue class meets `[1,X]` in `≤ X/2^N+1 ≤ 3` points | **Correct** | 0 failures, `X < 600` |
| — entropy bound `Σ_{i≥γN} C(N,i) ≤ 2^{NH(γ)}` for `γ ≥ 1/2` | **Correct** (standard) | 1,794 cases (`N ≤ 299`, six `γ`), 0 failures |
| — optimization `β* = γ*λ = H(γ*)` | **Correct** | `γ* = 0.609089767923`, `β* = 0.965384441732`, `1/β* = 1.035856760034`, all matching the paper to its stated precision |
| **Remark 2.4** (no exact match identified in the literature) | A disclaimer, not a claim | — |
| **Proposition 3.1** (reciprocal summability) | **Correct** | dyadic sum `Σ(i+2)2^{i(β−1)}` converges iff `β<1`; `β*<1` verified |
| **(1), (2)** product form `y_n = y_0 2^{g_n} Q_n`, `Q_n ↗ Q_∞` | **Correct**; matches the repository's Eliahou–Rozier identity | — |
| **Theorem 4.1** (no divergent orbit has `g_n ≤ B log₂n + K`, `B ≤ 1`) | **Correct** | `Σ n^{-B} = ∞` for `B ≤ 1` |
| **Theorem 4.2** (occupation `#{n : g_n ≤ G} ≤ c₁2^{βG}(G+c₂)`) | **Correct, one repairable gap** | see §5 |
| **Corollary 4.3** (same for `B < 1/β* = 1.0358567…`) | **Correct** | exponent comparison `2^{G/B}` vs `2^{βG}` |
| **§5 Limitations** | Honest and accurate | — |

**No incorrect theorem was found.** Two defects, both repairable and local, are in §4 and §5 below.

## 3. Collision-free (brief item 1)

> "Call a set `A ⊂ ℕ` *collision-free* if distinct `u₁, u₂ ∈ A` never satisfy `T^j(u₁) = T^j(u₂)`
> for any `j ≥ 0`."

If `u₁ ≠ u₂` lie in one orbit, `u₁ = T^{i₁}(n₀)`, `u₂ = T^{i₂}(n₀)` with `i₁ < i₂`, then
`T^j(u₁) = T^j(u₂)` gives `T^{i₁+j}(n₀) = T^{i₂+j}(n₀)`: the orbit repeats a value, hence is
eventually periodic. Contrapositive: an infinite **aperiodic** orbit has collision-free value set.
**Correct.** For an aperiodic orbit all values are distinct, so the value set is in bijection with
time — used silently in §3–§4 of the note and legitimate.

## 4. Theorem 2.3 — full walk-through, and the one typo

`N = ⌊log₂X⌋` so `2^N ≤ X < 2^{N+1}`; `W = A ∩ [a, a+X)`.

**Covering (brief item 4).** Choose `z ≥ 0` with `z2^N < a ≤ (z+1)2^N` (possible since `a ≥ 1`).
For `y ∈ [a, a+X)`: `y − z2^N ≥ 1`, and if `y − z2^N ≤ X` take `z' = z`; otherwise
`y > z2^N + X ≥ (z+1)2^N` (using `X ≥ 2^N`), so `1 ≤ y − (z+1)2^N < X`. **Two pieces suffice**, so
one choice of `z' ∈ {z, z+1}` retains `#W/2`. Endpoints check out (`[a, a+X)` half-open; `a ≥ 1`
excludes `0 ∈ A`). Verified exhaustively.

**Pigeonhole.** `m_N(s) ∈ {0,…,N}`, so some `B₁ ⊆ B` with common value `m` has `#B₁ ≥ #B/(N+1)`.

**Heavy case `m ≥ γN` (item 5).** By Lemma 2.1 the elements of `B₁` lie in residue classes mod
`2^N` whose parity prefix has `≥ γN` ones; there are `≤ Σ_{i≥γN} C(N,i) ≤ 2^{NH(γ)}` such classes
(needs `γ ≥ 1/2`, which the hypothesis `γ ∈ (1/2, 1/λ)` supplies), each meeting `[1,X]` in
`≤ X/2^N + 1 ≤ 3` points. So `#B₁ ≤ 3·2^{NH(γ)} ≤ 3X^{H(γ)}`. **Correct.**

**Light case `m < γN` (item 6).** The note writes

> every `s ∈ B₁` has `T^N(s) < 3^{γN}(2^{−N}N + 1) ≤ 3·2^{γλN} ≤ 3X^{γλ}`.

> **TYPO.** Lemma 2.2 gives `T^N(s) < 3^{m}(2^{−N}·s + 1)`, so the middle factor is
> `2^{−N}s + 1`, not `2^{−N}N + 1`. **Repair:** since `s ≤ X < 2^{N+1}` we have `2^{−N}s < 2`, so
> the factor is `< 3` and the displayed conclusion `< 3·2^{γλN} ≤ 3X^{γλ}` is exactly right.
> **Presentation error only; the bound and everything downstream are unaffected.**

**The collision argument (item 6).** If `#B₁ > 3X^{γλ}`, two distinct `s₁,s₂ ∈ B₁` share
`T^N(s₁) = T^N(s₂)`, and they share `m`, so Lemma 2.1 gives
`T^N(s₁+z'2^N) = T^N(s₁) + z'3^m = T^N(s₂) + z'3^m = T^N(s₂+z'2^N)` — a collision between two
distinct elements of `A`. **Correct**, and this is the only place collision-freeness is used.

**Combining (item 7).** `#W ≤ 2(N+1)·3(X^{H(γ)} + X^{γλ})`, i.e. the stated
`6(⌊log₂X⌋+1)(X^{H(γ)}+X^{γλ})`. The bound is **uniform in `a`** — no constant depends on the
window position. `C_β` depends on `β` alone.

**Optimization (item 8).** On `(1/2, 1/λ)`, `H` is strictly decreasing and `γλ` strictly
increasing, so `max(H(γ), γλ)` is minimised at the crossing. Verified: the max is `0.96538448` at
`γ = 0.6090897` and larger on either side. Dividing `H(γ) = γλ` by `γ` gives `H(γ)/γ = λ`, Rozier's
defining equation, so `γ* = r_H`; checked to 12 digits. **Correct.**

## 5. Proposition 3.1 and §4 (items 9, 11, 12)

**Proposition 3.1.** Fix `β ∈ (β*, 1)` and sum Theorem 2.3 over `[2^i, 2^{i+1})`:
`Σ_{x∈𝒪}1/x ≤ Σ_i C_β 2^{iβ}(i+2)2^{−i} < ∞`, convergent **exactly because `β* < 1`**. This is the
"beyond the harmonic barrier" point and it is the load-bearing numerical fact of the whole note.
**Correct.**

**Theorem 4.2 — repairable gap.** The proof applies Theorem 2.3 "with `a = 1`,
`X = y₀Q_∞2^G`". But Theorem 2.3 is stated for **integers** `a ≥ 1`, `X ≥ 2`, and `y₀Q_∞2^G` need
not be an integer (`Q_∞` is an infinite product).

> **Repair:** apply Theorem 2.3 with `X' = ⌈y₀Q_∞2^G⌉ ≥ 2` for `G ≥ 1`. Then
> `[1, y₀Q_∞2^G] ⊆ [1, X')` and `X' ≤ y₀Q_∞2^G + 1 ≤ 2y₀Q_∞2^G`, so the bound changes only by the
> factor `2^β ≤ 2` inside `c₁` and by `log 2` inside `c₂`. **Local repair, constants only;
> Corollary 4.3 is unaffected** because it uses Theorem 4.2 only through the exponent `β`.

**Theorem 4.1 / Corollary 4.3.** 4.1 excludes `B ≤ 1` from summability directly. 4.3 pushes to
`B < 1/β* = 1.0358567…` by comparing `#{n : g_n ≤ G} ≥ ½2^{G/B}2^{−K/B}` against
`c₁2^{βG}(G+c₂)`, forcing `1/B ≤ β` for every `β > β*`. **Both correct.** Note 4.3 is a statement
about a **logarithmic floor**, and its conclusion is a `limsup`: for every `B < 1/β*` and every `K`,
`g_n > B log₂n + K` infinitely often. It is **not** a growth rate for `g_n`.

## 6. Self-containedness and external dependencies

**The note is self-contained once elementary parity and counting facts are supplied.**

* Lemma 2.1 and 2.2 cite Terras [2] and Everett [3] as classical but are **proved in the note**.
* Garcia–Tal [1] is credited for the *idea* (windowed pigeonhole over parity classes applied to one
  injective orbit) and for the qualitative density-zero theorem; the note gives its **own complete
  proof** of Theorem 2.3 and explicitly replaces Heppner [8] (used by Garcia–Tal) with explicit
  Terras–Everett counting. Heppner is therefore **not** load-bearing here.
* Rozier [4] is used only in the closing *remark* identifying `γ* = r_H`. **Not load-bearing.**
* The one fact used without proof is the entropy tail bound `Σ_{i≥γN} C(N,i) ≤ 2^{NH(γ)}` for
  `γ ≥ 1/2` — standard, and verified here over 1,794 cases.

So no external theorem needs to be taken on trust for Proposition 3.1. That matters: the divergence
reduction depends on Curry's note **alone**, not on a chain of unverified citations.

## 7. Verdict

> **The audited input rigorously supports the divergence-to-zero-confined-seed reduction.**

Theorem 2.3, Proposition 3.1, Theorem 4.1, Theorem 4.2 and Corollary 4.3 are all correct as
mathematics. The two defects found are a typographical slip in the light-case display (§4) and a
missing integrality/ceiling step in Theorem 4.2 (§5); both are local, both are repaired above, and
neither touches Proposition 3.1, which is the only input the reduction consumes.

What this does **not** establish: the note is unrefereed and unpublished as far as anything in it or
in the repository shows, and it is **not formalized**. It must therefore remain an explicit
hypothesis in Lean (`EOC/CurryInterface.lean`), never an axiom. The remaining formalization
obligation is named there as `PowerSavingImpliesSummable`.

---

## 8. Dependency table: external input vs formalized result

Reading downward, each row consumes the rows above it.

| # | Statement | Kind | Where |
|---|---|---|---|
| E1 | Entropy tail bound `Σ_{i≥γN}C(N,i) ≤ 2^{NH(γ)}`, `γ ≥ 1/2` | **classical**, used without proof; verified here | Curry §2 |
| E2 | **Thm 2.3** windowed count, exponent `β > β* = 0.9653844…` | **external, audited correct on paper, NOT formalized** | Curry §2; `CurryInterface.PowerSavingCount` / `WindowedSparsity` |
| O1 | *dyadic summation* `PowerSavingCount` + injectivity `⟹ ReciprocalSummable` | **DISCHARGED — now Lean** | `PowerSavingSummable.powerSaving_implies_summable` |
| E3 | **Prop 3.1** `Σ1/y_n < ∞` on a divergent orbit | **no longer a separate input** — now derived from E2 via O1 | `PowerSavingSummable.curry_summability_of_windowed'` |
| F1 | injective ⟺ divergent | **Lean** | `CurryInterface.injective_iff_divergent` (uses existing `UpperEscape.injective_orbit_tendsto`) |
| F2 | `E_n ↑ E_∞ < ∞`, `y_n → ∞`, `R_n → −∞` | **Lean** | `CurryFoundation.carryE_tendsto`, `orbit_tendsto_atTop`, `R_tendsto_atBot` |
| F3 | last global drift maximum | **Lean** | `CurryFoundation.exists_last_atBot_max` |
| F4 | restart at `m* = m_{n₀}` is zero-confined, drift `→ −∞` | **Lean** | `ZeroConfinedSeed.exists_zero_confined_seed_tendsto` |
| F5 | divergence ⟹ zero-confined positive seed | **Lean**, modulo E3 as a hypothesis | `CurryInterface.zero_confined_seed_of_divergent` |
| F6 | universal drift exit ⟹ no divergent orbit | **Lean**, modulo **E2 alone** | `PowerSavingSummable.no_divergent_orbit_of_windowed` |
| F7 | zero-confined ⟹ injective ⟹ divergent (the §D equivalence) | **Lean**, unconditional | `CurryInterface.injective_of_zero_confined`, `divergent_of_zero_confined` |
| — | **no positive integer realizes an infinite zero-confined word** | **OPEN** — the target | — |

> **After discharging O1, the single explicit external input in this part of the chain is
> `WindowedSparsity` — Curry's Theorem 2.3 itself.** `no_divergent_orbit_of_windowed` takes it as its
> one hypothesis. This strengthens verification; it is **not** a new exclusion mechanism and does not
> touch the open arithmetic target.

Curry's Thm 4.1 / Thm 4.2 / Cor 4.3 (the logarithmic-floor exclusion) sit *beside* this chain, not
in it: they sharpen what a hypothetical divergent orbit must look like, and the reduction does not
use them. That separation is deliberate — brief item 12.

## 9. Next-step assessment

**The one surviving candidate from the previous survey was C1, the deficit `Δ_k = ⌊kα⌋ − S_k`.** It
is a genuine added datum (`Δ_k ≥ 0` and `Δ_k → ∞`, now available at the same seed). It **fails** the
"mechanism beyond a reformulation" requirement, by the following decisive derivation:

> `leastRealizer(d,N) < 2^{S_N+1}` and `Δ_N = ⌊Nα⌋ − S_N`, so
> `log₂ leastRealizer(d,N) < ⌊Nα⌋ − Δ_N + 1`. **A larger deficit lowers the cap on the least
> realizer.** Proving least realizers unbounded requires a *lower* bound; the deficit supplies only
> an upper one, so it pushes in the wrong direction.

Checked exactly over all zero-confined words of length `N = 6…16` (312,455 words at `N = 16`). Two
statistics, read carefully:

* the covariance between `Δ_N` and `log₂` of the least realizer is negative at every `N` — but this
  is **largely mechanical**, forced by the cap above, and is not independent evidence;
* the decisive case is the extreme one: the **maximum**-deficit word is the all-ones word, whose
  least realizer is exactly `2^{N+1} − 1`, i.e. it *attains the top of its own shrunken cap*.

So a large deficit is fully compatible with an exponentially large least realizer. **The deficit
neither forces nor forbids large realizers.**

> **Qualification, important.** What is ruled out is the proposed inference **from the upper cap
> alone**. It is *not* ruled out that the deficit could be used *together with additional residue
> information*. The all-ones word is precisely the illustration: its least realizer `2^{N+1}−1` grows
> exponentially *despite* its maximal deficit — so the cap is not what decides the matter there, and
> something finer does. C1 is dropped as a standalone mechanism, not as an ingredient.

**No candidate meets the four requirements** (exact statement; mechanism beyond reformulation;
identified connection to positive realization; separate coverage obligation). Per the brief, this
phase stops at the completed audit and interface rather than manufacturing a direction.

**What remains open, precisely:**

1. **The target itself** — no positive integer realizes an infinite zero-confined word. Equivalent
   to universal drift exit and, given the background inputs, to its restriction to divergence
   candidates (scope note §D).
2. ~~The formalization obligation O1~~ — **done** (`EOC/PowerSavingSummable.lean`). The dyadic
   summation is formalized: block counts at `a = X = 2^k`, the bound `1/m ≤ 2^{−k}` on each block,
   injectivity to pass from the value set to the orbit index, and summability of
   `C·log2·(k+1)·(2^β/2)^k` for `β < 1`.
3. **Formalizing E2 outright** — the full window theorem (Thm 2.3). Substantial; not attempted. It
   is now the *only* explicit external input in this part of the chain.
4. **The arithmetic gap** — the audited counting estimates discard the exact realizer congruence
   (scope note §C). Combining counting with that residue information is the open problem; no
   universal claim is made that counting cannot work.
