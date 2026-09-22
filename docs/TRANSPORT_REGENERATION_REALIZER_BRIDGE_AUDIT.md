# Transport-regeneration / realizer-depth bridge audit

**Branch** `transport-regeneration-realizer-bridge-audit` from verified tip
`1f644d7d9f39ac6027cef6f426c781542d62d9ef` (`Add the normalized-carry terminal zero-gap audit`).
Isolated worktree; `main` untouched; no PR.

**Lean** `EOC/TransportRegeneration.lean` — 15 declarations, builds clean, standard axioms only,
no `sorry` / `admit` / `axiom` / `opaque`.

---

## A. Scope and question

The brief asks whether the modern pointwise realizer problem admits the deterministic reduction

> dangerous exact-realizer depth → large transport budget → previously generated
> failure-regeneration budget

and, if so, what cumulative regeneration theorem would close Open Problem C or E. Four specific
deliverables: (1) the exact relationship between `E_j` / `discreteGap_j` and `F_j`; (2) the
strongest correct relationship between dangerous realizer depth and `H_j`; (3) a decomposition of
`H_j` over failure events; (4) the weakest cumulative regeneration theorem that would suffice.
With a standing instruction not to assume that a pointwise envelope `G_max(H) = o(H)` is enough.

**Short answer.** The reduction exists and each link is exact — the chain is real, and this audit
proves it and formalizes it. But the final step does **not** work the way the source note's Open
Problem 37 invites one to read it: `G_max(H) = o(H)` is not merely unproved, it is **logically
insufficient**, and the audit exhibits the counterexample. The correct target is a bound on the
cumulative gain *per accelerated step*, which no envelope in `H` constrains.

## B. Provenance (Gate 0)

| artifact | hash |
|---|---|
| `~/Downloads/transportDeficits (1).pdf` | `c78539dad90722dd2ea7e72b1c07d897eb603b8d77f2e62791ab4dca6d563881` |
| `~/Downloads/transportDeficits (1) (1).pdf` | same |
| `~/Downloads/transportDeficits (1) (2).pdf` | same |
| extracted text `TD.txt` (1333 lines) | `1252c14e7cd5d96b2f400f6af6c2050267a8bfde64afb0148636281dfd688447` |

All three PDF copies are byte-identical; there is one source document, read in full (§1–§9,
appendices A–E). Origin tip fetched and verified against the commit graph, not against prose.
The repository contained no prior transport material; this is the first round to import it.

## C. The paper's coordinates, restated exactly

For a valuation prefix `D_j = (d_1,…,d_j)` with `S_j = Σd_i`, carry `C_{j+1} = 3C_j + 2^{S_j}`:

```
ξ_j = −C_j·3^{−j} ∈ ℤ₂        ξ_j = χ_j + 2^{S_j}·T_j ,  χ_j = ξ_j mod 2^{S_j}
r(D_j) = χ_j + (1−β_j)·2^{S_j}                           (the exact realizer, β_j the lift bit)
E_j = S_j − log₂ r(D_j)        F_j = S_j − log₂ χ_j
K_j(d) = (T_j − 3^{−(j+1)}) mod 2^d ∈ {0,…,2^d−1}
δ_{j+1} = log₂(1 + 2^{F_j}·K_j(d_{j+1})) ≥ 0             (transport deficit; = 0 iff K_j = 0)
A_{j,m} = Σ_{r<m} 2^{D_r}3^{−(j+1+r)}    A_{j,∞} = lim A_{j,m}
M_j = v₂(T_j − A_{j,∞})        H_j = F_j + M_j            (the transport budget)
```

A step is **perfect** when `K_j(d_{j+1}) = 0` and a **failure** otherwise.

## D. Status ledger of the imported facts

| fact | source | this audit |
|---|---|---|
| `χ_j` odd, `1 ≤ χ_j < 2^{S_j}`, hence `F_j > 0` | Lemma 1 | re-verified, 89,955 checks |
| `β_j = 0 ⟺ −1 < E_j ≤ 0`; `β_j = 1 ⟹ E_j = F_j` | Cor. 3 | re-verified, 89,955 checks |
| `χ_{j+1} = χ_j + 2^{S_j}K_j(d)`; `ΔF_{j+1} = d − δ_{j+1}` | Prop. 5, 8 | used |
| `F_N − F_τ = (S_N − S_τ) − D_{τ,N}`, `D_{τ,N} = Σδ` | eq. (14) | re-verified, 1,992 trajectories |
| `δ_{j+1}=…=δ_{j+m}=0 ⟺ M_j ≥ D_m` | Thm. 12, 16 | used |
| `M_{j+m} = M_j − D_m` on a perfect block | Thm. 18 | re-verified, 3,364 checks |
| `X_{j+1} = (X_j − K_j)/2^{d}` | Prop. 29 | used |
| `M_{j+1} = M_j − d + v₂(a−u)` at a first failure | Prop. 30 | re-verified, 8,485 checks |
| `H` conserved on every perfect step | Prop. 32 | re-verified, 2,133 checks |
| `ΔH = v₂(a−u) − δ_fail` at a first failure | Prop. 33 | re-verified, 5,841 checks |
| `δ_fail > F_j`, hence `F_{j+1} < d_{j+1}` | Cor. 34 | used, and see §J |
| finite regeneration cylinder | Prop. 35 | not re-verified (needs 2-adic targets beyond the scan window) |
| arbitrary-word regeneration unbounded | §D.8 | accepted; the note itself limits its force (Remark 36) |
| genuine-orbit positive regeneration at `H ≥ 8` | §D.9 | **corroborated but with a correction — §Y, §Z** |

## E. Notation collision #1 — two different `D`

`D_{τ,N}` in equation (14) is a sum of **transport deficits** `Σδ_{j+1}`. `D_m` in Theorems 12,
16 and 18 and in Proposition 35 is a cumulative **valuation** `Σd_{j+i}`. The proof of Theorem 12
settles it: it uses `D_{m+1} = D_m + d_{j+m+1}`. The two are unrelated quantities sharing a
letter, and equation (65) (`D_m ≥ M_j + q`) is about the valuation. Anyone reading (14) and (65)
together must not compose them. Flagged, not silently repaired.

## F. Notation collision #2 — two different "deficits"

The repository's EOC coordinates already carry a *corridor* deficit `Δ_N = ⌊αN⌋ − S_N ≥ 0`. The
note's `δ_{j+1}` is a *transport* deficit. Both reduce the realizer depth and both are called a
deficit, but they are independent: the corridor deficit measures how far the valuation word sits
below the Beatty ceiling, the transport deficit measures failure of a 2-adic congruence. §T
shows exactly where conflating them would produce a false step.

## G. Gate 1 — the exact relationship between `E_j`, `discreteGap_j` and `F_j`

Three statements, all proved, in increasing sharpness.

**(G1) `E_j ≤ F_j` unconditionally, with no case split.** Equation (5) gives `r(D_j) = χ_j` or
`r(D_j) = χ_j + 2^{S_j}`; in either case `r(D_j) ≥ χ_j`, and `log₂` is monotone. Hence
`E_j = S_j − log₂ r ≤ S_j − log₂ χ_j = F_j`.

This is worth isolating. Corollary 3 presents the relationship as a dichotomy on the lift bit
(`β=1 ⟹ E=F`; `β=0 ⟹ E ∈ (−1,0]`), and Remark 4 warns against conflating `E` and `F`. The warning
is right, but the *inequality* needs neither the dichotomy nor the warning: it follows from
monotonicity alone. Lean: `depth_le_anchor`.

**(G2) The converse question is vacuous.** By Lemma 1, `χ_j` is odd, so `1 ≤ χ_j < 2^{S_j}`,
so `F_j > 0` **always**. There is therefore no "`F_j ≤ 0`" regime to ask about, and the `β_j = 0`
branch of Corollary 3 (`E_j ≤ 0`) can never be an equality with `F_j`. The gap `F_j − E_j` is
`log₂(r/χ)`, which is `0` when `β=1` and in `(0, S_j]` when `β=0`.

**(G3) The discrete gap brackets `E`, it does not equal it.** With
`g_j := discreteGap(S_j, r(D_j)) = S_j − ⌊log₂ r⌋` (the previous round's integer coordinate),

```
E_j ≤ g_j < E_j + 1,          g_j − E_j = frac(log₂ r) ∈ [0,1).
```

Lean: `discreteGap_bracket`. Verified on 89,955 steps, 0 violations. **This corrects §Z of
`REALIZER_LIFT_DIGIT_POSITIVITY_AUDIT.md`**, which asserted that `E` *is* the terminal zero-run
length; `EOC/TerminalZeroGap.lean` already recorded the correction and this report confirms it
against the note's own `E`.

Chaining: **`g_j < F_j + 1`**, i.e. `g_j ≤ ⌈F_j⌉`. A long terminal zero gap forces a large
coarse-anchor depth, with a loss of strictly less than one bit.

## H. Gate 2 — the strongest correct relationship between dangerous depth and `H_j`

Since `M_j = v₂(X_j) ≥ 0` whenever `X_j ≠ 0`,

```
g_j  <  E_j + 1  ≤  F_j + 1  ≤  F_j + M_j + 1  =  H_j + 1.
```

Lean: `discreteGap_lt_budget_add_one`. Verified on 9,968 steps with a valid `M`, 0 violations.

**This is the strongest form, and the `M ≥ 0` step is the only lossy one.** It is worth being
precise about why the loss is acceptable, because a reader could reasonably object that `g_j ≤ S_j`
is free while `g_j < F_j + M_j + 1` is weaker than free whenever `M_j > log₂χ_j − 1`.

The answer is that the bridge is not used at arbitrary steps; it is used at the *deep* ones, and
there `M` is essentially zero. Theorem 18 drains `M` by `d` on every perfect step, and a deep `F`
is reached precisely at the end of a long perfect run, i.e. precisely when `M` has been spent.
Measured over 1,992 genuine trajectories, at the step of maximal coarse depth:

| peak `F` | trajectories | mean `M` | mean `F/H` |
|---|---|---|---|
| `[0,2)` | 482 | 0.193 | 0.9308 |
| `[2,4)` | 1140 | 0.154 | 0.9622 |
| `[4,6)` | 287 | 0.178 | 0.9703 |
| `[6,∞)` | 83 | 0.096 | 0.9882 |

`M = 0` exactly at the peak-depth step in **88.7%** of trajectories; overall mean `M` at peak is
`0.164`. The ratio `F/H` rises toward 1 as the depth grows. So `F ≤ H` is an equality where the
problem lives, and the inequality is used in the one direction and at the one place where it costs
nothing. That is an empirical remark about the sampled range, not a theorem.

## I. Gate 3 — decomposition of `H_j` over failure events

`H` is conserved on perfect steps (Prop. 32), so its entire history is carried by failures:

```
H_N  =  H_1  +  Σ_{k ∈ Fail, k < N} G_k ,        G_k = ΔH at failure k.
```

Lean: `budget_eq_partialSum`. At a *genuine first* failure Prop. 33 identifies
`G_k = v₂(a_k − u_k) − δ_{fail,k}`; at a later consecutive failure `v₂(K_j)` need not equal `M_j`,
Proposition 20 does not apply, and the identification fails — but the telescoping itself does not
depend on it. **The restriction matters for (58) and is recorded in §J.**

## J. What Corollary 34 gives universally and what (58) does not

Cor. 34 (`δ_fail > F_j`, hence `F_{j+1} < d_{j+1}`) is **universal**: writing `K_j = 2^{M}u` with
`M = v₂(K_j) ≥ 0` and `u ≥ 1` odd, `δ_fail = log₂(1 + 2^{F_j+M}u) > F_j + M + log₂u ≥ F_j`. No
first-failure hypothesis is used. Depth is strongly reset at *every* failure.

Equation (58) (`δ_fail > F_j + M_j = H_{tr,j}`) is **not** universal: it needs `v₂(K_j) = M_j`,
which is Proposition 20 and holds only at a genuine first failure after a perfect segment. The
note states (58) inside §D.4, which is headed by that hypothesis, so it is not an error — but the
"self-tightening requirement" reading in §D.4 and the epistemic-table row "Budget increase requires
`v₂(a−u) > δ_fail > H_tr`" should carry the restriction explicitly.

## K. The second cumulative identity — new

Equation (14) telescopes the depth. The matching precision telescopes the same way and the note
does not record it. Writing `w_{k+1} := 0` on a perfect step and `w_{k+1} := v₂(a−u)` at a first
failure, Theorem 18 and Proposition 30 together give `M_{k+1} = M_k − d_{k+1} + w_{k+1}`, hence

```
(I1)   F_N = F_1 + (S_N − S_1) − Σδ            [eq. (14)]
(I2)   M_N = M_1 − (S_N − S_1) + Σw            [new]
```

Lean: `cumulative`. Verified on 1,992 trajectories, 0 mismatches, together with the step laws it
rests on (`w = 0` on 3,364 perfect steps; `w = v₂(a−u)` on 8,485 first failures).

## L. Forced regeneration — the bound that runs the wrong way

Because `M_N ≥ 0`, (I2) immediately yields

```
(I3)   Σ_{k<N} w_k  ≥  (S_N − S_1) − M_1 .
```

Lean: `cumulative_regeneration_lower_bound`. Verified, 0 violations.

**Total cancellation precision over failures is forced to grow at least like `S_N`** — linearly in
`N` along any confined trajectory. Regeneration is not an exotic possibility that a contradiction
might exclude; it is *mandatory*, at linear cumulative rate, along every infinite trajectory
including the trivial cycle. Matching precision is consumed at rate `d` per step and can only be
replenished at failures, so the failures must supply it.

This is the single most important structural fact this audit found, and it inverts the intuition
that §D.10 of the note is built on.

## M. The perfect-tail dichotomy

If the last failure were at `j₀`, then `M_{j₀+m} = M_{j₀} − D_m` for all `m` by Theorem 18, with
`D_m ≥ m` since every `d ≥ 1`; `M ≥ 0` then forces `M_{j₀} = ∞`, i.e. `X_{j₀} = 0`, i.e. the tail
state *equals* the infinite target — the exactly-2-adic case.

> Along any trajectory with `X_j ≠ 0`, failures recur **infinitely often**.

Lean: `no_perfect_tail`. This is elementary and the note does not state it, but it is exactly what
makes §N and §O bite.

## N. Positivity forbids a negative drift

`F_j > 0` (Lemma 1) and `M_j ≥ 0`, so `H_j > 0` at every step. Combined with §I, the partial sums
of the failure gains are bounded below by `−H_1`. Therefore:

> No genuine infinite trajectory has a uniformly negative failure drift.

Lean: `no_negative_drift`. Together with §M (infinitely many failures) this is a real obstruction,
not a curiosity.

## O. Which proof strategies this kills

The natural contradiction architecture — the one §D.10 of the note sketches — is:

> deep excursions consume matching precision; failures destroy transport budget; therefore
> arbitrarily deep excursions cannot recur.

§L and §N kill it. Failures do not destroy budget on average along *any* infinite trajectory —
they cannot, because the budget is positive and the trajectory is infinite — and the cumulative
cancellation precision they supply is bounded *below* by `S_N − M_1`. Any argument whose engine is
"regeneration is hard, so it runs out" is contradicted by an identity, before any arithmetic about
Collatz is attempted. This is a firm negative result.

## P. Gate 10 (mandatory) — is `G_max(H) = o(H)` sufficient?

**No.** Not "unproved" — *insufficient*. Two independent reasons.

**(P1) Divergence.** The budget after `k` failures is `H_1 + Σ_{i<k}G_i`. If the gains have any
positive floor `c > 0`, then `H_k ≥ H_1 + kc → ∞`, and §M supplies infinitely many failures. An
envelope `G_max(H) = o(H)` — even `G_max(H) = √H`, even `G_max(H) ≡ 1` — is entirely compatible
with a positive floor. Lean: `envelope_diverges`, `sqrt_envelope_insufficient` exhibits
`H_k = k+1` obeying `ΔH ≤ √H` and diverging.

**(P2) Rate, which is the one that actually matters.** Open Problems C and E do not need `H`
bounded; they need `H` to grow at a rate **strictly below `α`** (§R, §S). And a sublinear envelope
constrains no linear rate at all:

> For every `c > 0` there is a strictly positive budget sequence obeying `ΔH ≤ √H` whose budget is
> exactly `c·n + c²`, i.e. whose cumulative gain grows at rate `c` — which may be taken larger
> than `α`.

Lean: `sqrt_envelope_allows_any_linear_rate`. Take `H_n = cn + c²`; the gain is `c` and
`√(cn + c²) ≥ √(c²) = c`.

**The error the envelope invites is a quantifier/units confusion.** `G_max(H)` measures gain *per
failure event*. What the problem needs bounded is gain *per accelerated step*, which is
`(events per step) × (gain per event)`. The envelope says nothing about the first factor, and §M
guarantees the first factor is not zero. Regime (71) of Open Problem 37 therefore carries none of
the force its placement between (70) and (72) suggests. Only regime (72) — `G_max(H) < 0`
eventually — actually bounds the budget, and it does so for the trivial reason that it makes the
gains eventually negative, which §N shows is impossible along an infinite trajectory.

**So all three regimes of Open Problem 37 fail to do the work**: (70) and (71) are insufficient,
and (72) is inconsistent with positivity. The problem as posed cannot resolve C or E in any of its
own stated branches.

## Q. Gate 4 — the weakest cumulative regeneration theorem

Combining §G, §H and §I into one statement (Lean: `discreteGap_lt_of_cumulative_gain`):

```
Σ_{k<N} G_k ≤ B      ⟹      g_N < H_1 + B + 1.
```

So the target is a bound on the **cumulative** gain, and the shape of that bound is what selects
between the open problems.

**(T_C) — sufficient for Open Problem C.** There exist `ε > 0` and `N₀` with

```
Σ_{k ∈ Fail, k < N} max(G_k, 0)  ≤  (α − ε)·N            for all N ≥ N₀,
```

along every relevant `c`-confined genuine trajectory. Then `g_N ≤ (α−ε)N + O(1)`, which is
Open Problem C (`r(D) ≥ 2^{εN} − O(1)`) by the translation in §Y of
`NORMALIZED_CARRY_TERMINAL_ZERO_GAP_AUDIT.md`.

**(T_E) — sufficient for Open Problem E.** The same with `B = H₂(ρ_c)·S_N + Φ(N)`, `Φ = o(N)`;
with `ρ_c = 1/α` the constant is `H₂(1/α) = 0.949956`.

`(T_C)` is genuinely weaker than "the budget is bounded": it permits linear growth, just at a rate
below `α`. That is the honest answer to Gate 4 — and it is also why the envelope framing fails, as
`(T_C)` is a statement about a rate constant and `G_max(H) = o(H)` is a statement about a shape.

## R. Open Problem C in cumulative-gain form

`r(D) ≥ 2^{εN} − O(1)` ⟺ `g(D) ≤ S_N − εN + O(1)`, and under zero confinement `S_N ≤ ⌊αN⌋`, so
`g(D) ≤ (α−ε)N + O(1)` suffices. By §Q that follows from `(T_C)`.

Equivalently, in the depth coordinate directly: by (I1), Open Problem C is **exactly** a linear
lower bound on the cumulative transport deficit,

```
D_{1,N}  ≥  (S_N − S_1) − (α−ε)N + F_1 − O(1).
```

Since `δ_fail > F_j` at every failure (§J, universal), `D_{1,N} ≥ Σ_{fail} F_j`: the problem is to
show that the pre-failure depths sum to enough. This is a clean restatement and the audit's second
useful translation.

## S. Open Problem E in cumulative-gain form

`E ≤ H₂(ρ_c)S + Φ(N)`. Using §G's bracket, the integer form is equivalent up to an additive 1 in
each direction, so `(T_E)` gives E with `Φ` shifted by `H_1 + 1`. Numerically the target is
`g ≲ 1.5056·N` against the trivial ceiling `g ≤ S_N ≈ 1.5850·N` — a margin of `0.0794·N`, which is
`I₀·N` with `I₀ = α(1−H₂(1/α)) = 0.0793186`. The two open problems differ only in whether `ε` is
required to be explicit.

## T. Gate 13 — the `S_N` versus `αN` substitution

In §R the step `S_N ≤ ⌊αN⌋ ≤ αN + c` is used once, in the direction that **weakens** the
conclusion, which is legitimate. The illegitimate move, which this audit does not make, is the
reverse: writing `S_N = αN` in

```
D_{1,N} ≥ (S_N − S_1) − (α−ε)N + F_1
```

to conclude that the requirement is `D_{1,N} ≥ εN`. For a word with a large corridor deficit
`Δ_N = ⌊αN⌋ − S_N`, the left side of the requirement is `S_N − (α−ε)N = εN − Δ_N + O(1)`, which
can be negative — the condition is then free, and quoting it as `εN` overstates what must be
proved by exactly `Δ_N`. The two "deficits" of §F meet here, and they must be kept apart:
corridor deficit relaxes the target, transport deficit achieves it.

## U. Is `(T_C)` a restatement?

Partly, and the report should say which part.

`H` bounded ⟺ the partial sums of `G` bounded (Lean: `bddAbove_iff_partialSums`) — that direction
is a pure restatement and buys nothing. But `(T_C)` is **not** the boundedness statement; it is a
rate bound, and it is strictly weaker than boundedness while still sufficient. So Gate 4 has a
genuine answer rather than a circular one.

What `(T_C)` is *equivalent* to is the linear lower bound on `D_{1,N}` in §R, by (I1). So the
content has not been created, only moved into a coordinate where it reads as a counting statement
about failures rather than a size statement about realizers. Whether that is progress depends on
whether failure counting is more tractable than realizer size; this audit found no reason to think
so, and §V says where a non-circular input would have to come from.

## V. Where non-circular content would have to come from

`(T_C)` needs the *number* of budget-increasing failures times their typical size to stay below
`α` per step. §L says the total `Σw` is at least `S_N ≈ αN`, so the margin is thin by construction:
regeneration must supply `≈ αN` bits of cancellation and must not supply much more. The whole
problem sits in the constant.

Nothing in the note or in this audit bounds the event count. Proposition 35 converts a `q`-bit
regeneration demand into a congruence `A_{j,m} ≡ T_j − K_j (mod 2^{M_j+q})`, and §D.7 of the note
already explains why this does not reduce to one congruence on the current iterate: the required
stopping length is trajectory-dependent, so the condition is a *union* of realizer classes over
admissible continuations. That union is what would have to be counted, and counting it is the
problem.

## W. Computational protocol

Direct implementation of the definitions in §C over `ℤ₂` represented as residues mod `2^P` with
`P = S_N + pad`, `pad ∈ {260,300,400}`. Genuine accelerated-Collatz orbits from odd seeds.
`A_{j,∞}` replaced by `A_{j,m}` with `m` the least index with `D_m` exceeding the working
precision, and every `M_j` discarded unless `M_j` is strictly below the certified precision — so
no reported `M` depends on the truncation. Failure statistics restricted to **genuine first
failures** (`v₂(K_j) = M_j`, Prop. 20), which is the hypothesis under which Props. 30 and 33 hold.

Scripts: `scratch/transport_regeneration.py`, `scratch/gmax_envelope.py`,
`scratch/two_criteria.py`, `scratch/v2_conditional.py`, `scratch/cumulative_identities.py`.

## X. Verification results

| statement | checks | mismatches |
|---|---|---|
| Lemma 1 (`χ` odd, `1 ≤ χ < 2^S`, `F > 0`) | 89,955 | 0 |
| Corollary 3 (both branches) and `χ = r mod 2^S` | 89,955 | 0 |
| `E ≤ g < E+1` (§G3) | 89,955 | 0 |
| **bridge `g ≤ ⌈H⌉` (§H)** | 9,968 | 0 |
| `H > 0` | 9,968 | 0 |
| Prop. 32 (`H` conserved on perfect steps) | 2,133 | 0 |
| Thm. 18 (`w = 0` on perfect steps) | 3,364 | 0 |
| Prop. 30 (`w = v₂(a−u)` at first failures) | 8,485 | 0 |
| Prop. 33 (`G = v₂(a−u) − δ_fail`) | 5,841 | 0 |
| (I1) depth identity | 1,992 trajectories | 0 |
| **(I2) precision identity (new)** | 1,992 trajectories | 0 |
| **(I3) forced regeneration `Σw ≥ S − M_1`** | 1,992 trajectories | 0 |
| partial sums never drive `H` below 0 | all | 0 |

## Y. Gate — the D.9 criterion audit

Section D.9 reports 380,078 failure events with `H_tr ≥ 8`, of which 267 "exhibited cancellation
precision exceeding the existing transport budget, `v₂(a−u) > H_tr`". Equation (56) says a budget
*increase* requires `v₂(a−u) > δ_fail`, and Cor. 34 gives `δ_fail > H_tr` **strictly**. So

```
v₂(a−u) > H_tr        is necessary but NOT sufficient for      ΔH_tr > 0.
```

The wedge is `δ_fail − H_tr = log₂(1 + 2^{H}u) − H`, which tends to `log₂ u`. Measured over
478,613 genuine first failures, the median wedge is 0.88 bits at `H ≈ 0` and falls to 0.006 bits
at `H ≈ 8` (large `M` forces `u = 1`), so at large budget the two criteria nearly coincide — but
they are not the same criterion, and at `H ≥ 8` the counts differ by a factor of 5 in my sample
(5 events satisfy `v₂ > H_tr`; 1 satisfies `v₂ > δ_fail`). **D.9's stated criterion is the weaker
one**, and the epistemic-table row "Genuine trajectories exhibit positive budget regeneration at
`H_tr ≥ 8`" is a claim about the stronger one. The gap should be closed in the note, either by
re-reporting against `δ_fail` or by weakening the claim.

## Z. Independent corroboration of D.9

With that correction made, D.9's substantive claim survives. Over 200,000 odd seeds × 50
accelerated steps, 478,613 genuine first failures, I find **one** event with `ΔH_tr > 0` at
`H_tr ≥ 8` (gain `+0.994` bits, 1,529 events in that range). The paper's rate is
`267/380,078 ≈ 7×10⁻⁴`; applied to 1,529 events that predicts ≈ 1 event. My result is consistent
with the paper's, and it independently confirms that **genuine positive-integer orbits do achieve
budget-increasing failures at `H_tr ≥ 8`**. I did not reproduce the "margins as large as 9.83
bits at `H_tr ≈ 13`" figure, which my sample is far too small to reach.

## AA. The `G_max(H)` measurement

Binning 478,613 first-failure events by pre-failure budget:

| `H` bin | events | `v₂ > H_tr` | `v₂ > δ_fail` | max `G` |
|---|---|---|---|---|
| 0 | 197,320 | 197,320 | 111,163 | 13.778 |
| 2 | 57,417 | 25,930 | 15,922 | 10.337 |
| 4 | 19,236 | 2,405 | 1,370 | 8.913 |
| 6 | 4,211 | 168 | 51 | 4.978 |
| 8 | 867 | 5 | 1 | 0.994 |
| 10 | 162 | 0 | 0 | −3.001 |
| 12 | 30 | 0 | 0 | −7.000 |
| 14 | 4 | 0 | 0 | −11.000 |

Read naively this is regime (72): `max G` falls off linearly with slope ≈ −2 and crosses zero near
`H ≈ 8.5`. **That reading is wrong, and §AB says why.**

## AB. The measurement is an extreme-value artifact

The empirical conditional tail of `v₂(a−u)` given the budget bin is **flat in `H`**:

| `H` bin | n | `P(v₂≥4)` | `P(v₂≥6)` | `P(v₂≥8)` | max `v₂` | `log₂n` | ratio |
|---|---|---|---|---|---|---|---|
| 0 | 197,320 | 0.222 | 0.074 | 0.019 | 15 | 17.59 | 0.853 |
| 2 | 57,417 | 0.261 | 0.083 | 0.020 | 13 | 15.81 | 0.822 |
| 4 | 19,236 | 0.259 | 0.063 | 0.018 | 13 | 14.23 | 0.913 |
| 6 | 4,211 | 0.270 | 0.073 | 0.020 | 11 | 12.04 | 0.914 |
| 8 | 867 | 0.286 | 0.061 | 0.014 | 9 | 9.76 | 0.922 |
| 10 | 162 | 0.198 | 0.025 | 0.000 | 7 | 7.34 | 0.954 |
| 12 | 30 | 0.167 | 0.000 | 0.000 | 5 | 4.91 | 1.019 |

The tail shows no trend with `H` whatever, and `max v₂ ≈ 0.9·log₂ n` uniformly across bins. The
bin counts decay geometrically (≈ ×0.44 per bin) while `δ_fail ≈ H` grows by 1 per bin, so

```
max G(H) ≈ 0.9·log₂ n(H) − H  ≈  const − 1.2·H − H  ≈  const − 2.2·H,
```

which is precisely the observed slope. **The entire apparent decay of `G_max(H)` is explained by
the sample shrinking, with no arithmetic ceiling required.** Pooled over all bins, mean
`v₂ = 2.594`, max `16`, tail ratios approaching `1/2`.

## AC. Gate 24 — these are not probabilities

Everything in §AA and §AB is an empirical frequency over one specific finite enumeration (odd
seeds `3 … 200,001`, 50 accelerated steps, genuine first failures only). It is **not** a measure on
cylinders. A `q`-bit regeneration cylinder is not an event of probability `2^{−q}`: the note's own
Remarks 13 and 28 say so, and §D.7 explains why the condition is a union of realizer classes rather
than a single congruence. The tables above are evidence about *what the data can distinguish*, not
evidence about arithmetic. I draw exactly one conclusion from them, in §AD, and it is a negative
one about the evidence.

## AD. Consequence: Open Problem 37 as posed is not the right question

Two problems with the statement

```
G_max(H) := sup{ v₂(a−u) − δ_fail : H_tr = H at a genuine failure }.
```

**(AD1) The sup is probably infinite for every `H`.** Taken over all genuine failures on all
positive-integer trajectories, each budget level carries infinitely many events, and §AB found no
`H`-dependence in the `v₂` tail. If `v₂` is unbounded on that ensemble — which nothing here
excludes and the data positively suggests — then `G_max(H) = +∞` for every `H` and none of (70),
(71), (72) holds. The finite computations of D.9 and of this audit are measuring the maximum of a
shrinking sample, not a ceiling.

**(AD2) Even a finite `G_max` in the middle regime is insufficient** — §P.

A better-posed replacement, and the one the deterministic chain actually needs, is `(T_C)`: a
bound on `limsup_N (1/N)·Σ_{k<N} max(G_k,0)` along a single trajectory. That is a per-trajectory
asymptotic rate, not an ensemble supremum, and it is the quantity that decides Open Problem C.

## AE. The trivial cycle is the degenerate branch of the dichotomy

Worth recording because it is an exact instance and it corrects a guess I made before checking.
On `m₀ = 1` the accelerated orbit is `1 → 1` with `d ≡ 2`, and the transport coordinates are:

```
S_j = 2j,   χ_j = 1,   F_j = S_j = 2j,   K_j = 0 for every j,   X_j = 0 exactly.
```

So `M_j = ∞`: the tail state *equals* the infinite target, every step is perfect, and there is
never a failure. This is precisely branch (i) of §M — and it is the only way `no_perfect_tail`
can be evaded, so the trivial cycle *validates* the dichotomy rather than bounding it. It is not,
as I had assumed before computing it, a zero-drift boundary witness for §N: it has no failures at
all, so there is no drift to speak of.

Note also that `χ_j = 1` gives `g_j = S_j`, the **maximal** possible terminal zero gap, with the
bridge `g < H + 1` holding vacuously because `H = ∞`. The finiteness of `M` in §H is a real
hypothesis, not a formality.

## AF. Anti-tautology tests

**Does the bridge have content?** Yes. Re-running 15,946 valid steps against the true `H` and
three corruptions:

| variant | violations | rate |
|---|---|---|
| true `H = F + M` | 0 | 0.00% |
| `M → −1` | 5,414 | 33.95% |
| `F → F/2` | 421 | 2.64% |
| `H → log₂(1+H)` | 646 | 4.05% |

The inequality is not satisfied by any plausible perturbation of `H`, so the 9,968 passing checks
in §X are not automatic.

**Is `(T_C)` weaker than its conclusion?** Yes: it permits `H_N → ∞` linearly, which boundedness
does not. `bddAbove_iff_partialSums` is an iff with boundedness; `(T_C)` is not.

**Does the Gate 10 counterexample cheat?** No: `H_n = cn + c²` is strictly positive, obeys
`ΔH ≤ √H` for every `n`, and `√H = o(H)`. All three are proved in Lean, not asserted.

## AG. Proved / imported / computational / conjectural

**Proved here (Lean, standard axioms):** `E ≤ F` unconditionally; `E ≤ g < E+1`; the bridge
`g < H+1`; the perfect-tail dichotomy; no negative drift; the two telescopings; forced
regeneration `Σw ≥ S − M_1`; the cumulative-gain gap bound; the Gate 10 insufficiency in both the
divergence and the rate form.

**Imported (proved in the note, re-verified computationally here):** Lemma 1, Cor. 3, Props. 5, 8,
20, 29, 30, 32, 33, Cor. 34, Thms. 12, 16, 18, eq. (14).

**Computational only:** the tightness of `F ≤ H` at peak depth (§H); the wedge measurement (§Y);
the corroboration of D.9 (§Z); the `G_max(H)` tables and the extreme-value explanation (§AA, §AB).

**Conjectural / open:** `(T_C)` and `(T_E)` themselves; the asymptotics of the failure rate; any
bound on the number of budget-increasing failures; Open Problems C, E, 37.

## AH. Corrections owed

1. **To `REALIZER_LIFT_DIGIT_POSITIVITY_AUDIT.md` §Z** — `E` is not the terminal zero-run length;
   `E ≤ g < E+1` with `g` the integer run length. Already recorded in `EOC/TerminalZeroGap.lean`;
   confirmed here against the note's own `E`.
2. **To the note, §D.9 / epistemic table** — the reported criterion `v₂(a−u) > H_tr` is weaker
   than `ΔH_tr > 0`; the claim should be re-stated or re-measured (§Y).
3. **To the note, §D.4** — (58) requires the genuine-first-failure hypothesis; Cor. 34 does not
   (§J).
4. **To the note, §D.10 / D.12** — the architecture "failures deplete the budget, so deep
   excursions must stop" is contradicted by (I3) and by positivity (§L, §N, §O).
5. **To any future use of Open Problem 37** — the three regimes do not partition the useful cases
   and none of them resolves C or E (§P, §AD).

## AI. Lean module

`EOC/TransportRegeneration.lean`, 15 declarations:

`natLog_le_logb`, `logb_lt_natLog_add_one`, `discreteGap_bracket`, `depth_le_anchor`,
`discreteGap_lt_budget_add_one`, `no_perfect_tail`, `no_negative_drift`, `envelope_diverges`,
`sqrt_envelope_allows_any_linear_rate`, `sqrt_envelope_insufficient`, `budget_eq_partialSum`,
`bddAbove_iff_partialSums`, `cumulative`, `cumulative_regeneration_lower_bound`,
`discreteGap_lt_of_cumulative_gain`.

Builds against Lean 4.34.0-rc1 + Mathlib; every declaration depends only on
`propext`, `Classical.choice`, `Quot.sound` (`no_perfect_tail` on the first and third only). No
`sorry`, `admit`, `axiom`, `opaque`. Following the convention of the preceding audit rounds, the
module is not added to the `EOC.lean` aggregator.

## AJ. Why no 2-adic infrastructure was built

The statements that carry the audit are about real sequences, natural-number logarithms and
telescoping sums. Formalizing `ℤ₂`, the targets `A_{j,∞}`, and Proposition 20 would be a large
undertaking whose payoff would be re-proving facts the note already proves and that this audit
verified numerically. The repository has no `ℤ₂` layer and this round does not start one; §AC of
the previous audit recorded the same judgment for the same reason.

## AK. What would falsify this audit's conclusions

- A proof that the failure rate along zero-confined trajectories is `o(1)` per step would restore
  the envelope reading of §P by making the event count sublinear. Nothing here rules that out; §M
  only gives infinitely many failures, not positive density.
- A demonstration that `v₂(a−u)` is bounded above on genuine orbits would make `G_max(H)` finite
  and regime (72) reachable — but it would then collide with (I3), which forces `Σw ≥ S_N`, so it
  would have to come with a compensating growth in the failure count.
- An error in (I2) would undo §L and §O. It is verified on 1,992 trajectories and rests only on
  Theorem 18 and Proposition 30, both re-verified independently.

## AL. Summary of the four deliverables

1. **`E_j` / `g_j` / `F_j`**: `E_j ≤ F_j` unconditionally (monotonicity, no `β`-split);
   `E_j ≤ g_j < E_j + 1`; hence `g_j ≤ ⌈F_j⌉`. `F_j > 0` always, so the converse question is
   vacuous.
2. **Dangerous depth vs `H_j`**: `g_j < H_j + 1`, with the `M ≥ 0` step tight exactly at the deep
   steps (`M = 0` at 88.7% of peak-depth steps).
3. **Decomposition over failures**: `H_N = H_1 + Σ_{Fail} G_k`, with `G_k = v₂(a_k−u_k) − δ_{fail,k}`
   at genuine first failures only; plus the new dual identity `M_N = M_1 − S_N + Σw` and its
   consequence `Σw ≥ S_N − M_1`.
4. **Weakest cumulative theorem**: `(T_C)` — cumulative positive gain `≤ (α−ε)N` — which is
   strictly weaker than boundedness, and is *not* implied by any `o(H)` envelope.

## AM. Relation to the earlier rounds

This is the ninth consecutive audit in the series. Rounds 4–8 closed the Curry window, the Chang
cross-scale and infinite-compatibility routes, the `W=2` Fourier selector, the lift-digit
coordinate and the carry/peeling gap. This round is the first to find a route whose links are all
exact and none of which is a restatement — the chain in §AL genuinely reduces realizer depth to a
cumulative failure statistic — and simultaneously the first to prove that the source's own
proposed closing mechanism cannot work. The route is open at exactly one place: the constant in
`(T_C)`.

## AN. Verdict

**The reduction is real and now proved, but the proposed closing mechanism is refuted; the
problem is relocated, not solved.**

Every link of *dangerous exact-realizer depth → large transport budget → failure-regeneration
budget* is an exact inequality or identity, all thirteen are formalized with no escape hatches, and
the bridge is empirically tight where it matters. The chain therefore delivers a genuine
reformulation: **Open Problem C is equivalent to a linear rate bound on cumulative failure gain,
`(T_C)`**, which is strictly weaker than budget boundedness.

It does not deliver a proof, and — the finding this round was asked to test — it cannot be closed
by the route the source note proposes. `G_max(H) = o(H)` is insufficient, demonstrably: a
sublinear envelope is compatible with every linear growth rate. Worse, the identity
`Σw ≥ S_N − M_1` forces linear cumulative regeneration along *every* infinite trajectory, so no
argument of the form "regeneration runs out" can succeed, and the empirical decay of `G_max(H)` in
both D.9's data and mine is an extreme-value artifact of shrinking bin counts rather than an
arithmetic ceiling. Open Problem 37 should be replaced by the per-trajectory rate question.
