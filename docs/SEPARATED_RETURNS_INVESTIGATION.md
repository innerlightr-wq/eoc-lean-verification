# Separated returns: episode decomposition and the missing inequality

*Bounded investigation of the gap Revision 6 leaves open: single-window lifetime `L_c(m)` does not
control total occupation `O_c(m)`. Branch `separated-returns-investigation`, base `5be9346`.*

**Deliverable.** An exact episode decomposition; an exact reframing of `O_c`; the missing
inequality identified explicitly; a **no-tradeoff obstruction** showing that within the
single-window framework the episode count must be bounded and cannot be traded against episode
length; and a conditional occupation theorem with the isolated hypothesis named.

No claim here proves or disproves EOC.

---

## A. Exact episode decomposition

Fix `c ≥ 0` and an odd seed `m₀`. The corridor is `𝒞 = {n ≥ 0 : R_n ≤ c}`; since `R₀ = 0 ≤ c`,
`0 ∈ 𝒞`. Decompose `𝒞` into maximal contiguous intervals — *episodes* — with entry times
`a₁ = 0 < a₂ < ⋯ < a_P` and lengths `ℓ₁,…,ℓ_P`, so that

```
O_c(m₀) = Σ_{i=1}^{P} ℓ_i .
```

**Restart relation** (Lean: `sum_concat`). Valuation sums concatenate along the orbit,
`S_{a+k}(m₀) = S_a(m₀) + S_k(m_a)`, so subtracting `(a+k)α`

```
R_{a+k}(m₀) = R_a(m₀) + R_k(m_a) .          (exact)
```

**Local threshold.** For `n = a_i + k`,

```
R_n ≤ c   ⟺   R_k(m_{a_i}) ≤ c_i ,        c_i := c − R_{a_i}(m₀) ≥ 0,
```

hence

```
ℓ_i = 1 + L_{c_i}(m_{a_i}) .
```

> **Each episode is the initial confined window of the restarted orbit at its own local threshold**
> — and that threshold *widens* exactly as far as the drift has fallen by the entry time. This is
> the precise reason single-window theory at a fixed `c` does not control occupation: later
> episodes are governed by a different, larger corridor.

## B. An exact reframing: `O_c` counts time at or above the starting scale

From the Eliahou–Rozier identity `R_n = log₂(m₀/m_n) + E_n`,

```
R_n ≤ c   ⟺   m_n ≥ m₀ · 2^{E_n − c} .
```

Verified on 29,999 seeds at `c = 1`: **0 mismatches**. Since `E_n` is small (`≤ 0.275` across the
tested range, and bounded by `E_∞ < ∞` on any divergent orbit),

> **`O_c(m₀)` is, up to the carry factor `2^{E_n}`, the total number of steps the orbit spends at
> or above `2^{−c}` times its starting value.**

This makes the three temporal scales concrete:

| object | reading |
|---|---|
| `L_c(m₀)` | length of the *first* sojourn at/above the starting scale |
| `P` | number of *returns* to the starting scale |
| `O_c(m₀)` | *total* time at/above the starting scale |

and it explains the paper's example `L₁(285175) = 14`, `O₁(285175) = 97`: that orbit leaves its
starting scale quickly but comes back six more times.

## C. The missing inequality, stated exactly

Suppose the corridor-uniform single-window bound holds: `L_{c'}(m) ≤ K(log₂ m + c')` for all odd
`m` and all `c' ≥ 0`. Using the orbit-floor identity `log₂ m_{a_i} = log₂ m₀ − R_{a_i} + E_{a_i}`,

```
ℓ_i ≤ 1 + K·( log₂ m_{a_i} + c_i )
    = 1 + K·( log₂ m₀ + E_{a_i} + c − 2 R_{a_i} ) .          (*)
```

Summing,

```
O_c(m₀) ≤ P + K · Σ_{i=1}^{P} ( log₂ m₀ + E_{a_i} + c − 2 R_{a_i} ) .
```

**The missing inequality is a bound on that sum by `O(log m₀)`.** Everything else is exact.

## D. The no-tradeoff obstruction

Each summand in (*) satisfies

```
log₂ m₀ + E_{a_i} + c − 2R_{a_i}  ≥  log₂ m₀ − c ,
```

since `E_{a_i} ≥ 0` and `R_{a_i} ≤ c`. So by the elementary counting fact (Lean:
`count_le_of_summands_ge`):

> **Proposition (no tradeoff).** If the episode sum in §C is bounded by `T`, then
> `P ≤ T/(log₂ m₀ − c)`. In particular `T = O(log m₀)` forces `P = O(1)`.

**Consequence.** Within the single-window-summation framework there is *no* tradeoff to exploit:
one cannot compensate a growing episode count with shorter episodes, because every episode's bound
already costs a full `log₂ m₀`. Bounding count and length separately by `O(log m₀)` yields
`O((log m₀)²)` and nothing better.

So the route requires **`P = O(1)`** — a bounded number of returns to the starting scale — as a
genuinely separate input. This is the reviewer's question answered: the resource being sought must
bound the *count*, not redistribute the *length*.

## E. What a return costs, and why the natural resource is too large

Each return is an up-crossing of the level `Λ_n = m₀2^{E_n−c}`. Because a single accelerated step
satisfies `2m_{n+1} ≤ 3m_n + 1` (Lean: `upcrossing_band`), an up-crossing from below `Λ` must land
in

```
Λ ≤ m_{n+1} < (3Λ+1)/2 ,
```

a band of multiplicative width `3/2` immediately above the level. Because the orbit is injective
until it cycles, **distinct returns consume distinct orbit values of that band.** Verified: 41,837
up-crossings over odd `m₀ < 120001`, all landing in the predicted band, no repeated landing value
within any orbit.

This is a genuine non-double-counted resource — and it is **exponentially too large**. The band
holds about `Λ/4 ≈ m₀2^{−c}/4` odd integers, i.e. `2^{Θ(log₂ m₀)}` of them, against the `O(1)`
needed. Even Curry's spatial sparsity, which for a divergent orbit bounds the orbit values in
`[Λ, 1.5Λ)` by `C_β(1.5Λ)^β log(3Λ)` with `β ≈ 0.9654`, leaves `Λ^{0.9654}` — still exponentially
more than `O(1)`.

> **Exact obstruction.** The injectivity-plus-band accounting identifies the right kind of
> resource but overshoots the requirement by an exponential factor. It cannot yield `P = O(1)`,
> and no sharpening of the band (which is already optimal, since the growth factor `3/2` is
> attained) changes that.

## F. Conditional occupation theorem

Collecting §C and §D:

> **Theorem (conditional).** Suppose
> **(U)** `L_{c'}(m) ≤ K(log₂ m + c')` for all odd `m ≥ 3` and all `c' ≥ 0`, and
> **(P)** `P_c(m₀) ≤ P₀` for all odd `m₀`, with `P₀` independent of `m₀`.
> Then for every odd `m₀`,
> ```
> O_c(m₀) ≤ P₀ + K·P₀·( log₂ m₀ + E_∞ + c + 2·max_i(−R_{a_i}) ) ,
> ```
> and if in addition the entry drifts satisfy `−R_{a_i} = O(log m₀)`, then
> `O_c(m₀) = O(log m₀)`: Existence EOC at `c`.

**Status of the hypotheses.** (U) is the corridor-uniform hypothesis, which Revision 6 §7.1 shows
is equivalent to an `O(log m)`-scale stopping/lifetime hypothesis — substantially stronger than
excluding divergence. **(P) is the isolated new hypothesis** and is, as far as this investigation
can determine, entirely unstudied. The side condition on entry drifts is mild: by the automatic
corridor, `−R_n ≤ log₂(max_k m_k / m₀)`, so it asks only that the orbit's maximum not be
super-polynomial in `m₀`.

Neither hypothesis is proved here, and (U) alone is insufficient.

## G. Computations

All diagnostics; none promoted to a theorem. Discipline note: episode-count maxima are reported at
**constant sample size per bucket**, because a maximum over a larger sample is larger for trivial
reasons — the error corrected in an earlier audit.

| quantity | result |
|---|---|
| reframing `R_n ≤ c ⟺ m_n ≥ m₀2^{E_n−c}` | 29,999 seeds, **0 mismatches** |
| up-crossing band and distinctness | 41,837 up-crossings, **0 outside the band**, no repeats |
| mean `P` at 2000 seeds/bucket, `log₂m₀ = 13…24` | **1.62 – 1.73, flat** |
| max `P` at 2000 seeds/bucket, same range | 7 – 12, drifting slowly and noisily |
| mean `O₁` at same buckets | 8.1 – 9.1, flat |
| max `O₁` at same buckets | 63 → 92 across `log₂m₀ = 12 → 24` |

The mean episode count shows **no growth** with `log₂ m₀`, which is the robust signal and is
consistent with (P). The maxima are sampling-sensitive and no trend is inferred from them. Max
`O₁` growing roughly linearly in `log₂ m₀` (slope ≈ 3.5 over the tested range) is consistent with
EOC's shape but proves nothing.

## H. What this investigation establishes

1. The episode decomposition, restart relation and local threshold are exact, and formalized.
2. `O_c` has a clean dynamical meaning: total time at or above the starting scale.
3. **The missing inequality is a bound on `Σ_i (log₂ m_{a_i} + c_i)`**, and by the no-tradeoff
   proposition this is *equivalent* to bounding the episode count. There is no redistribution to
   be found.
4. The natural non-double-counted resource for charging returns — distinct orbit values in a
   width-`3/2` band above the starting scale — is identified exactly and is exponentially too
   large. This is a genuine obstruction to the accounting, not a failure to find the argument.
5. The conditional theorem isolates **(P)**, bounded returns to the starting scale, as the new
   hypothesis EOC needs beyond single-window control.

## I. What it does not establish

It does not bound `P`, does not prove EOC at any tier, and does not show (P) is true — the
empirical flatness of mean `P` is a diagnostic only. It also does not rule out an approach outside
the single-window-summation framework; the no-tradeoff proposition constrains that framework, not
every possible argument.
