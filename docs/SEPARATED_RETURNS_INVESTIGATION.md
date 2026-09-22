# Separated returns: episode decomposition, and what it does not give

*Bounded investigation of the gap Revision 6 leaves open: single-window lifetime `L_c(m)` does not
control total occupation `O_c(m)`.*

> **Revised.** The first version of this document (commit `8493f55`) contained several incorrect
> claims. They are listed, corrected and re-derived in
> `docs/SEPARATED_RETURNS_CORRECTION_AUDIT.md`, which is the authoritative record of what changed
> and why. This document has been rewritten to state only what is actually proved.

**Net result.** The episode decomposition is exact and now fully formalized, and it yields two
definite outcomes — neither of them the conditional reduction originally claimed:

1. the proposed new hypothesis (bounded episode count) is **false**, constructively and for every
   threshold;
2. the hypothesis it was meant to supplement, **(U)**, already implies an occupation bound on its
   own, so there was no gap for a return-counting hypothesis to fill.

No claim here proves or disproves EOC.

---

## A. Exact episode decomposition

Fix `c ≥ 0` and an odd seed `m₀`. The corridor is `𝒞 = {n ≥ 0 : R_n ≤ c}`; since `R₀ = 0 ≤ c`,
`0 ∈ 𝒞`. Decompose `𝒞` into maximal contiguous intervals — *episodes* — with entry times
`a₁ = 0 < a₂ < ⋯ < a_P` and lengths `ℓ₁,…,ℓ_P`, so that `O_c(m₀) = Σ ℓ_i`. The episode at `a₁ = 0`
is not a return, so `#episodes = #re-entries + 1`.

**Restart relation** (Lean: `sum_concat`). Valuation sums concatenate,
`S_{a+k}(m₀) = S_a(m₀) + S_k(m_a)`, so

```
R_{a+k}(m₀) = R_a(m₀) + R_k(m_a) .          (exact)
```

Hence `R_n ≤ c` for `n = a_i + k` reads `R_k(m_{a_i}) ≤ c_i` with `c_i := c − R_{a_i}(m₀) ≥ 0`, and

```
ℓ_i = 1 + L_{c_i}(m_{a_i}) .
```

Each episode is the initial confined window of the *restarted* orbit at its own **local threshold**.

## B. The entry lemma: the local threshold is pinned

At a genuine re-entry `a > 0` we have `R_{a−1} > c` and `R_a ≤ c` with `R_a = R_{a−1} + d_{a−1} − α`.
Because `1 < α < 2` and `d_{a−1}` is a positive integer, a digit `≥ 2` would *raise* the drift; so

> **Entry lemma** (Lean: `entry_digit_one`, `entry_threshold_pinned`, `entry_threshold_real`).
> `d_{a−1} = 1`, and consequently
> ```
> c − (α−1) < R_a ≤ c ,        i.e.        0 ≤ c_a < α − 1 = log₂(3/2) = 0.58496… .
> ```

The bound is independent of `c`, of `m₀`, and of how deep the drift went during the excursion.
**Only the first episode has threshold `c`; every later one starts in a corridor narrower than
`0.585`.** Drift can of course fall far below `c` *inside* an episode — that is the interior, not
the entry point.

Verified: 97,091 re-entries over odd `m₀ < 60001` at `c ∈ {0,1,2,5}`; every one has `d_{a−1} = 1`
and `c_a ∈ [0, α−1)`, maximum `0.571438`.

*(The first version of this document claimed the opposite — that later thresholds widen with the
accumulated drift. That was false; see the correction audit §B.)*

## C. An exact reframing, with its range of validity

From the Eliahou–Rozier identity `R_n = log₂(m₀/m_n) + E_n`,

```
R_n ≤ c   ⟺   m_n ≥ Λ_n := m₀ · 2^{E_n − c} .
```

This is an identity, verified on 29,999 seeds at `c = 1` with 0 mismatches. But `Λ_n` **moves with
`n`** through the carry `E_n`, and `E_n` is not uniformly small: `T(1) = 1`, so on every orbit
reaching `1` the carry gains `log₂(4/3)` per step and `E_∞ = +∞`. (On a *divergent* orbit the
opposite holds — `m_n → ∞` gives `Σ1/m_j < ∞` and a finite `E_∞`, as the Curry foundation records.
The mistake in the first version was applying the divergent-orbit fact to all orbits.) Measured
maxima: `0.190665` over corridor times, `0.325550` over all orbit times. So the reading

> `O_c(m₀)` is the total time spent at or above `2^{−c}` times the starting value

is legitimate on the corridor range, where the carry is small, and must not be used as a fixed-level
statement about the whole orbit.

| object | reading (on the corridor range) |
|---|---|
| `L_c(m₀)` | length of the *first* sojourn at/above the starting scale |
| `P − 1` | number of *returns* to that scale |
| `O_c(m₀)` | *total* time at/above that scale |

This explains the paper's example `L₁(285175) = 14`, `O₁(285175) = 97`.

## D. Arrival at `1` ends occupation — so (U) alone suffices

With `m_n = 1` the aggregate identity gives `2^{S_n} = 3^n m₀ + C_n > 3^n m₀ ≥ 2^c 3^n` whenever
`2^c ≤ m₀`, using `C_n > 0`. So no time at which the orbit equals `1` lies in the corridor, and
every corridor time precedes arrival at `1`:

> **Theorem** (Lean: `corridor_excludes_one`, `corridor_time_lt_of_reaches_one`,
> `occupation_le_of_reaches_one`). For `m₀ ≥ 2^c`, `O_c(m₀) ≤ n*(m₀)`, the arrival time at `1`.

The finitely many seeds below `2^c` are covered separately and unconditionally: on the tail every
digit is `2`, and `2^{S_{n*}} ≥ 3^{n*}`, so being in the corridor at `n*+k` forces `4^k ≤ 2^c3^k`,
hence `k ≤ 3·2^c`:

> **Theorem** (Lean: `tail_digit_two`, `tail_corridor_bound`,
> `occupation_le_of_reaches_one_general`). For **every** seed reaching `1`,
> `O_c(m₀) ≤ n*(m₀) + 3·2^c + 1`.

The lifetime audit showed **(U)** — corridor-uniform `L_{c'}(m) ≤ K(log₂m + c')` — is equivalent to
an `O(log m)` total-stopping-time bound. Hence **(U) implies `O_c(m₀) = O(log m₀)`**, with no
auxiliary hypothesis. Verified: 0 violations of `O_c ≤ n*` over 29,999 seeds.

**The three layers, kept apart.** Calling this "(U) ⟹ EOC, formalized" would overstate it:

| layer | status |
|---|---|
| (U) ⟹ `O(log m)` stopping time | **not formalized** — imported from the lifetime audit, whose absorption of an `E_L = O(log L)` term is a real-analytic step that audit records as unformalized |
| stopping bound ⟹ occupation bound | **formalized**, for every seed |
| the orbit stays at `1` after arrival | **formalized** for the genuine map (`a 1 = 2`, `T 1 = 1`, `orbit_one_of_one`); a hypothesis for the abstract `Orbit` structure, which does not force oddness |

This is a withdrawal, not a gain: (U) implies Collatz, so this relocates the difficulty rather than
reducing it. Its value is negative information — **the gap this investigation set out to fill does
not exist.**

## E. The proposed hypothesis (P) is false

Let the symbolic rule play digit `2` inside the corridor (drift `+ (2−α)`) and digit `1` outside
(drift `− (α−1)`). Three formalized facts — an invariant `3·2^{S_n} ≤ 4·2^c 3^n`, immediate
re-entry after any digit-`1` step, and recurrence of exits via `(4/3)^j → ∞` — show the drift
oscillates across `c` forever, with unboundedly many completed exits and re-entries.

Every finite prefix is realized by a positive odd integer: `leastRealizer d N` is odd and satisfies
the exact realizer congruence, so by `realizerCongruence` the genuine orbit reproduces the prefix.

> **Theorem** (Lean: `exists_odd_seed_with_many_reentries`). For every `c ≥ 0` and every `B` there
> are `N` and an odd `m₀ > 0` whose genuine accelerated orbit follows the word for `N` steps and has
> at least `B` corridor re-entries before time `N`.

So the hypothesis **(P)** `P_c(m₀) ≤ P₀` uniformly in `m₀` — offered in the first version of this
document as the isolated new hypothesis — is **false for every `c`**.

Scope: the realizing seed grows with `B`; the count is finite-horizon; nothing is inferred about
infinite realization, and **nothing about the rate** — see §F.

Verified at `c = 1`, `N = 60`: `S_N = 96`, seed `136975455177362381873293329281`, all 60 valuations
reproduced by the actual map.

## F. Many short episodes do compensate

The seeds of §E, evaluated over their *whole* orbits at `c = 1`:

| `N` | `log₂ m₀` | episodes `P` | `O₁` | `O₁/log₂m₀` | `P/log₂m₀` |
|---|---|---|---|---|---|
| 20 | 32.73 | 8 | 13 | 0.397 | 0.244 |
| 40 | 58.64 | 18 | 26 | 0.443 | 0.307 |
| 60 | 96.79 | 25 | 41 | 0.424 | 0.258 |
| 80 | 127.74 | 34 | 49 | 0.384 | 0.266 |

These whole-orbit numbers are **computational**: `P ≈ 0.28 log₂m₀` episodes of mean length `≈ 1.4`
give `O₁ ≈ 0.42 log₂m₀`. The orbits violate (P) badly and satisfy EOC comfortably, so episode count
**cannot** be the obstruction, and the earlier "no tradeoff between count and length" conclusion is
false as stated.

**From unboundedness to a rate.** §E gives unboundedly many episodes and nothing about the rate.
Two further facts supply one, and both are proved:

* **exits recur within three steps** (`post_exit_lower`, `exit_within_three`) — after an exit the
  word re-enters with the drift pinned `> log₂(3/2)` below the level, and two digit-`2` steps raise
  it by `2log₂(4/3) > log₂(3/2)`; hence `exitTime(B) ≤ e₀ + 3B` with `e₀ := exitTime(0)` depending
  only on `c`. *(Measured gap set: exactly `{2,3}`.)*
* **the seed is only exponentially large in `B`** — `m₀ < 2^{S_N+1}` and `S_N ≤ 2N` (`oscS_le`).

> **Theorem** (Lean: `many_reentries_with_small_seed`). With `N = exitTime(B)+1`, there is an odd
> `m₀` realizing the prefix with
> ```
> ≥ B re-entries before N ,   m₀ < 2^{6B+2e₀+3} ,   #{n < N : R_n ≤ c} ≤ e₀ + 2B .
> ```

The middle bound inverts to `B ≥ (log₂m₀ − 2e₀ − 3)/6`: along this family the episode count is
**at least linear in `log₂m₀`** — a theorem, not a measurement.

**An inference that does not follow.** The seed estimate bounds `m₀` from *above*, hence `B` from
*below*, and gives no upper bound on `B`. So `O_prefix ≤ e₀ + 2B` may **not** be read as
`O(log m₀)`; that would require `B = O(log m₀)`, the opposite direction. That step is withdrawn.

**What replaces it — a ratio, in which the `B`'s cancel.** With `Q ≥ (B+1)(log₂m₀ − c)` the
surrogate charge and `O_prefix ≤ e₀ + 2B` the proved bound, `(2+e₀)(B+1) ≥ e₀ + 2B` gives
(Lean: `surrogate_ratio_lower`)

```
Q / O_prefix  ≥  (log₂m₀ − c) / (2 + e₀) ,        e₀ depending only on c.
```

**The seeds are unbounded, by construction.** Realizers of a fixed prefix form a full residue class
mod `2^{S_N+1}`, so `leastRealizer + t·2^{S_N+1}` realizes the same prefix, stays odd, and exceeds
any prescribed `M` (Lean: `exists_large_realizer`); the re-entry count and prefix occupation depend
only on the word and are unchanged (Lean: `many_reentries_with_large_seed`). So `log₂m₀` really does
grow, and the ratio bound is not vacuous.

> **Proved obstruction.** On the constructed prefixes the coarse per-episode accounting
> overestimates the actual prefix occupation by a factor `Ω(log m₀)`, along an **unbounded** sequence
> of realizing seeds, and no choice of constants repairs it.

*(Checked at `c = 1`, `B = 5,10`, `t` up to `10³⁰`: the enlarged seed is odd and reproduces every
valuation; measured ratios `75.4`, `93.6` against proved lower bounds `25.1`, `28.9`.)*

*(Not formalized, and not needed above: by `boundedPrefixRealizers_iff_positiveRealizer`, the
**least** realizers are bounded iff some integer realizes the whole infinite word — which by §D
could never reach `1`. So either they are unbounded, and then `Q = Ω((log m₀)²)` along them, or a
positive orbit never reaches `1`.)*

**Scope.** Only the lower bound `P = Ω(log m₀)` is proved — the direction the argument needs;
`P = Θ(log m₀)` is not, and nothing bounds `O_prefix` by `O(log m₀)`. The obstruction concerns
**prefix** occupation; the **total** occupation of these seeds depends on the orbit beyond `N` and
is not controlled here, so the `O₁` column above remains a measurement. And it is an obstruction to
one accounting route, not to EOC and not to arguments that do not decompose per episode.

## G. The up-crossing band: what it does and does not say

`2m_{n+1} ≤ 3m_n + 1`, so a crossing of a **fixed integer level** `L` lands in `[L, (3L+1)/2)`
(Lean: `upcrossing_band`). This does not transfer to corridor re-entries: the threshold `Λ_n` is
real and moves, distinct re-entries cross distinct levels so their landings lie in different bands
whose union is uncontrolled, and injectivity holds only until the orbit cycles — for an orbit
reaching `1` it fails on the tail. What re-entry *does* force exactly is `d_n = 1` (§B), i.e.
`2m_{n+1} = 3m_n + 1`.

*(The first version drew an "exact obstruction" from counting all landings in one band. Retracted.)*

## H. The surviving question

Since `P = O(1)` is false and `P = Ω(log m₀)` is attained, the question is quantitative. With
episodes and re-entries as in §A, define for integer `c ≥ 0`

```
σ_c(p) := min { m odd, m > 0 : the orbit of m has at least p corridor episodes } .
```

A lower bound `σ_c(p) ≥ 2^{γp}` would give **episode count `O(log m₀)`**. The theorem of §F caps
`γ ≤ 6` outright (and the measured family caps it near `3.5`), since it exhibits seeds with `p`
episodes below `2^{6p+2e₀+3}`. Exhaustively over odd `m < 4·10⁶` (so `p ≤ 13`),
`log₂σ₁(p)/p` lies between `1.5` and `1.9`
— consistent with exponential growth, far too short a range to suggest a constant, and no
conjecture is offered.

**Honest label.** By `realizerCongruence` the seeds realizing a word form one residue class, so
`σ_c(p)` is the repository's existing **least-realizer / residue–time duality problem restricted to
a new family** — many-episode words in place of zero-confined words. A reformulation, not a new
mechanism; the two families are incomparable, and a larger family has a smaller minimum, so this is
not automatically easier.

**And it is not enough by itself.** `O_c = Σℓ_i`: bounding `P` says nothing about the lengths, and
§F shows the per-episode route cannot supply them. The estimate actually needed is joint:

> a bound on `Σ_i ℓ_i` that does **not** factor through per-episode single-window estimates,
> because each such estimate costs a full `log₂m₀` while there can be `Ω(log m₀)` episodes.

Any candidate must fit both measured regimes: random seeds give `P ≈ 1.7` with mean `ℓ ≈ 5.1`; the
family of §E gives `P ≈ 0.28 log₂m₀` with mean `ℓ ≈ 1.4`.

## I. Computations

All diagnostics; none promoted to a theorem. Episode-count maxima are reported at **constant sample
size per bucket**, since a maximum over a larger sample is larger for trivial reasons.

| quantity | result |
|---|---|
| entry lemma `d_{a−1}=1`, `c_a ∈ [0,α−1)` | 97,091 re-entries, `c ∈ {0,1,2,5}`, **0 counterexamples** |
| reframing `R_n ≤ c ⟺ m_n ≥ m₀2^{E_n−c}` | 29,999 seeds, **0 mismatches** |
| `O_c ≤ n*` (arrival at 1) | 29,999 seeds, **0 violations** |
| realization of constructed prefixes vs the actual map | `N = 10…60`, **all valuations reproduced** |
| mean `P`, 2000 seeds/bucket, `log₂m₀ = 13…24` | **1.64 – 1.75, flat** |
| mean episode length, same buckets | **4.85 – 5.31, flat** |
| mean `O₁`, same buckets | **8.1 – 9.1, flat** |
| max `P` / max episode length, same buckets | 8–11 / 55–123, sampling-sensitive, no trend inferred |

## J. What this investigation establishes, and what it does not

**Establishes.** The episode decomposition, restart relation and local threshold, exactly and
formalized; the entry lemma pinning every re-entry threshold below `α−1`; that occupation ends at
arrival at `1` for **every** seed, hence the bridge from a stopping bound to an occupation bound;
that **bounded episode count is false**, with episode counts `Ω(log m₀)` realized by seeds of
controlled size; and that the per-episode single-window accounting overestimates prefix occupation
by a factor `Ω(log m₀)` along an unbounded sequence of realizing seeds.

**Does not establish.** It does not prove or disprove EOC at any tier. The step **(U) ⟹ `O(log m)`
stopping time** is imported, not formalized, so "(U) ⟹ EOC" is a proved bridge on top of an
unformalized layer. `P = Θ(log m₀)` is not proved — only `Ω` — and prefix occupation is **not**
shown to be `O(log m₀)`; only the accounting *ratio* is controlled. Nothing is proved about the **total**
occupation of the constructed seeds, only about their prefixes; the constants `0.28`, `0.42`, `1.4`
are computational. It gives no bound on `σ_c(p)`. It does not show per-episode accounting is the
only route. The flatness of mean `P` on random seeds is a diagnostic only — §E shows it is not a
law.
