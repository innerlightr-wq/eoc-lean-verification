# Separated returns: correction audit

*Every claim of `docs/SEPARATED_RETURNS_INVESTIGATION.md` (commit `8493f55`) re-derived from the
definitions, with each incorrect claim identified, replaced, and given a mathematical status.
Branch `separated-returns-correction`, base `8493f55` (verified against `origin`).*

Prompted by an external review. Neither the earlier report nor the review was taken as
authoritative: every item below was checked independently, and one of the review's own suggested
framings is narrowed in §G.

Revision 6 remains frozen. Manuscript consequences are deferred to
`docs/REVISION7_DEFERRED_ITEMS.md`.

---

## A. Summary table

| # | Claim in `8493f55` | Status | Replacement |
|---|---|---|---|
| 1 | Episode threshold "*widens* exactly as far as the drift has fallen by the entry time" | **False** | Entry lemma: at a re-entry `d_{a−1}=1` and `0 ≤ c_a < α−1 ≈ 0.585`. The threshold is *pinned*, never widens. |
| 2 | "later episodes are governed by a different, **larger** corridor" | **False** | Later corridors are *narrower* than `c` whenever `c > α−1`. |
| 3 | `E_∞ < ∞` used as a finite constant in the conditional theorem | **Unsupported** | `T(1)=1`, so on every orbit reaching `1` the carry grows by `log₂(4/3)` per step: `E_∞ = +∞`. |
| 4 | "`E_n ≤ 0.275` across the tested range" | **Wrong number** | `0.190665` over corridor times; `0.325550` over all orbit times (seed `993`). |
| 5 | **(P)** "`P_c(m₀) ≤ P₀` … entirely unstudied", offered as the isolated new hypothesis | **Refuted** | False for every `c`. Constructive, formalized. |
| 6 | Conditional theorem **(U)**+**(P)** ⟹ EOC | **Withdrawn** | (P) is false, and (U) alone already suffices. |
| 7 | "**(U)** alone is insufficient" | **False** | (U) ⟹ stopping bound ⟹ occupation ends at arrival at `1`. Formalized. |
| 8 | Missing inequality is "*equivalent*" to bounding episode count; "no redistribution" | **Overstated** | One-way, and only for the surrogate sum. Many short episodes *do* compensate — demonstrated on an explicit family. |
| 9 | "the route requires **`P = O(1)`**" | **False** | `P = O(1)` is impossible; `P = O(log m₀)` with `O(1)` lengths is what actually occurs. |
| 10 | Up-crossing band applied to corridor returns; "distinct returns consume distinct orbit values of that band" | **Mis-applied** | The threshold `Λ_n = m₀2^{E_n−c}` moves with `n`; distinct re-entries have distinct bands and the union is uncontrolled. |
| 11 | "**Exact obstruction** … no sharpening of the band changes that" | **Overstated** | A failed coarse estimate, not an impossibility theorem. |

**Unaffected and still correct:** the restart relation `R_{a+k}(m₀) = R_a(m₀) + R_k(m_a)`
(`sum_concat`); the reframing identity `R_n ≤ c ⟺ m_n ≥ m₀·2^{E_n−c}` (29,999 seeds, 0 mismatches);
`count_le_of_summands_ge` as an arithmetic fact; `upcrossing_band` as a fixed-level statement; the
controlled computations of §G of the old report.

---

## B. Correction 1 — the entry threshold is pinned, not widened

Let `a > 0` be a genuine re-entry: `R_{a−1} > c`, `R_a ≤ c`, and `R_a = R_{a−1} + d_{a−1} − α`.

Since `1 < α < 2` and `d_{a−1} ≥ 1` is an integer, `d_{a−1} ≥ 2` would give
`R_a ≥ R_{a−1} + (2−α) > R_{a−1} > c`, contradicting `R_a ≤ c`. Hence

```
d_{a−1} = 1 ,          c − (α−1) < R_a ≤ c ,          0 ≤ c_a := c − R_a < α − 1 .
```

**Formalized integrally**, with no real numbers: for integer `c` the corridor is
`2^{S_n} ≤ 2^c·3^n`, and

* `entry_digit_one` — a digit `≥ 2` multiplies `2^S` by `≥ 4` while the bound multiplies by `3`, so
  a point already above the bound cannot return under it;
* `entry_threshold_pinned` — `2·(2^c·3^{a}) < 3·2^{S_a}`, which is exactly `c_a < log₂(3/2) = α−1`;
* `entry_threshold_real` — the real-number reading, once the digit is known to be `1`.

**Verified exactly:** 97,091 re-entries over odd `m₀ < 60001` at `c ∈ {0,1,2,5}` — every one has
`d_{a−1} = 1`, every one has `c_a ∈ [0, α−1)`, maximum observed `c_a = 0.571438 < 0.584963`.

**Consequence for the old report.** The stated *reason* single-window theory fails to control
occupation ("later episodes live in a larger corridor") is wrong. Only the first episode has
threshold `c`; every later one has threshold `< α−1`, a universal constant. The real reason
single-window theory does not control occupation is simply that it controls the length of one
window and says nothing about how many windows there are.

Drift can still go far below `c` *inside* an episode. That is a statement about the interior, and
the old report conflated it with the entry point.

---

## C. Correction 2 — (P) is false

**Construction.** Fix `c ≥ 0`. Define a valuation word by the symbolic rule

* digit `2` when `R_n ≤ c` (drift rises by `2−α > 0`);
* digit `1` when `R_n > c` (drift falls by `α−1 > 0`).

Three facts, all formalized (`oscS`, `oscD`, `InC`):

1. **Invariant** `3·2^{S_n} ≤ 4·(2^c·3^n)` (`osc_invariant`) — the drift never rises more than
   `log₂(4/3)` above `c`.
2. **Immediate re-entry** `¬InC n → InC (n+1)` (`reentry_immediate`) — one digit-`1` step always
   returns, since a fall of `log₂(3/2)` exceeds a rise of `log₂(4/3)`.
3. **Exit always recurs** (`exists_exit_ge`) — staying in the corridor means digit `2` forever,
   multiplying `2^S` by `4` per step against a bound multiplying by `3`; `(4/3)^j` is unbounded, so
   the corridor condition fails within `3·2^c·3^n` further steps. (Proved from a Bernoulli
   inequality `3^j(3+j) ≤ 3·4^j`, formalized.)

So exits recur forever, and each is followed immediately by a re-entry: `exists_horizon_many_reentries`
gives, for every `B`, a horizon `N` with at least `B` re-entries before `N`.

**Realization bridge.** `EOC/Realizer.lean` already supplies it. For digits `≥ 1`,
`leastRealizer d N` is odd (`leastRealizer_odd`) and satisfies the exact realizer congruence
(`leastRealizer_modEq`), so by `realizerCongruence` it genuinely realizes the prefix:
`a (orbit m₀ i) = d i` for all `i < N`. Its prefix sums therefore *equal* `oscS` on `[0,N]`, so the
re-entry count is a statement about that orbit's own drift, not about a symbolic word.

> **Theorem** (`exists_odd_seed_with_many_reentries`). For every `c` and every `B` there is an odd
> `m₀ > 0` and a horizon `N` such that the genuine accelerated orbit of `m₀` follows the word for
> `N` steps and has at least `B` corridor re-entries before time `N`.

Hence **(P) is false for every `c`.**

**Scope, stated explicitly.** The realizing seed grows with `B` (only `m₀ < 2^{S_N+1}` is known
from above). The count is a **finite-horizon** count of re-entries before `N`. Nothing is inferred
about infinite realization, and nothing about these seeds' total occupation follows from the
construction — that is computed separately in §E.

**Verified against the genuine map.** For `c = 1` the word begins
`222121221212212121221212212121` (digits `1` and `2` only, as the construction requires). At
`N = 60`: `S_N = 96`, `leastRealizer = 136975455177362381873293329281` (odd), and running the
*actual* accelerated map from that seed reproduces all 60 valuations. Same check at
`N = 10,20,30,40,50`. The Lean definitions were independently re-implemented and agree exactly:
same word, `exitTime 1 = [3,5,8,10,13,15,17,20]`, `|reentries(1,60)| = 24`.

---

## D. Correction 3 — (U) alone already implies an occupation bound

`T(1) = (3·1+1)/2^{ν₂(4)} = 1`, so an orbit that reaches `1` stays there. From the aggregate
identity with `m_n = 1`,

```
2^{S_n} = 3^n·m₀ + C_n  >  3^n·m₀  ≥  2^c·3^n        whenever  2^c ≤ m₀ ,
```

using `C_n > 0` for `n ≥ 1`. So **no time at which the orbit equals `1` lies in the corridor**
(`corridor_excludes_one`), hence every corridor time precedes arrival at `1`
(`corridor_time_lt_of_reaches_one`), hence

```
O_c(m₀)  ≤  n*(m₀)            (occupation_le_of_reaches_one)
```

for every `m₀ ≥ 2^c`. The lifetime audit already established that **(U)** is equivalent to an
`O(log m)` total-stopping-time bound. Therefore **(U) ⟹ `O_c(m₀) = O(log m₀)` ⟹ EOC**, with no
second hypothesis.

Verified: 29,999 seeds, `c = 1`, **0 violations** of `O_c ≤ n*`.

The old report's "(U) alone is insufficient" is withdrawn, and with it the conditional theorem,
which added a false hypothesis to a sufficient one.

This is not good news for the programme: it relocates the difficulty rather than reducing it. (U)
implies Collatz, so "(U) ⟹ EOC" is a statement about a hypothesis strictly stronger than the
problem EOC is meant to help with. The point of recording it is that **the gap the separated-returns
investigation set out to fill does not exist**: there is no missing return-counting hypothesis
between (U) and EOC.

---

## E. Correction 4 — the "no-tradeoff" conclusion, narrowed and then refuted as stated

The arithmetic fact is untouched: `f_i ≥ B > 0` and `Σf_i ≤ T` give `P·B ≤ T`. Three things must be
kept apart, and the old report ran them together:

1. actual episode lengths `ℓ_i`;
2. the coarse upper bounds `1 + K(log₂ m_{a_i} + c_i)` assigned to them under (U);
3. an independently proved bound on the sum of those upper bounds.

A lower bound on (2) is **not** a lower bound on (1). What survives is only:

> If one bounds occupation by summing those particular coarse estimates and wants `O(log m₀)`, then
> `P = O(1)`.

It does not follow that occupation is `O(log m₀)` only when `P = O(1)`, and the old report's
"*equivalent*" and "there is no redistribution to be found" are withdrawn.

**Refuted concretely, inside the programme.** The seeds built in §C have, for `c = 1`:

| `N` | `log₂ m₀` | episodes `P` | occupation `O₁` | `O₁/log₂m₀` | `P/log₂m₀` |
|---|---|---|---|---|---|
| 20 | 32.73 | 8 | 13 | 0.397 | 0.244 |
| 40 | 58.64 | 18 | 26 | 0.443 | 0.307 |
| 60 | 96.79 | 25 | 41 | 0.424 | 0.258 |
| 80 | 127.74 | 34 | 49 | 0.384 | 0.266 |

So `P ≈ 0.28·log₂m₀` episodes of mean length `≈ 1.4` give `O₁ ≈ 0.42·log₂m₀`. **Many short episodes
compensate exactly as the review said they could**, and these orbits satisfy EOC comfortably while
violating (P) badly.

**What this does establish — a real, and now proved, obstruction to the surrogate route.** On this
explicit family `P = Θ(log m₀)`, so the surrogate sum is
`≥ P·K·(log₂m₀ − c) = Θ((log m₀)²)` while the truth is `Θ(log m₀)`. The per-episode single-window
estimate is therefore **provably lossy by a factor `Θ(log m₀)` on an exhibited family**, and no
choice of constants repairs it.

That is a much better statement than the one it replaces, and it is correctly scoped: it is an
obstruction to *one accounting route*, not to EOC and not to every argument.

---

## F. Correction 5 — the carry term and the moving band

**The threshold moves.** `Λ_n = m₀·2^{E_n−c}`, and `R_n ≤ c ⟺ m_n ≥ Λ_n` is an exact identity, so
that much stands. But `Λ_n` depends on `n` through `E_n` and may not be replaced by the fixed
starting scale without a proved comparison. The old report's gloss — "`O_c` is the total time at or
above `2^{−c}` times the starting value" — is valid only where `E_n` is small. Measured: over
corridor times the maximum is `0.190665`; over whole orbits `0.325550`. Over the tail at `1` it is
unbounded.

**`E_∞` is not a constant.** With `m_n ≡ 1` the carry gains `log₂(4/3) = 0.415037` per step, so
`E_∞ = +∞` on *every* orbit reaching `1`. Its appearance as a finite constant in the old
conditional theorem is removed. Even a seedwise-finite carry bound would need quantitative uniform
control to imply anything.

Two precisions, so that nothing here reads as over-retracted or inconsistent with earlier audits:

* `E_∞ < ∞` **is** correct in its original setting — a *divergent* orbit has `m_n → ∞`, hence
  `Σ1/m_j < ∞` (Curry), hence a finite carry limit. `docs/CURRY_FOUNDATION.md` and
  `docs/CURRY_DIVERGENCE_PART2_AUDIT.md` are unaffected. The error was quantifying that
  divergent-orbit fact over *all* orbits inside a theorem whose conclusion was about every seed.
* the measured maximum `0.325550` (odd `m₀ < 60001`, attained at seed `993`, whose whole orbit has
  length 32) does not contradict the `max E ≤ 0.245` recorded in
  `docs/TIME_AXIS_DRIFT_EXIT_IMPOSSIBILITY_AUDIT.md` §AS: that figure was taken over a narrower
  sample, and a maximum over a larger sample is larger for trivial reasons. Neither figure is a
  bound on anything.

**The band argument.** `upcrossing_band` is true and is retained, but it is a statement about a
**fixed integer level** `L`: from `2m_{n+1} ≤ 3m_n + 1`, a crossing lands in `[L, (3L+1)/2)`. It is
not a statement about corridor re-entries, because

* the corridor threshold is real and moves with `n`;
* different re-entries cross different levels, so their landings lie in different bands and their
  union is not controlled by this lemma;
* injectivity is available only while the orbit has not cycled — for an orbit reaching `1` it fails
  on the tail outright.

What re-entry *does* force exactly is `d_n = 1` (§B), i.e. `2m_{n+1} = 3m_n + 1`: the
maximal-growth step. The docstring now says this.

Finally, "no sharpening of the band changes that" is withdrawn. Sharpness of the one-step growth
constant `3/2` says nothing about whether some stronger orbit-dependent counting argument exists.

---

## G. The surviving research target

Since `P = O(1)` is false and `P = Θ(log m₀)` is attained, the right question is quantitative.

**Definition.** Fix `c ≥ 0` integer. For `p ≥ 1` let

```
σ_c(p) := min { m odd, m > 0 : the accelerated orbit of m has at least p corridor episodes }
```

with the conventions fixed in §C: episodes are the maximal contiguous runs of `{n : R_n ≤ c}`; the
episode beginning at `n = 0` counts (`R_0 = 0 ≤ c` always), and re-entries are counted by their exit
time, so `#episodes = #re-entries + 1`. For a seed reaching `1`, all of these are finite by §D.

**Why a lower bound would be the useful thing.** If `σ_c(p) ≥ 2^{γp}` for some `γ > 0` and all large
`p`, then any seed with `p` episodes satisfies `p ≤ log₂(m₀)/γ`, i.e. **episode count is
`O(log m₀)`** — exactly the scale the refuting family attains, so `γ` cannot exceed about `3.5`.

**Measured** (exhaustive over odd `m < 4·10⁶`, so only small `p` are reachable):

| `p` | 1 | 2 | 3 | 5 | 8 | 10 | 12 | 13 |
|---|---|---|---|---|---|---|---|---|
| `σ₁(p)` | 25 | 129 | 195 | 417 | 25729 | 38881 | 1183959 | 1183959 |
| `log₂σ₁(p)/p` | 4.64 | 3.51 | 2.54 | 1.74 | 1.83 | 1.52 | 1.68 | 1.55 |

`log₂σ₁(p)/p` sits between `1.5` and `1.9` over the reachable range. That is consistent with
exponential growth but is **not** evidence for a particular constant: `p ≤ 13` is a very short
range, the ratio is not monotone, and an exhaustive search is bounded by the search limit, not by
the mathematics. No conjecture is offered.

### Honest labelling: this is not a new kind of problem

By `realizerCongruence`, the seeds realizing a given finite word form one residue class modulo
`2^{S_N+1}`, so

```
σ_c(p) = min { leastRealizer(W, |W|) : W a finite valuation word with ≥ p corridor episodes } ,
```

and `DriftExit.realizerFloor_of_lifetime` is already the general inversion lemma for this transfer.
So **this is the repository's existing least-realizer / residue–time duality problem, restricted to
a new family of words** — the many-episode family, in place of the zero-confined family. It is a
reformulation, not a new mechanism.

Two honest caveats:

* the many-episode family neither contains nor is contained in the confined family (confinement is
  one long episode; this is many short ones), so no reduction in either direction is claimed;
* a larger family has a smaller minimum, so a lower bound on `σ_c(p)` is not automatically easier
  than the confined-word bounds already sought.

### Episode-count control alone still does not give EOC

`O_c = Σ_{i=1}^{P} ℓ_i`. Bounding `P` says nothing about `Σℓ_i`, and §E shows the per-episode
single-window estimate is provably too lossy to close the gap. So the estimate actually needed is
the **joint/weighted** one:

> a bound on `Σ_i ℓ_i` that does **not** factor through per-episode single-window estimates,
> because each such estimate costs a full `log₂ m₀` while there can be `Θ(log m₀)` episodes.

Stating that requirement precisely is the genuine content of this correction. Two measured
constraints any candidate must respect: on random seeds `P ≈ 1.7` with mean `ℓ ≈ 5.1`; on the
refuting family `P ≈ 0.28 log₂ m₀` with mean `ℓ ≈ 1.4`. Neither factor alone is the mechanism.

No computations beyond those reported here are recommended, and no novelty is claimed for the
reformulation.

---

## H. Deliverables and verification

* **Lean.** `EOC/SeparatedReturns.lean`, 15 theorems, builds clean under Lean `4.34.0-rc1` +
  Mathlib. Every theorem checked with `#print axioms`: `[propext, Classical.choice, Quot.sound]`
  (four need only `[propext, Quot.sound]`). No `sorry`, `admit`, `axiom`, `opaque`, `native_decide`.
* **New:** `entry_digit_one`, `entry_threshold_pinned`, `entry_threshold_real`,
  `corridor_excludes_one`, `corridor_time_lt_of_reaches_one`, `occupation_le_of_reaches_one`,
  `osc_invariant`, `reentry_immediate`, `exists_exit_ge`, `exists_horizon_many_reentries`,
  `exists_odd_seed_with_many_reentries`, `S_oscD`.
* **Retained, docstrings corrected:** `sum_concat`, `count_le_of_summands_ge`, `upcrossing_band`.
* **Paper-level, not formalized:** the equivalence "(U) ⟺ `O(log m)` stopping time" is imported from
  the earlier lifetime audit (its real-analytic absorption step was never formalized); the
  `Θ((log m₀)²)` lossiness of the surrogate route in §E is arithmetic over measured data, not a Lean
  theorem; the `σ_c(p)` table is computation.
* **Exact checks:** entry lemma on 97,091 re-entries (0 counterexamples); reframing identity on
  29,999 seeds (0 mismatches); `O_c ≤ n*` on 29,999 seeds (0 violations); realization of the
  constructed prefixes against the genuine map at `N = 10…60`; the Lean definitions re-implemented
  independently and matched exactly (word, exit times, re-entry counts); counting conventions
  audited (`#episodes = #re-entries + 1`; `reentries c N` is indexed by exit time, and every index
  it touches lies within the realized prefix, so there is no off-by-one gap).

Scripts: `scratch/correct.py`, `scratch/correct2.py`, `scratch/refuteP.py`, `scratch/sigma.py`,
`scratch/joint.py`, `scratch/conventions.py`, `scratch/family_eoc.py`.
