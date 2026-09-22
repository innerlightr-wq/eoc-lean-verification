# Time-axis drift-exit / divergence-impossibility audit

Zero-corridor lifetimes, drift stopping times, and the qualitative time axis of EOC.

## A. Starting state

| item | value |
|---|---|
| base commit | `1bb5826e68777859345ba3b42bcdbfc5159ceb09` (`Record commit hash and push status in the audit report`) |
| verified how | `git fetch origin`, then `git rev-parse origin/positive-orbit-confinement-lifetime-audit` |
| ordinary checkout | **dirty** (53 entries). Not touched. |
| worktree | isolated, `scratchpad/eoc-ta`, `.lake/packages` symlinked |
| branch | `time-axis-drift-exit-impossibility-audit` |
| `main` | untouched. No PR. |

## B. Residue / time / occupation axes (Gate 0)

For odd `m`, `m_0 = m`, `2^{d_{n+1}}m_{n+1} = 3m_n + 1`, `S_n = Σ_{j≤n}d_j`, `R_n = S_n − nα`,
`α = log₂3`, `Q_n = Π_{j<n}(1+1/(3m_j))`, `E_n = log₂Q_n ≥ 0`.

| axis | object |
|---|---|
| **residue** | `r_min(N,c)` — least positive odd `m` whose first `N` valuation symbols form a `c`-confined word |
| **time (single window)** | `L_c(m) = max{N : R_j(m) ≤ c for all 0 ≤ j ≤ N}` — one *contiguous* episode |
| **occupation** | `O_c(m) = #{n ≥ 0 : R_n ≤ c}` — the *total* over all separated returns |

These are not interchangeable: `L_c` measures the initial episode, `O_c` sums all episodes (§AH).

**Everything is purely integral.** Since `S_n ∈ ℤ` and `nα = log₂(3^n)`,

```
R_n ≤ 0  ⟺  2^{S_n} ≤ 3^n ,        R_n > 0  ⟺  3^n < 2^{S_n} .
```

Verified on 99,999 seeds, 0 mismatches. The whole audit is conducted in this form, so no
real-number reasoning enters.

## C. Lifetime-frontier inversion (Gate 1)

`L_0(m) ≥ N` iff the first `N` symbols of `m`'s valuation word are `0`-confined, by definition.
Hence

```
r_min(N,0) = min{ m odd > 0 : L_0(m) ≥ N }.
```

Lean: `realizerFloor_of_lifetime` states the usable direction — if every `m < B` has `L_0(m) < N`
then every `m` with `L_0(m) ≥ N` satisfies `m ≥ B`.

**Novelty check.** This inversion is the "record chronology" used implicitly throughout the
programme; it is elementary and is *not* claimed as new. What is recorded here is the explicit
statement and its Lean form.

## D. Quantitative time-axis duality (Gate 2)

| lifetime bound `L_0(m) ≤ F(log₂m)` | resulting floor |
|---|---|
| `F(x) = Kx` | `log₂ r_min(N) ≥ N/K` — **exponential**, Open Problem C |
| `F(x) = Kx^p` | `log₂ r_min(N) ≥ (N/K)^{1/p}` — stretched exponential |
| `F(x) = K·2^{θx}` (i.e. `≤ K m^θ`) | `r_min(N) ≥ (N/K)^{1/θ}` — **polynomial** |
| `F(x) = K·2^{x}` (i.e. `≤ K m`) | `r_min(N) ≥ N/K` — linear |

The previous branch showed the `F(x) = Kx` case is essentially the `O(log n)` total-stopping-time
conjecture. **This branch does not attempt that.** The table's point is §AM: weaker scales still
transfer.

## E. Drift exit time (Gate 5)

```
τ_c(m) := inf{ n ≥ 1 : R_n(m) > c },      τ_0(m) = inf{ n ≥ 1 : 3^n < 2^{S_n} }.
```

`τ_0(m) = ∞` exactly when the orbit stays in the zero corridor forever. **"Drift exit time" is
used as a working name only**; §AC finds no standard term for it, and §J shows the underlying
statement is not new.

## F. Ordinary stopping time (Gate 3)

`σ(m) := inf{n ≥ 1 : m_n < m}`. This is Terras's **stopping time** (Roosendaal's *glide*), not the
total stopping time of the previous branch.

## G. Drift exit versus ordinary descent (Gate 3, 13, 14)

From `2^{S_n}m_n = 3^n m_0 + C_n` with `C_n > 0` (Lean: `carry_pos`):

> **Future-minimum theorem.** `2^{S_n} ≤ 3^n ⟹ m_0 < m_n` (Lean:
> `zeroCorridor_implies_seed_lt`). An orbit that never exits the zero corridor has its seed as a
> **strict minimum of its entire future**.

Contrapositive (Lean: `driftExit_of_not_gt`): `m_n ≤ m_0 ⟹ 3^n < 2^{S_n}`. Note the *weak*
inequality suffices. Hence

```
σ(m) < ∞  ⟹  τ_0(m) < ∞,      and     τ_0(m) ≤ σ(m).
```

Equivalently, via `log₂m_n = log₂m_0 − R_n + E_n` (verified, 0 mismatches): descent needs
`R_n > E_n`, drift exit only `R_n > 0`, and `E_n > 0`. So drift exit is a **formally weaker**
barrier. §H measures how much weaker.

## H. Strictness examples (Gate 4) — and a correction to my own search

**Initial finding, and why it was misleading.** Scanning odd `m ∈ [3, 200001]`: `τ_0(m) = σ(m)` in
**every** case; `min(R_τ − E_τ) = 0.0158`; `max E_τ = 0.245`; `min R_τ = 0.01654` (at `τ = 41`,
where `1 − {41α} = 0.016537` — the Diophantine bound is attained exactly).

**The structural reason.** At `n = τ_0`, strictness needs `R_n ≤ E_n`. Under zero confinement for
`j < n`, §G gives `m_j > m_0`, so `E_n ≤ (1/(3ln2))Σ_{j<n}1/m_j ≤ 0.4809·n/m_0`. And `S_n ∈ ℤ`
with `R_n > 0` forces `R_n ≥ 1 − {αn}`. Therefore strictness at depth `n` requires

```
m_0  ≤  0.4809·n / (1 − {αn})        and simultaneously      m_0 ≥ r_min(n,0).
```

Since `α` has finite irrationality measure, the upper bound is **polynomial in `n`**. So:

> **Any superpolynomial least-realizer floor forces `τ_0 = σ` for all large seeds.**

Exhaustive search of every odd `m` below the size bound, at every depth `n < 200` where the bound
is not already violated by `r_min(n,0)`: **0 strict examples** (largest `m` searched: 6724).

**But strictness is real, and I missed it by starting the scan at `m = 3`.** For `m = 1`:
`d ≡ 2`, `S_n = 2n`, `R_n = (2−α)n = 0.415n > 0`, so `τ_0(1) = 1`; while `σ(1) = ∞`, nothing
being below `1`. Moreover `R_n = E_n` **exactly** on the trivial cycle (both `0.4150n`), since
`m_n = m_0` forces `log₂m_n = log₂m_0`.

> **`τ_0 < σ` occurs exactly at cycle minima.** At the minimum element of any genuine positive
> cycle, `σ = ∞` while the cycle's positive period drift (§O) gives `τ_0 < ∞`.

This is precisely why drift exit is weaker than Collatz: it tolerates cycles. Away from cycle
minima, the two coincide in everything tested, for the reason above.

## I. Qualitative drift-exit statement (Gate 5)

```
(DE)   For every odd m ≥ 1 there is n ≥ 1 with   3^n < 2^{S_n(m)} .
```

Integer form throughout; no floors, no reals, no irrationality input.

## J. Relation to prior zero-corridor / Chain-B work (Gate 6, 34, 35) — mandatory novelty audit

**(DE) is not new.** Its negation is "some positive integer has an infinite `0`-confined orbit",
which is `docs/CURRY_FOUNDATION.md` §8.9's stated frontier —

> *Determine whether an infinite zero-confined, diverging-deficit valuation word can be realized by
> a positive ordinary integer under the accelerated Collatz map* —

and the object of `docs/ZERO_CORRIDOR_REALIZABILITY_FRONTIER.md`. The two match exactly once §L's
argument supplies the "diverging-deficit" clause from plain zero confinement.

**Acronym discipline (Gate 35).** ZCRE in this repository is
`ZCRERealizerGrowth.boundedPrefixRealizers_iff_positiveRealizer` — bounded prefix realizers ⟺
positive-integer realizability. That is a *realizer* statement about words; (DE) is an *orbit*
statement. They are related but not identical, and **no new acronym is coined here**: the report
uses "drift exit" as a descriptive phrase and defers to the repository's existing frontier naming.

The contribution of this section is therefore a **reclassification**, not a theorem: the existing
frontier is exactly a qualitative time-axis statement.

## K. Curry last-global-maximum reduction (Gate 7) — already in the repo

`docs/CURRY_FOUNDATION.md` §8.5 and `EOC/CurryFoundation.lean` already contain this: `R_n → −∞`
(Level B) gives a **last** global maximiser `n₀` (`exists_last_atBot_max`), and restarting there,
`R'_k = R_{n₀+k} − R_{n₀} < 0` strictly for `k ≥ 1`, hence `S'_k ≤ ⌊kα⌋` — `zero_corridor_tail`.
The repo even records a correction there (the step needs no irrationality of `α`).

**Not claimed as new.** It is cited and reused.

## L. Drift exit excludes Type II (Gate 8)

Type-II ⟹ (Curry, Level B) `R_n → −∞` ⟹ last global max at `n₀` ⟹ restart at the actual positive
integer `m* = m_{n₀}` has `R'_k < 0` for all `k ≥ 1` ⟹ `τ_0(m*) = ∞` ⟹ ¬(DE).

Dependencies, exactly: Curry's reciprocal summability (Level A, audited), `R_n → −∞` (Level B),
`exists_last_atBot_max`, and nothing else. **No cycle assumption is used.**

## M. Converse: no Type II implies drift exit (Gate 9)

Suppose ¬(DE): some `m` has `2^{S_n} ≤ 3^n` for all `n ≥ 1`.

- The orbit cannot repeat: if `m_{p+1} = m_0` then `2^{S_{p+1}}m_0 = 3^{p+1}m_0 + C_{p+1} >
  3^{p+1}m_0`, so `3^{p+1} < 2^{S_{p+1}}` (Lean: `cycle_driftExit`) — contradiction. The same
  applies to any repeat along the orbit, restarting at the repeated state.
- So the orbit is injective; injective + positive gives `m_n → ∞` (the repo's Type-I/Type-II
  classification), i.e. Type II.

Hence ¬(DE) ⟹ Type II.

## N. Divergence-equivalence theorem (Gate 9)

Combining §L and §M:

> **(DE) ⟺ there is no Type-II divergent positive orbit**, given Curry's audited input and the
> repository's orbit classification.

Both directions are elementary given those inputs; §K notes the harder direction was already
formalized.

## O. Cycle compatibility (Gate 26)

A genuine cycle has `2^{S_p} > 3^p` (Lean: `cycle_driftExit`), so every point of a cycle — and,
by finitely many steps, every transient point entering one — has finite `τ_0`. Therefore

> **(DE) is fully compatible with hypothetical nontrivial cycles.** The time axis is a
> *divergence* obstruction, never a cycle obstruction.

This is the exact sense in which (DE) is strictly weaker than the full Collatz conjecture.

## P. Single-window versus occupation hierarchy (Gate 12, 32)

| level | statement | strength |
|---|---|---|
| 1 | `L_0(m) < ∞` for every `m` — i.e. (DE) | qualitative |
| 2 | `L_0(m) = O(log m)` | quantitative single window; ⟹ Open Problem C (§D) |
| 3 | `O_0(m) < ∞` for every `m` | total occupation |

Level 3 ⟹ Level 1 trivially (`L_0 ≤ O_0`). Level 1 ⇏ Level 3: an orbit may re-enter the corridor
infinitely often in separated episodes while every episode is finite. Level 2 ⟹ Level 1; Level 1
⇏ Level 2 (no rate). A Type-II orbit has `O_c = ∞` for every fixed `c`, so **any** theorem giving
`O_c(m) < ∞` for one fixed `c` would also exclude Type II — finite occupation is strictly stronger
than finite initial exit.

## Q. Infinite-final-episode formulation (Gate 33, 34)

Decomposing `{n : R_n ≤ c}` into maximal contiguous intervals, `O_c` is the sum of episode
lengths. **Divergence exclusion needs only the absence of an infinite final episode** — neither
episode counts nor episode lengths in general. That is the weakest time-axis target, and it is
exactly (DE) at `c = 0` after the §K restart.

## R. Zero corridor implies future minimum (Gate 13)

§G, Lean `zeroCorridor_implies_seed_lt`. Verified: 0 violations over 99,999 seeds.

## S. Eternal-future-minimum route (Gate 15)

A Type-II orbit restarted at its last `R`-maximum gives a positive `m` with `m_n > m` for every
`n ≥ 1` *and* `R_n < 0` for every `n ≥ 1`. The first property alone — "`m` is a strict future
minimum forever" — is equivalent to `σ(m) = ∞`, and proving it impossible for all `m` is exactly
the (open) finiteness of Terras's stopping time, which implies Collatz by strong induction.

The drift restriction `R_n < 0` is formally stronger than `m_n > m` (§G: `R_n ≤ 0 ⟹ m_n > m_0`,
not conversely). §H shows the gap is `E_n`, bounded by `0.245` in everything tested and
`≤ 0.4809n/m_0` in general — **so the extra leverage is at most logarithmic and vanishes for large
seeds.**

## T. Prefix-average formulation (Gate 16)

(DE) says `∃n : (1/n)Σ_{j<n}d_j > α`. Its negation is that **every** prefix average of the
valuation word is `≤ α`. Word-level versions of this are defeated by the cardinality barrier
(§AI), so any proof must use the ordinary `m_j`.

## U. Actual multiplicative growth (Gate 17)

`m_n = m_0 2^{−R_n}Q_n ≥ m_0 Q_n > m_0` under zero confinement, and `R_n → −∞` gives `m_n → ∞`
with `log₂(m_n/m_0) = −R_n + E_n`. Ordinary values grow at exactly the rate the drift falls.

## V. Recovery-event dynamics (Gate 18, 19)

`ΔR_n = d_n − α`: `d = 1` costs `α−1 = 0.585`; `d ≥ 2` gains. An infinite zero-corridor orbit must
balance `d=1` runs against recoveries without crossing `R = 0`. Symbolically this is free
(full-shift constructions). The only actual-orbit input is the valuation cap of §X.

## W. Recovery timing (Gate 19)

No temporal inequality between gap length and recovery valuation was found that is not already a
consequence of the cap in §X. The cap is a statement about the *current iterate*, not about
timing, and §X shows it is never binding.

## X. Large-valuation recovery cost (Gate 20, 46) — and why it fails

At an actual iterate, `2^{d_n} ∣ 3m_n+1`, so `2^{d_n} ≤ 3m_n + 1`
(Lean: `OrbitLifetime.valuation_le`). The *sufficient* condition for drift exit in one step is
(Lean: `driftExit_of_valuation`)

```
2^{d}·m_0 > 3·m_n .
```

So the required valuation is `2^d > 3m_n/m_0`, while the available cap is `2^d ≤ 3m_n + 1`.

> **The cap exceeds the requirement by a factor of about `m_0`.**

## Y. Excursion clock (Gate 21) — closed

Deep dives cost time (`≥ G/(α−1)` steps to reach depth `G`), but that is a *lower* bound on
lifetime and cannot bound it above. Recovery may occur in one step. No usable clock.

## Z. Restart invariance (Gate 22, 23)

Every iterate is itself a valid seed, so (DE) applies at every point: no orbit point can be a
permanent future `R`-maximum. That is exactly the content of §L read backwards, and yields no
additional record process — §AA explains why.

## AA. Record increments (Gate 24) — mandatory anti-overclaim

`R_k = S_k − kα` with `α` irrational, so positive values can be arbitrarily close to `0`
(Diophantine approximation). Measured: `min R_τ = 0.01654` at `τ = 41`, exactly
`1 − {41α}`. **Repeated positive exits therefore do not give a uniform positive drift increment**,
and no "records must grow" argument is available.

## AB. Diophantine gap audit (Gate 25)

`R_n > 0` with `S_n ∈ ℤ` gives `R_n ≥ 1 − {αn}`, which is `≫ n^{−μ}` for the irrationality measure
`μ` of `α`. This is used once, in §H, to show the strictness window is polynomial. It gives no
temporal leverage: the bound is a lower bound on the *overshoot*, not on the *time*. The old Pell
route is not reopened.

## AC. Classical stopping-time literature (Gate 27, 41, 57)

Verified against the previous branch's primary-source audit (Lagarias's annotated bibliographies,
his 2010 overview, Tao 2022, Roosendaal's records).

| result | time variable | descent or drift? | quantifier | actual orbit? | bearing on (DE) |
|---|---|---|---|---|---|
| Terras, Acta Arith. **30** (1976) 241–252 | stopping time `σ` | ordinary descent | density 1 | yes | gives (DE) for a density-one set only |
| Everett, Adv. Math. **25** (1977) 42–45 | `σ` | descent | density 1 | yes | same |
| Allouche (1979); Korec, Math. Slovaca **44** (1994) 85–89 | `Col_min ≤ N^θ` | descent | density 1, fixed `θ` | yes | same |
| Tao, Forum of Math. Pi **10** (2022) e12, Thm 1.3 | orbit minimum | descent | **logarithmic** density | yes | no pointwise content (Rmk 1.4) |
| Applegate–Lagarias, Math. Comp. **72** (2003) 1035–1049 | total stopping | — | pointwise | yes | a **lower** bound; wrong direction |
| Lagarias overview §6.1 (W1)–(W5) | — | — | — | — | **no upper bound of any kind is listed** |

**No standard name for the condition `∃n: S_n > αn` was found.** It is not Terras's stopping time
(that is `m_n < m_0`, i.e. `R_n > E_n`), and it does not appear in the surveyed literature as a
named quantity. Novelty is *not* claimed on that basis — §J shows the statement itself is the
repository's existing frontier.

## AD. Exit overshoot process (Gate 28, 29)

`O_n := R_n − E_n`; descent iff `O_n > 0`. Measured over 199,999 seeds: `min(R_τ − E_τ) = 0.0158`,
never `≤ 0`. Can a positive orbit have infinitely many drift exits while always `R_n ≤ E_n`? On the
**trivial cycle** yes, exactly: `R_n = E_n` identically (§H). Off cycles, §H's size bound makes it
require a polynomially small realizer floor.

## AE. Qualitative versus quantitative EOC (Gate 30)

(DE) excludes Type II but says nothing quantitative. Open Problem C needs `L_0(m) = O(log m)`
(§D). The gap between them is the whole quantitative theory; §AM grades the intermediate scales.

## AF. `c > 0` extension (Gate 31)

After the §K restart a Type-II tail is zero-confined *relative to its own maximum*, so `c = 0`
suffices for divergence exclusion. `c > 0` plays a role only in the quantitative single-window
theory (`r_min(N,c)`), not in the qualitative statement.

## AG. Occupation reconnection (Gate 32)

§P. Finite occupation is strictly stronger than finite initial exit, and either excludes Type II.

## AH. Episode decomposition (Gate 33)

§Q. Divergence exclusion needs only "no infinite final episode".

## AI. Word-shadow cardinality barrier (Gate 36) — mandatory filter

The previous branch built uncountably many infinite words with zero confinement, `R_n → −∞`
linearly, `Σ2^{R_n} < ∞` and Curry-scale occupation, of which all but countably many have no
positive-integer realizer. So **no proof of (DE) can use only `D`, `S_n`, `R_n` or their
asymptotics.** Every mechanism in this audit was tested against `famWord`:

| mechanism | applies to `famWord`? | verdict |
|---|---|---|
| drift asymmetry, excursion clock (§V, §Y) | **yes** | word shadow — inert |
| Diophantine overshoot bound (§AA, §AB) | **yes** | word shadow — inert |
| future-minimum theorem (§G) | **no** — uses `m_n ≥ 1` and `C_n > 0` | actual-orbit |
| valuation cap `2^d ≤ 3m_n+1` (§X) | **no** | actual-orbit |
| self-financing inequality (§X, §AR) | **no** | actual-orbit |
| strictness size bound (§H) | **no** — uses `m_j > m_0` | actual-orbit |

## AJ. Actual-orbit inputs (Gate 37)

The four surviving actual-orbit inputs are: `m_n ≥ 1`; `C_n > 0`; `2^{d_n} ∣ 3m_n+1`; and the
aggregate identity. Every theorem in `EOC/DriftExit.lean` uses only these.

## AK. Launch-renormalization interface (Gate 38)

A dangerous word yields a long actual positive launch orbit (`launchRenormalization.pdf` Thm 5.4,
Prop 6.3). A time-axis theorem `L_0(m) ≤ F(m)` converts to a realizer floor by §C/§D. The previous
branch showed `F = O(log m)` is essentially the `O(log n)` stopping-time conjecture; §AM asks what
weaker `F` still buys.

## AL. Lifetime-to-realizer transfer function (Gate 39)

§D's table, inverted generally: `L_0(m) ≤ F(m)` gives `r_min(N) ≥ F^{−1}(N)` where `F^{−1}(N) =
min{m : F(m) ≥ N}`. Lean: `realizerFloor_of_lifetime`.

## AM. Intermediate time-axis progress scales (Gate 40)

| unconditional lifetime bound | realizer floor obtained | new? |
|---|---|---|
| `L_0(m) ≤ K log₂m` | `r ≥ 2^{N/K}` | = Open Problem C |
| `L_0(m) ≤ K(log₂m)²` | `r ≥ 2^{√(N/K)}` | stretched exponential — would be new |
| `L_0(m) ≤ K m^θ` | `r ≥ (N/K)^{1/θ}` | **polynomial — would be new** |
| `L_0(m) ≤ K m` | `r ≥ N/K` | linear — would be new |

**This is the audit's most useful constructive output**: the programme need not be all-or-nothing.
Even a linear-in-`m` lifetime bound yields a linear realizer floor, and none is currently known
(§AN).

## AN. Best unconditional time result (Gate 41)

**None.** Any unconditional bound `L_0(m) ≤ F(m)` would, applied to a hypothetical Type-II tail
after the §K restart, contradict `τ_0 = ∞` and hence exclude divergence. So no unconditional
pointwise lifetime bound can exist short of excluding Type II. This mirrors the previous branch's
finding for total stopping time and is stated here for the drift axis.

## AO. Almost-all time results (Gate 42)

Terras/Everett/Allouche/Korec give density-one descent, hence (DE) for a density-one set; Tao gives
logarithmic density with no pointwise content. All are about `σ`, which by §G implies `τ_0 < ∞`.

## AP. Exceptional-set limitation (Gate 43)

Launch integers arise from dangerous words — an exceptional set by hypothesis. A density-one
statement therefore says nothing about them, and no distribution theorem for launch integers
exists. The pointwise anti-fallacy applies: a density-zero exceptional set may contain every
least-realizer champion, and no independent reason was found that it cannot.

## AQ. Predecessor / recovery congruence audit (Gate 44, 45)

Recovery events `d_n ≥ 2` put `m_n` in residue classes mod powers of 2. The lift-digit and
nested-realizer branches established that the seed-side congruences are automatic (grouped binary
digits of a fixed realizer). Repeated recoveries therefore impose no incompatible nested
congruences. **Closed quickly, as the gate directs.**

## AR. Recovery-resource balance (Gate 47, 48) — high priority, and decisive

Under sustained negative drift `log₂m_n = log₂m_0 − R_n + E_n`: the resource permitting a large
valuation grows at **exactly** the rate of the accumulated negative drift it must repay. Making
this exact (§X, Lean `driftExit_of_valuation`): one step suffices when `2^d m_0 > 3m_n`, while the
cap is `2^d ≤ 3m_n+1` — a surplus factor of about `m_0`.

Measured over 99,999 seeds, the minimum over all steps of
`log₂(3m_n+1) − (α − R_n)` — available valuation minus what a one-step return to `R = 0` needs — is
**`+1.8301`**, never negative.

> **Recovery capacity is self-financing, with surplus.** The natural "deep excursions cannot be
> repaid" mechanism is blocked, and this is the audit's main negative result.

## AS. `+1` correction / `E_n` (Gate 49, 50)

The only nonhomogeneous term is the `+1`, encoded by `C_n` and `E_n`. For a divergent orbit Curry
gives `E_n → E_∞ < ∞`; measured `max E ≤ 0.245`. A bounded `E_∞` plus an eternal zero corridor
produces no contradiction: `R_n ≤ 0` and `E_n` bounded are simultaneously satisfiable (the trivial
cycle has `R_n = E_n` exactly). **The `+1` bias is too small to force exit**, and §H quantifies
exactly how small — it is the entire difference between drift exit and ordinary descent.

## AT. `R`-record chronology (Gate 51)

For a Type-II orbit the `R`-records stop at `n₀`. A universal theorem forcing new records is
precisely (DE) restated (§Z), so it is not an easier formulation. §AA rules out a uniform increment.

## AU. Weakest divergence-impossibility theorem (Gate 52)

```
For every odd m ≥ 1 there exists n ≥ 1 with 3^n < 2^{S_n(m)}.
```

No rate, no occupation count, no realizer floor. `limsup R_n > 0` is per-seed equivalent to it.
No weaker sufficient statement was found: by §N it is *equivalent* to excluding Type II, so nothing
strictly weaker can suffice.

## AV. Periodicity-conjecture boundary (Gate 53) — mandatory

The earlier branches found that "a non-eventually-periodic word cannot have a positive-integer
realizer" is the classical 2-adic periodicity boundary, and that it is *not* implied by what is
known. (DE) is **not** that statement: (DE) concerns orbits and is equivalent to excluding Type II
(§N), which permits aperiodic words with positive realizers only in the divergent case. So (DE) is
weaker than the periodicity boundary and is exactly the repository's existing zero-corridor
frontier (§J) — reached from the time side rather than the residue side.

## AW. What is genuinely new from this audit (Gate 54)

1. **Everything integral.** `R_n ≤ 0 ⟺ 2^{S_n} ≤ 3^n`; the whole time axis needs no real analysis.
2. **The future-minimum theorem** `2^{S_n} ≤ 3^n ⟹ m_0 < m_n`, with the contrapositive that even
   `m_n ≤ m_0` forces drift exit (Lean, 4 lines).
3. **The strictness structure**: `τ_0 ≤ σ` always; `τ_0 < σ` occurs *exactly at cycle minima*;
   off cycles, strictness at depth `n` requires `r_min(n,0) ≤ 0.4809n/(1−{αn})`, polynomial in `n`,
   so any superpolynomial realizer floor forces `τ_0 = σ`.
4. **Self-financing** (§AR), with the exact sufficient inequality `2^d m_0 > 3m_n` against the cap
   `2^d ≤ 3m_n+1`.
5. **The transfer table** (§AM): polynomial and stretched-exponential lifetime bounds give
   correspondingly graded realizer floors — the programme is not all-or-nothing.
6. **The equivalence (DE) ⟺ no Type-II divergence** assembled explicitly, with the cycle direction
   (§M) supplied by `cycle_driftExit`.

Not new, and cited as such: the last-global-maximum restart (§K), the inversion (§C), and the
frontier statement itself (§J).

## AX. Targeted computation (Gate 55)

| check | result |
|---|---|
| `R_n ≤ 0 ⟺ 2^{S_n} ≤ 3^n` | 99,999 seeds, 0 mismatches |
| `2^{S_n} ≤ 3^n ⟹ m_n > m_0` | 0 violations |
| `m_n < m_0 ⟺ R_n > E_n` | 0 mismatches |
| `τ_0 = σ` off cycles | 199,999 seeds, 0 exceptions |
| `min(R_τ − E_τ)` | 0.0158 |
| `min R_τ` | 0.01654 at `τ=41` `= 1 − {41α}` exactly |
| `max E_τ` | 0.245 |
| self-financing margin | `+1.8301` minimum |
| strict examples below the §H size bound, `n < 200` | **0** |

## AY. Temporal record comparison (Gate 56)

Largest `τ_0(m)/log₂m` over odd `m < 200001`: `7.78` at `m = 27`, then `7.06` (31), `6.12` (47),
`5.69` (63), `5.62` (35655). The previous branch's total-stopping ratio `L/log₂m` peaked at `13.77`
in a comparable range — about twice as large, as expected since `τ_0` is the *first* descent and
`L` the full descent to `1`. The record holders overlap (27, 35655) but are not identical, so the
two time axes are empirically related but distinct.

## AZ. Literature table (Gate 57)

§AC.

## BA. Lean formalization (Gate 58)

`EOC/DriftExit.lean`, 6 theorems, built on `EOC.OrbitLifetime.Orbit`. No Curry, no external
theorem, no real analysis.

| theorem | content |
|---|---|
| `carry_pos` | `C_{n+1} > 0` |
| `zeroCorridor_implies_seed_lt` | `2^{S_{n+1}} ≤ 3^{n+1} ⟹ m_0 < m_{n+1}` (§G) |
| `driftExit_of_not_gt` | `m_{n+1} ≤ m_0 ⟹ 3^{n+1} < 2^{S_{n+1}}` |
| `cycle_driftExit` | a cycle has strictly positive period drift (§O) |
| `driftExit_of_valuation` | `2^d m_0 > 3m_n ⟹` drift exit next step (§AR) |
| `realizerFloor_of_lifetime` | the residue/time inversion (§AL) |

Existing repo results reused rather than restated: `zero_corridor_tail`, `exists_last_atBot_max`
(`EOC/CurryFoundation.lean`), `OrbitLifetime.aggregate_identity`, `OrbitLifetime.valuation_le`.
Following the convention of preceding rounds the module is not added to the `EOC.lean` aggregator.

## BB. Tests / build

```
lake build EOC.OrbitLifetime  →  2263/2263, success
lake build EOC.DriftExit      →  2264/2264, success
lake env lean EOC/DriftExit.lean →  exit 0
```

Scripts: `scratch/timeaxis.py`, `scratch/overshoot.py`, `scratch/coincidence.py`,
`scratch/strictsearch.py`.

## BC. Axiom audit

All six declarations: `[propext, Quot.sound]`, except `driftExit_of_valuation` which also uses
`Classical.choice`. No `sorry`, `admit`, `axiom`, `opaque`.

## BD. Files changed

```
EOC/DriftExit.lean                                  (new)
docs/TIME_AXIS_DRIFT_EXIT_IMPOSSIBILITY_AUDIT.md    (new)
scratch/timeaxis.py                                 (new)
scratch/overshoot.py                                (new)
scratch/coincidence.py                              (new)
scratch/strictsearch.py                             (new)
```

## BE. Commits

`fca3b7e` — *Time axis: recovery is self-financing, so the temporal mechanism is blocked*, on top
of base `1bb5826`, plus a follow-up commit recording this hash and the push status. `main`
untouched.

## BF. Push status

Pushed to `origin/time-axis-drift-exit-impossibility-audit`. **No PR opened.**

## BG. Research verdict

**`RECOVERY CAPACITY IS SELF-FINANCING AND BLOCKS THE TEMPORAL MECHANISM`**

The time-axis reformulation is correct and worth keeping, but the mechanism it was supposed to
enable does not exist, and the reason is exact rather than heuristic.

Why this verdict rather than the neighbours:

- `UNIVERSAL DRIFT EXIT IS EQUIVALENT TO EXCLUDING TYPE-II DIVERGENCE` is **established** (§N) and
  is the cleanest single statement here — but the hard direction was already in the repository
  (§K), so taking it as the verdict would overstate the novelty;
- `TIME-AXIS REFORMULATION REACHES THE EXISTING CHAIN-B BOUNDARY` is also true (§J) and is the
  honest novelty finding, but it describes provenance rather than a result;
- `ZERO-CORRIDOR ESCAPE IS THE WEAKEST QUALITATIVE TIME-AXIS TARGET` is true (§Q, §AU) but is a
  classification;
- `DRIFT EXIT IS STRICTLY WEAKER THAN ORDINARY STOPPING` is **only half true** and would mislead:
  `τ_0 ≤ σ` always, but strictness occurs *exactly at cycle minima* (§H), and off cycles any
  superpolynomial realizer floor forces equality;
- `THE TIME AXIS REOPENS THE DIVERGENCE-IMPOSSIBILITY ROUTE` is refuted by §AR;
- `A NEW ACTUAL-ORBIT TEMPORAL RESTRICTION SURVIVES` — none does.

The chosen verdict is the one load-bearing *mechanical* finding: under sustained negative drift the
ordinary height `log₂m_n = log₂m_0 − R_n + E_n` grows at exactly the rate of the drift deficit, and
the valuation cap `2^{d} ≤ 3m_n+1` therefore exceeds the one-step exit requirement `2^d m_0 > 3m_n`
by a factor of about `m_0` — measured margin `+1.83` at minimum over 99,999 seeds. Every "the orbit
cannot afford to recover" argument is blocked at its source.

**What survives as useful:** the integral formulation (§B), the future-minimum theorem (§G), the
strictness structure and its cycle explanation (§H), the equivalence (§N), the compatibility with
cycles (§O), and — the most constructive output — the graded transfer table (§AM) showing that
polynomial or stretched-exponential lifetime bounds would already yield new realizer floors.
