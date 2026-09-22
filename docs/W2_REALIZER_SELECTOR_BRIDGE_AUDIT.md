# W=2 offset-zero / positive-realizer bridge audit

Follow-up to [`docs/CHANG_INFINITE_COMPATIBILITY_FORMALIZATION.md`](CHANG_INFINITE_COMPATIBILITY_FORMALIZATION.md),
which machine-checked an explicit symbolic full shift inside the exact zero corridor and left the
frontier at *compatible symbolic data versus positive ordinary-integer realization*.

**Question.** Does the W=2 offset-zero machinery contain a positivity-sensitive mechanism that can
constrain the least positive realizer of a zero-confined word?

**Answer: no, and it fails all three decisive tests.**

| test | result |
|---|---|
| **q-sensitivity** — does any observable distinguish `r` from `r + q·2^{S+1}`? | **No.** Every harmonic observable is `q`-invariant or `q`-periodic. The only `q`-sensitive object is the offset-zero indicator itself, which *is* the target — circular. |
| **defect** — does the mechanism survive the `d ≥ 3` events the zero corridor permits? | **No.** `ChangFullShift` gives a zero-confined sequence with a digit `3` every seven steps forever; pure `{1,2}` runs there never exceed length **6**. |
| **pointwise** — would a proved transfer gap bound one target `r(D)`? | **No.** `G_s(k)` is a signed population statistic, and the trivial character `η = 0` — which *is* the offset-zero count — is excluded from the family by construction. |

Two findings cut the other way and are worth preserving. **Offset zero is exactly the
least-representative convention** plus a no-double-counting cutoff (formalized). And the note's
Lemma 8 — *"the suffix recorder is perfectly balanced; the prefix selector breaks the balance"* —
is **general, not W=2-specific** (formalized): it reaches, from a completely different direction,
the same structural conclusion as the Chang round.

---

## A. Starting state

| | |
|---|---|
| branch point | `chang-infinite-compatibility-formal` = `5ad638a00815dc94c5f7ec3ce3e2f4d2385dad8a`, **fetched and verified**, not taken from the prompt |
| new branch | `w2-realizer-selector-bridge-audit` |
| worktree | isolated; Mathlib shared by read-only symlink |

Ordinary checkout on `research-sparse-visits-2026-09-16`, 53 dirty files, untouched. `main`
(`1c4d6700`) unmodified.

## B. Source inventory

| | source |
|---|---|
| **W1** | `~/Downloads/collatz_w2_pullback_progress(2).md` — *Collatz W=2 Offset-Zero Pullback Program*, 1573 lines, sha256 `4d2c2daa63675531…`. **Read in full.** The only `~/Downloads` match for `*w2*`/`*pullback*`/`*offset*`. |
| **P1** | EOC Rev 5 manuscript — Prop 5.2 (exact realizer congruence), §6 (shell injectivity, `E(D)`), §8 Open Problems A–G |
| repo | `EOC/Realizer.lean`, `EOC/ZCRERealizerGrowth.lean`, `EOC/ChangZeroCorridor.lean`, `EOC/ChangInfiniteCompatibility.lean`, `EOC/ChangFullShift.lean`, `EOC/Confinement.lean` |

**No pre-existing W=2 material in the repository** — a search for `offset-zero`, `W=2`, `pullback`
across all `.lean` and `.md` returned nothing. This is the first time the program meets the
repository.

## C. Old W=2 epistemic register

Preserved exactly as W1 states it; **nothing is upgraded**.

**Tier 1 (proved).** Cylinder parameterization and injectivity (Lemma 0); exact-hit complete suffix
baseline cancellation (Lemma 1); the overshoot correction (failure at `2^{S_B+3}` for odd `η`,
restored at `2^{S_B+4}`); active Fourier shell (Lemma 2); half-orbit antipode via LTE (Lemma 3);
odd-support antiperiodicity (Lemma 4); two-orbit assembly with `S_−(η) = conj S_+(8−η)` (Lemma 5);
completion reduction of interval sums to `G_s(k)`; the Parseval identity
`Σ_k |G_s(k)|² = 2^{s+1} N_s^live`; dual-builder integrity rule; exact two-branch recursion
(Lemma 6); carry and phase cocycles (Lemma 7); **lift-completion vanishing (Lemma 8)**; and the
**negative** result that no sup-norm contraction exists (`D_j = 2^j` for all measured `j ≤ 4`).

**Tier 2 (theorem target, unproved).** The twisted transfer gap `|G_s(k)| ≤ C N_s^{1−δ}`; its
corollary `|Σ_I| ≲ N^{1−δ} log N`; generic-`Y` or mean-square variants; square-root cancellation
with log loss.

**Tier 3 (computational only).** Powered-wall normality `R_live < 2` in all tested dyadic cells;
non-dyadic powered normality near `2^33`; the random-phase reading of the suffix wall; uniform
`C√N` behaviour in tested regimes.

W1's own bottom line: *"the exact algebraic skeleton is real … but exact suffix balance does not
automatically enforce cancellation in prefix r-space"*, and the main theorem is now *"prove a
twisted transfer gap for `G_s(k)`"*.

## D. Notation dictionary

| W1 | current | relation |
|---|---|---|
| `A ∈ {1,2}^p` | `D`, a valuation word | **W1 restricts the alphabet; the current setting does not** |
| `p` | `N` | word length |
| `S_A` | `S_N = s d N` | total valuation |
| `C(A)` | `C_N(D) = Σ_{j<N} 3^{N−1−j} 2^{s_j}` | affine carry — same recursion |
| `r(A)`, "least odd residue realizing `A`" | `leastRealizer d N` | **the same object** |
| `m_A^0 = (3^p r(A) + C(A))/2^{S_A}` | terminal state `m_N` | same formula |
| — | `ξ_N(D) = −C_N(D)·3^{−N} mod 2^{S_N}` | W1 has no separate symbol; see §Y |

**Convention check, done rather than assumed.** W1 Lemma 0 states that the realizing set is a
single residue class **modulo `2^{S_A+1}`** and that `A ↦ r(A) mod 2^{s+1}` is injective on a
layer. P1 Prop 5.2 states the exact realizers form one class **modulo `2^{S_N+1}`** — *not*
`2^{S_N}` — and P1 §6 proves shell injectivity. **Same modulus, same indexing, same representative
range (least positive, necessarily odd), no sign difference, and the `+1` in the exponent agrees.**

So `r(A)` **is** the current least positive realizer, with no conversion needed. The one difference
is scope: W1's objects are defined only for `A ∈ {1,2}^p`.

## E. Exact meaning of offset-zero

W1's condition is `r(A) < Y ≤ r(A) + 2^{S_A+1}`.

The positive realizers of `A` are `r(A) + q·2^{S_A+1}` for `q = 0, 1, 2, …`. So the lower inequality
says the least realizer is below the cutoff, and the upper says the *second* realizer is not. Hence:

> **Offset zero at cutoff `Y` ⟺ exactly one positive realizer of `A` lies in `[1, Y)`, namely `r(A)`
> itself — i.e. `q = 0` is the unique admissible lift.**

Formalized as `W2SelectorBridge.offsetZero_iff_unique_lift`:
`0 < M → r < Y → (Y ≤ r + M ↔ ∀ q, r + q·M < Y ↔ q = 0)`.

## F. Anti-tautology audit

**Offset zero is a bookkeeping convention, not new arithmetic information.**

Given `r(A) < Y`, the extra upper inequality is exactly the no-double-counting clause (§E). It adds
nothing about `A`; it only ensures each word is counted once when `r`-space is swept.

Moreover the upper inequality is **automatic in the deep regime**: `Y ≤ r(A) + 2^{S_A+1}` holds for
every `r(A) ≥ 0` as soon as `2^{S_A+1} ≥ Y`. Checked: for `Y = 2^20, 2^30, 2^40` it is automatic for
all `S_A ≥ 19, 29, 39` respectively — i.e. precisely when `S_A + 1 ≥ log₂ Y`. Only *shallow* words,
whose cylinder modulus is smaller than the cutoff, can have a second realizer below `Y`.

**Classification: merely a convenient bookkeeping convention**, equivalent to small-realizer
placement `r(A) < Y` throughout the regime the program actually works in.

## G. Hypothetical T2 implication chain

Suppose `|G_s(k)| ≤ C N_s^{1−δ}` were proved. Tracing W1's own chain:

```
transfer gap on G_s(k)
   → (Fourier completion on Z/2^{s+1}, with the interval-indicator coefficient loss)
|Σ_I| ≲ N^{1−δ} log N,      Σ_I = Σ_{A : r(A) ∈ I} ψ_{η,S_B}(m_A^0)
```

So the conclusion is **(A): cancellation of the suffix character over the offset-zero–selected
population**, and from it a weak form of **(B)**: the selected population's terminal classes mod 8
are equidistributed to within `N^{−δ} log N`.

It does **not** give **(C)** an upper bound on `#{A : r(A) < Y}`, nor **(D)** a lower bound on
`r_min`. Both would need the trivial character, and §I shows it is outside the family. W1 does not
claim otherwise: its own framing is cancellation of `ψ`, and §16 explicitly abandons the
boundary-packet route to counting.

## H. Pointwise-versus-population barrier

**Mandatory gate; it is decisive on its own.**

`Σ_I` is a signed sum over *many* words. Open Problem C requires `r(D) ≥ 2^{εN−O(1)}` for **every**
relevant confined word. A cancellation statement about an aggregate cannot produce a lower bound on
an individual member, and the two are logically independent in the strongest sense:

> **Toy counterexample.** Take any finite multiset of words whose terminal classes mod 8 are
> perfectly balanced, so `Σ ψ = 0` exactly for every non-trivial `η`. Now replace one member by a
> word with the same terminal class but a much smaller realizer. The character sum is **unchanged**
> — `ψ` depends only on the terminal class — while `min_A r(A)` has dropped arbitrarily.

This is not an artefact: §V measures exactly this phenomenon in real data, where realizers inside a
single terminal class mod 8 spread over **10–16 bits**.

So character cancellation can never imply a lower bound on `min_A r(A)` without an additional
positivity or localization theorem, and W1 contains none.

## I. Does old machinery bound realizer counts?

**No. The character cancellation is orthogonal to realizer count.**

The reason is structural and comes straight from W1's definition: the dangerous character is
`ψ_{η,S_B}(x) = exp(2πi·η·F_{S_B}(x)/8)` with

```
η ∈ {1, 2, 3, 5, 6, 7}
```

`η = 4` is excluded (it is `−1` on odd terminal classes and does not cancel), and **`η = 0` — the
constant character, whose sum is exactly the offset-zero count `N_Y` — is not in the family at
all.** The machinery measures how the selected population *distributes* among suffix states; the
total mass is the one mode it deliberately does not touch.

`G_s(0)` is not the count either: it is the `k = 0` *frequency* of a `ψ`-weighted sum, and W1 §16
notes it is not identically zero. The Parseval identity `Σ_k |G_s(k)|² = 2^{s+1} N_s^live` runs the
other way — it *takes* `N_s^live` as input rather than bounding it.

## J. Positive-kernel / counting possibility

Briefly audited, per the gate's instruction not to launch an analytic program.

A positive majorant for `1[r(A) < Y]` (Fejér, Selberg, large sieve) would have to be built from the
same characters. Every such kernel has a non-negative mean, so its expansion **necessarily** carries
a non-zero weight on the trivial frequency, and the resulting bound reads

```
#{A : r(A) < Y}  ≤  (main term from the trivial mode)  +  (error from the non-trivial modes).
```

The main term is precisely the quantity the machinery does not control (§I), and the transfer gap
only shrinks the error. **Every usable kernel reduces to the same uncontrolled low-frequency mass.**
Recorded as the obstruction; no program started.

## K. Open Problems C/D/E comparison

Assuming the Tier-2 transfer gap were proved in full:

| target | exact statement | would a completed W=2 theorem imply it? |
|---|---|---|
| **OP C** | `r(D) ≥ 2^{εN} − O(1)` for all relevant `c`-confined `D` | **No** — pointwise vs population (§H); and W=2-restricted besides (§L) |
| **OP D** | a deterministic arithmetic property of `ξ_N(D) mod 2^{S_N}` preventing exceptionally small realizers | **No** — the machinery is `q`-invariant, so it cannot see representative size (§X, §Y) |
| **OP E** | `E(D) ≤ H₂(ρ_c)S + Φ(N)`, `Φ = o(N)` | **No connection found** — E is an entropy-depth statement; `G_s(k)` is a character sum |
| — | a **W=2-restricted average** analogue of C | **Yes, plausibly** — this is the honest scope (§AB) |

Implication diagram:

```
transfer gap  ──►  suffix-character cancellation on the W=2 selected population
                        │
                        ├──► equidistribution of terminal classes mod 8  (weak form)
                        │
                        └──✗  count of small realizers      (η = 0 excluded, §I)
                        └──✗  min over words                (population ≠ pointwise, §H)
                        └──✗  anything outside d ∈ {1,2}    (§L)
```

## L. W=2 restriction versus formal Chang full shift

**The stress test is decisive, and it uses this repository's own machine-checked theorem.**

Take `ChangFullShift.changSeq` with `y ≡ true`. Its digits are the repeating block

```
1, 1, 1, 1, 2, 1, 3
```

verified by `#eval` and reproduced in `scratch/w2_selector_bridge.py`:

| quantity | value |
|---|---|
| digit-3 density | `10/70 = 1/7` exactly, forever |
| maximal pure `{1,2}` run | **6** |
| zero-confined at every prefix | **yes** (`changSeq_zeroConfined`) |

> **Zero confinement does NOT imply eventual W=2 survival.** A zero-confined sequence may contain a
> digit `3` at positive density `1/7` indefinitely, and its `{1,2}` corridors are then uniformly
> bounded by length six.

No eventual-W=2 reduction is proposed, and none is available.

## M. High-valuation defect budget

Let `h_N = #{j < N : d_j ≥ 3}`. Every digit contributes at least 1 and every high digit at least 2
extra, so

```
S_N  ≥  N + 2 h_N,            hence     2 h_N  ≤  S_N − N  ≤  ⌊αN⌋ − N.
```

Asymptotically `h_N / N ≤ (α − 1)/2 = 0.292481250…`, and the excess budget is
`Σ_{j<N}(d_j − 1) = S_N − N ≤ (α − 1)N`, with `α − 1 = 0.584962501`.

Formalized: `W2SelectorBridge.add_two_mul_highCount_le_S` and `two_mul_highCount_le`. Verified on
all zero-confined words with `N ≤ 14`: **0 violations**, max observed `h_N/N = 0.2857`.

**Interpretation.** The bound constrains *density*, not *spacing*. The Chang construction sits at
`1/7 = 0.1429`, comfortably inside the budget while still placing a defect every seven steps. The
budget is therefore consistent with — and powerless against — bounded W=2 corridors.

## N. Can zero corridor force long W=2 runs?

**Refuted.** §L exhibits an explicit, machine-checked zero-confined sequence whose `{1,2}` runs
never exceed 6. The density budget of §M cannot force longer runs because it says nothing about
spacing.

Any argument requiring longer and longer pure-W=2 segments inside the corridor is therefore dead.

## O. One-defect algebra

`A = U · e · V` with `U, V ∈ {1,2}*`, `e ≥ 3`. What changes:

| object | effect of one defect |
|---|---|
| cylinder modulus | `2^{S_A+1}` with `S_A` larger by `e`; **form unchanged** (Lemma 0 never used the alphabet) |
| least realizer | still the unique least positive member of one class; unchanged in kind |
| carry `C(A)` | same recursion `C ↦ 3C + 2^{s}`; unchanged |
| terminal state | same formula; **`lift_shift` holds verbatim** |
| suffix character `ψ` | unchanged — it reads only the terminal class mod 8 |
| **complete-fiber cancellation (Lemma 8)** | **survives unchanged** — see §S |
| active Fourier shell (Lemma 2) | shell *location* depends on `S_A`, which shifts; constants change |
| two-branch recursion (Lemma 6) | **fails as stated** — there are now `e`-many children, not 2 |
| two-orbit assembly (Lemma 5) | **fails as stated** — built on the binary child structure |
| half-orbit antipode (Lemma 3) | LTE argument is about `3^p` and powers of 2; survives, constants change |

## P. General-d branch recursion

Appending a digit `d` to a word of length `N`, total `S`, refines the cylinder from modulus
`2^{S+1}` to `2^{S+d+1}`, so the child lift parameter ranges over `2^d` values rather than `2`. The
general update is the exact realizer recurrence already in the repository
(`Realizer.realizerCongruence`, P1 Prop 5.2 step (a)): `2^{s_{j+1}} m_{j+1} = 3^{j+1} m_0 + q_{j+1}`
with `q_{j+1} = 3 q_j + 2^{s_j}`.

**So the general-`d` branch recursion is the current exact-realizer recurrence in W1's
coordinates.** W1's Lemma 6 is its `d ∈ {1,2}` specialization. Recorded as **coordinate reuse**,
not new structure.

## Q. Which Tier-1 lemmas are truly W=2-specific?

| lemma | W=2-specific? | reason |
|---|---|---|
| Lemma 0 cylinder/injectivity | **no** | = P1 Prop 5.2 + §6 shell injectivity, any alphabet |
| Lemma 1 complete suffix baseline | **no** | complete packets, no alphabet input |
| Lemma 8 lift-completion vanishing | **no** | only uses `3^N` odd — §S, formalized |
| Lemma 3 antipode (LTE) | mostly no | constants shift with `S_A` |
| Lemma 2 active Fourier shell | partly | shell support tied to layer geometry |
| Lemma 6 two-branch recursion | **yes** | exactly two children |
| Lemma 5 two-orbit assembly | **yes** | binary conjugacy `S_−(η) = conj S_+(8−η)` |
| Lemma 7 carry/phase cocycles | **yes as stated** | indexed by the two branches |
| `D_j = 2^j` no-contraction | **yes as stated** | `2^j` counts binary descendants |

**Pattern: the *arithmetic* layer is general; the *transfer-operator* layer is binary.** Everything
W1 needs for its Tier-2 target lives in the binary layer.

## R. Periodic d=3 stress test

The canonical adversarial sequence is §L's `(1,1,1,1,2,1,3)^∞`. Extending W1's state machine across
it would require a transfer operator whose alphabet includes `3`, i.e. a `2^3`-way branch at every
seventh step interleaved with binary steps — a period-7 inhomogeneous operator with mixed branch
degree.

Such an operator can certainly be *written down* (§P gives the general child update). What does not
survive is the analytic architecture built on it: exact packet size, the binary antipode pairing,
the two-orbit conjugacy and the `D_j = 2^j` accounting are all binary-indexed (§Q). **No attempt was
made to construct the enlarged operator**, per the gate's instruction not to infer the
arbitrary-defect case from the periodic one — and because §H and §X already close the bridge
regardless of whether it could be built.

## S. General complete-fiber cancellation

**Proved general, and formalized.** W1's Lemma 8 reasons: `{2u·3^p : u mod 2^{S_B+2}}` sweeps all
even residues modulo `2^{S_B+3}` *because `3^p` is odd*. The alphabet is never used.

Two formal statements:

- `W2SelectorBridge.lift_shift` — if `2^S·m = 3^N·r + C` then the lift `r + q·2^{S+1}` has terminal
  state `m + 2q·3^N`. Holds for **any** valuation word.
- `W2SelectorBridge.lift_shift_injOn` — `q ↦ 2·3^N·q` is injective mod `2^{T+1}` on `q < 2^T`,
  hence the `2^T` lifts sweep all `2^T` even residues. Only input: `3^N` odd.

So the complete lift fibre is balanced for every word, not just for `d ∈ {1,2}`.

## T. Selector imbalance

W1 already localizes the obstruction, in its own Tier-1 language:

> `G_s(k)` **is entirely a fiber-selection functional.**
> *"the suffix recorder is perfectly balanced; the prefix selector breaks the balance."*

Define the selector imbalance as the difference between the complete-fibre average (zero, by §S)
and the `q = 0` contribution. By §S the first term vanishes identically, so

```
selector imbalance  =  −ψ_{η,S_B}(m_A^0)        (the q = 0 term alone).
```

It is well defined and exactly computable. **Status: it is not a new invariant — it is the `q = 0`
term itself, renamed.**

## U. Selector imbalance versus r(D)

**Closed.** By §T the imbalance equals `−ψ(m_A^0)`, a function of the terminal class mod 8 only.
By `lift_shift` the terminal class depends on `q` **periodically** (period 4, since
`m ↦ m + 2q·3^N`), and on `r` only through `r mod 2^{S+1}`.

So the imbalance depends only on the residue and carries **no** monotone information about the
Archimedean size of `r(D)`: neither "small `r` ⇒ large bias" nor its converse can hold, because two
words with the same terminal class have the same imbalance and, by §V, realizers differing by
`2^{15}`.

## V. Matched harmonic-state realizer spread

Within a fixed zero-confined shell `(N,S)` **and** a fixed terminal class mod 8 — i.e. holding the
entire suffix-character observable constant — `log₂ r(D)` still spreads widely:

| `N` | `S` | class mod 8 | words | min `log₂ r` | max `log₂ r` | spread |
|---|---|---|---|---|---|---|
| 12 | 18 | 7 | 639 | 7.28 | 19.00 | **11.72** |
| 13 | 20 | 1 | 2038 | 8.14 | 21.00 | **12.85** |
| 14 | 21 | 7 | 4428 | 6.15 | 22.00 | **15.85** |
| 14 | 21 | 1 | 4444 | 7.97 | 22.00 | **14.03** |

Realizer sizes vary by a factor of up to `2^{15.85}` inside a single harmonic state. **The harmonic
coordinate cannot be the missing pointwise invariant.**

## W. Character resolution in r-space

For fixed `(N,S)` the realizer lives modulo `2^{S+1}`, i.e. `S+1` bits. The suffix character sees
`F_{S_B}(m_A^0) mod 8` — **3 bits**.

| `S` | bits in `r` | bits seen | fraction |
|---|---|---|---|
| 20 | 21 | 3 | 0.143 |
| 40 | 41 | 3 | 0.073 |
| 80 | 81 | 3 | 0.037 |
| 160 | 161 | 3 | 0.019 |

The fraction `3/(S+1) → 0`. The character family has 6 usable elements (`η ∈ {1,2,3,5,6,7}`), a
fixed-dimensional quotient of a space whose dimension grows with `S`. **The harmonic measurements
see only a bounded quotient of `r`-space, so they cannot yield pointwise anti-concentration** —
structurally the same lossiness the Chang round found for its local observable.

## X. q-sensitivity table

The single most important anti-tautology test. Under `r ↦ r + q·2^{S+1}`, using
`lift_shift` (`m ↦ m + 2q·3^N`):

| observable | behaviour in `q` | sees Archimedean size? |
|---|---|---|
| `r(A) mod 2^{S_A+1}` | completely invariant | **no** |
| prefix twist `e(k·r/2^{s+1})` | completely invariant | **no** |
| `m_A^0 mod 2^{S_B+3}` | periodic, period `2^{S_B+2}` | **no** |
| terminal class mod 8, `ψ_{η,S_B}` | periodic, period **4** (verified numerically) | **no** |
| suffix survival `F_{S_B}` | periodic | **no** |
| `G_s(k)`, `Σ_I` | built from the above; `q`-periodic | **no** |
| offset-zero indicator | cutoff-dependent — selects `q = 0` | yes, **but it is the target** |
| `r(A)` as an integer | grows linearly in `q` | yes |

Worked example (`A = (1,2,1,1,2,1)`, `p = 6`, `S_A = 8`, `r = 91`, `m^0 = 263`): `m mod 8` runs
`7, 1, 3, 5, 7, 1, …` as `q = 0,1,2,3,4,5` — period 4, never growing.

**Only the last two rows are `q`-sensitive, and the only one belonging to the machinery is the
selection condition itself.** Every harmonic quantity is residue-sensitive, not
positivity-sensitive.

## Y. Moving-anchor relation

OP D concerns `ξ_N(D) = −C_N(D)·3^{−N} mod 2^{S_N}` and exceptionally small least representatives.
By P1 Prop 5.2, `r(D) ≡ 2^{S_N} − C_N(D)·3^{−N} (mod 2^{S_N+1})`, so W1's `r(A)` is **the least
positive representative of (a `2^{S_N}`-shift of) `ξ_N`**.

That is the whole relation: W1 rewrites the anchor's least representative in its own coordinates.
It supplies **no new inequality** for it — by §X the machinery is invariant under changing
representative. **Classification: coordinate reuse, not progress**, which is exactly what P1 Open
Problem D says is needed and not available.

## Z. ZCRE relation

`ZCRERealizerGrowth.boundedPrefixRealizers_iff_positiveRealizer`:
`(∃ M, ∀ N, leastRealizer d N ≤ M) ↔ (∃ m₀, Odd m₀ ∧ ∀ i, a (orbit m₀ i) = d i)`.

Can any W=2 statistic force `r_N` to change infinitely often, or `sup_N r_N = ∞`? **No.** Every
statistic in W1 is a function of residues (§X) and is invariant under the very lift that
distinguishes a bounded prefix-realizer sequence from an unbounded one. A `q`-invariant quantity
cannot detect whether `r_N` stabilizes.

**W1 does not cross the LEVEL-3 → LEVEL-4 boundary**, recorded explicitly.

## AA. Old coherent-corridor target relevance

*If the coherent-corridor mass-decay lemma were proved tomorrow, would it advance OP C/D?*

Its strongest consequence would be the Tier-2 transfer gap, hence (§G) **better suffix-character
cancellation inside the W=2 selected population** and equidistribution of terminal classes mod 8
there. Nothing more.

**Mark the old T2 ladder as mathematically interesting but NOT CURRENT-FRONTIER RELEVANT.** No work
on the corridor lemma was done in this branch.

## AB. Surviving interface

Of the gate's options, **(C) the general complete-fiber cancellation lemma** survives, and is now
formalized (§S). **(A)** a standalone W=2 anti-concentration theorem also survives as an honest
self-contained target, and **(B)** an average small-realizer count within W=2 would be a legitimate
W=2-restricted result — but neither bears on the EOC frontier (§K).

**(D)** a defect-robust transfer framework does not survive: the binary layer is where all the
analytic structure lives (§Q), and the corridor forces defects (§L). **(E)** a harmonic diagnostic
for residue selection is precisely what §U and §W close.

The genuinely valuable residue is conceptual and worth stating plainly: **W1 reached, from a
transfer-operator direction and before the Chang work, the same structural conclusion this
repository reached from symbolic dynamics** — the compatible 2-adic fibre is perfectly balanced, and
all the information sits in choosing the ordinary representative. W1 says it as *"the suffix
recorder is perfectly balanced; the prefix selector breaks the balance"*. That convergence is
evidence the frontier has been correctly located; it is not itself progress across it.

## AC. Optional order-clock crosscheck

**Not used.** No clean identification between order–clock resonance and the W=2 active Fourier
modes was pursued, since §H, §X and §W close the bridge independently of it, and the gate directs
stopping otherwise.

## AD. Lean formalization

**New module `EOC/W2SelectorBridge.lean`**, 5 theorems + 1 definition, no
`sorry`/`admit`/`axiom`/`opaque`.

| declaration | statement | audit use |
|---|---|---|
| `offsetZero_iff_unique_lift` | `0 < M → r < Y → (Y ≤ r + M ↔ ∀ q, r + q·M < Y ↔ q = 0)` | §E, §F |
| `lift_shift` | `2^S·m = 3^N·r + C → 2^S·(m + 2q·3^N) = 3^N·(r + q·2^{S+1}) + C` | §S, §X |
| `lift_shift_injOn` | `q ↦ (2·3^N·q) mod 2^{T+1}` is injective on `q < 2^T` | §S (general Lemma 8) |
| `highCount` | `#{t < k : 3 ≤ d t}` | §M |
| `add_two_mul_highCount_le_S` | `(∀ i, 1 ≤ d i) → k + 2·highCount d k ≤ s d k` | §M |
| `two_mul_highCount_le` | `… → s d k ≤ ⌊kα⌋ → 2·highCount d k ≤ ⌊kα⌋ − k` | §M |

**Deliberately not formalized**, per Gate 31: the twisted transfer gap (Tier 2, and a population
statistic), the coherent-corridor lemma, and anything asserting a character bound constrains an
individual realizer.

## AE. Computational checks

`scratch/w2_selector_bridge.py` — standard library only, deterministic, small and targeted.
Reproduces §F (cutoff regime), §L (Chang stress test), §M (budget, 0 violations on all
zero-confined words `N ≤ 14`), §V (matched-state spread), §W (resolution), §X (q-periodicity).

Finite data is used for structural falsification only; nothing is extrapolated.

## AF. Files changed

```
new:  EOC/W2SelectorBridge.lean                        5 theorems + 1 definition
new:  scratch/w2_selector_bridge.py                    reproducible checks
new:  docs/W2_REALIZER_SELECTOR_BRIDGE_AUDIT.md        this report
```

No existing Lean file modified; no theorem statement changed; the W=2 source note was not edited.

## AG. Tests/build

| command | result |
|---|---|
| `lake build EOC.W2SelectorBridge` | **success, 2041 jobs, 0 errors** |
| `lake build EOC.ChangZeroCorridor` | success, 2040 jobs (no regression) |
| `lake build EOC.ChangFullShift` | success, 2042 jobs (no regression) |
| `python3 scratch/w2_selector_bridge.py` | exit 0 |
| forbidden-token grep | clean |

## AH. Axiom audit

```
offsetZero_iff_unique_lift    : [propext, Classical.choice, Quot.sound]
lift_shift                    : [propext]
lift_shift_injOn              : [propext, Classical.choice, Quot.sound]
add_two_mul_highCount_le_S    : [propext, Classical.choice, Quot.sound]
two_mul_highCount_le          : [propext, Classical.choice, Quot.sound]
```

Standard Mathlib axioms only; `lift_shift` needs only `propext`.

## AI. Commits

Branch `w2-realizer-selector-bridge-audit`, from `5ad638a`.

| commit | contents |
|---|---|
| `3fe1ec5` | `EOC/W2SelectorBridge.lean` + `scratch/w2_selector_bridge.py` |
| (this file) | this report |

## AJ. Push status

Branch pushed to `origin/w2-realizer-selector-bridge-audit`. **No pull request opened.** `main`
unmodified; dirty ordinary checkout untouched.

## AK. Research verdict

**`W2 TRANSFER GAP IS POPULATION-ONLY; NO POINTWISE REALIZER BRIDGE`**

Chosen as the strongest rigorously justified conclusion, and chosen over three neighbours that are
each true but weaker or narrower:

- `OFFSET-ZERO IS ONLY A LEAST-REPRESENTATIVE REPARAMETERIZATION` is proved (§E, §F, formalized) but
  describes only the *selection convention*, not the analytic machinery.
- `W2 MECHANISM FAILS UNDER NECESSARY d≥3 DEFECTS` is also proved (§L, §Q) — the binary transfer
  layer does not survive defects the corridor forces. But this is a *contingent* obstruction: it
  would matter only if the population→pointwise gap were otherwise crossable.
- `GENERAL COMPLETE-FIBER CANCELLATION SURVIVES, SELECTOR REMAINS THE OBSTRUCTION` records the real
  positive finding (§S, formalized) — but "the selector remains the obstruction" is a restatement of
  the frontier, not a bridge across it.

The chosen verdict is the binding one because it holds *independently of the defect problem and of
the alphabet*: even granting the full Tier-2 transfer gap on a defect-free W=2 subsystem, the
conclusion is cancellation of `ψ` over a selected population (§G). The trivial character — which is
the count — is excluded from the family by construction (§I); a population can be perfectly balanced
while containing an arbitrarily small member (§H), and §V measures realizer spreads of up to
`2^{15.85}` inside a single harmonic state. Decisively, every harmonic observable is `q`-invariant or
`q`-periodic (§X), so none of them can distinguish `r` from `r + q·2^{S+1}` — they do not see the
Archimedean representative at all.

**Disposition.** Close the direct EOC bridge. Preserve the W=2 program as a standalone
structural/analytic subsystem with its own honest targets (§AB), and keep the one general fact it
contributes: the complete lift fibre is balanced for every valuation word, so all information about
positivity lives in the choice of ordinary representative — the same boundary the Chang round
reached, now confirmed from a second, independent direction.
