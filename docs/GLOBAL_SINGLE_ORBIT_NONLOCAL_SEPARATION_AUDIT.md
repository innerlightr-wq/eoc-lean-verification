# Global single-orbit / nonlocal separation audit

Finite-cylinder impossibility, infinite-tail compatibility, and the search for a genuinely global
positive-orbit constraint.

## A. Starting state

| item | value |
|---|---|
| base commit | `43c979800da491b011d32eefd09a70bdd275e575` (`Record commit hash and push status in the audit report`) |
| verified how | `git fetch origin`, then `git rev-parse origin/intrinsic-extrinsic-constraint-independence-audit` |
| ordinary checkout | **dirty** (53 entries). Not touched. |
| worktree | isolated, `scratchpad/eoc-go`, `.lake/packages` symlinked |
| branch | `global-single-orbit-nonlocal-separation-audit` |
| `main` | untouched. No PR. |

## B. Finite/infinite logical diagram (Gate 0)

Quantifiers explicit throughout. Write `D|_N` for the length-`N` prefix and
`Real(m, D|_N)` for "the positive odd integer `m` realizes `D|_N`".

| arrow | status |
|---|---|
| `D|_N` admissible `⟹ ∃m. Real(m, D|_N)` | **theorem**, and the witnesses are *unbounded* — `exists_odd_positive_in_class`, §C |
| nested prefixes `⟹ ∃! x ∈ ℤ₂` compatible with all of them | **theorem** — the classes are nested with moduli `2^{S_N+1} → ∞` |
| `x ∈ ℤ₂` compatible `⟹ x` is an ordinary positive integer | **FALSE** — `−1`, `−5`, and §Y's uncountable family |
| `∃m. ∀N. Real(m, D|_N) ⟹ ∀N. ∃m. Real(m, D|_N)` | **theorem**, trivial |
| `∀N. ∃m. Real(m, D|_N) ⟹ ∃m. ∀N. Real(m, D|_N)` | **FALSE** — §Q |
| `∃m. ∀N. Real(m, D|_N) ⟺ (leastRealizer d N)` bounded | **theorem** — `ZCRERealizerGrowth.boundedPrefixRealizers_iff_positiveRealizer` |

> **The entire content sits in the quantifier swap.** `∀N ∃m_N` is free; `∃m ∀N` is the problem;
> and the gap between them is exactly boundedness of `r_N`, i.e. ZCRE.

## C. Finite-cylinder positivity theorem (Gate 1)

> **Theorem.** For `k ≥ 1` and any odd `r < 2^k`, and any bound `B`, there is an odd `m > B` with
> `m ≡ r (mod 2^k)`.

Witness `m = r + 2^k(B+1)`. Lean: `exists_positive_in_class`, `exists_odd_positive_in_class`.

Translated: a valuation prefix `D|_N` determines exactly one odd class mod `2^{S_N+1}`
(`Realizer.realizerCongruence`), and that class contains arbitrarily large positive odd integers.
So finite-prefix realizability is never the obstruction, and `leastRealizer d N` is always defined.

## D. Finite valuation-prefix limitation (Gate 2)

> No property depending only on `d_1,…,d_N` can **decide** whether the infinite word has a
> positive ordinary realizer.

Because every finite admissible word has positive realizers (§C), any such property is satisfied by
prefixes of words that do have one and by prefixes of words that do not — §Y exhibits uncountably
many of the latter sharing every prefix pattern.

**Exact scope, stated to avoid overclaiming.** This does *not* say finite information is useless.
Finite data can still prove quantitative statements — e.g. a lower bound on `log₂ r_N` for a given
`N`, which is precisely the form of Open Problem C. The claim is only about *deciding* the infinite
ordinary-realization property.

## E. `ℤ₂` density / topological interpretation (Gate 3)

§C is exactly the statement that **the positive integers are dense in `ℤ₂`**: every nonempty open
cylinder `r + 2^kℤ₂` meets `ℤ_{>0}`. Consequently any continuous map `ℤ₂ → F` into a finite
discrete space factors through finite precision and cannot be the indicator of `ℤ_{>0}`.

Stated, not formalized with topology infrastructure (as the gate permits). The concrete arithmetic
form that *is* formalized is `no_finite_precision_sign_separator`: a property of integers
determined mod `2^k` cannot be equivalent to `0 < x`, since `1` and `1 − 2^k` share a class and
differ in sign.

## F. Eventual-zero positivity marker (Gate 4) — existing result, not new

For an ordinary **nonnegative** integer the binary expansion terminates (eventually `0`); for a
**negative** integer it is eventually `1`; for a generic non-integral 2-adic integer neither holds.
Under the repository's conventions,

```
positive ordinary realization
  ⟺ prefix realizers eventually constant        (ZCRERealizerGrowth)
  ⟺ lift digits eventually zero                 (RealizerLiftDigit.eventuallyZero_iff_eventuallyConstant)
```

This is the baseline global positivity marker and it is **not** claimed as new here; both
equivalences are already in the repository with their caveats (the lift-digit statement is proved
for an abstract nested sequence, which is the generality in which it holds).

## G. Anti-ZCRE criterion (Gate 5)

Every candidate global property `P` is tested against three requirements:

1. **necessary** — every relevant positive orbit satisfies `P`;
2. **strictly weaker** — `P` does not imply positive realization (otherwise it *is* ZCRE);
3. **independently analyzable** — `P` can be attacked without first solving realization.

A candidate failing (2) is closed as **ZCRE-equivalent**. A candidate failing (1) is not a
necessary condition and cannot be used. A candidate passing (1) and (2) but failing (3) is
recorded but useless.

## H. Global positive-orbit condition inventory (Gate 6)

Classes: **A** proved for all positive orbits; **B** proved conditional on divergence; **C**
conjectural; **D** equivalent to positive realization; **E** valuation-word-only; **F** genuinely
orbit-level.

| condition | class | necessary? | strictly weaker than realization? | verdict |
|---|---|---|---|---|
| one seed realizes every prefix | D, F | yes | **no** — it *is* realization | ZCRE-equivalent (§O) |
| prefix realizers bounded | D | yes | no | ZCRE (`boundedPrefixRealizers_iff_positiveRealizer`) |
| lift digits eventually zero | D | yes | no | ZCRE (§F) |
| all iterates `m_n` positive odd integers | D, F | yes | no | restatement of realization |
| eventually periodic alternative (Type I) | A, F | — | — | the non-divergent branch (§I) |
| injectivity of the orbit (Type II) | B, F | yes for Type II | yes | **no size control** (§S) |
| `m_n → ∞` (Type II) | B, F | yes for Type II | yes | no rate known (§AE) |
| `Σ 1/m_n < ∞` (Curry) | B, F | yes for Type II | yes | no pointwise envelope (§AF, §AG) |
| `Q_n → Q_∞ < ∞` (Curry) | B, F | yes | yes | exact identity, no content (§M) |
| `R_n → −∞` | B, **E** | yes for Type II | yes | **word-only, and too weak** (§K, §L, §Y) |
| Garcia–Tal Banach-density-zero orbit set | A/B, F | yes | yes | no pointwise bridge (§U) |
| Curry window sparsity | B, F | yes | yes | audited previously; population-level (§J) |
| Chang Map Balance (Chang Thm 4.2) | A, F | — | — | a **counting/population** theorem (§T) |
| Curry occupation `#{n : R_n ≥ −G} ≪ 2^{βG}G` | B, E/F | yes | yes | population, not placement (§AH) |

## I. Type-I / Type-II split (Gate 7)

Repo status (`docs/CURRY_FOUNDATION.md`): a repeated orbit state gives eventual periodicity
(Type I); no repeated state gives injectivity; an injective positive orbit with only finitely many
values below any `M` must tend to infinity; Type II is the divergent injective branch. Curry's
results are stated there as a **necessary-condition theorem** for Type II.

**The answer to the gate's question is the important part.** This classification is a statement
about *orbits of ordinary positive integers*. It says nothing about an arbitrary infinite
zero-confined valuation word, because such a word need not come from any positive integer at all
(§Y). The split therefore applies **only after** ordinary positive realization has been assumed —
it cannot be used to exclude a word.

## J. Curry global consequences: actual orbit versus word shadow (Gate 8)

| Curry consequence | expressible from `D` alone? |
|---|---|
| `R_n → −∞` | **yes** — `R_n = S_n − αn` is a function of the word |
| `Q_n → Q_∞ < ∞` | no — `Q_n = Π(1 + 1/(3m_j))` needs the ordinary iterates |
| `Σ 1/m_n < ∞` | no — needs ordinary iterates |
| window sparsity | no — defined on the orbit |
| occupation bound `#{n : R_n ≥ −G}` | **yes** — it is a statement about `R_n`, hence about `D` |

So exactly two Curry consequences have word-level shadows: `R_n → −∞` and the occupation bound.
§K and §AH test both.

## K. Curry valuation shadows (Gate 9)

The strongest word-only shadow is `R_n → −∞`, and it is genuinely strong: under zero confinement
`S_n ≤ ⌊αn⌋` gives only `R_n ≤ 0`, whereas `R_n → −∞` forces the valuation sum to fall behind `αn`
without bound.

**It excludes nothing.** §L gives two explicit witnesses and §Y gives uncountably many. Recording
the gate's own conclusion:

> **Curry's word-level shadow is too weak.**

## L. Negative / nonordinary witnesses (Gate 10)

| witness | valuation word | `S_n/n` | `R_n` | zero-confined? | positive realizer? |
|---|---|---|---|---|---|
| `−1` | `1,1,1,1,…` | `1` | `(1−α)n = −0.585n → −∞` | **yes** | **no** |
| `−5` | `1,2,1,2,…` | `1.5` | `(1.5−α)n = −0.085n → −∞` | **yes** | **no** |

Both satisfy zero confinement **and** the strongest Curry word shadow `R_n → −∞`, **linearly**, and
neither has a positive-integer realizer. Two lines of arithmetic defeat the entire word-shadow
programme. (Both are periodic, so they also satisfy any "eventually periodic" condition; §Y removes
that caveat.)

## M. Product identity at infinite scale (Gate 11)

With `m_n 2^{R_n} = m_0 Q_n` and `Q_n = Π_{j<n}(1 + 1/(3m_j))`, the exact identity

```
C_n / 3^n  =  m_0 (Q_n − 1)
```

holds (verified: 4,800 checks over 200 seeds × 24 steps, **0 mismatches**).

Does `Q_∞ < ∞` supply a new cross-scale constraint? **No.** Given the word, `R_n` is determined;
given the seed, `Q_n` is determined; and the identity relates them with no freedom left. The
inequality it yields, `Σ_{j≥0}2^{R_j} = 3m_0(Q_∞ − 1) ≥ 1`, is the trivial `2^{R_0} = 1`. This is
another coordinate identity, exactly as the gate warned.

## N. Global carry sum (Gate 12)

Exactly: `C_n/3^n = Σ_{j<n} 2^{S_j}3^{−(j+1)} = (1/3)Σ_{j<n}2^{R_j}`.

For a divergent orbit `R_j → −∞` and the series converges **in ℝ**, to `3m_0(Q_∞−1)` by §M. The
same formal series converges **2-adically** to `−3m_0` (previous branch: `Z = −n_0`). So one series
has two limits in two topologies, both determined by the seed and the word.

That is a genuine cross-scale fact and it carries **no new constraint**: both values are functions
of data already fixed. Recorded here so that it is not rediscovered as a mechanism.

## O. Same-seed coherence (Gate 13)

Candidate weaker cross-prefix coherence conditions, each audited:

| candidate | verdict |
|---|---|
| growth compatibility of least representatives | `r_N` non-decreasing is automatic; boundedness is ZCRE |
| sign consistency of affine iterates | §AA — equivalent to realization |
| uniform Archimedean bound on `r_N` | **is** ZCRE by `boundedPrefixRealizers_iff_positiveRealizer` |
| cross-scale residue/height relations | previous branch: all factor through `D` |

No strictly weaker same-seed coherence condition was found. Every formulation either is automatic
from residue nesting (§P) or is boundedness in disguise.

## P. Automatic nesting no-go (Gate 14)

`r_{N+1} ≡ r_N (mod 2^{S_N+1})` holds by construction, and the moving anchors are nested in `ℤ₂`
by construction. **"All prefixes are compatible" is therefore not global information at all.** The
missing property is compatibility with **one bounded nonnegative ordinary representative** — stated
explicitly here because the two are easy to conflate.

## Q. Compactness / König obstruction (Gate 15)

The tempting argument — every finite prefix has a positive realizer, therefore an infinite positive
realizer exists — fails, and the failure is not subtle.

- **Nodes**: pairs (depth `N`, positive odd integer realizing `D|_N`).
- **Branching**: each node has **infinitely many** children (a realizer of `D|_N` that fails at
  depth `N+1` is replaced by infinitely many others), so the tree is *not* finitely branching and
  König's lemma does not apply.
- **What a branch gives**: the nested classes do determine a unique point of `ℤ₂` — but a 2-adic
  limit, not an integer.
- **Why positivity is not compact**: `ℤ_{>0}` is not compact, and the sets
  `R_N = {m > 0 : m ≡ r_N mod 2^{S_N+1}}` are infinite and decreasing with possibly **empty**
  intersection.

Lean: `decreasing_infinite_inter_empty` exhibits a decreasing chain of infinite subsets of `ℕ` with
empty intersection. `∩_N R_N ≠ ∅` holds exactly when `r_N` is bounded — which is §R, not
compactness.

## R. Bounded-realizer criterion (Gate 16)

`ZCRERealizerGrowth.boundedPrefixRealizers_iff_positiveRealizer`:

```
(∃M, ∀N, leastRealizer d N ≤ M)  ↔  (∃m₀, Odd m₀ ∧ ∀i, a (orbit m₀ i) = d i).
```

So any compactness-style argument must produce a **uniform ordinary bound** on `r_N`.

**Does any current global orbit theorem give such a bound? No.** §S tabulates why: every global
condition in the inventory is either a statement about the word (which by §Y cannot bound `r_N`) or
a statement about the orbit that presupposes realization.

## S. Global conditions without size control (Gate 17)

| condition | implies a bound on `r_N` or `sup_N r_N`? |
|---|---|
| `R_n → −∞` | **no** — `−1` has `R_n → −∞` linearly and `r_N = 2^{S_N+1}−1 → ∞` |
| zero Banach density of the orbit set | no — a statement about which integers are visited |
| Chang balance | no — a counting statement over histories |
| injectivity | no — says nothing about representative size |
| `m_n → ∞` | no — concerns iterates, not prefix realizers |
| `Σ1/m_n < ∞` | no — §AG |

None controls size, so none can produce positive realization by compactness. This is the cleanest
statement of why the global conditions currently known are inert for this problem.

## T. Chang infinite-orbit status (Gate 18)

Not re-derived; only the status is recorded. Already established in the repository: arbitrary
finite Chang histories are realizable (2048/2048, `docs/CHANG_CROSS_SCALE_REALIZER_AUDIT.md`), and
`EOC/ChangFullShift.lean` proves a machine-checked zero-corridor **full shift** exists symbolically.
Chang's **Map Balance Theorem (Chang Thm 4.2)** is a counting theorem over histories — a
*population* statement.

> **No proved orbit-level asymptotic Chang condition for a single positive orbit is known to this
> repository.** Any such condition would have to be a statement about asymptotic frequencies along
> one seed, which is §V, and none is available. Chang is therefore not usable as an input here, and
> is not used.

## U. Garcia–Tal orbit sparsity (Gate 19)

`[GT99]` M. V. P. Garcia and F. A. Tal, *A note on the generalized 3n+1 problem*, Acta Arith. **90**
(cited in `docs/LITERATURE_CONTEXT.md`); Banach-density-zero of the orbit set, qualitative, with
Curry supplying the explicit form.

Sparsity constrains **which integers the orbit visits**. The realizer floor is a statement about
the *size of the least representative of a residue class determined by the word*. To convert one
into the other one would need a bound on `r_N` from a density statement about `{m_n}` — and density
zero is compatible with every size profile. No bridge that avoids Curry's already-audited route was
found; this branch is closed.

## V. Return statistics (Gate 20)

A theorem about asymptotic frequencies of Chang events / residue classes / valuation blocks / return
times **along one seed** would be genuinely new information, precisely because it is not a statement
about arbitrary finite histories across different seeds.

**No such theorem is known.** What exists is the opposite: full-shift realizability of arbitrary
finite histories (§T), which is a population statement across seeds. The distinction the gate warns
about is real and the useful side of it is empty.

## W. Tail / shift-invariant classification (Gate 21)

| property | class |
|---|---|
| `S_N ≤ ⌊αN⌋` for a given `N` | finite-prefix / cylinder |
| zero confinement (all `N`) | shift-invariant, tail-closed |
| `R_n → −∞` | tail |
| eventual periodicity | tail |
| lift digits eventually zero | **tail** — the positivity marker |
| `r_N` bounded | tail (equivalent to the above) |
| orbit injectivity | orbit-global, not word-level |
| `Σ1/m_n < ∞` | orbit-global, tail in `n` |

Positivity is a tail property, and so are all its known equivalents. No known positive-orbit
theorem supplies a *different* tail or shift-invariant property that interacts non-trivially with
zero confinement — §Y shows why any word-level one cannot.

## X. Full-shift stress test (Gate 22)

The machine-checked zero-corridor full shift (`EOC/ChangFullShift.lean`) has a free label stream.
Can a global candidate be forced to fail by choosing the labels? For the candidates that are
word-level — `R_n → −∞`, prescribed asymptotic label frequency, normality, bias, low complexity —
the answer is that **arbitrary label histories coexist with the construction**, because the label
stream is free by construction. So no word-level candidate restricts the full shift.

Guarding against the gate's warning: this says nothing about valuation-word freedom beyond what the
full-shift theorem actually proves. The stronger statement this audit needs is §Y, which is proved
independently and does not rely on the Chang construction at all.

## Y. Shadow-model construction (Gate 23) — the audit's main result

**Construction.** Index by an arbitrary `b ⊆ ℕ`. Define the valuation word (digits indexed from 0)

```
famWord b i  =  2  if i ≡ 2 (mod 3) and i/3 ∈ b,
                1  otherwise.
```

**Properties, all proved.**

1. Every digit is `≥ 1`, so every member is an admissible word (`famWord_pos`).
2. `Σ_{i<n} famWord b i ≤ n + n/3` (`famWord_sum_le`).
3. **Zero-confined.** For an integer `S`, the corridor condition `S ≤ ⌊αj⌋` is *equivalent* to
   `2^S ≤ 3^j`, since `2^{αj} = 3^j`. And `2^{j + j/3} ≤ 3^j` holds for every `j`
   (`famWord_confined`; proof: cube both sides, `16 ≤ 27`). Confirmed exhaustively for small depth:
   32/32, 128/128, 512/512 of all members at lengths 12, 18, 24.
4. **Linear negative drift.** `4/3 = 1.3333 < α = 1.58496`, so
   `R_j ≤ (4/3 − α)j = −0.2516·j → −∞` linearly — strictly stronger than zero confinement, and the
   strongest word-level Curry shadow.
5. **Uncountable.** `famWord` is injective (`famWord_injective`), so the family has cardinality
   `2^ℵ₀`.
6. **Every word-level shadow in the inventory holds.** Since `R_j ≤ −0.2516j`, the series
   `Σ_j 2^{R_j}` is dominated by a geometric series and **converges** — this is the word shadow of
   Curry's reciprocal summability (§AF). And `R_n ≥ −G` forces `n ≤ G/0.2516 ≈ 3.97G`, so
   `#{n : R_n ≥ −G} = O(G)`, far inside Curry's occupation bound `≪ 2^{βG}G`. Measured on five
   representative members (all-`1`, all-`2`, random, `b` = squares, `b` = evens) at length 3000:
   confinement holds for all (also in the exact integer form `2^{S_j} ≤ 3^j`), `R_L/L` ranges over
   `−0.585 … −0.2516`, and `Σ2^{R_j}` lands in `3.00 … 5.18`.

**The barrier.** One positive integer realizes at most one infinite valuation word. So if every
member of an injectively indexed family had a positive-integer realizer, we would have an injection
`Set ℕ → ℕ`, contradicting Cantor (`not_all_realizable_of_injective`). Therefore:

> **Theorem.** All but countably many members of this uncountable family of zero-confined valuation
> words with `R_j → −∞` linearly have **no positive-integer realizer**.

Every word-level global condition in §H is satisfied by all of them — confinement, linear negative
drift, convergence of `Σ2^{R_j}`, and the occupation bound. **Word-level global conditions are
defeated by cardinality, before any arithmetic.** This is the strongest form of the negative result
the brief asked for, and it subsumes §L (which gives two explicit witnesses) and §X.

Honest scope: the theorem does not *name* a specific unrealizable member, and it does not claim
Curry's genuine orbit conditions (`Σ1/m_n < ∞` etc.) hold for these words — they are not defined
without ordinary iterates. That restraint is exactly what Gate 23 demanded.

## Z. Word shadow versus actual orbit (Gate 24)

**Word shadow** — expressible from `D` alone: zero confinement, `R_n → −∞`, the occupation bound,
aperiodicity, complexity, Chang labels.
**Actual-orbit condition** — involves the ordinary iterates `m_n` of one positive seed:
`Σ1/m_n < ∞`, `Q_∞ < ∞`, injectivity, `m_n → ∞`, orbit-set sparsity, window sparsity.

§Y settles the first column: no combination of word shadows can separate positive realization,
because uncountably many words satisfy all of them and at most countably many are realizable.

The second column is where new information could live — but every member of it **presupposes** a
positive seed. Using it to exclude a word requires first assuming the word is realized, which is
the assumption one is trying to contradict. That is the precise logical shape of the impasse.

## AA. Sign consistency (Gate 25)

For a 2-adic `x` the "affine iterates" are `x_n = (3^n x + C_n)/2^{S_n}`, elements of `ℤ₂`. Asking
that every `x_n` be a positive ordinary integer is **equivalent** to `x` being a positive ordinary
integer: `x_0 = x`. Asking only that `x_n ∈ ℤ_{>0}` for `n ≥ 1` is also equivalent, since
`x = (2^{S_1}x_1 − C_1)/3` and integrality plus the word force `x` back.

So sign consistency is not weaker. Closed as realization-equivalent. (For genuinely non-ordinary
`x` the phrase "positive" has no meaning in `ℤ₂`, which is the rigorous reason the gate asked for.)

## AB. Global realizer-height profile (Gate 26)

`H_N := log₂ r_N`. Known: `r_N` is non-decreasing and `r_{N+1} ≡ r_N (mod 2^{S_N+1})`, so `H_N` is
non-decreasing; positive realization is exactly eventual constancy (§R).

Tested candidates for a law beyond that: bounded increments — **false**, `r_N` can jump by
`t_N·2^{S_N+1}` with `t_N` up to `2^{d_{N+1}}−1`; subadditivity and convexity — no mechanism, and
the lift-digit audit shows the increments are just grouped binary digits of a fixed realizer, hence
arbitrary; recurrence — none.

Nothing beyond monotonicity and eventual constancy. The latter is ZCRE.

## AC. Cross-scale jump sequence (Gate 27)

`r_{N+1} = r_N + t_N·2^{S_N+1}` with `t_N` the lift digit, and
`RealizerLiftDigit.liftDigit_eq_bitBlock` proves `t_N` is literally the block of binary digits of a
fixed realizer in positions `S_N+1,…,S_{N+1}`. So the jump sequence carries no law beyond the binary
expansion identity. Confirmed and closed, as the gate anticipated.

## AD. Current iterate as a global variable (Gate 28)

`m_N = (3^N m_0 + C_N)/2^{S_N}`. For a **fixed** `m_0`, requiring `m_N ∈ ℤ_{>0}` for all `N` is
exactly realization, so nothing is gained directly.

Is any *aggregate* inequality over all `N` weaker and independently provable? The natural aggregates
are `Σ 1/m_N` (Curry, §AF), `Π(1+1/(3m_j)) = Q_∞` (§M), and `inf_N m_N ≥ 1` (positivity, shown
vacuous under confinement in the previous branch). None is both weaker and independently provable.

## AE. Type-II growth (Gate 29)

Known for Type II: `m_N → ∞`. **No quantitative lower-growth rate is known**, and divergence to
infinity is compatible with arbitrarily slow growth. Without a rate, no realizer floor can follow —
an `εN` floor on `log₂ r_N` needs exponential information, and "`m_N → ∞`" supplies none.

## AF. Reciprocal summability (Gate 30)

Curry gives `Σ_N 1/m_N < ∞` for divergent orbits, which is much stronger than `m_N → ∞`. Combined
with `m_N = m_0 2^{−R_N} Q_N` and `Q_N ∈ (1, Q_∞)`, summability is equivalent to
`Σ_N 2^{R_N} < ∞` up to the bounded factor `m_0 Q_N` — i.e. it is *equivalent to convergence of the
global carry sum of §N*, hence to a word-level statement.

**Strongest deterministic consequence:** `Σ_N 2^{R_N} < ∞`, which is a word shadow, and therefore
falls to §Y — where every member of the uncountable family is verified to satisfy it.

A consistency check on the identity of §M, using the negative witness: for the all-`1` word
(realizer `−1`), `Q_n = Π(1 − 1/3) = (2/3)^n → 0`, so `3m_0(Q_∞ − 1) = 3(−1)(−1) = 3`, and the
measured `Σ_j 2^{R_j}` for that word is exactly `3.000`. The identity holds even off the positive
branch, which is precisely why it carries no positivity information.

## AG. Summability versus pointwise growth (Gate 31)

Summability permits sparse small values: taking `x_n = n²` except `x_n = 1` at powers of two gives
`Σ1/x_n < ∞` while `x_n = 1` infinitely often (verified numerically: block minima
`1, 1, 1, 361201, 641601, 1, …`). So no pointwise lower envelope follows.

**Does Collatz structure remove the freedom?** Partly: `m_N = m_0 2^{−R_N}Q_N` with `Q_N` bounded
means `m_N` is determined by `R_N` up to bounded factors, so "sparse small `m_N`" means "sparse
`R_N` near 0" — which is exactly Curry's occupation bound (§AH), already known and already a
population statement. So the extra structure converts the abstract freedom into a known bound and
no further.

## AH. Occupation versus placement (Gate 32)

Curry's `#{n : R_n ≥ −G} ≪ 2^{βG}G` is a word-level statement (§J) counting *how often* the drift
is shallow. Combining it with one-seed nesting does not bound `r_N`: the count constrains the
*population of times*, while `r_N` is the *size of one representative* at one time.

This is the population-versus-pointwise barrier identified in earlier rounds, rechecked here at the
single-orbit level. It still holds, and §Y explains why it must: the occupation bound is a word
shadow, and word shadows cannot separate realizability at all.

## AI. Consequence for Open Problem C (Gate 33)

For every candidate `P` in the inventory: assuming zero confinement `+ P`, can one derive
`log₂ r_N ≥ εN`? **No, for all of them.** The word-level candidates fail by §Y (uncountably many
words satisfy them with no realizer at all, so they cannot force any lower bound on a realizer that
need not exist). The orbit-level candidates fail because they presuppose realization (§Z) and
supply no size control (§S).

## AJ. Consequence for qualitative escape (Gate 34)

Maintaining the hierarchy

```
eventual constancy excluded  <  r_N → ∞  <  log r_N → ∞ at a rate  <  exponential floor,
```

no candidate reaches even the first level *from outside*: "eventual constancy excluded" is itself
the negation of realization (§R), so deriving it from `P` would make `P` at least as strong as
non-realizability. No candidate gives `r_N → ∞` either, for the same reason.

## AK. Periodicity-conjecture boundary (Gate 35)

A theorem of the shape "a non-eventually-periodic infinite valuation word cannot have an ordinary
positive integer realizer" is the classical 2-adic periodicity boundary, already identified in the
repository, and the previous branch showed it is not even implied by what is known (a hypothetical
divergent orbit would have `Z = −n_0` integral with an aperiodic word). Not presented as a new
mechanism.

## AL. Nonlocality classification (Gate 36)

| level | members |
|---|---|
| 1. **finite/cylinder** — automatically insufficient | every prefix condition; `S_N ≤ ⌊αN⌋` at fixed `N`; every coordinate of the previous branches |
| 2. **infinite but intrinsic** — ZCRE-equivalent | bounded `r_N`; eventual constancy; eventually-zero lift digits; same-seed coherence; sign consistency |
| 3. **global word shadow** — asymptotic but symbolic | zero confinement; `R_n → −∞`; `Σ2^{R_n} < ∞`; occupation bound; aperiodicity; complexity; Chang labels |
| 4. **actual positive-orbit necessary condition** — uses ordinary iterates | injectivity; `m_n → ∞`; `Σ1/m_n < ∞`; `Q_∞ < ∞`; orbit-set sparsity; window sparsity |
| 5. **quantitatively useful pointwise condition** | **EMPTY** |

Level 3 is defeated wholesale by §Y. Level 4 is non-empty but every member presupposes realization
(§Z) and none controls size (§S). **Level 5 is empty**, which is the audit's finding.

## AM. Finite-local impossibility theorem (Gate 37)

> **Theorem (finite-precision impossibility).** Let `k ≥ 1` and let `P` be a property of integers
> that depends only on the residue mod `2^k`. Then `P` is not equivalent to `0 < x`.

Lean: `no_finite_precision_sign_separator`. Valuation-word corollary, via §C: no bounded-prefix
condition can separate finite realizability from infinite positive realizability, because every
finite prefix is positively realizable by unboundedly many integers.

**Careful wording, as the gate requires.** This is a theorem about the representation topology — it
says finite precision cannot *characterize* positivity. It is **not** an impossibility theorem for
quantitative realizer floors: a floor `log₂ r_N ≥ εN` is a statement at each finite `N` and is not
excluded by anything here.

## AN. Strictly weaker positivity proxy (Gate 38)

**NONE.**

Requirement: `P` necessary for positive infinite realization, not implying it, and independently
analyzable. Candidates and their failure modes:

| candidate | fails |
|---|---|
| orbit-set sparsity | necessary and weaker, but no bridge to `r_N` (§U) |
| reciprocal summability | necessary and weaker, but its word shadow is `Σ2^{R_n} < ∞`, killed by §Y (§AF) |
| return statistics | no theorem exists (§V) |
| global sign constraints | equivalent to realization (§AA) |
| growth conditions | no rate known (§AE) |

Two candidates (sparsity, summability) do satisfy "necessary and strictly weaker". Both fail the
third requirement in the same way: **their analyzable content is a word shadow, and word shadows are
defeated by cardinality.**

## AO. Nonredundant-intersection test (Gate 39)

Not reached, since no proxy survived §AN. Recording what the test would have required, in the
previous branch's language: a surviving `P` would need (i) zero-confined words satisfying `P`,
(ii) zero-confined words violating `P`, and (iii) all positive Type-II orbits in class (i), **with
quantitative force at scale `εN`**. For `Σ2^{R_n} < ∞` classes (i) and (ii) both exist, but (iii)
gives nothing because §Y populates (i) with uncountably many unrealizable words. No fake Jacobian is
introduced; the criterion used is constraint independence as defined in the previous branch.

## AP. Weakest genuinely new global theorem needed (Gate 40)

The weakest shape that would advance matters, and which is **not** a disguised `log r_N` or terminal
gap:

> **(G-def)** There is `ε > 0` such that every positive Type-II orbit incurs, by depth `N`, a
> cumulative defect `Δ(N) ≥ εN` in some quantity defined from the **ordinary iterates** `m_n` — not
> from the valuation word — which is bounded by `o(N)` for any indefinitely zero-confined word.

The two clauses are the point: the defect must be measurable on the orbit side (so that §Y does not
apply) and bounded on the word side (so that the contradiction closes). **No such quantity is known
to this audit**, and §Z explains the obstacle: every orbit-side quantity currently available is
defined only once realization is assumed.

An independent route to estimating such a defect would have to come from the Archimedean dynamics of
`m_n` directly — Curry's `Σ1/m_n < ∞` is the closest existing statement, and §AF shows its
deterministic content collapses to a word shadow.

## AQ. Lean formalization (Gate 42)

`EOC/GlobalSeparation.lean`, 9 declarations, built on the previous branches' modules. No topology
infrastructure was created and no external theorem was re-formalized.

| theorem | content |
|---|---|
| `exists_positive_in_class` | every class mod `2^k` has arbitrarily large positive members |
| `exists_odd_positive_in_class` | the same preserving oddness — §C |
| `no_finite_precision_sign_separator` | §AM, the finite-precision impossibility theorem |
| `decreasing_infinite_inter_empty` | §Q, the compactness no-go |
| `famWord` | the uncountable family, indexed by `Set ℕ` |
| `famWord_pos` | admissibility |
| `famWord_sum_le` | `Σ_{i<n} ≤ n + n/3` |
| `famWord_confined` | `2^{j+j/3} ≤ 3^j`, i.e. zero confinement in exact integer form |
| `famWord_injective` | cardinality `2^ℵ₀` |
| `not_all_realizable_of_injective` | §Y, the countability barrier (via `Function.cantor_injective`) |

Following the convention of preceding rounds the module is not added to the `EOC.lean` aggregator.

## AR. Tests / build

```
lake build EOC.ConstraintHeight   →  2261/2261, success
lake build EOC.GlobalSeparation   →  2262/2262, success
lake env lean EOC/GlobalSeparation.lean →  exit 0 (deprecation warnings only)
```

Scripts: `scratch/global_checks.py`, `scratch/gate23_family.py`, `scratch/family_shadows.py`.

Computational results: `C_n/3^n = m_0(Q_n − 1)` — 4,800 checks, 0 mismatches; family confinement —
exhaustive 32/32, 128/128, 512/512 at lengths 12, 18, 24, plus 3,000 random members at length 300
and the extreme all-`2` member to length 600; summability counterexample as tabulated in §AG.

**A correction made during the audit.** My first proposed family put the free digit at every
*second* position. That family is **not** zero-confined: `b₁ = 2` already gives `S_1 = 2 > ⌊α⌋ = 1`.
The construction was replaced by the every-third-position version above and re-verified
exhaustively. Recorded rather than silently fixed.

## AS. Axiom audit

All nine declarations: `[propext, Classical.choice, Quot.sound]` (`exists_positive_in_class` uses
only `[propext, Quot.sound]`). No `sorry`, `admit`, `axiom`, `opaque`.

## AT. Files changed

```
EOC/GlobalSeparation.lean                               (new)
docs/GLOBAL_SINGLE_ORBIT_NONLOCAL_SEPARATION_AUDIT.md   (new)
scratch/global_checks.py                                (new)
scratch/gate23_family.py                                (new)
```

## AU. Commits

`69df8b3` — *Close the global word-shadow route by a cardinality barrier*, on top of base
`43c9798`, plus a follow-up commit recording this hash and the push status. `main` untouched.

## AV. Push status

Pushed to `origin/global-single-orbit-nonlocal-separation-audit`. **No PR opened.**

## AW. Research verdict

**`THE MISSING INFORMATION IS GENUINELY NONLOCAL, BUT NO KNOWN GLOBAL ORBIT CONSTRAINT CONTROLS THE
REALIZER FLOOR`**

All six stop conditions of Gate 43 hold:

1. every finite condition is defeated — every residue cylinder contains arbitrarily large positive
   odd integers (§C, §AM);
2. the only exact infinite positivity marker remains the eventual-zero lift tail (§F);
3. all other intrinsic global conditions are ZCRE-equivalent or weaker (§O, §AA, §AB, §AC, §AL
   level 2);
4. Curry and Garcia–Tal constrain actual divergent orbits but not least-realizer placement (§J, §U,
   §AF, §AH);
5. Chang and global return conditions remain population-level or absent (§T, §V);
6. no strictly weaker positive-orbit proxy intersects zero confinement with quantitative force
   (§AN).

Why this verdict rather than the neighbours: `FINITE CYLINDERS CANNOT SEPARATE POSITIVE
REALIZATION` (§C, §AM) and `EVENTUAL-ZERO LIFT TAIL REMAINS THE ONLY EXACT POSITIVITY MARKER` (§F)
are both established but are single components; `KNOWN GLOBAL WORD SHADOWS ARE TOO WEAK` is
established in the strongest possible form by §Y but omits the orbit-level column; `CURRY IS GLOBAL
BUT DOES NOT CONTROL REALIZER PLACEMENT` (§AF, §AH) is one row of the ledger. The chosen verdict is
the conjunction that all six stop conditions support, and it is the deepest statement the evidence
carries. `A STRICTLY WEAKER POSITIVE-ORBIT PROXY SURVIVES` is refuted by §AN.

**What is new here, beyond the closure:**

1. **The cardinality barrier (§Y).** An explicit uncountable family of zero-confined valuation
   words with `R_j → −∞` *linearly*, of which all but countably many have no positive-integer
   realizer. Word-level global conditions are therefore insufficient before any arithmetic is
   attempted — this replaces case-by-case refutation with one argument.
2. **Zero confinement has an exact integer form**, `S_j ≤ ⌊αj⌋ ⟺ 2^{S_j} ≤ 3^j`, which removes
   real-number reasoning from confinement proofs entirely (`famWord_confined`).
3. **The compactness failure is located precisely (§Q):** the realizer tree is *infinitely*
   branching, so König never applied; and the nested classes converge to a 2-adic point, not an
   integer. What is missing is a uniform bound, which is ZCRE.
4. **Where new information can still enter (§Z, §AP):** only from the ordinary iterates `m_n` of
   one positive seed, via a quantity that is *not* expressible from the word. Every such quantity
   currently known presupposes realization, which is the exact logical shape of the impasse.
