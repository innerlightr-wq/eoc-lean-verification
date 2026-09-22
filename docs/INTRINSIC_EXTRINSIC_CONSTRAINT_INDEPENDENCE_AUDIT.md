# Intrinsic–extrinsic constraint independence audit

Periodic closure, aperiodic moving anchors, and the Archimedean–2-adic intersection.

## A. Starting state

| item | value |
|---|---|
| base commit | `c23b14a7f8c7784895567cfca7bd64c753e9549a` (`Record the correct commit hash in the audit report`) |
| verified how | `git fetch origin`, then `git rev-parse origin/superbudget-cancellation-external-arithmetic-audit` |
| ordinary checkout | **dirty** (53 entries). Not touched. |
| worktree | isolated, `scratchpad/eoc-ie`, `.lake/packages` symlinked |
| branch | `intrinsic-extrinsic-constraint-independence-audit` |
| `main` | untouched. No PR. |

## B. Conceptual source paper

`~/Downloads/IntrinsicCubic_ver (2).pdf` (three byte-identical copies),
sha256 `f53b851077e454e9c33361144b43e6631713aca4bd6c8aaa9584bc105a0bf3c4`; extracted text
`IC.txt`, 1171 lines, sha256 `5cdd9b59484d15928c02ddefba146c0c373ccc1e0ac6435636efbe903e1a3a16`.
Read: §7, §8, §9, App. A (A.1–A.7), App. B.5.

**Imported — exactly two things, both methodological.**

1. **The A.5 three-level hierarchy.** Two quantities may (i) merely coexist; (ii) form a
   *complementary pair through an exact identity* `Φ(X,Y) = 0`; (iii) have *locally independent
   directions*. The paper states plainly that "only the third notion corresponds directly to
   transversality", and that an exact identity is "a complementary reflection identity, not a
   Wronskian or Jacobian criterion". This is the classifier this audit uses, and §Q shows the
   Collatz case lands squarely in (ii).
2. **The paper's own caution about its strongest result.** After Proposition 8.2 it says
   transversality "does not establish … that any physical system realizes `F` and `G` as
   **independently derived constraints**". The open question is independence of *generation*, not
   the determinant. That is precisely Gate 7's redundancy test.

A third, cautionary import from B.5: transversality there is **generic** across the whole
positive `q`-family and therefore "does not distinguish `q = 3`". Independence that is generic
carries no information; it must be quantitative at the required scale.

**Not imported:** the numerical cubic root, `q = 3`, any physical transition claim, smooth
Jacobians, the Ramanujan comparison, and the words "transversal"/"degenerate" as Collatz
predicates. See §AI.

## C. Current Collatz dependency graph

Writing `D = (d_1,…,d_N)`, `S_j = Σ_{i≤j}d_i`, `C_{j+1} = 3C_j + 2^{S_j}`,
`Z = Σ_{i≥0}2^{S_i}3^{−(i+1)}`:

```
                     D  (the valuation word)
                     │   everything below is a function of D (and of N)
          ┌──────────┼───────────────┬─────────────────┐
          ▼          ▼               ▼                 ▼
        S_N        C_N        confinement flag     shell (N,S_N)
          │          │
          └────┬─────┘
               ▼
   ξ_N = −C_N·3^{−N},   χ_N = ξ_N mod 2^{S_N} = (−Z) mod 2^{S_N}
               │
   ┌───────────┼──────────────┬──────────────┬─────────────┐
   ▼           ▼              ▼              ▼             ▼
 r_N=r(D_N)  lift digits  terminal gap g_N  E_N, F_N   B_N = C_N+3^N χ
   │                          │              │             │
   └──────────────────────────┴──────────────┴─────────────┘
          all exact coordinate changes of one another (§F)

  M_N = v₂(X_N),  H_N = F_N+M_N      — transport; on a genuine orbit
                                       X_N = ⌊n₀/2^{S_N}⌋ (previous branch)
```

**Genuinely independent hypotheses** in this diagram: only two — (i) that `D` is zero-confined,
and (ii) that some *positive integer* realizes `D`. Everything else is a function of `D`.

## D. Operational definition of intrinsic

`Q` is **intrinsic at depth `N`** if `Q` factors through `(D, N)`: whenever two admissible objects
have the same valuation word to depth `N`, they have the same `Q`. Equivalently `Q = Q(D,N)` is a
well-defined function on words.

## E. Operational definition of extrinsic

`C_ext` is **extrinsic** if it is not logically determined by `(D,N)` over the ambient class under
consideration — i.e. there exist two ambient objects with the same `(D,N)` and different `C_ext`
status. Notational difference is not sufficient (Gate 0's warning).

Ambient classes used below: `ℤ₂`-realizers; ordinary integers; positive vs. negative integer
realizers; finite exact realizer classes mod `2^{S_N+1}`.

## F. Factorization test (Gate 1)

| quantity | factors through `(D,N)`? | class |
|---|---|---|
| `S_N`, `C_N`, `ξ_N`, `Z` mod `2^{S_N}` | yes, by definition | A (exact coordinate) |
| `χ_N`, `r_N` | yes — `χ_N = (−C_N3^{−N}) mod 2^{S_N}` | A |
| lift digits | yes — grouped binary digits of `r` (`RealizerLiftDigit`) | A |
| terminal gap `g_N = S_N − ⌊log₂ r_N⌋` | yes | A |
| `E_N`, `F_N` | yes | A |
| `M_N`, `H_N` (transport) | yes, given the infinite word | A |
| `B_N = C_N + 3^Nχ` | yes, given `χ` | A |
| `|B_N|` (ordinary magnitude) | **yes** — see §Q | A |
| confinement | a predicate **on `D`** | restricts domain, not value |
| Curry window sparsity | a predicate **on `D`** | restricts domain, not value |
| positivity of the realizer | not a function of `(D,N)` alone | **D**, but see §Y |

Verified rather than assumed: the "A" rows are verified numerically in the previous two branches
(88,000 steps for the transport rows; 89,955 for the depth rows) and here for `B_N` (§M).

## G. Positivity boundary (Gate 2)

`ℤ₂`-realizability and positive-integer realizability genuinely differ: the all-ones word is
realized by `−1`, the word `1,2,1,2,…` by `−5`, and both have `M_j ≡ 0` (previous branch, §AA
there). So positivity is **not** a function of `(D,N)`: it lands in class D of §F, and is the one
candidate that survives the factorization test.

The extra information positivity supplies, stated exactly: `−Z` has a **terminating** binary
expansion. That is a real Archimedean fact — it bounds `|−Z|` — and it is what made the previous
branch's `O(log n₀)` regeneration bound work. §Y measures whether it is quantitatively useful
here. It is not.

## H. Periodic closure mechanism (Gate 3, 13)

Every exact-realizer condition in the program has one shape: `χ` realizes `D` iff

```
2^{S_N}  divides  A + χ·Λ ,
```

with `A, Λ` integers **generated by the word**. The only general tool converting this into a size
statement is the universal integer fact "a nonzero multiple of `2^m` has absolute value `≥ 2^m`",
which yields the **dichotomy**

> either `A + χΛ = 0`, pinning `χ` to the single rational `−A/Λ`,
> or `|χ| ≥ 2^{S_N}/H − 1`, where `H = max(|A|,|Λ|)` is the **height** of the relation.

For a purely periodic word of period `p`, the previous branch's `geom_closed_form` collapses the
carry to `C_{Np}·Δ = c₀(3^{Np} − 2^{Nσ})` with

```
c₀ = Σ_{t<p}3^{p−1−t}2^{s_t},    Δ = 3^p − 2^σ,
```

both **independent of `N`**. So `H = max(|c₀|,|Δ|) = O(1)` in `N` and the second branch gives
`log₂|χ| ≥ S_N − log₂H − O(1)`.

**The smallest exact closure principle responsible for success**, stated as the gate demands:

> Periodicity amortizes a *fixed* height over an unbounded number of repetitions. Measured:
> `h_N/S_N ≈ 1/(number of repetitions)`.

| block | reps | `S_N` | `h_N` | `h_N/S_N` | proved floor `S_N−h_N` | actual `log₂χ` |
|---|---|---|---|---|---|---|
| `(1,2)` | 2 | 6 | 2.32 | 0.3870 | 3.68 | 5.88 |
| `(1,2)` | 8 | 24 | 2.32 | 0.0967 | 21.68 | 24.00 |
| `(1,2)` | 32 | 96 | 2.32 | 0.0242 | 93.68 | 96.00 |
| `(2,1,1,2)` | 2 | 12 | 6.69 | 0.5572 | 5.31 | 11.91 |
| `(2,1,1,2)` | 32 | 192 | 6.69 | 0.0348 | 185.31 | 187.91 |

Answers to the gate's five questions: the anchor is **fixed** (`−c₀/Δ`, one rational); it is
rational in `ℤ₂`; it is controlled by a finite recurrence (order 2, roots `3^p`, `2^σ`); and
**yes**, the proof uses an Archimedean lower bound — but the universal one, `|A+χΛ| ≥ 2^{S_N}`,
not a Collatz-specific estimate.

## I. Eventually periodic sector (Gate 3 extension)

If `D` is eventually periodic (preperiod `L`, period `p`), then `Z` is the sum of a finite part and
a geometric tail, hence a **rational** `P/Q` with `Q` odd and `|P|,|Q|` bounded in `N`. The
relation becomes `2^{S_N} ∣ P − Qχ`, again of bounded height, and the §H dichotomy applies
verbatim. So eventual periodicity extends the sector with no new mechanism.

Verified by rational reconstruction of the anchor from `χ_N`, then checking the *same* `P/Q`
against every larger depth:

| word | anchor `P/Q` | `h_N` | `h_N/S_N` at `S_N`= 22→58 | anchor fixed? |
|---|---|---|---|---|
| preperiod `(3,1)`, period `(1,2)` | `−91/9` | 6.51 | 0.296 → 0.112 | yes |
| preperiod `(2,2,3)`, period `(2,1,1,2)` | `−13813/459` | 13.75 | 0.320 → 0.120 | yes |
| preperiod `(1,1,1,4)`, period `(1,2)` | `−235/27` | 7.88 | 0.315 → 0.129 | yes |
| one-defect on `(1,2)` | `−725/81` | 9.50 | 0.307 → 0.173 | yes (from `N=20`) |
| one-defect on `(2,1,1,2)` | `−103/17` | 6.69 | 0.186 → 0.062 | yes |

The relation `2^{S_N} ∣ P − Qχ_N` holds at every depth tested. (At the smallest depth of the
`(1,2)`-defect case the reconstruction returns a different, spurious short vector — the
reconstruction bound `√M` admits one there — and locks onto `−725/81` from `N = 20` onward. Noted
rather than hidden.) **One-defect words are eventually periodic and behave exactly so**; that row
of §AF is verified, not assumed.

**One direction only.** Eventually periodic word ⟹ `Z` rational. The converse is **false**, and
the point matters: a hypothetical divergent orbit has `Z = −n₀`, an integer, with an aperiodic
word. The classical "rational ⟺ eventually periodic" concerns a 2-adic *digit* expansion, not
this valuation word; conflating them would be an error and is avoided here.

## J. Aperiodic failure of closure (Gate 4)

For an arbitrary word the only word-generated relation available is `(A,Λ) = (C_N, 3^N)`, so

```
h_N = log₂ max(C_N, 3^N) = αN + O(log N).
```

Under zero confinement `S_N ≤ ⌊αN⌋`, hence `S_N − h_N ≤ 0`: the second branch of the dichotomy is
**vacuous**. Stated algebraically, the failure is

> `h_N ≥ S_N` — the height of the relation grows at the same exponential rate as the divisor.

Measured on confined irregular words:

| | `N` | `S_N` | `h_N` | `h_N/S_N` | proved floor | actual `log₂χ` |
|---|---|---|---|---|---|---|
| confined irregular | 12 | 16 | 19.06 | 1.1914 | **−3.06** | 15.82 |
| confined irregular | 16 | 24 | 26.24 | 1.0932 | **−2.24** | 23.60 |
| confined irregular | 20 | 31 | 33.14 | 1.0690 | **−2.14** | 30.49 |

Lean: `height_separation_vacuous_of_confined`.

## K. Fixed-anchor versus moving-anchor split (Gate 17)

Yes — this is the sharper split, and §H–§J make it quantitative. The correct invariant is not
periodicity but

```
ρ_N  :=  h_N / S_N   ∈  (0, ∞),
```

the height of the best **word-generated** relation, normalized by the divisor exponent. The
dichotomy's second branch is useful exactly when `ρ_N ≤ 1 − ε/α`.

| sector | `ρ_N` | second branch |
|---|---|---|
| periodic | `→ 0` (as `1/reps`) | exponential floor |
| eventually periodic | `→ 0` | exponential floor |
| genuine positive orbit (`Z = −n₀`) | `→ 0` (`h = log₂ n₀`) | **degenerate branch taken**: `A+χΛ = 0`, `χ = n₀` |
| confined irregular | `≥ 1` | vacuous |

This subsumes the known successful sectors better than periodicity, and it also explains the
genuine-orbit case, which periodicity alone does not: there the height is bounded *and* the
degenerate branch is the one realized.

## L. Discrete constraint-independence criterion (Gate 6, 26)

No Jacobian is manufactured. The criterion used is the operational one:

> Two conditions on a class are **independent enough to test** if (1) neither is a deterministic
> function of the other on that class; (2) ambient examples satisfy one without the other; (3)
> joint satisfaction shrinks the feasible set beyond either alone; (4) the shrinkage is
> quantitative at the required scale.

I use the phrase **constraint independence**, not transversality, throughout — the source paper's
own B.5 shows that a determinant criterion can be generic and therefore uninformative, and there
is no differential structure here to support the geometric word.

## M. Current `B_N` definition (Gate 8)

Reconstructed from the branch, not from prose. For a word `D` of length `N` and an integer
`1 ≤ χ < 2^{S_N}`:

```
C_N  = Σ_{i<N} 3^{N−1−i}·2^{S_i}          (odd; the i=0 term is 3^{N−1})
B_N(D,χ)  =  C_N + 3^N·χ
χ_N = χ   ⟺   2^{S_N} | B_N(D,χ).
```

**The identity the previous branch did not record.** If `χ` realizes `D` for `N` steps, with
accelerated iterates `m_0 = χ`, `m_{j+1} = (3m_j+1)/2^{d_{j+1}}`, then

```
B_N(D,χ)  =  2^{S_N} · m_N ,        m_N odd and positive.
```

Verified on 10,000 words: identity mismatches **0**, `m_N` odd violations **0**. Consequences:

```
v₂(B_N) = S_N            EXACTLY (not merely ≥)
log₂|B_N| = S_N + log₂ m_N
log₂|B_N| − v₂(B_N) = log₂ m_N
```

and the dual 3-adic form `m_N ≡ C_N·2^{−S_N} (mod 3^N)`, also verified, 0 violations.

## N. Intrinsic divisibility condition (Gate 8 second half)

By §M and the terminal-gap translation of the earlier branches, with `r_N = χ_N` when the lift bit
is 1:

```
g_N ≤ S_N − ⌊log₂ χ_N⌋,      Open Problem C:  log₂ χ_N ≥ εN − O(1).
```

And by §M, `log₂ χ_N` and `log₂ m_N` differ by `O(log N)` in the heavy shell
(`2^{S_N}m_N = 3^Nχ_N + C_N` with `2^{S_N} ≍ 3^N`). So the dangerous-realizer quantity, the
terminal gap, and the size of the terminal iterate are three readings of one number.

## O. Archimedean baseline (Gate 9, 20)

The product formula over `ℚ` gives `2^{v₂(B)}·|B|_∞·Π_{p odd}|B|_p = 1` with `|B|_p ≤ 1`, hence
`v₂(B) ≤ log₂|B|`. **For `B_N` this is not merely weak — it is an equality up to the cofactor**,
because §M gives `v₂(B_N) = S_N` and `log₂|B_N| = S_N + log₂ m_N` exactly. There is no bound here
to improve; there is a cofactor whose size *is* the problem.

## P. Required `Ω(N)` improvement (Gate 9) — and a correction

Re-derived from current definitions with signs and shell direction checked.

The previous branch wrote the target as "improve the trivial bound `v₂(B) ≤ log₂|B|` by `Ω(N)`".
**That framing is misleading and is corrected here.** `v₂(B_N)` is not bounded by `log₂|B_N|` with
slack to be recovered; it is *exactly* `S_N`. The quantity `log₂|B_N| − v₂(B_N)` is *exactly*
`log₂ m_N`. So the target

```
v₂(B_N) ≤ log₂|B_N| − εN + O(1)
```

is literally `log₂ m_N ≥ εN − O(1)`, i.e. "the terminal iterate is exponentially large", which by
§N is Open Problem C restated. The `Ω(N)` size of the required gain was right; the description of
it as an improvable inequality was not. There is no inequality to sharpen — only an unknown
integer to bound below.

## Q. Is ordinary height genuinely extrinsic? (Gate 10, 19)

**No.** This is the audit's central finding.

Distinguishing the gate's three possibilities:

1. *universal integer fact* `2^{v₂(B)} ≤ |B|` — true, but by §O an equality-with-cofactor here;
2. *Collatz-specific independent Archimedean bound on `|B_N|`* — **none found**;
3. *exact identity defining `B_N`* — `B_N = 2^{S_N}m_N`, which is what actually relates the two
   norms.

Only (2) could supply a new direction, and the whole content of (1) and (3) is that
`log₂|B_N|` and `v₂(B_N)` are **a complementary pair joined by an exact identity**. In the source
paper's own A.5 hierarchy that is level (ii), and the paper says explicitly that level (ii) is not
independence. Lean: `natLog_two_pow_mul`.

So "the same integer under two norms" is not two constraints. Knowing the word and either norm
determines the other.

## R. Candidate second constraints (Gate 11)

| candidate | verdict | reason |
|---|---|---|
| positivity of `n₀` | extrinsic but **vacuous under confinement** | §Y |
| positivity of `n_N` (`= m_N ≥ 1`) | same; it *is* the positivity of `n₀`'s image | §Y |
| ordinary height `|B_N|` | **redundant** — exact identity | §Q |
| product formula | redundant — yields exactly `v₂ ≤ log₂|B|` | §O |
| confinement `S_N ≤ ⌊αN⌋` | restricts the domain of words, not the value | §F, §AA |
| Curry window sparsity | restricts the domain of words | §Z |
| fixed-shell restriction | restricts domain; gives the injectivity used in §AB | §AB |
| monotonicity / integrality + sign | contained in positivity | §Y |
| bounds on `C_N` from confinement | intrinsic (`C_N` is a function of `D`) | §F |
| odd-prime support of `B_N` | unconstrained | §W |
| lattice/Minkowski short vector | **circular** | §AA |
| Type-II growth `n_j → ∞` | see §Z | §Z |

## S. Periodic calibration (Gate 12)

Does the known fixed-anchor proof use both an intrinsic and an Archimedean ingredient? **Yes, and
exactly two:**

- intrinsic: `2^{Nσ} ∣ c₀ + χΔ`, with `c₀, Δ` from one period;
- Archimedean: a nonzero integer divisible by `2^{Nσ}` has absolute value `≥ 2^{Nσ}`.

But the Archimedean ingredient is the **universal** one, available for every integer, carrying no
Collatz information. What makes the pair productive is not independence of the two ingredients —
it is that the first ingredient has *bounded height*. Under the §L criterion the pair fails test
(4): the shrinkage is quantitative only because of `H = O(1)`, which is an intrinsic fact about the
word, not a second direction.

**So even the successful sector is not an example of two independent constraints.** It is one
constraint whose height happens to be amortizable.

## T. Aperiodic moving-target complexity (Gate 14)

| what grows | periodic | irregular |
|---|---|---|
| number of terms in `C_N` after simplification | 3 (`c₀`, `3^{Np}`, `2^{Nσ}`) | `N` |
| numerator height `|A|` | `O(1)` | `≈ 3^N` |
| `|Λ|` | `|Δ| = O(1)` | `3^N` |
| recurrence order | 2 | none fixed |
| symbolic complexity | period `p` | `N` |
| target family | one fixed rational `−c₀/Δ` | fully history-dependent |

Classification demanded by the gate: the irregular target family is **fully history-dependent** —
one target per word, `2^{Θ(N)}` of them in a shell.

## U. Aperiodicity as a condition (Gate 15)

**Too weak, as suspected.** "Not eventually periodic" is a negation and supplies no subword-complexity
growth, no discrepancy bound, no irrationality measure, no height separation. §V shows the
strongest possible form of this objection: the *minimal-complexity* aperiodic word already defeats
the height framework.

Conclusion, in the gate's own words: **aperiodicity identifies the hard sector but is not itself
the missing extrinsic constraint.**

## V. Low-complexity aperiodic classes (Gate 16, 33)

The canonical zero-corridor word is the Beatty/Sturmian word `S_j = ⌊αj⌋`, `d_j ∈ {1,2}`, with
subword complexity `p(n) = n+1` — the **minimum possible** for an aperiodic word.

| `N` | `S_N` | `h_N` | `h_N/S_N` | proved floor | actual `log₂χ` |
|---|---|---|---|---|---|
| 8 | 12 | 12.68 | 1.0566 | −0.68 | 11.58 |
| 16 | 25 | 25.36 | 1.0144 | −0.36 | 24.80 |
| 32 | 50 | 50.72 | 1.0144 | −0.72 | 48.32 |
| 64 | 101 | 101.44 | 1.0043 | −0.44 | 100.25 |
| 128 | 202 | 202.88 | 1.0043 | −0.88 | 195.94 |

`ρ_N > 1` and the proved floor is negative at every depth. Meanwhile the **periodic convergent
approximants** built from the continued-fraction convergents of `α` — periods 2, 5, 12, 41, 53 —
all keep `ρ_N ≈ 0.26` with large positive floors.

> **The transition is not about complexity.** The Sturmian word and its convergent approximants
> have the same local structure; what differs is whether the word *closes* into a finite geometric
> sum. Any complexity dichotomy is therefore the wrong knob.

This is the most useful negative in the audit: external height control fails at the very bottom of
the aperiodic hierarchy, so no refinement of the periodic/aperiodic split by complexity can rescue
it.

## W. Odd-prime escape (Gate 21)

By §M, `B_N = 2^{S_N}m_N`, so `rad(B_N) = 2·rad(m_N)` where `m_N` is the terminal accelerated
iterate — an **arbitrary odd positive integer**. Sampled: `m_N = 1`, `103`, `7·13`, `5·503`. Nothing
in zero confinement restricts `rad(B_N)`, the largest odd prime factor, the S-unit support, or the
gcd with 3 (`B_N` is a sum of a multiple of `3^{N−1}`-type terms and `3^Nχ`; no constraint survives).

So the odd-prime factors are exactly the escape route: the full product formula collapses to the
trivial bound because `Π_{p odd}|B|_p` is unconstrained. **Gate 20's question is answered no.**

## X. S-unit / bounded-rank possibility (Gate 22)

Structural answer only, as instructed. After intrinsic closure:

- **periodic** words: `B_N`'s defining relation lies in the bounded-rank group `⟨2,3⟩` — the three-term
  form of §H. Rank 2, fixed.
- **irregular** words: `B_N = 2^{S_N}m_N` with `m_N` an arbitrary odd integer of unconstrained
  radical (§W). So `B_N` leaves every bounded-rank multiplicative group, necessarily.

This is descriptive, not useful: it restates §W. The previous branch's growing-dimension closure
stands and is not reopened.

## Y. Positivity quantitative content (Gate 23)

Positivity says `m_N ≥ 1`, i.e. `B_N ≥ 2^{S_N}`, i.e.

```
χ  ≥  (2^{S_N} − C_N)/3^N.
```

Under zero confinement `S_N ≤ ⌊αN⌋`, and since `2^α = 3` exactly, `2^{S_N} ≤ 3^N`; with `C_N > 0`
the right-hand side is `< 1`. **The bound is weaker than the already-known `χ ≥ 1`: vacuous.**

Verified over 40,001 zero-confined words: the largest value the bound ever takes is **−0.0123** —
it is not merely below 1, it is negative throughout the confined range. Lean:
`positivity_bound_vacuous`.

**And the failure is structural, not incidental.** The same bound is *exponentially strong* for
non-confined (descending) words, where `S_N > αN` gives `χ ≳ 2^{S_N − αN}`. Positivity's
quantitative content is exactly complementary to confinement: it bites precisely where confinement
fails, and is vacuous precisely where Open Problem C lives.

So positivity is genuinely extrinsic (§G) and quantitatively useless here.

## Z. Type-II / Curry external content (Gate 24, 25)

Curry's window sparsity is derived from the dynamics of divergent positive-integer orbits, not from
arbitrary symbolic words, so it is **extrinsic to the word language** in a real sense.

But what it produces is a predicate on `D` — a restriction on which valuation words a divergent
orbit may exhibit. And `χ_N` is a deterministic function of `D` (§F). Therefore Curry can shrink
the *set of words quantified over*; it cannot bound `χ_N` at a given word.

Likewise `n_j → ∞` combined with `2^{S_j}n_j = 3^jn_0 + C_j` (verified, 45,000 steps, 0 mismatches
in the previous branch) is an identity relating intrinsic quantities; the growth statement
constrains the orbit, not the placement.

Conclusion, in the gate's own words: **Curry is extrinsic to the word language but not transverse
to the realizer placement target.**

## AA. Nonredundant-intersection test (Gate 26, 27) — the decisive gate

Degrees of freedom at fixed `(D,N)`:

| after imposing | remaining degrees of freedom for `χ_N` |
|---|---|
| confinement alone | the shell; `χ_N` not yet determined |
| the exact intrinsic realizer condition | **zero — `χ_N` is a single point** |
| any candidate extrinsic condition | still zero |

`χ_N = (−C_N·3^{−N}) mod 2^{S_N}` is a *function* of `D`. So a second constraint cannot act by
shrinking the feasible set: there is nothing left to shrink.

**Stated precisely, without overclaiming.** A second constraint could still be useful by
*excluding words* — by being a predicate on `D` incompatible with `χ_N(D)` being small. Every
candidate in §R is either (a) a deterministic function of `D`, hence unable to exclude anything not
already determined, or (b) a restriction on the word language alone (confinement, Curry), which
restricts the domain but says nothing about the value. No candidate is of the third kind: a
quantitative statement *about the value* `χ_N(D)` generated independently of the identity that
defines it.

**The lattice route, checked and rejected as circular.** The lattice
`L = {(Λ,A) : A + χΛ ≡ 0 mod 2^{S_N}}` has determinant `2^{S_N}`, so Minkowski always supplies a
vector of height `≤ 2^{S_N/2}`, apparently halving `h_N`. But `(1, −χ)` is always in `L` and lies
in the **degenerate branch** `A + χΛ = 0`. So the short vector is generated by `χ` itself, and the
resulting "bound" is "either `χ` is small or `χ` is large". Redundant, exactly as Gate 7 warns.

Measured on the Sturmian word, rational reconstruction does return a non-degenerate relation, of
height `h_N/S_N ≈ 0.39, 0.41, 0.38, 0.49` at `S_N = 25, 50, 101, 152` — the generic lattice value
`≈ 1/2` — but **the reconstructed anchor changes with `N`**, unlike every eventually periodic case
above. So the object it produces is not a word-generated relation; it is a per-word certificate.

This is worth stating precisely because it shows the method's natural strength and its exact
defect. For an individual word, running the reconstruction and *checking* non-degeneracy certifies
`log₂χ_N ≥ S_N/2 − 1` via `floor_of_height_separation` — a floor with `ε ≈ α/2 ≈ 0.79`, far more
than Open Problem C needs. But non-degeneracy at level `2^{S_N/2}` is *equivalent* to
`χ_N ≥ 2^{S_N/2}`, so it is a verification procedure, not a proof, and the uniform statement over
all confined words is again the problem itself.

## AB. Same-intrinsic / different-extrinsic examples (Gate 28)

At **full** resolution the question is empty: within a fixed shell `(N,S_N)` the map `D ↦ χ_N` is
injective (previous branch, verified on seven shells to `N=9`), so equal residues force equal words.

At **coarse** resolution it is not. Pairs with the same `N`, the same `S_N = 16`, and the same
low anchor bits `χ mod 64`, but different ordinary height:

| `χ mod 64` | word | `log₂χ` |
|---|---|---|
| 63 | `(1,1,1,1,1,1,1,3,3,3)` | 12.392 |
| 63 | `(1,1,1,1,1,3,3,3,1,1)` | 15.902 |
| 31 | `(1,1,1,1,2,1,1,2,3,3)` | 14.789 |
| 31 | `(1,1,1,1,3,3,3,1,1,1)` | 14.685 |

So ordinary height is a genuinely different observable *below the resolution at which the problem
is posed*, and becomes determined at full resolution. That is the precise sense in which the
Archimedean direction is independent — and it is the wrong sense, because Open Problem C is a
statement at full resolution.

## AC. Periodic/aperiodic finite-prefix indistinguishability (Gate 29)

The same finite prefix `(1,2,1,1,2)` extends both to a periodic continuation and to an irregular
one; both are realizable. So **periodicity is an infinite-tail property, invisible to any
bounded-depth marker.** Any proposed extrinsic theorem that is checkable at finite depth therefore
cannot distinguish the sectors, which constrains the shape of §AE.

## AD. Closure-forcing theorem audit (Gate 30)

The candidate "if a positive integer realizes an indefinitely zero-confined word then the word is
eventually periodic" is examined and **rejected as a route**:

- It is the ZCRE boundary in different words. The repo already has
  `boundedPrefixRealizers_iff_positiveRealizer`, and the previous branch showed `Z = −n₀` for any
  genuine orbit — so a divergent positive orbit would have a rational (indeed integral) `Z` with a
  presumably aperiodic word. Rationality of `Z` therefore does **not** force eventual periodicity
  of the valuation word (§I), and the candidate is not even implied by what is known.
- Presenting it as a new route would be presenting the existing conjecture under a new name.

## AE. Separation theorem shape (Gate 31)

The weakest genuinely new statement that would advance Open Problem C, stated abstractly so that
it names the missing input rather than disguising it:

> **(H-sep)** There is `ε > 0` such that every zero-confined word `D` of length `N` admits a
> **word-generated** relation `2^{S_N} ∣ A_N + χ·Λ_N` with `max(|A_N|,|Λ_N|) ≤ 2^{S_N − εN}` and
> `A_N + χ_N·Λ_N ≠ 0`.

Then `log₂χ_N ≥ εN − 1`. Lean: `floor_of_height_separation`.

Two honest caveats. First, the non-degeneracy clause is essential and is where the genuine-orbit
and cycle cases hide (§K). Second, (H-sep) is *not* known to be weaker than Open Problem C — the
lattice argument of §AA shows that a relation of height `≈ 2^{S_N/2}` always exists but is
degenerate, so the content of (H-sep) is entirely in producing a **non-degenerate** low-height
relation from the word, which no current technique does.

## AF. `B_N` structural comparison (Gate 34)

| word class | terms after simplification | height `h_N` | `ρ_N = h_N/S_N` | prime support | recurrence order |
|---|---|---|---|---|---|
| periodic (period `p`) | 3 | `≈ pα`, fixed in `N` | `→ 0` as `1/reps` | `⟨2,3⟩` for the relation | 2 |
| eventually periodic | 3 + preperiod | fixed in `N` | `→ 0` | bounded rank | 2 |
| one-defect | 3 + `O(1)` | fixed in `N` | `→ 0` | bounded rank | 2 |
| Sturmian (minimal aperiodic complexity) | `N` | `≈ αN` | **`≥ 1`** | unconstrained | none |
| arbitrary confined irregular | `N` | `≈ αN` | **`≥ 1`** | unconstrained | none |

The arithmetic transition from fixed to growing complexity is exactly the transition from *a word
that closes into a finite geometric sum* to one that does not — and it happens immediately, at the
lowest aperiodic complexity (§V).

## AG. Height-growth question (Gate 35)

Does aperiodicity force height growth? **The question is ill-posed as stated, and the honest answer
is that the implication runs the wrong way.** `h_N ≈ αN` is not caused by aperiodicity; it is the
*default*, holding for every word, and periodicity is what *reduces* it. The Sturmian data (§V)
confirms there is no gradient: minimal aperiodic complexity already sits at the default. So
"lack of repetition ⟹ no compression ⟹ height grows" is not a mechanism to be made quantitative;
it is the absence of the periodic mechanism.

## AH. Intrinsic/extrinsic claim ledger (Gate 36)

| object/constraint | intrinsic or extrinsic | exact reason | factors through | periodic behaviour | aperiodic behaviour | quantitative strength | useful for C? | useful for E? |
|---|---|---|---|---|---|---|---|---|
| confinement | domain restriction | predicate on `D` | `D` | — | — | defines the problem | defines | defines |
| `S_N` | intrinsic | `Σd_i` | `D` | `= σ·reps` | `≤ ⌊αN⌋` | — | no | no |
| `C_N` | intrinsic | carry recursion | `D` | `c₀(3^{Np}−2^{Nσ})/Δ` | `N` terms | — | no | no |
| `Z_N`, `ξ_N` | intrinsic | `−C_N3^{−N}` | `D` | rational | `ℤ₂`-generic | — | no | no |
| `r_N`, `χ_N` | intrinsic | `(−C_N3^{−N}) mod 2^{S_N}` | `D` | fixed anchor | moving | the target itself | is C | is E |
| lift digits | intrinsic | grouped bits of `r_N` | `D` | eventually 0 | — | none | no | no |
| terminal gap `g_N` | intrinsic | `S_N − ⌊log₂ r_N⌋` | `D` | small | large | equals C up to 1 | is C | is E |
| transport `H_N` | intrinsic | `F_N + M_N` | `D` | — | `= ∞` past `log₂n₀` | none on orbits | no | no |
| Curry divergence condition | extrinsic to word language | dynamics of divergent orbits | restricts `D` | — | — | domain only | **no** | no |
| positivity | **extrinsic** | `−Z` terminates | not a function of `D` | — | — | **vacuous under confinement** | no | no |
| ordinary height `|B_N|` | **redundant** | `B_N = 2^{S_N}m_N` | `D`, `χ` | — | — | identity, not constraint | no | no |
| product formula | redundant | gives `v₂ ≤ log₂|B|` | — | — | — | trivial bound only | no | no |
| periodic fixed anchor | intrinsic | `−c₀/Δ` | period | `h = O(1)` | absent | **exponential floor** | yes, in sector | yes, in sector |
| `B_N` divisibility | intrinsic | defines `χ_N` | `D`, `χ` | — | — | the problem | is C | is E |
| candidate external theorem (H-sep) | would be extrinsic | §AE | — | trivially true | **unknown** | would give `ε = 1−ρ` | yes | yes |

## AI. Anti-analogy boundaries (Gate 37) — mandatory

Where the cubic-paper analogy stops:

1. **Collatz state space is discrete and arithmetic.** There is no manifold, no tangent space, and
   no default smooth structure; the implicit function theorem has no role.
2. **No Jacobian is supplied, and none is manufactured here.** §L uses a logical independence
   criterion, not a determinant.
3. **Periodicity is not degeneracy.** The periodic sector is where the *strongest* results hold;
   in the source paper degeneracy marks structural instability. The two have nothing to do with
   each other. Explicitly rejected.
4. **Aperiodicity is not transversality.** §U shows aperiodicity carries no quantitative content
   at all, whereas transversality in the source is an exact determinant condition.
5. **Two norms on one integer are not two constraints.** §Q: they are a complementary pair joined
   by an exact identity — level (ii) of the paper's own hierarchy, not level (iii).
6. **"Intrinsic"/"extrinsic" here are working research terms**, defined operationally in §D–§E,
   and are not asserted as standard Collatz terminology.
7. **Independence would not by itself suffice even if found.** The source's B.5 shows transversality
   can be generic and therefore non-discriminating; criterion (4) of §L (quantitative at the
   required scale) is the binding one.

## AJ. Strongest surviving architecture (Gate 38)

What survives is a *framework*, not a second arrow:

```
intrinsic:  word D  ⟹  2^{S_N} | A_N + χ·Λ_N        (always available)
            dichotomy:  A_N + χ_N Λ_N = 0   or   log₂|χ_N| ≥ S_N − h_N − O(1)
missing:    a word-generated, NON-DEGENERATE relation with h_N ≤ S_N − εN
```

The framework is exact, formalized, and explains every known sector via the single invariant
`ρ_N = h_N/S_N`. The second arrow the brief asks about — an independently generated Archimedean
restriction on `B_N` — **does not exist in current mathematics**, and §Q gives the structural
reason it cannot be obtained from `|B_N|`.

## AK. Weakest genuinely new missing lemma (Gate 40 target)

**(H-sep)** of §AE, formalized as `floor_of_height_separation`. It is the weakest statement I could
find that (i) implies Open Problem C, (ii) is not an immediate restatement of it, and (iii) names
an object — a low-height non-degenerate word-generated relation — that is not by construction
equal to the realizer. Its status is open and it may still be equivalent to Open Problem C; §AE
records that honestly.

## AL. Lean formalization (Gate 40)

`EOC/ConstraintHeight.lean`, 5 theorems, elementary bridges only; no philosophy and no external
number theory formalized.

| theorem | content |
|---|---|
| `natLog_two_pow_mul` | `log₂(2^S·m) = S + log₂ m` — the two-norm identity of §Q |
| `floor_of_height` | `2^m ≤ H·(1+|χ|)` — everything the size argument delivers |
| `floor_of_height_separation` | `H·2^k ≤ 2^m` and non-degeneracy ⟹ `2^k − 1 ≤ |χ|` — **the missing input, named** |
| `height_separation_vacuous_of_confined` | `2^S ≤ H` ⟹ no `k ≥ 1` separates — §J as a theorem |
| `positivity_bound_vacuous` | `2^S ≤ L`, `A > 0` ⟹ `2^S − A < L` — §Y as a theorem |

Built on the previous branch's `EOC.SuperBudget.periodic_floor` and `geom_closed_form`. Following
the convention of preceding rounds the module is not added to the `EOC.lean` aggregator.

## AM. Tests / build

```
lake build EOC.SuperBudgetCancellation  →  2260/2260, success
lake build EOC.ConstraintHeight         →  2261/2261, success
lake env lean EOC/ConstraintHeight.lean →  exit 0, no diagnostics
```

Scripts: `scratch/gate08_BN_identity.py`, `scratch/gate23_34_height.py`,
`scratch/gate27_29_dof.py`, `scratch/gate33_sturmian.py`, `scratch/gate34_defect.py`.

Computational results, all with 0 violations: `B_N = 2^{S_N}m_N` and `v₂(B_N) = S_N` exactly
(10,000 words); `m_N ≡ C_N2^{−S_N} mod 3^N` (10,000); positivity bound `< 1` under confinement
(40,001 confined words, max value −0.0123); periodic closed form and height trend (tabulated in
§H); Sturmian height (§V).

## AN. Axiom audit

All five theorems: `[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`, `axiom`,
`opaque`.

## AO. Files changed

```
EOC/ConstraintHeight.lean                                   (new)
docs/INTRINSIC_EXTRINSIC_CONSTRAINT_INDEPENDENCE_AUDIT.md   (new)
scratch/gate08_BN_identity.py                               (new)
scratch/gate23_34_height.py                                 (new)
scratch/gate27_29_dof.py                                    (new)
scratch/gate33_sturmian.py                                  (new)
scratch/gate34_defect.py                                    (new)
```

## AP. Commits

`9b20c62` — *Close the intrinsic/extrinsic route; the two norms of `B_N` are one identity*, on top
of base `c23b14a`, plus a follow-up commit recording this hash and the push status. `main`
untouched.

## AQ. Push status

Pushed to `origin/intrinsic-extrinsic-constraint-independence-audit`. **No PR opened.**

## AR. Research verdict

**`ALL CURRENT SECOND CONSTRAINTS REMAIN REDUNDANT OR TOO WEAK`**

The audit's methodological hypothesis — that repeated failures come from studying different
coordinates of the same intrinsic constraint — is **confirmed**, and now has a proof rather than a
suspicion behind it: at fixed `(D,N)` the realizer residue is a deterministic function of the word
(§AA), so no constraint can shrink the feasible set, and every candidate examined either factors
through `D` or restricts only which words are admitted.

Why this verdict rather than the neighbours:

- not `ARCHIMEDEAN HEIGHT PROVIDES A NONREDUNDANT SECOND CONSTRAINT` — refuted by
  `B_N = 2^{S_N}m_N` (§M, §Q): the two norms are a complementary pair joined by an exact identity,
  which the source paper's own hierarchy classifies as *not* independence;
- not `POSITIVITY IS EXTRINSIC BUT QUANTITATIVELY TOO WEAK` — true (§G, §Y) but only one row of the
  ledger; the verdict must cover ordinary height, the product formula, Curry and the lattice route
  as well;
- not `CURRY IS EXTRINSIC BUT NOT TRANSVERSE TO REALIZER PLACEMENT` — also true (§Z), same
  objection;
- not `FIXED-ANCHOR VERSUS MOVING-ANCHOR IS THE SHARPER SPLIT` — this *is* supported and is the
  audit's best positive output (§K), but it is a reorganization of the intrinsic side, not an
  answer to the primary question, which asks whether the second arrow exists. It does not;
- not `B_N EXHIBITS A GENUINE INTRINSIC–EXTRINSIC INTERSECTION` — the opposite is what was found.

**Positive content, despite the closure:**

1. `B_N = 2^{S_N}·m_N` exactly, `m_N` the terminal iterate. Hence `v₂(B_N) = S_N` exactly, and
   `log₂|B_N| − v₂(B_N) = log₂ m_N`. **Correction to the previous branch:** there is no trivial
   inequality here to improve by `Ω(N)`; `v₂(B_N)` is exactly determined and the open content is
   the size of a cofactor (§P).
2. The single invariant `ρ_N = h_N/S_N` — the height of the best word-generated relation over the
   divisor exponent — explains every known sector: `→ 0` for periodic, eventually periodic and
   genuine-orbit words, `≥ 1` for confined irregular ones. Periodic closure works by **amortizing a
   fixed height over unboundedly many repetitions**, with `ρ_N ≈ 1/reps`.
3. The mechanism is a **dichotomy**, not a floor: either the relation degenerates (`A + χΛ = 0`,
   pinning `χ` to one bounded rational — the cycle and genuine-orbit cases) or `χ` is exponentially
   large.
4. The split is **not about complexity**. The minimal-complexity aperiodic word (Sturmian,
   `p(n) = n+1`) already has `ρ_N ≥ 1` at every depth, while its periodic convergent approximants
   keep `ρ_N ≈ 0.26`. What matters is whether the word *closes* into a finite geometric sum.
5. Positivity is genuinely extrinsic but its quantitative content is exactly complementary to
   confinement: exponentially strong where confinement fails, negative-valued where it holds.
6. The missing input is named and formalized: **(H-sep)**, a word-generated non-degenerate relation
   of height `≤ 2^{S_N−εN}`. Whether it is strictly weaker than Open Problem C is open.
