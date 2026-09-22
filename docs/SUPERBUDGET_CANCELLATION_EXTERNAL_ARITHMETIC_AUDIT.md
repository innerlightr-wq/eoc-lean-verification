# Super-budget 2-adic cancellation / external arithmetic audit

## A. Starting state

| item | value |
|---|---|
| base commit | `d5d12c20a08fcba6692bd4dc2ccd5d09a9caf951` (`Bridge realizer depth to the transport budget; refute the o(H) envelope`) |
| verified how | `git fetch origin`, then `git rev-parse origin/transport-regeneration-realizer-bridge-audit` — not from prose |
| ordinary checkout | **dirty** (53 entries: modified `EOC.lean`, `docs/LITERATURE_CONTEXT.md`, `docs/RESEARCH_STATUS.md`, plus 50 untracked `EOC/*.lean`). Not touched. |
| worktree | isolated, `scratchpad/eoc-sb`, `.lake/packages` symlinked |
| branch | `superbudget-cancellation-external-arithmetic-audit` |
| `main` | untouched. No PR. |

## B. Current proved frontier

Inherited from `docs/TRANSPORT_REGENERATION_REALIZER_BRIDGE_AUDIT.md` and
`EOC/TransportRegeneration.lean`:

```
E_j ≤ F_j            (unconditional; monotonicity of log₂, no β-split)
E_j ≤ g_j < E_j + 1  (g_j = discreteGap(S_j, r_j) = S_j − ⌊log₂ r_j⌋)
g_j < H_j + 1        (H_j = F_j + M_j, using M_j ≥ 0)
H_N = H_1 + Σ_{failures} G_j,   G_j = v₂(a_j − u_j) − δ_fail,j  at genuine first failures
M_N = M_1 − (S_N − S_1) + Σ w   ⟹   Σ w ≥ S_N − M_1   (regeneration is forced, linear)
```

and the Gate 10 result: a pointwise envelope `G_max(H) = o(H)` is insufficient, so the target is
the cumulative positive excess `R₊(N) = Σ_{failures j ≤ N} max(G_j, 0)`.

The brief's standing instruction is honoured throughout: **gross** regeneration is provably
linear and must not be attacked; only the **positive excess** is in play.

## C. Source inventory

| artifact | hash / location |
|---|---|
| transport note, `~/Downloads/transportDeficits (1).pdf` (and `(1)`,`(2)` copies) | `c78539dad90722dd2ea7e72b1c07d897eb603b8d77f2e62791ab4dca6d563881`, byte-identical |
| extracted text `TD.txt`, 1333 lines | `1252c14e7cd5d96b2f400f6af6c2050267a8bfde64afb0148636281dfd688447` |
| `~/Downloads/confinementAbundanceArithmeticPlacement (4).pdf` | present, consulted for notation only |
| `~/Downloads/halfcylinderv2.pdf`, `peeling_theorem_ledger.md` | present, not re-audited |
| repo | `EOC/TransportRegeneration.lean`, `EOC/TerminalZeroGap.lean`, `EOC/Carry.lean` |

Literature verified from primary sources; see §J, §K, §L, §AC.

## D. Exact failure algebra (Gate 0)

From the note, §4–§5 and Appendix D, with the paper's own hypotheses:

```
ξ_j = −C_j·3^{−j} ∈ ℤ₂,      ξ_j = χ_j + 2^{S_j}T_j,      χ_j = ξ_j mod 2^{S_j}
K_j(d) = (T_j − 3^{−(j+1)}) mod 2^d ∈ {0,…,2^d−1}
A_{j,m} = Σ_{r<m} 2^{D_r}3^{−(j+1+r)},   D_r = S_{j+r} − S_j,   A_{j,∞} = lim A_{j,m}   (Prop. 14)
X_j := T_j − A_{j,∞},        M_j := v₂(X_j)
F_j = S_j − log₂ χ_j,        H_j = F_j + M_j
δ_{j+1} = log₂(1 + 2^{F_j}K_j(d_{j+1}))                                        (Def. 10 + Prop. 8)
```

A step is **perfect** iff `K_j(d_{j+1}) = 0`. At a **genuine first failure** — a failure
immediately following a perfect segment — Proposition 20 gives `v₂(K_j) = M_j`, which is the
hypothesis licensing the factorization

```
X_j = 2^{M_j}a_j ,      K_j(d_{j+1}) = 2^{M_j}u_j ,      a_j, u_j odd.
```

Proposition 29 (exact, no hypothesis): `X_{j+1} = (X_j − K_j)/2^{d_{j+1}}`. Proposition 30:
`M_{j+1} = M_j − d_{j+1} + v₂(a_j − u_j)`. Proposition 33: `G_j = ΔH_j = v₂(a_j−u_j) − δ_fail,j`.

**Hypothesis audit.** Corollary 34 (`δ_fail > F_j`) is universal — it needs only `v₂(K_j) ≥ 0`
and `u ≥ 1`. Equation (58) (`δ_fail > H_j`) and Propositions 30/33 need the genuine-first-failure
hypothesis. Every count in this report restricts to genuine first failures (`v₂(K_j) = M_j`).

## E. Explicit formulas for `a` and `u` (Gate 1)

This is the decisive gate, and it resolves completely.

From Proposition 29, `X_j − K_j = 2^{d_{j+1}}X_{j+1}`, so

```
a_j − u_j = (X_j − K_j)/2^{M_j} = 2^{d_{j+1} − M_j}·X_{j+1},
```

giving the **exact forced/excess split**

```
v₂(a_j − u_j)  =  (d_{j+1} − M_j)  +  M_{j+1}.
   ‾‾‾‾‾‾‾‾‾‾      ‾‾‾‾‾‾‾‾‾‾‾‾‾‾     ‾‾‾‾‾‾‾
   total            forced             excess
```

(Verified: 478,613 genuine first failures over 100,000 odd seeds, **0 mismatches**.) The forced
term is exactly the note's inequality (47); the excess is exactly Definition 31's `R_j`, and the
note already records `M_{j+1} = R_j`.

**Now the closed form.** Put `Z := Σ_{i≥0}2^{S_i}3^{−(i+1)} ∈ ℤ₂`, the series over the whole
infinite word. Then, since `3^{−j}C_j = Σ_{i<j}2^{S_i}3^{−(i+1)}`,

```
A_{j,∞} = 2^{−S_j}(Z − 3^{−j}C_j),     T_j = 2^{−S_j}(−3^{−j}C_j − χ_j),
X_j = T_j − A_{j,∞} = −(χ_j + Z)/2^{S_j}.
```

Every power of 3 cancels identically. Along a **genuine positive-integer orbit with seed `n₀`**,
the realizer congruence `n₀ ≡ χ_N (mod 2^{S_N})` holds for all `N` and `S_N → ∞`, hence

> **`Z = −n₀` exactly, as 2-adic integers.**

Therefore

```
χ_j = n₀ mod 2^{S_j},        X_j = ⌊n₀ / 2^{S_j}⌋,        M_j = v₂(⌊n₀ / 2^{S_j}⌋).
```

**`M_j` is the length of the run of zero bits of the seed `n₀` beginning at bit position `S_j`.**

Verified: `Z = −n₀` on 2,000 seeds (0 mismatches); `χ_j = n₀ mod 2^{S_j}` and
`X_j = ⌊n₀/2^{S_j}⌋` on 88,000 steps (0 mismatches).

**Classification demanded by Gate 1.** Not A, B, C, D or E as posed. The object is none of
"difference of exponentials", "fixed-length linear form", "variable-length sparse sum" or
"odd part of such a sum": it is a **single integer division of the seed by a power of two**. The
apparent exponential-sum complexity of `a_j − u_j` is entirely an artifact of the coordinates;
it cancels.

## F. Primitive excess-cancellation object (Gates 18, 19, 20)

Factoring out the forced divisibility `2^{d_{j+1}−M_j}` leaves

```
B_j^primitive  =  X_{j+1}  =  ⌊n₀ / 2^{S_{j+1}}⌋ ,      excess = v₂(B_j^primitive) = M_{j+1}.
```

Gate 20 asks whether the primitive remainder simplifies or still carries an `O(N)`-term
history-dependent sum. **It simplifies completely**: one integer, coefficient height `n₀`,
one power of two, *no powers of 3 at all*, no dependence on the future word beyond `S_{j+1}`.

Gate 18's excess coordinate `Q_j = v₂(a_j−u_j) − H_j` is then
`Q_j = d_{j+1} − M_j + M_{j+1} − F_j − M_j`, and since `G_j = v₂(a_j−u_j) − δ_fail,j` with
`δ_fail,j = log₂(1+2^{H_j}u_j) > H_j`, we have `G_j < Q_j` as the brief anticipated. But the
useful coordinate turns out to be neither: it is simply `M_{j+1}`.

## G. Cleared-denominator integer form (Gates 3, 4)

**Genuine-orbit form.** Proposition 35's criterion `v₂(a−u) ≥ q ⟺ A_{j,∞} ≡ T_j − K_j
(mod 2^{M_j+q})` becomes, after clearing the `3^{-1}`s (which cancel identically),

```
q-bit regeneration   ⟺   2^{q − d_{j+1} + M_j}  divides  ⌊n₀ / 2^{S_{j+1}}⌋.
```

Terms: **one**. Coefficient height: `n₀`. Exponents of 2: `S_{j+1}`. Exponents of 3: **none**.
Dependence on `j`, `m`: only through `S_{j+1}`. The adaptive future length that Proposition 35
warns about disappears, because the infinite target is determined by the same seed.

**Word form** — this is where Open Problem C actually lives. For a finite word `D` of length `N`,
`χ_N = (−C_N 3^{−N}) mod 2^{S_N}`, so for an integer `1 ≤ χ < 2^{S_N}`,

```
χ_N = χ   ⟺   2^{S_N}  divides  B(D,χ) := C_N + 3^N·χ = Σ_{i<N} 3^{N−1−i}2^{S_i} + 3^N χ.
```

Terms: **`N+1`, growing**. Coefficient heights: up to `3^N`. Exponents of 2: `S_0<…<S_{N−1}`
and the divisor exponent `S_N`. Exponents of 3: `0,…,N`. `C_N` is odd (the `i=0` term `3^{N−1}`
is odd, all others even; verified on 400 random words).

## H. Complexity growth (Gate 2 — the mandatory early-stop test)

| setting | terms in the primitive object | dimension grows with `N`? |
|---|---|---|
| genuine positive orbit | **1** (`⌊n₀/2^{S_{j+1}}⌋`) | no |
| purely periodic word, period `p` | **3** (§S) | no — `p` only |
| eventually periodic word | `O(p + preperiod)` | no |
| irregular confined word | **`N+1`** | **yes, linearly** |

The early-stop test fires for exactly one case — irregular words — and that is the only case
Open Problem C is about. Every fixed-dimension theorem family is therefore confined to the
sectors the repository already controls.

## I. Required asymptotic scale (Gates 7, 8)

For the word form, with `S_N = s·N` and `χ < 2^{εN}`: under confinement `S_i ≤ αi`, every term of
`C_N` satisfies `log₂(3^{N−1−i}2^{S_i}) ≤ α(N−1)`, so `log₂ C_N ≤ α N + log₂ N`, while
`log₂(3^Nχ) = (α+ε)N`. Hence

```
log₂|B(D,χ)| = (α + ε)N + O(log N),     required valuation  v₂(B) ≥ S_N = sN.
```

Measured (N=40, ε=0.05):

| shell `s = S_N/N` | `log₂|B|/N` | needed `v₂/log₂|B|` | improvement needed over trivial |
|---|---|---|---|
| 1.000 | 1.6430 | 0.6086 | `0.643·N` |
| 1.250 | 1.6480 | 0.7585 | `0.398·N` |
| 1.500 | 1.6671 | 0.8998 | `0.167·N` |
| 1.575 | 1.6795 | 0.9378 | `0.105·N` |
| `→ α` | `→ α+ε` | `→ 1/(1+ε/α)` | **`→ ε·N`** |

So the binding case is the heavy shell `s → α`, where the required improvement over the trivial
bound is only `εN` — and the trivial bound is precisely what the product formula gives (§Y).
**Open Problem C is exactly the statement that the trivial 2-adic valuation bound for an
`(N+1)`-term `{2,3}`-sum can be improved by a positive linear amount.** A candidate theorem is
useful only if it beats `log₂|B|` by `Ω(N)`; an `O(N)` bound with a constant `≥ α` is worthless,
an `O(log N)` bound would be overwhelming.

## J. p-adic linear forms in logarithms (Gate 6)

**Sources, verified.** The series is K. Yu, *p-adic logarithmic forms and group varieties* I
(J. reine angew. Math. **502** (1998) 29–92), II (Acta Arith. **89** (1999) 337–378), III
(Forum Math. **19** (2007) 187–280); sharpened in K. Yu, *p-adic logarithmic forms and a problem
of Erdős*, Acta Math. **211** (2013) 315–382 (DOI 10.1007/s11511-013-0106-x), Main Theorem eq.
(1.18) and Theorem 1 eq. (1.24). *(Correction to this audit's own working premise: none of these
is in Trans. AMS.)* The form applications quote is the "consequence of the Main Theorem, p. 190"
of Yu 2007, reproduced verbatim in Scoones, Mathematika **69** (2023), Lemma 3; Cai, Commun. Math.
**30** (2022), Theorem 3.3; Bérczes–Bugeaud–Győry–Mello–Ostafe–Sha, arXiv:2310.09704, Prop. 3.12;
and normalized over `ℚ` in Bugeaud–Kaneko, Math. Proc. Cambridge Philos. Soc. **165** (2018)
533–540, Theorem 2.1:

```
ord_𝔭(α₁^{b₁}···α_n^{b_n} − 1)
    < (16ed)^{2(n+1)} · n^{5/2} · log(2nd) · log(2d) · e_𝔭^n · p^{f_𝔭}/(f_𝔭 log p)²
      · h′(α₁)···h′(α_n) · log B
```

with `B = max{|b_i|, 3}`, `h′(α) = max{h(α), 1/(16e²d²)}`, under the hypothesis
`ord_𝔭(α_j) = 0`. Fully **effective**; all constants explicit.

| property | value |
|---|---|
| object bounded | `Ξ − 1` where `Ξ` is a **product** of powers — a binomial, never a sum of ≥3 terms |
| dependence on `B` | `log B`, single power |
| dependence on heights | product `h′(α₁)···h′(α_n)`, degree 1 in each |
| dependence on `p` | `≈ p^{f_𝔭}/(f_𝔭 log p)²`, essentially linear in `N(𝔭)` |
| dependence on `n` | `(16ed)^{2(n+1)}` — a factor `(16e)² ≈ 1892` per extra logarithm at `d=1`; Yu 2013's raw constant carries `n^n(n+1)^{n+1}/n!`, i.e. up to `n^{n(1+o(1))}` |
| `n` fixed? | not formally, but the constant is never polynomial in `n` |

**Three independent reasons this family is inapplicable here, in increasing order of finality.**

1. **Wrong object.** The theorem bounds a *product minus one*. `n` counts bases in a single
   monomial, not additive terms. `B(D,χ) = Σ_{i<N}3^{N−1−i}2^{S_i} + 3^Nχ` is an `(N+1)`-term
   **sum**. Two-term S-unit sums do reduce (`3^a2^b + 3^c2^e = 3^{min}2^{min}(1 + 3^{a−c}2^{b−e})`);
   three or more admit no such factorization and there is no effective substitute. Confirmed
   explicitly against the primary statements.

2. **Growing `n` is fatal even if the object were right.** With `n ≈ N` the constant alone is
   `> 1892^N`, dwarfing the `≈ 2^{αN}` size of `B`. The documented maximum growth of `n` in this
   theory is Stewart's device as used by Yu 2013 §1, where `n ≈ log p/log log p` — *logarithmic*
   in the parameter, and only because a compensating `p`-gain outruns the `c^n` loss. Linear
   growth is off the table by orders of magnitude. This is Gate 2's early stop, confirmed from
   the source rather than assumed.

3. **`p = 2` makes it vacuous anyway.** The hypothesis `ord_𝔭(α_j) = 0` fails for `α = 2` at
   `p = 2`, and the quantity is trivially zero regardless: `2^a3^b − 1` and `3^b − 2^a` are odd
   for `a ≥ 1`. The only genuinely 2-adic instance is `ord₂(3^b − 1)`, where
   lifting-the-exponent gives the **exact** answer (`1` if `b` odd, `2 + ord₂(b)` if `b` even) and
   Baker theory is many orders of magnitude weaker than the elementary truth.

For calibration, where the theorem does bite (`n = 2`, `α = 2,3`, `p ∤ 6`, `d = 1`) the explicit
bound is `ord_p(2^a3^b − 1) < 5.4×10^{10}·log B` for `p = 5`. The **shape** `O(log B)` would be
overwhelming for our purposes (§I needs only an `Ω(N)` improvement) — but the shape is
unreachable, for reasons 1–3.

## K. S-unit equations (Gate 9)

**Source, verified.** J.-H. Evertse, H. P. Schlickewei, W. M. Schmidt, *Linear equations in
variables which lie in a multiplicative group*, Ann. of Math. (2) **155** (2002) 807–836,
**Theorem 1.1**: for `Γ ≤ (K*)^n` of finite rank `r`, the number of **non-degenerate** solutions of
`a₁x₁ + … + a_nx_n = 1` with `x ∈ Γ` is at most

```
A(n,r) = exp( (6n)^{3n} · (r+1) ).
```

*(Flag carried forward from verification: the author preprint and arXiv:math/0409604 both give
exponent `3n`; Evertse's 2019 lecture notes state `4n`. The published Annals PDF was not
reachable. Also: this audit's own working memory of "`2^{35n³}·r^{n²}`" was a conflation of
Evertse, Invent. Math. **122** (1995) 559–601 (`2^{35n⁴s}`) with Schlickewei–Schmidt
(`(2d)^{41n³r}·r^{n²r}`); corrected.)*

**Three findings, and the third is fatal.**

1. **It counts, it does not size.** Theorem 1.1 bounds the *number* of non-degenerate solutions.
   It gives no bound on heights, sizes, or valuations. For `n ≥ 3` the proofs are **ineffective**:
   Evertse's lecture notes, after Theorem 8.13, state that for more than two unknowns "no such
   effective proof is known". Effective height bounds exist only for `n = 2` (Baker's method;
   Győry–Yu, Acta Arith. **123** (2006) 9–41).

2. **`B(D,χ)` is not an equation.** `v₂(B) ≥ S_N` does not make `B` an S-unit. The family becomes
   formally applicable only if one *imposes* `B = 2^k` — which is the Collatz **cycle** condition,
   not the realizer condition. Even then, with `n = N+1` and `Γ = ⟨2,3⟩^n` of rank `2n`, the bound
   is `exp((6(N+1))^{3(N+1)}(2N+3))` non-degenerate solutions *for each fixed `N`*: a count, not a
   size, astronomically large, and not uniform in `N`.

3. **Non-uniformity in `n` is provable, not an artifact.** ESS record the lower bounds
   `Ã(n,0) ≥ n!` (for `n = p−1`, from `−ζ−ζ²−…−ζ^{p−1} = 1`) and `Ã(n,1) ≥ c·n²`
   (Bavencoffe–Bézivin, Monatsh. Math. **120** (1995) 189–203). **So no bound depending only on
   `r` can exist, and no theorem in this family can be uniform in the number of variables.** With
   `n ≈ N` there is nothing to extract.

One incidental positive: all terms of `B(D,χ)` are **positive**, so no subsum vanishes and
non-degeneracy is automatic. That removes a standard escape clause without helping.

## L. Subspace-theorem route (Gate 10 of this brief)

**Source, verified.** J.-H. Evertse, H. P. Schlickewei, *A quantitative version of the absolute
Subspace Theorem*, J. reine angew. Math. **548** (2002) 21–127. **Theorem 3.1**: for `E` a number
field, `S ⊆ M(E)` with `|S| = s`, `n` independent forms per place of degree `≤ D` and height `≤ H`,
and `0 < δ < 1`, the `x ∈ Q̄^n` with `H(x) > max{n^{4n/δ}, H}` satisfying the product inequality
lie in `t₂` proper subspaces defined over `E`, where

```
t₂ ≤ (3n)^{2ns} · 2^{3(n+9)²} · δ^{−ns−n−4} · log(4D) · log log(4D).
```

(Theorem 1.1 gives `t ≤ 4^{(n+9)²}δ^{−n−4}` for the special forms; Theorem 2.1 the parametric
version.) **Ineffective**: Evertse's notes, after Theorem 7.1 and again after Theorem 8.7, state
plainly that the proofs "do not provide a method to determine the subspaces".

**This is the one family with a genuine formal fit — and it is worth stating exactly, because it
is the audit's only LEVEL-1 result.** Take `S = {2,3}`, `n = N+1`,
`y_i = 3^{N−1−i}2^{S_i}` and `y_N = 3^Nχ`, so `B(D,χ) = Σ y_i`, and divide out the gcd. Apply the
general-position `p`-adic Subspace Theorem (Schlickewei 1976; Theorem 8.8 of the notes) with forms
`X₁,…,X_n` at `∞` and at `3`, and `X₁,…,X_n, X₁+…+X_n` at `2`. The left side collapses to exactly
`|B|₂ = 2^{−v₂(B)}` and the exponent on `‖y‖` is `−ε`, giving

```
v₂(B)  <  ε·log₂‖y‖ + O_ε(1)        outside finitely many proper subspaces.
```

**That is precisely the ε-saving over the trivial bound that §I identifies as the requirement.**
The mechanism is the one behind Evertse, *On sums of S-units and linear recurrences*, Compositio
Math. **53** (1984) 225–244, Theorem 2. *(Flag: the numdam OCR of that 1984 paper lost its
displayed formulas; existence, numbering and shape verified, exact inequality not.)*

**Why it nevertheless gives nothing — six reasons, all from the verified statements.**

1. `n = N+1` is a *parameter of the theorem*, not a constant. The subspace count, the height
   threshold and the implied constant all depend on `n`; each `N` invokes a different theorem with
   a rapidly worsening constant, and no statement in this literature is uniform in `n`.
2. The constant is **ineffective**. The descent from "solutions lie in `≤ t` subspaces" to
   "finitely many solutions" recurses into subspaces whose equations are unknown, to depth `≈ n`.
3. The subspaces are **undetermined**, and there are `≈ 4^{(n+9)²}δ^{−n−4}` of them at `n ≈ N`.
   Using the ε-saving would require proving that the family of exponent sequences
   `(S_0,…,S_{N−1})` avoids all of them.
4. **The effective half points the wrong way.** What is explicit is the *threshold*
   `max{n^{4n/δ}, H}` below which solutions are not covered at all. At `n ≈ N` that is
   `≈ N^{4N/δ}` — it swallows the entire regime of interest.
5. **Non-uniformity is provable** (ESS lower bounds, §K3): there is no hidden uniform theorem.
6. **The place-set grows too.** The clean derivation needs `χ` to be an `S`-unit for fixed `S`.
   Open Problem C quantifies over *every* integer `χ < 2^{εN}`, so `S` must absorb the prime
   divisors of `χ` and `s` grows with the family — and `t₂` carries `(3n)^{2ns}·δ^{−ns}`,
   exponential in `n·s`.

So the Subspace route reaches LEVEL 1 (formal applicability, correct shape) and stops there.

## M. p-adic rational approximation (Gate 11)

Ridout/Roth-type `p`-adic approximation bounds how well a **fixed** algebraic number can be
approximated. Here the object approximated is `−Z = lim_N χ_N`, and:

- for a **genuine orbit**, `−Z = n₀` is a fixed *rational integer*, and approximation theorems say
  nothing non-trivial about rational targets;
- for an **arbitrary word with a free continuation**, `−Z` is an arbitrary element of `ℤ₂` chosen
  by the future word — a completely unrestricted moving target.

Neither case is a fixed-algebraic-target problem. This is the obstruction Gate 11 anticipated, and
it is fatal to the whole family. See §R for the exact classification.

## N. Powers-of-3 digit-block results (Gate 12)

Not applicable, for a reason stronger than expected: **in the primitive object the powers of 3
cancel identically** (§E). On the word side they survive only as the unit `3^{−N}` multiplying a
history-dependent odd residue (§O), not as a fixed rational whose expansion could be studied.
Results on binary digits of `3^k`, or on `(3/2)^k` mod 1, have no point of contact: there is no
fixed rational expansion here, only a moving linear combination selected by the valuation word.

## O. Multiplicative order / LTE (Gates 13, 14)

**Multiplicative order — decisive and cheap, as the gate predicted.** The regeneration condition
reads `χ_N ≡ (−C_N)·3^{−N} (mod 2^{S_N})`. The order of `3` modulo `2^m` is `2^{m−2}` for `m ≥ 3`,
i.e. `3` generates an index-2 subgroup of `(ℤ/2^m)^×`. But the target `−C_N` is an **arbitrary
history-dependent odd residue** determined by the word, not a constrained constant. Knowing the
order of `3` therefore constrains `q` not at all. Rejected.

**LTE.** Lifting-the-exponent applies to `x^n ± y^n`. `C_N` is an `N`-term sum, not a difference
of powers, so LTE cannot see it. In the *periodic* case `C_{Np}·Δ = c₀(3^{Np} − 2^{Nσ})` is a
difference of powers — but `3^{Np}` is odd and `2^{Nσ}` even, so `v₂` of the difference is `0` and
LTE yields nothing. The periodic sector is resolved by a **size** argument instead (§S), not a
valuation identity.

## P. Recurrence-sequence route (Gate 15)

`C_{j+1} = 3C_j + 2^{S_j}` is a first-order recurrence with **word-dependent forcing**. It is not
a fixed-order linear recurrence with constant coefficients unless the word is periodic, in which
case it becomes order 2 with characteristic roots `3^p` and `2^σ`. Describing the carry recursion
itself as "a fixed recurrence" would be exactly the error the gate warns against: the sequence
whose valuation must be bounded is `B(D,χ)`, whose coefficients change with the word. Rejected for
irregular words; for periodic words it reduces to §S, which needs no recurrence theory.

## Q. Forced versus excess precision (Gate 19 — the key normalization)

Summarizing §E–§F, and this is the audit's central normalization:

```
v₂(a_j − u_j)  =  (d_{j+1} − M_j)  +  M_{j+1},
```

forced part `d_{j+1} − M_j`, excess `M_{j+1} = v₂(⌊n₀/2^{S_{j+1}}⌋)`.

Feeding an external theorem the *total* `v₂(a_j−u_j)` would be feeding it a quantity that is
mostly tautologically forced by 2-adic integrality of the recurrence. After normalization the
remaining object is a zero-run length in the binary expansion of the seed. Lean:
`EOC/SuperBudgetCancellation.lean`, `excess`.

## R. Moving-target obstruction (Gate 22)

Classification, as demanded:

| regime | target `A_{j,∞}` / `−Z` | class |
|---|---|---|
| genuine positive orbit | `= n₀`, the seed itself | **fixed — and equal to the source, so vacuous** |
| purely periodic word | `−c₀/Δ`, one fixed rational | **fixed, one target** |
| eventually periodic word | fixed rational after the preperiod | **finite family** |
| irregular confined word, free continuation | any element of `ℤ₂` | **unrestricted moving target** |

**Gate 21 (past/future self-consistency) is fully discharged.** The primitive condition is written
entirely in terms of a *single* seed: `M_j = v₂(⌊n₀/2^{S_j}⌋)`. Nothing in it treats the future as
freely chosen — past and future are literally the same integer, which is the strongest possible
form of self-consistency, and it is exactly what collapses the problem. (For reference the classic
relation `2^{S_j}n_j = 3^j n₀ + C_j` recovers the current iterate, but `X_j` is a statement about
`n₀`, not about `n_j`.)

The paper's §D.8 construction (choose a tail state agreeing with a prescribed future to arbitrary
precision) is exactly the exploitation of the last row; Remark 36 correctly says it does not settle
the genuine-orbit question. This audit settles the genuine-orbit question (§V) and finds that the
unrestricted row is the only one left — which is the row no fixed-target theorem can touch.

## S. Periodic-sector calibration (Gate 23)

For a purely periodic word of period `p`, block `(e_1,…,e_p)`, `σ = Σe_t`, partial sums `s_t`, set

```
c₀ := Σ_{t<p} 3^{p−1−t}2^{s_t}        (fixed),        Δ := 3^p − 2^σ   (fixed, odd).
```

Then `C_{Np}·Δ = c₀·(3^{Np} − 2^{Nσ})` — **exact, verified 48/48** — and since `3` and `Δ` are
units mod `2^{Nσ}`, the realizer condition collapses to

```
2^{Nσ}  divides  c₀ + χ·Δ,          with c₀, Δ independent of N.
```

Two branches, and no Diophantine machinery is needed for either:

1. `c₀ + χΔ = 0`: `χ = −c₀/Δ`, a single fixed rational. This is the **cycle** case. Checked:
   block `(2)` gives `c₀=1, Δ=−1, χ=1` — the trivial `1`-cycle. Block `(1)` gives `c₀=1, Δ=1`,
   so `χ ≡ −1`, i.e. `χ = 2^{S_N}−1` — the negative witness `−1`.
2. `c₀ + χΔ ≠ 0`: then `2^{Nσ} ≤ |c₀| + |χ||Δ|`, so `χ` is exponentially large in `S_N = Nσ`.
   Measured `log₂χ/S_N ∈ {0.904, 0.932, 0.972, 0.979, 1.000}` on the tested blocks.

Lean: `geom_closed_form`, `periodic_floor`.

**Answer to the gate.** External theory does *not* need to recover the periodic sector — the
sector is elementary, and the reason is the three-term collapse, not any deep input. So the
periodic case provides **no evidence** that heavier machinery would help elsewhere; it provides
the opposite, by showing that what makes it work is precisely the property irregular words lack.

## T. Irregularity complexity cost (Gate 24)

The complexity parameter replacing the fixed periodic anchor is the number of distinct terms
needed for `C_N` in closed form: `O(p)` for period `p`, and **`N`** for an irregular word. Height
of coefficients grows as `3^N`. Number of "logarithms" in any linear-form rendering grows as `N`.
S-unit equation dimension grows as `N`. Every one of these grows linearly, which is exactly the
regime in which the constants of §J–§L become unusable.

## U. One-event bounds (Gate 16, 17)

**Genuine orbit.** The best one-event bound is exact and elementary:
`M_{j+1} = v₂(⌊n₀/2^{S_{j+1}}⌋) ≤ ⌊log₂ n₀⌋ + 1 − S_{j+1}`. Since `G_j < Q_j` and
`δ_fail,j > H_j`, a one-event bound feeds through as `G_j⁺ ≤ max(v₂(a_j−u_j) − δ_fail,j, 0)`.

**Word side.** No one-event bound better than the product-formula bound `v₂(B) ≤ log₂|B|` was
found; see §Y for why that bound is exactly the trivial one.

## V. Cumulative-regeneration implication (Gates 25, 26, 27 — the main positive result)

At a failure, `M_{j+1} < d_{j+2}`, so the excess run `[S_{j+1}, S_{j+1}+M_{j+1})` ends **strictly
before** `S_{j+2}`. The runs at distinct failures are therefore **disjoint bit intervals**, all
inside `[0, ⌊log₂ n₀⌋]` because `X_j = ⌊n₀/2^{S_j}⌋ = 0` as soon as `2^{S_j} > n₀`. Telescoping:

> **Theorem.** Along any genuine positive-integer accelerated Collatz orbit with seed `n₀`,
> the number of transport failures is at most `log₂ n₀`, and the total excess regeneration
> satisfies `Σ_{failures} M_{j+1} ≤ ⌊log₂ n₀⌋ + 1`.

Lean: `sum_excess_le_span`, `sum_excess_le`, `div_eq_zero_of_log_lt`. Verified on 100,000 odd
seeds / 478,613 failure events: disjointness violations **0**, sum-bound violations **0**,
failure-count violations **0**, worst observed `(Σ excess)/log₂ n₀ = 0.765`.

This answers the brief's primary question outright — and with no external arithmetic at all.
It also realizes the favourable outcome Gate 27 hoped for ("the same bits cannot finance two
events"): they literally cannot, because they are the same finitely many bits of `n₀`.

**Consistency check against the note's own data.** §D.9 reports 380,078 failure events over
40,000 genuine trajectories — about **9.5 failures per trajectory**, which is what `≤ log₂ n₀`
predicts for seeds in the range such a scan would use. The note's own statistics corroborate the
bound without having identified it.

**But it does not advance Open Problem C**, for the reason §W makes precise.

## W. Failure-frequency interaction (Gate 26) and why §V does not transfer

The brief's framing — "repeated high-order 2-adic cancellation along ONE genuine positive-integer
Collatz orbit" — rests on a premise that is false. Along one genuine orbit there are at most
`log₂ n₀` failures, all confined to the initial segment `S_j ≤ log₂ n₀`, i.e. `j ≲ log₂(n₀)/α`;
after that `M_j = ∞`, transport is perfect forever, `H_j = ∞`, and the bridge `g_j < H_j + 1`
becomes vacuous. Measured last-failure indices: `n₀ = 7 → j=2`, `27 → 3`, `871 → 8`,
`77031 → 12`, `837799 → 15`.

So `R₊(N)` along a genuine orbit is not merely sublinear — it is **bounded by a constant depending
on the seed**, and it stops growing entirely. This is consistent with the previous round's forced
lower bound `Σw ≥ S_N − M_1`: once `M = ∞` that inequality is vacuous, and before then `S_j`
is bounded by `log₂ n₀`.

The transport paper's §D.9 statistics and the previous round's are therefore all measurements of
**initial segments**, and its Open Problem 37 ("can regeneration persist at arbitrarily large
transport budget") is implicitly a question about a *family of seeds* `n₀ → ∞`, not about one
orbit. Open Problem C lives on **arbitrary confined words with free continuations**, where there
is no seed whose bits run out, and where §D.8 already proves regeneration is unbounded.

**This holds for divergent orbits too, which is the sharp form of the obstruction.** The argument
uses only that `n₀` is a positive integer and `S_j → ∞`; it never uses that the orbit reaches `1`.
So even a hypothetical divergent positive-integer orbit has at most `log₂ n₀` failures and
`M_j = ∞` thereafter. **The transport coordinates therefore cannot detect divergence along a
genuine orbit at all** — they degenerate after `O(log n₀)` steps regardless of what the orbit
does. Any divergence argument built on them must live on the word side.

## X. Repeated-congruence interaction (Gate 27, 28)

**Gate 28 guard, respected.** All moduli here are powers of 2, so there is no CRT independence and
no multiplicative rarity may be claimed from stacking high-precision 2-adic congruences; nested
powers of 2 are perfectly compatible. The genuine-orbit result of §V does **not** use independence:
it uses **disjointness of bit intervals inside a finite expansion**, which is a counting fact, not
a probabilistic one. That is the correct substitute for the unavailable CRT argument, and it is
why the argument works for genuine orbits and fails for words: a free 2-adic continuation has no
finite expansion to exhaust.

## Y. Product-formula / height audit (Gate 29)

For `B ∈ ℤ`, the product formula over `ℚ` gives `|B|_2·|B|_∞·Π_{p odd}|B|_p = 1` with
`|B|_p ≤ 1`, hence `2^{v₂(B)} ≤ |B|`, i.e.

```
v₂(B)  ≤  log₂|B|  =  (α + ε)N + O(log N).
```

**That is exactly the trivial bound, and the product formula gives nothing more.** What is needed
is `v₂(B) < S_N = sN`. At the binding heavy shell `s → α` the shortfall is `εN + O(log N)`. So the
product-formula route confirms the scale computation of §I and closes as predicted: the Archimedean
size of `B` is already `≈ 3^N`, so the product formula permits a 2-adic valuation linear in `N`
with the wrong constant.

## Z. Positivity-sensitive content (Gate 30)

Positivity enters at exactly one place, and sharply:

> `−Z` is a **positive integer** ⟺ its binary expansion **terminates** ⟺ the zero-runs `M_j` are
> eventually infinite ⟺ transport is eventually perfect ⟺ total excess regeneration is finite.

This is a genuinely positivity-sensitive statement, unlike the coordinates examined in the
lift-digit and eventual-zero rounds, which could not distinguish positive from negative witnesses.
Here the distinction is the whole mechanism: a *negative* integer realizer has an eventually
all-ones expansion, so its zero-runs are bounded and regeneration is identically zero; a *generic*
2-adic realizer has neither property.

But note what this buys: it explains why genuine orbits are tame, not why confined words must have
large realizers. The positivity content is on the wrong side of the problem.

## AA. Negative-witness stress test (Gate 31)

| witness | valuation word | `M_j` | regeneration |
|---|---|---|---|
| `n = −1` | `1,1,1,1,…` | `0,0,0,0,…` | identically 0 |
| `n = −5` | `1,2,1,2,…` | `0,0,0,0,…` | identically 0 |

Both are valid 2-adic realizers with **every** step a failure and **zero** excess regeneration
forever. Any proposed bound of the form "bounded regeneration ⟹ bounded realizer depth" is
therefore immediately false: these witnesses have the least possible regeneration and unbounded
`S_N`. Consistently, their gaps are `g_j = 0` (for `−1`, `r_j = 2^{S_j+1}−1`, so
`⌊log₂ r_j⌋ = S_j`), so the inherited bridge `g < H+1` is satisfied with room to spare and no
contradiction arises. The test passes, and it rules out an entire family of overclaims.

## AB. Targeted computational scaling (Gate 32)

Diagnostic only, as instructed; no broad transport study was repeated.

| quantity | result |
|---|---|
| `Z = −n₀` | 2,000 seeds, 0 mismatches |
| `χ_j = n₀ mod 2^{S_j}`, `X_j = ⌊n₀/2^{S_j}⌋` | 88,000 steps, 0 mismatches |
| `v₂(a−u) = d_{j+1} − M_j + M_{j+1}` | 478,613 events, 0 mismatches |
| excess runs pairwise disjoint | 100,000 seeds, 0 violations |
| `Σ excess ≤ ⌊log₂ n₀⌋+1`; `#failures ≤ log₂ n₀` | 0 violations; worst ratio 0.765 |
| periodic closed form `C_{Np}Δ = c₀(3^{Np}−2^{Nσ})` | 48/48 exact |
| `C_N` odd | 400 random words, 0 violations |
| `2^{S_j}n_j = 3^j n₀ + C_j` (classic) | 45,000 steps, 0 mismatches |
| shell injectivity of `D ↦ χ_N` | 7 shells to `N=9`, exact in all |
| bit height vs. valuation | §I table; ratio `→ 1/(1+ε/α)` at the heavy shell |

## AC. Literature applicability table (Gate 33)

| theorem / source | object bounded | dimension | bound shape | constants depend on | fits `B(D,χ)`? | resulting regeneration bound | suff. for C? | suff. for E? | verdict |
|---|---|---|---|---|---|---|---|---|---|
| Yu, Acta Math. **211** (2013) 315–382, Main Thm (1.18) / Thm 1 (1.24); Forum Math. **19** (2007) 187–280, p. 190 | `ord_𝔭(α₁^{b₁}···α_n^{b_n} − 1)` — a **product** minus 1 | fixed `n`; constant `(16ed)^{2(n+1)}` to `n^{n(1+o(1))}` | `C(n,d,p)·∏h′(α_i)·log B`, **effective** | `n`, `d`, `e_𝔭`, `p^{f_𝔭}`, heights | **no** — `B` is an `(N+1)`-term sum, not a binomial; and at `p=2` the hypothesis `ord_𝔭α_j=0` fails for `α=2` and the quantity is trivially `0` | none | no | no | **inapplicable (wrong object; `n` grows; vacuous at `p=2`)** |
| Evertse–Schlickewei–Schmidt, Ann. of Math. **155** (2002) 807–836, Thm 1.1 | **number** of non-degenerate solutions of `Σa_ix_i = 1` | `exp((6n)^{3n}(r+1))` | a count, **not** a size; ineffective for `n ≥ 3` | `n`, `r` | only if one imposes `B = 2^k` (the *cycle* condition) | none — counts, does not size | no | no | **inapplicable (counts only; `n!` lower bound forbids uniformity)** |
| Evertse–Schlickewei, Crelle **548** (2002) 21–127, Thm 3.1 (+ Schlickewei's `p`-adic Subspace Thm) | `∏_v∏_i ‖L_i(x)‖_v/‖x‖_v` — includes `|B|₂` | `t₂ ≤ (3n)^{2ns}2^{3(n+9)²}δ^{−ns−n−4}…` | `v₂(B) < ε·log₂‖y‖ + O_ε(1)` outside `t₂` subspaces; **ineffective** | `n`, `s`, `D`, `δ` | **yes, formally** (§L) | the right *shape*, but ineffective, non-uniform in `n`, threshold `n^{4n/δ}` | no | no | **LEVEL 1 only** |
| Evertse, Compositio Math. **53** (1984) 225–244, Thm 2 (sums of S-units) | lower bound for `∏_{v∈T}` of an S-unit sum | fixed term count | ineffective | term count, `S` | same mechanism as above | same | no | no | **LEVEL 1 only**; exact inequality unverified (OCR) |
| Lifting-the-exponent | `v₂(x^n ± y^n)` | 2 terms | exact | — | only in the periodic sector, where it yields `0` (§O) | none | no | no | **inapplicable** |
| multiplicative order of `3` mod `2^m` | `3^A ≡ c (mod 2^q)` | — | exact | — | target `−C_N` is an arbitrary history-dependent odd residue | none | no | no | **inapplicable** |
| product formula over `ℚ` | `v₂(B)` | any | `v₂(B) ≤ log₂|B|` | — | yes | exactly the **trivial** bound (§Y) | no | no | **gives the trivial bound and nothing more** |
| fixed-order linear recurrences | `v_p` of recurrence terms | fixed order | — | order, coefficients | only for periodic words (order 2) | subsumed by §S | n/a | n/a | **inapplicable for irregular words** |
| Ridout / `p`-adic Roth | approximation to a **fixed** algebraic number | — | ineffective | — | target moves with the word (§R) | none | no | no | **inapplicable (moving target)** |

Verified from primary sources except where flagged. Items explicitly **not** verified and
therefore not relied upon: Evertse–Győry, *Unit Equations in Diophantine Number Theory* (CUP 2015)
— no theorem numbers quoted; Beukers–Schlickewei's own `n=2` constant; the Amoroso–Viada
improvement `exp(5n⁵log(8n)(r+1))` (second-hand from Evertse's notes); Győry–Yu's explicit
constants; the ESS `3n` vs `4n` exponent discrepancy.

## AD. Strongest surviving theorem (Gate 34)

**LEVEL 1 — formal applicability.** The `p`-adic Subspace Theorem applies formally to
`B(D,χ) = Σ_{i<N}3^{N−1−i}2^{S_i} + 3^Nχ` and produces a bound of exactly the needed shape,
`v₂(B) < ε·log₂‖y‖ + O_ε(1)`, outside finitely many proper subspaces (§L). This is the strongest
rigorously justified statement in the audit, and it is genuinely LEVEL 1 rather than nothing.

**LEVEL 2 — nontrivial bound on one regeneration event. Not reached.** The constant `O_ε(1)` is
ineffective, and the theorem's own height threshold `n^{4n/δ} ≈ N^{4N/δ}` excludes the regime of
interest. No explicit word can be excluded.

**LEVEL 3 — cumulative bound strong enough to move the realizer floor. Not reached**, and not
reachable by this route: `n = N+1` grows, and ESS's `Ã(n,0) ≥ n!` shows the `n`-dependence cannot
be removed.

The only theorem that reaches LEVEL 3 in this audit is the audit's own §V result, and it reaches
it for genuine orbits, where the conclusion is not needed.

I explicitly decline to promote the LEVEL 1 result. It is the kind of statement that reads as
progress and is not.

## AE. Why existing theory fails (Gate 35)

The narrowest obstruction, isolated as the gate requires:

> **The number of additive terms in the primitive object grows linearly with `N`, and every
> theorem in the relevant literature is quantified "for each `n`" with a constant that is
> provably forced to blow up in `n`.**

This is one obstruction, not a list, and it is the binding one. Supporting detail:

- It is **provable**, not an artifact: ESS exhibit `Ã(n,0) ≥ n!` and `Ã(n,1) ≥ c·n²`, so no
  `n`-uniform counting theorem can exist. The documented maximum growth of `n` in Baker/Yu theory
  is `n ≈ log p/log log p` (Stewart's device, Yu 2013 §1) — logarithmic, not linear.
- The secondary obstructions each suffice on their own but are less fundamental: the moving target
  (§R) kills fixed-target approximation; `p = 2` with `α = 2` kills linear forms vacuously (§J3);
  the arbitrary history-dependent odd residue kills multiplicative order (§O); ineffectivity kills
  the Subspace route even at fixed `n` (§L2).
- The self-consistency that a genuine orbit provides is representable — it is the single statement
  `−Z ∈ ℤ_{>0}` (§Z) — but it is **not** among the hypotheses any of these theorems can use, and
  on the word side it is exactly what is absent.

## AF. Weakest new arithmetic theorem needed (Gate 36)

The natural candidate is

> **(N1)** There is `ε>0` such that for every zero-confined word `D` of length `N` and every
> integer `1 ≤ χ < 2^{εN}`, `v₂(C_N + 3^Nχ) < S_N`.

**This is Open Problem C verbatim, not a weaker statement.** For `χ < 2^{S_N}`, `v₂(C_N+3^Nχ) ≥
S_N` holds iff `χ = χ_N`, so (N1) says exactly `χ_N ≥ 2^{εN}`. The gate's own warning applies and
the candidate must be rejected.

I could not formulate a genuinely weaker arithmetic statement about `a_j, u_j` with an independent
proof route. Every cleared-denominator rendering of the regeneration condition is the realizer
congruence rewritten, which is Gate 5's tautological branch. The one statement that is *not* a
restatement is §V's theorem — and it is about genuine orbits, where the problem is already trivial.

The honest shape of what would be needed: a bound on `v₂` of an `(N+1)`-term `{2,3}`-unit sum that
beats the product-formula bound by a positive linear amount, **uniformly in the exponent sequence
`S_0 < … < S_{N−1}`**. No such result appears to exist, and §H explains the structural reason.

**Calibration: what *is* provable, and why it falls short.** Within a fixed shell `(N, S)` the map
`D ↦ χ_N(D)` is injective (repo `realizerCongruence`; the note's §D.7 calls it the coarse residue
map). Verified exhaustively on seven shells up to `N=9`: e.g. `(8,13)` gives 784 words and 784
distinct `χ`, `(9,14)` gives 1278 and 1278. Since `χ_N` is odd in `[1, 2^S)`, at most `2^{εN−1}`
words can have `χ_N < 2^{εN}`, while the shell has `C(S−1, N−1)` words. At the confined shell
`S = αN`, `log₂ C(S−1,N−1) ~ α·H₂(1/α)·N = 1.5056·N`, so

```
fraction of shell words with χ_N < 2^{εN}   ≤   2^{(ε − 1.5056)N},
```

exponentially small for every `ε < 1.5056`. So **Open Problem C holds outside an exponentially
small exceptional set, by pigeonhole alone** — and the typical word beats Open Problem E's target
`log₂ r ≥ I₀N = 0.0793N` by a factor of about **19**. This is a genuine statement but a trivial
one, and it is not a candidate for Gate 36: Open Problems C and E are worst-case statements over
*every* confined word, and pigeonhole cannot reach a worst case by construction. It does, however,
calibrate the difficulty: the obstruction is an exponentially thin set of exceptional words, not a
generic phenomenon.

## AG. Open Problem C threshold (Gate 37)

From the inherited bridge `S_N − log₂ r_N < H_1 + R₊(N) + 1` and `R₊(N) ≤ θN + O(1)`:

```
log₂ r_N  >  S_N − θN − O(1).
```

The **only** guaranteed lower bound on `S_N` is `S_N ≥ N` (every `d_i ≥ 1`). Therefore

```
log₂ r_N  >  (1 − θ)N − O(1),        so   θ < 1   gives Open Problem C with ε = 1 − θ.
```

**Gate 13/37 trap, avoided explicitly.** Substituting `S_N ≈ αN` here would give the weaker-looking
threshold `θ < α − ε` and overstate the floor by the corridor deficit `⌊αN⌋ − S_N`, which can be
linear. The previous round's `(T_C)` was stated in the *gap* coordinate (`g_N ≤ (α−ε)N`), where
`S_N ≤ ⌊αN⌋` is used in the safe direction; converting it to a realizer floor in terms of `N`
requires the lower bound, and the correct threshold is `θ < 1`. **This corrects the reading that
`(T_C)` with `θ = α − ε` suffices.**

Fixed-shell refinement: with `S_N = S` pinned, `log₂ r_N > S − θN − O(1)`, so the threshold is
`θ < S/N`, ranging from `1` (light shells) to `α` (heavy shells). The light shell is binding.
Lean: `floor_of_cumulative_gain`, `floor_of_cumulative_gain_shell`.

## AH. Open Problem E threshold (Gate 37)

Open Problem E: `E(D) ≤ H₂(ρ_c)·S + Φ(N)` with `Φ = o(N)`. Since `E_N < H_1 + R₊(N) + 1`, it
suffices that `R₊(N) ≤ H₂(ρ_c)·S_N + o(N)`. Taking the safe lower bound `S_N ≥ N` gives the
threshold

```
θ  ≤  H₂(1/α)  =  0.949956          (with ρ_c = 1/α = 0.6309298),
```

i.e. `ε = 1 − θ ≥ 0.050044`, consistent with `I₀/α = 1 − H₂(1/α) = 0.050044` and
`I₀ = α(1−H₂(1/α)) = 0.0793186`. Open Problem E therefore demands a strictly smaller `θ` than the
bare `θ < 1` of Open Problem C, as expected for the sharper statement.

## AI. Lean changes (Gate 38)

`EOC/SuperBudgetCancellation.lean`, 7 declarations, all elementary bridges as the gate permits —
no external number theory is formalized:

`excess`, `sum_excess_le_span`, `sum_excess_le`, `div_eq_zero_of_log_lt`, `geom_closed_form`,
`periodic_floor`, `floor_of_cumulative_gain`, `floor_of_cumulative_gain_shell`.

Following the convention of the preceding audit rounds, the module is not added to the `EOC.lean`
aggregator.

## AJ. Tests / build

```
lake build EOC.TransportRegeneration     →  2259/2259, success
lake build EOC.SuperBudgetCancellation   →  2260/2260, success
lake env lean EOC/SuperBudgetCancellation.lean  →  exit 0, no diagnostics
```

Scripts: `scratch/gate01_closed_form.py`, `scratch/gate19_primitive.py`,
`scratch/gate23_word_side.py`, `scratch/gate29_scale.py`, `scratch/gate36_pigeonhole.py`.

## AK. Axiom audit

All seven theorems: `[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`, `axiom`,
`opaque` (the sole grep hit is the docstring line asserting their absence).

## AL. Files changed

```
EOC/SuperBudgetCancellation.lean                            (new)
docs/SUPERBUDGET_CANCELLATION_EXTERNAL_ARITHMETIC_AUDIT.md  (new)
scratch/gate01_closed_form.py                               (new)
scratch/gate19_primitive.py                                 (new)
scratch/gate23_word_side.py                                 (new)
scratch/gate29_scale.py                                     (new)
scratch/gate36_pigeonhole.py                                (new)
```

## AM. Commits

`5b456f8` — *Close the external-arithmetic route; the cancellation object has a closed form*,
on top of base `d5d12c2`. Single commit; `main` untouched.

## AN. Push status

Pushed to `origin/superbudget-cancellation-external-arithmetic-audit`. **No PR opened.**

## AO. Research verdict

**`EXISTING EXTERNAL ARITHMETIC DOES NOT CONTROL CUMULATIVE SUPER-BUDGET CANCELLATION`**

Chosen over the neighbouring options deliberately:

- not `GROWING DIMENSION DEFEATS CURRENT p-ADIC/S-UNIT BOUNDS` alone — true (§H, §AE) but it
  understates the case, since `p`-adic linear forms fail for two further independent reasons
  (wrong object; vacuous at `p = 2`);
- not `MOVING TARGET BLOCKS FIXED-TARGET DIOPHANTINE THEOREMS` alone — true of §M and §R, but the
  Subspace route is not a fixed-target theorem and fails for different reasons;
- not `AN EXTERNAL ARITHMETIC INTERFACE SURVIVES` — the Subspace bridge is LEVEL 1 only (§AD), and
  promoting it would be exactly the overclaim Gate 34 forbids;
- not `FORCED DIVISIBILITY FACTORS OUT; PRIMITIVE CANCELLATION IS TRACTABLE` — forced divisibility
  *does* factor out cleanly (§F), and on the genuine-orbit side the primitive object *is* tractable
  and fully solved (§V). But the verdict must be chosen for the problem the brief targets, and on
  the word side, where Open Problem C lives, the primitive object is not tractable.

**What the audit establishes positively**, beyond the closure:

1. The cancellation object has a closed form. `Z = −n₀`, hence `X_j = ⌊n₀/2^{S_j}⌋` and
   `M_j` is a zero-run in the binary expansion of the seed. All powers of 3 cancel identically.
2. `v₂(a_j−u_j) = (d_{j+1} − M_j) + M_{j+1}`: forced plus excess, with the excess equal to the
   next matching precision.
3. **Cumulative excess regeneration along one genuine positive orbit is at most `⌊log₂ n₀⌋ + 1`,
   and the number of failures is at most `log₂ n₀`** — by disjointness of bit intervals, with no
   external arithmetic. The note's own §D.9 statistics (≈9.5 failures per trajectory) corroborate
   this without having identified it.
4. Consequently the brief's primary question rests on a false premise: there is no *repeated*
   high-order cancellation along one genuine orbit. The transport coordinates degenerate after
   `O(log n₀)` steps — **even for a hypothetical divergent orbit** — so they cannot detect
   divergence at all.
5. The periodic sector is settled by a three-term collapse and a size argument, needing no
   Diophantine input (§S), which shows that what makes that sector work is precisely what
   irregular words lack.
6. Open Problem C is exactly the statement that the **product-formula bound `v₂(B) ≤ log₂|B|` can
   be improved by `Ω(N)`** (§Y), with the binding case the heavy shell `S_N → αN` where the
   required improvement is `εN`.
7. The correct cumulative threshold is `θ < 1` (`ε = 1 − θ`), not `θ < α − ε` (§AG).
