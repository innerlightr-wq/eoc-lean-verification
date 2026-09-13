# Round 2 — Lean Formalization Candidates

No Lean file was edited this round. This is a candidate list only.

## A. `cylinder_digits_joint`

**Statement**: for `m` realizing prefix `d` to depth `t`, and any finite
`k`, the pushforward of the uniform-dyadic-`k` cylinder measure onto
`(d_t(k),…,d_{t+k-1}(k))` equals `∏ 2^{-q_i}` exactly.

**Required existing lemmas**: `EOC.TaoLike.Cylinder.cylinder_restart`,
`EOC.TaoLike.Cylinder.restart_step`, the existing one-step
digit-distribution machinery in `PersistenceModel.lean`
(`genProdWeight_tsum_eq_pow` already proves the *abstract* iid-product
normalization — the new content is the *transfer lemma* connecting the
concrete cylinder-lift `k`-parametrization to that abstract product law).

**Target file**: a new file, e.g. `EOC/TaoLike/CylinderJointLaw.lean`.

**Estimated difficulty**: Medium. The single-step case
(`v₂(2·3^{t+1})=1`) is already implicit in the repository's one-step law;
the induction step (re-applying the same valuation fact one level deeper,
independent of the residue achieved at the previous level) is
mechanically similar but needs its own induction on `k`, tracking the
residue-class bookkeeping explicitly. No new mathematical idea beyond
Round 1's hand derivation is required.

## B. `cylinder_sum_distribution`

**Statement**: `P(D_k = s) = C(s-1,k-1)·2^{-s}` for `s ≥ k`, as a
corollary of A plus a stars-and-bars count.

**Required existing lemmas**: candidate A above, plus
`EOC.CompositionCounting.valuationShell_card` — **already proved** in
this repository, requires no new combinatorics, only the connecting
observation that all compositions of a fixed sum have equal cylinder
mass (Part II/IV of the Round 2 report).

**Target file**: same file as A, or `EOC/CompositionCounting.lean`
directly (it is a natural extension of that file's existing content).

**Estimated difficulty**: Low, given A and `valuationShell_card` both
exist — this is close to a one-line corollary.

## C. `confined_mass_dp`

**Statement**: the cylinder-measure mass of `{d : Confined c d N ∧ S_N d
= s}` equals (the combinatorial count of confined length-`N` compositions
summing to `s`) `· 2^{-s}`.

**Required existing lemmas**: A, plus a *new* combinatorial definition
(a Lean formalization of the forward DP `confined_count_dp` from
`scratch/extremal_orbit_prefix_audit.py`, not yet formalized anywhere in
`EOC/`).

**Target file**: new file, e.g. `EOC/TaoLike/ConfinedMass.lean`.

**Estimated difficulty**: Medium-High. The DP itself is a finite
recursive count over `ℕ`-valued states; formalizing "no exact Lean
object currently represents this count" is the main work (unlike A/B,
which mostly assemble existing lemmas).

## D. `conditioned_digit_kernel` (Doob h-transform)

**Statement**: for the backward survival function `B(j,S) := cylinder
mass of confined completions from state (j,S) to depth N`, `P(q_{j+1}=r |
survive to N) = 2^{-r}·B(j+1,S+r)/B(j,S)` whenever `B(j,S) > 0`.

**Required existing lemmas**: definition of `B` (new, a backward
recursion dual to candidate C), basic conditional-probability algebra
(Mathlib `ProbabilityTheory` conditional expectation/Bayes lemmas, or a
direct from-definitions computation avoiding the general measure-theory
apparatus, which is likely simpler here given the finite/discrete
setting).

**Target file**: `EOC/TaoLike/ConfinedMass.lean` (extends C) or a new
`EOC/TaoLike/DoobTransform.lean`.

**Estimated difficulty**: Medium. The proof itself (this round's Part V)
is a two-line application of the definition of conditional probability
once `B` exists as a recursively-defined object with its defining
recursion available as a `simp`/`unfold` lemma — the difficulty is mostly
in setting up `B`'s recursion cleanly in Lean (well-founded recursion on
`N - j`), not in the probability algebra.

## E. `first_crossing_mass`

**Statement**: the exact recursion for `P(τ = j)` (Part VII of the
Round 2 report) as a telescoping identity in terms of `B`/the forward DP.

**Required existing lemmas**: C, D.

**Target file**: same as C/D.

**Estimated difficulty**: Low-Medium once C/D exist — this round found
it to be a direct restatement of the existing DP in probabilistic
language, not a new combinatorial fact, so the Lean proof should mostly
follow by `unfold`/`simp` from C's recursion plus a telescoping-sum
lemma.

## F. Large-deviation identity: `I0_eq_geom2_cramer_rate`

**Statement**: `I0 = sSup {θ·α − Λ(θ) : θ ∈ (−∞, ln 2)} / ln 2` (or the
closed-form equality `I0 = α − α·log2 α + (α−1)·log2(α−1)` reproven via
an explicit Legendre-transform calculus argument at the critical point
`θ* = ln(2(α−1)/α)`, matching `lambdaStar` already in the repository up
to the base-e/base-2 unit conversion already handled by
`rateNats_eq_I0_mul_log_two`).

**Required existing lemmas**: `EOC.TaoExternal.I0`, `lambdaStar`,
`Mfun`, `rateNats_eq_I0_mul_log_two` — **all already in
`PersistenceModel.lean`**. This candidate is essentially a *reframing*
theorem: proving that the existing `lambdaStar`/`Mfun`/`I0` construction
**is** the standard Cramér/Legendre transform of the `Geom(2)` law,
rather than an ad hoc Chernoff optimization. No new numeric content
(this round confirmed the identity both symbolically and to machine
precision — see Part XIII of the report); the value would be purely
expository/structural (making the existing repository's own derivation
recognizable as the textbook large-deviation construction).

**Target file**: `EOC/TaoLike/PersistenceModel.lean` itself, as an
additional remark/theorem near `I0`'s definition, or left as
documentation only, since it re-derives (not extends) what the file
already proves.

**Estimated difficulty**: Low — this is an alternative *proof* of an
already-proved numerical identity; mathlib's `Real.log`/`Real.exp`
calculus lemmas already used elsewhere in the same file are sufficient.
**Recommended priority: lowest** of the six, precisely because it adds
no new content, only a new derivation route for an existing constant.

---

## Priority recommendation

If only one candidate is pursued next: **A + B together** (they are
almost the same formalization effort, and B is a near-free corollary of
A plus an already-proved Lean lemma). These would be the first
genuinely new Lean theorems this exploration has produced evidence for
in two rounds — Round 1's independence law (A) and Round 2's exact sum
law (B) are the two most fully hand-and-computer-verified results across
both rounds.
