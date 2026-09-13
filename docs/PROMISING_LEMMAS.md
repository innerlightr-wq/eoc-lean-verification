# Promising lemmas: cyclic rotation / cycle-lemma findings, and Lean suitability

Companion to `docs/CONSTRAINED_WORD_THEOREM_AUDIT.md` §8, §17. Full data in
`results/constrained_word_asymptotics/cyclic_rotation_audit.json`.

## Lemma 1 (PROVED): unique maximizer of the centered partial sum

**Statement.** For any valuation word `d` of length `N` and any `j != j'`
in `{0,...,N}`, `R_j != R_{j'}` (where `R_j := s_j - j*alpha`,
`alpha=log_2(3)`). Consequently the maximizer of `R_j` over `j in
{0,...,N}` is unique.

**Proof.** `R_j = R_{j'}` would give `s_j - s_{j'} = (j-j')*alpha`, i.e.
`alpha = (s_j-s_{j'})/(j-j')` is rational. But `log_2(3)` rational would
mean `log_2(3) = p/q` for positive integers `p,q`, i.e. `3^q = 2^p` — impossible
by unique factorization (the left side is odd for `q>=1`, the right side
is a positive power of 2 for `p>=1`, and `p=q=0` is excluded since
`j!=j'`). Contradiction. A finite set of distinct reals has a unique
maximizer. **QED.**

**Verification.** Confirmed on all 32,518 words enumerated across `N in
{3,4,5,6}`, all feasible `s`, `c in {0,1}`: 100% unique-argmax rate,
matching the proof exactly (`test_unique_argmax_for_all_small_words`).

## Lemma 2 (REFUTED, with minimal counterexample): rotation count depends only on (N,s,c)

**Candidate statement** (the natural cycle-lemma-style guess): the number
of confined rotations of a word depends only on its length `N`, total `s`,
and confinement bound `c` — not on the specific digit arrangement.

**Refutation.** Minimal counterexample at `(N,s,c)=(3,5,1)`: among the six
compositions of `5` into `3` positive parts, the number of confined
rotations takes at least two distinct values (`2` and `3`), depending on
arrangement. Verified exhaustively; smallest case found by direct search
over `N in {3,...,6}`. **72 of 84 tested `(N,s,c)` groups DO have a
constant rotation count** — so the phenomenon is not universal failure,
but it is not universally true either, and no simple characterization of
which groups are constant was found in this audit (left open, §Open
Questions below).

## Lemma 3 (REFUTED, with minimal counterexample): the natural cycle-lemma-style construction

**Candidate statement**, generalizing the classical Dvoretzky-Motzkin
cycle lemma's proof mechanism: rotating a word to start immediately after
the (unique, by Lemma 1) maximizer of `R_j` produces a confined rotation.

**Refutation.** Minimal counterexample: `d=(1,3,1)`, `c=0`. The unique
maximizer of `R_j` is at `j=2` (verified directly). Rotating to start
there gives `(1,1,3)`. Its prefix sums are `1,2,5`; at `j=3`,
`confined_exact(5,3,0)` requires `2^5=32 <= 3^3=27`, which is **false** —
the rotated word is not confined. **Across all 32,518 tested words with a
unique maximizer (100% of them, by Lemma 1), this construction succeeds
only 435 times (1.34%).**

**Diagnosed root cause, not merely observed.** The classical cycle lemma
(Dvoretzky & Motzkin 1947; see also the standard ballot-theorem proofs,
e.g. via Sparre Andersen's/Feller's cyclic-permutation argument) requires
steps bounded ABOVE by `1`, so that the running minimum (equivalently, the
running maximum of the centered sum here) can only IMPROVE by at most `1`
per step — this is exactly what guarantees the "first return past the
running extreme" construction is well-defined and produces a valid
rotation. Valuation digits are positive integers with **no upper bound**:
a single digit can jump `R_j` upward by an arbitrary amount in one step,
so a rotation that looked safe relative to the ORIGINAL word's maximum can
overshoot the barrier immediately after the cut point. This is a
structural, not incidental, failure of the classical mechanism's
hypothesis — exactly the "minimal explicit counterexample showing why the
Catalan cycle lemma fails for unbounded positive valuation digits" the
task's Phase IV asked for as a valuable negative outcome.

**Classical cycle lemma itself independently re-verified** (as a sanity
check on this audit's own code, using bounded-above-by-1 steps, genuinely
unrelated to valuation digits): confirmed on 200 random test sequences
(`test_classical_cycle_lemma_hand_example`,
`test_classical_cycle_lemma_larger_hand_example`) — the audit's rotation
and confinement machinery is not itself the source of the refutation.

## Open questions (not resolved by this audit)

1. Is there a characterization of which `(N,s,c)` groups have a CONSTANT
   confined-rotation count (72/84 tested groups did)? A necessary
   condition search was not attempted.
2. Does the "endpoint defect" `s_N - alpha*N` control the number of
   admissible rotations in some WEAKER sense than the classical cycle
   lemma's exact count (e.g. as an upper or lower bound rather than an
   exact value)? Not tested.
3. Is there a Raney-lemma-style (rather than Dvoretzky-Motzkin-style)
   argument that survives unbounded steps? Raney's original lemma is
   stated for the SAME `<=1`-step hypothesis, so this is not automatic;
   not investigated further here.

## Lean suitability audit (Phase IX)

**Do not attempt in Lean before a paper proof exists** (T4/T5-level
asymptotic statements) — this audit's own findings confirm that
discipline was correct: several "natural" statements (Lemma 2, Lemma 3
above) turned out to be FALSE on first serious testing, which would have
wasted substantial Lean formalization effort had they been attempted
first.

**Recommended immediate Lean targets, in priority order:**

1. **`valuationShell_card`** (stars-and-bars, `C(s-1,N-1)`) in a new file
   `EOC/Combinatorics/PrefixConstrainedCompositions.lean`. This corrects
   the repeated false "already proved" claims found in `explorations/
   hypercuboid_transfer/ROUND2_REPORT.md` and related files (§2 of the
   main report) and is mathematically elementary (a standard bijection
   with `Finset.range`-indexed compositions; Mathlib likely already has a
   usable stars-and-bars lemma under `Nat.choose`/`Finset.Nat.antidiagonal`
   or similar — not independently confirmed in this audit, flagged for
   the implementer).
2. **The exact confinement-predicate equivalence** `R_j <= c <-> (S_j <= c
   \/ 2^(S_j-c) <= 3^j)` as a standalone `Nat`/`Real` bridge lemma,
   independent of any Collatz-specific definition — this is exactly the
   generic combinatorial fact this audit's `confined_exact` function
   encodes, and it should be formalized ONCE, generically, then imported
   by both the existing `EOC.Confinement.R`-based code and any new
   `PrefixConstrainedCompositions` module.
3. **Lemma 1 above** (unique-maximizer via irrationality of `log_2 3`) —
   a clean, short, self-contained Lean lemma; Mathlib has
   `Nat.Prime.irrational_log2_of...`-style tools or a direct unique-
   factorization argument (`Nat.Coprime`/`Nat.factorization`) sufficient
   for `log_2 3 ∉ ℚ`, already effectively used in this repository's own
   `EOC.Confinement.one_lt_alpha`-adjacent material (via `Real.log`
   monotonicity, not irrationality directly — a fresh short lemma would
   be needed).
4. **The Catalan specialization (T1)** as a standalone, Collatz-independent
   module — since it is an exact combinatorial identity about `{-1,+1}`
   sequences, it belongs in a generic combinatorics file, not under `EOC`.

**What should explicitly remain OUT of Lean for now**: the exponent
`gamma(c)` (unresolved even on paper for `c=3`), the collision rate
function `I_2(theta)` (not yet derived analytically), and any rational/
Sturmian-approximation machinery (Phase VI, not executed in this audit
round).

## Generic combinatorial definitions recommended to stay Collatz-independent

`W_c(N,s)`, the forward/backward DP, the Catalan specialization interface,
and Lemma 1's irrationality argument should all be stated for a GENERIC
irrational `alpha` and a generic integer bound `c`, with `alpha = log_2 3`
supplied only at the point of instantiation for the EOC-specific use —
mirroring exactly how `EOC.Confinement.alpha` is already defined as a
`noncomputable def` separate from its use sites, and consistent with this
audit's own Python code (`confined_exact` takes `c` as a parameter and
never hard-codes anything EOC-specific beyond the choice `alpha=log_2 3`
baked into the `2^(S-c)<=3^j` identity, which is itself worth stating
generically as `2^(S-c) <= b^j <-> S - c <= j*log_2(b)` for a general
integer base `b>1`, of which `b=3` is one instance).
