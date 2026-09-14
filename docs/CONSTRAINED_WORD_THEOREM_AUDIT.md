# Constrained-word theorem audit: main report

**Adversarial theorem-discovery audit, exploratory only.** No Lean file was
modified. No claim here is a claim about the Collatz conjecture or EOC.

## 1. Executive verdict

**A genuine, provable, standalone combinatorial theory exists for the
irrational-prefix-barrier composition problem, and this audit both proves
and refutes specific pieces of it.** Two rigorous results are established
(Catalan specialization of the generic DP, exact; the unrestricted-shell
Stirling asymptotic with the correct `alpha*N*H_2(rho) - (1/2)log_2 N +
O(1)` form, confirmed to residual < 10^-4 by N=3200). The classical cycle
lemma is shown, with an explicit minimal counterexample, **not** to
generalize to unbounded positive digits. The confined-count exponent
gamma is measured at gamma≈1.0 (not 1/2) for small c via honest dense-
regression, but its c-dependence in the tested range is not resolved. The
collision-rate hypothesis of a single stationary R_2 is **refuted**: the
measured rate is clearly theta-dependent. Classification: **C/D** (see
§14) — a useful new computational framework with one candidate standalone
theorem (T1, proved) and several promising but incompletely-resolved
conjectures (T3/T4/T5).

## 2. Repository state and files examined

```
pwd: ~/Desktop/eoc-lean-verification
git log -1: c6bc929 "correct EOC documentation after mathematical audit"
git status --short (BEFORE this audit's own new files):
  ?? EOC/TaoLike/CylinderDigitCounting.lean   (pre-existing, untracked)
  ?? EOC/TaoLike/PersistenceRateCramer.lean   (pre-existing, untracked)
  ?? explorations/                            (pre-existing, untracked)
```
No file was modified. New files created (this audit) are listed in §18.

Files read in full: `README.md`, `EOC/Basic.lean`, `EOC/ValuationWord.lean`,
`EOC/Carry.lean`, `EOC/Realizer.lean`, `EOC/Confinement.lean`,
`EOC/TaoLike/Cylinder.lean`, `EOC/TaoLike/CylinderAppend.lean`,
`CHANG_CYLINDER_SCRATCHPAD.md` (grepped for DP/counting content, key
sections read), `docs/RESEARCH_CHECKPOINT_2026-09.md` (in full),
`scratch/supp_long.py`, `scratch/supp_negatives.py`,
`explorations/hypercuboid_transfer/scripts/round2_verification.py` (in
full), `explorations/hypercuboid_transfer/PAUSE_CHECKPOINT_2026-09-11.md`
(in full).

**Critical Phase-0 discrepancy found and flagged**: `explorations/
hypercuboid_transfer/ROUND2_REPORT.md`, `ROUND2_LEAN_CANDIDATES.md`, and
`ROUND3_FORMALIZATION_REPORT.md`, together with
`round2_verification.py`'s own code comments, repeatedly assert that
`EOC.CompositionCounting.valuationShell_card` is **"already proved"** /
**"already Lean-proved"** / **"already in the repository."** This file
**does not exist**: confirmed by `find . -iname "*Composition*"` (no
match) and by `EOC.lean`'s import list (no `CompositionCounting` entry).
The underlying mathematical claim (stars-and-bars, `C(s-1,N-1)`) is true
and elementary, but it is **not currently a Lean theorem anywhere in this
repository**. This is reported here, not silently corrected in the
pre-existing exploration files (per the instruction not to rewrite
existing material) — see §17 for the recommended fix.

**Two pre-existing untracked Lean files** (`CylinderDigitCounting.lean`,
`PersistenceRateCramer.lean`) are explicitly recorded, per the pause
checkpoint's own honest labeling, as **hand-reviewed only, never
compiled** (`.lake` absent, no Mathlib cache, build deliberately deferred
to avoid repeating a prior disk-exhaustion incident). This audit did not
attempt `lake build` (would fail identically, and the instructions
prohibit touching the toolchain) — this status is preserved exactly, not
upgraded or downgraded.

## 3. Exact definition of W_c(N, s_N)

Matching the repository's own Lean definitions exactly (`EOC.Confinement`):
```
alpha := log_2(3)                         [EOC.Confinement.alpha]
R(d, j) := s(d,j) - j*alpha                [EOC.Confinement.R]
Confined(c, d, N) := forall j<=N, R(d,j) <= c   [EOC.Confinement.Confined]
```
This audit defines, on top of the repository's existing vocabulary (no
prior file defines this counting object):
```
W_c(N, s) := { d : (Z_{>=1})^N | sum(d) = s  and  Confined(c, d, N) }
A_N := |W_c(N, s_N)|,  U_N := C(s_N - 1, N - 1)  (unrestricted shell)
```
The **exact integer barrier**, reused verbatim from `round2_verification.py`
(pre-existing, untracked) and preserved unchanged in every new experiment
file: `R_j <= c  <=>  S_j <= c  or  2^(S_j-c) <= 3^j` — no floating-point
`alpha` ever enters a confinement decision anywhere in this audit's code
(verified by a structural unit test,
`test_no_floating_point_alpha_in_confinement_decision`).

## 4. Correction/confirmation of the entropy normalization

**CONFIRMED, and the suspicion in the task was correct**: the extensive
term is `alpha*N*H_2(rho)`, not `N*H_2(rho)` — because the natural large
parameter in the binomial Stirling expansion is `s_N` (or `s_N - 1`), and
`s_N ~ alpha*N`, so `log_2 C(s_N-1,N-1) ~ s_N * H_2(N/s_N) ~ alpha*N*H_2(rho)`.
**Full derived form, verified**:
```
log_2 C(s_N-1,N-1) = alpha*N*H_2(rho) - (1/2)*log_2(N) + C(convention) + o(1)
```
Numerically confirmed to N=3200: the "extensive-only" residual (using
`alpha*N*H_2(rho)` alone) diverges like `-0.5*log_2(N)` exactly (residual
grows from -4.09 at N=50 to -7.09 at N=3200, a change of -3.0 over a 64x
increase in N — exactly `-0.5*log_2(64) = -3.0`), while the FULL derived
form (extensive term + the exact Stirling `-0.5 log_2(2*pi*n*p(1-p))`
correction, evaluated honestly rather than guessed) has residual shrinking
from -0.0051 (N=50) to -0.0001 (N=3200) — consistent with the standard
`O(1/N)` Stirling error. **Floor vs. ceiling conventions for `s_N` differ
only in a bounded shift of the O(1) constant** (both converge to residual
≈0, with the ceiling residuals uniformly ≈0.0002 smaller in magnitude than
the floor residuals at every tested N) — no exponent or coefficient
change, exactly as a Sturmian/bounded phase correction should behave.
**Label: PROVED ON PAPER, COMPUTATIONALLY CONFIRMED (T2 in the ladder).**

## 5-6. Catalan control: what transfers / what does not

See `docs/CATALAN_CONTROL_AND_LIMITS.md` for full detail. Summary:
**Transfers exactly**: the forward/backward DP architecture itself (T1,
proved: the generic DP specializes EXACTLY to Catalan numbers for all 25
tested n from 0 to 100, both as a closed-form match and via an independent
backward-DP cross-check); the `n^{-1}` survival-fraction law (here EXACT,
`C_n/C(2n,n) = 1/(n+1)`, not merely asymptotic); the qualitative
bridge-cost/positivity-cost decomposition (`n^{-1/2}` times `n^{-1}` =
`n^{-3/2}`, confirmed numerically). **Does NOT transfer**: the classical
cycle lemma's clean exact count (§8); a single stationary collision rate
(the Dyck-path control itself shows theta-dependent `-log_2(P)/k`, refuting
even the CONTROL model's own naive stationary-rate hypothesis, so this
should not have been expected to transfer to the harder problem either).

## 7. Count asymptotics and estimated polynomial correction

Dense OLS regression (N=20..400, 381 points; N=20..200 for c=3) of
`log(q_N)` vs `log(N)`, `q_N := A_N/U_N`:

| c | gamma (full range) | gamma (1st half) | gamma (2nd half) |
|---|---|---|---|
| 0 | 0.997 ± 0.025 | 1.001 | 0.990 |
| 1 | 0.965 ± 0.013 | 0.952 | 0.983 |
| 3 | 0.783 ± 0.009 | 0.712 | 0.888 |

**Adjacent-doubling exponent estimates were tried first and found highly
unstable (ranging from -2.05 to +1.80 for c=0 between successive N) —
this is exactly the Sturmian-oscillation risk Phase I warned about, and
the dense-regression fix (381 points, not 7) resolves it for c=0,1 (tight
internal consistency between the two halves) but NOT for c=3 (712 vs 888,
a real, not-yet-resolved gap).** **Honest conclusion: gamma is close to 1
for small c (c=0,1), with good internal consistency; whether gamma is
c-dependent or converges universally to 1 with slower finite-N convergence
at larger c is OPEN — not resolved by N≤400.** No decimal gamma is
reported as a discovery; this is stated as measured-with-uncertainty,
consistent with the task's explicit prohibition.

## 8. Cyclic-rotation/cycle-lemma findings

Full detail: `docs/PROMISING_LEMMAS.md`. Three findings, all exact
(exhaustive enumeration, N=3..6, all s, c in {0,1}, 32,518 words total):

1. **PROVED**: `R_j` is injective in `j` for every word (irrationality of
   `alpha`: `alpha` rational would force `3^q=2^p`, impossible). Hence the
   maximizer of `R_j` is ALWAYS unique — confirmed on all 32,518 tested
   words (100%), matching the proof exactly.
2. **REFUTED, with minimal counterexample**: "`n_confined_rotations`
   depends only on `(N,s,c)`" — fails at `(N,s,c)=(3,5,1)`, where words of
   the same shape have 2 or 3 confined rotations depending on digit
   arrangement.
3. **REFUTED, with minimal counterexample**: the natural cycle-lemma-style
   construction "start right after the (unique) maximizer of `R_j`" gives a
   confined rotation only **1.34%** of the time (435/32,518). Explicit
   minimal counterexample: word `(1,3,1)`, `c=0`; the unique argmax is at
   `j=2`; rotating to start there gives `(1,1,3)`, which is **not**
   confined. **Diagnosed mechanism**: the classical cycle lemma's proof
   needs steps bounded above by 1 so the running minimum changes by at
   most 1 per step; here a single digit can jump the barrier by an
   arbitrary amount, breaking the argument at its root, not incidentally.

## 9. Collision definition and scaling regimes

Definition used (matching the task's specification exactly): two words
drawn independently and uniformly from `W_c(N,s_N)`; `P_{N,k}` = probability
their first `k` digits agree, computed via `sum_S [forward_count(k,S) *
backward_count(k,S)^2] / A_N^2` (exact integer/Fraction arithmetic; cross-
checked against full brute-force pair enumeration for all tested small
cases). At `N=40, c=0`: `P_{N,0}=1`, `P_{N,N}=1/A_N` exactly, monotone
decreasing throughout (all verified). `-log_2(P_{N,k})/k` rises smoothly
and monotonically from 0 (theta=0) to ≈1.27 (theta=1) — **NOT flat**,
directly refuting a single stationary `R_2`. See §10 and
`docs/COLLISION_RATE_PROOF_OBLIGATIONS.md`.

## 10. Geometric-model prediction, independently derived

The base (unconditioned) single-digit Geom(2) law has Renyi-2 entropy
`-log_2(sum 2^{-2q}) = -log_2(1/3) = log_2(3) = alpha` **exactly** (an
algebraic identity, re-derived here independently: `sum_{q>=1} 4^{-q} =
1/3`). This is the NAIVE candidate for `R_2`. **It does not match the
measured collision rate at any tested theta in [0,1]** on the confined,
endpoint-conditioned, UNIFORM-measure problem (measured rate spans 0 to
1.27, alpha=1.585 sits above the entire measured range, only plausibly
approached in extrapolation beyond theta=1, which is not a meaningful
regime). **Conclusion: R_2 = alpha is refuted as the collision rate of this
problem; if a limiting rate function exists, it is a genuinely theta-
dependent `I_2(theta)`, not a single number equal to the base digit's own
Renyi-2 rate.**

## 11. Rational/Sturmian approximation findings

**Not executed at full depth in this audit** (time-scoped out; see §15
for the exact obligation). The relevant structural fact IS established:
`alpha`'s irrationality is exactly what makes `R_j` injective (§8, item 1)
and is exactly what the pre-existing `docs/RESEARCH_CHECKPOINT_2026-09.md`
already identifies as blocking any finite-state/Sturmian-transducer
argument for the deficit process (`Delta_n` depends on `floor(beta*n)`,
provably not eventually periodic). This audit did not independently
re-derive continued-fraction convergent bounds; that remains open work
(§15, item 3).

## 12. Proven lemmas (this audit, hand-proof level)

1. **Stars-and-bars unrestricted shell count** `C(s-1,N-1)` — elementary,
   re-verified exactly by direct enumeration for small cases
   (`test_unrestricted_shell_matches_stars_and_bars_hand_example`).
2. **Catalan specialization of the generic forward DP** — exact match for
   n=0..100 (25 values tested), both via the closed form and an
   independent backward-DP cross-check.
3. **Survival-fraction exact identity** `C_n/C(2n,n) = 1/(n+1)` (not
   merely asymptotic).
4. **Injectivity of `R_j` / uniqueness of the maximizer**, via irrationality
   of `alpha` — proof given in full in §8 and in
   `experiments/cyclic_rotation_audit.py`'s own docstring/output.
5. **The Stirling asymptotic with the exact `-1/2 log_2 N` coefficient and
   derived (not guessed) `O(1)` constant** — derived by hand, confirmed
   numerically to residual `<10^-4` at N=3200.

## 13. Counterexamples and killed hypotheses

1. `n_confined_rotations` is a function of `(N,s,c)` alone — **KILLED**,
   minimal counterexample `(N,s,c)=(3,5,1)`.
2. The "start after the max" cycle-lemma-style construction gives a
   confined rotation — **KILLED**, minimal counterexample `(1,3,1)`, `c=0`.
3. A single stationary Renyi-2 collision rate `R_2` (in particular,
   `R_2=alpha`) — **KILLED**, refuted by direct exact computation showing
   theta-dependence.
4. The extensive entropy coefficient is `N*H_2(rho)` rather than
   `alpha*N*H_2(rho)` — **KILLED** (this was the task's own suspicion,
   confirmed correct).
5. A naive exponential-tilt "mean-matching" law for the bulk conditioned
   marginal — **already killed in the pre-existing `explorations/
   hypercuboid_transfer/ROUND2_REPORT.md`** (numerically failed; not
   re-litigated here, cited as prior art).

## 14. Strongest credible conjecture

**Conjecture (Confinement exponent).** For fixed small integer `c >= 0`,
`A_N / U_N = K_c(N) \cdot N^{-gamma(c)} (1+o(1))` for a bounded,
possibly-oscillating phase factor `K_c(N)` and an exponent `gamma(c)` that
is close to `1` for `c` near `0` and appears to decrease as `c` grows, in
the tested range `N<=400`. **Status: COMPUTATIONALLY SUPPORTED for c=0,1
(good internal consistency across sub-ranges); UNRESOLVED for c=3 (the two
half-range estimates disagree at the ~15% level, more than can be
attributed to statistical noise at this sample size). This conjecture is
explicitly NOT elevated to a proved theorem.**

## 15. Exact proof obligations

1. Prove `gamma(0) = 1` exactly (or refute it), via an explicit
   generating-function/transfer-operator argument for the `c=0` case,
   which is the cleanest (the barrier touches the axis exactly at `S_j=0`
   for all `j` with `S_j<=c=0`, giving the tightest possible pinning).
2. Determine whether `gamma(c)` is genuinely `c`-dependent or whether
   `c=3`'s regression instability is a finite-`N` artifact requiring
   `N` into the low thousands to resolve (this audit's DP is only
   practically fast enough for `N<=800`, per the benchmark in §19 — a
   further constant-factor speedup, e.g. via NumPy vectorization of the
   forward-DP dictionary, would be needed to push further).
3. Derive `I_2(theta)` for the confined-word collision problem
   analytically (a large-deviation-style rate function, by analogy with
   the already-proved `I_0` Cramer-rate identity in
   `explorations/hypercuboid_transfer/scripts/round2_verification.py`
   Part F — but for the UNIFORM, not geometric, measure, which is a
   different variational problem).
4. Formalize continued-fraction rational-barrier bounds for `alpha=log_2(3)`
   (Phase VI, not executed here).

## 16. Separation from Collatz/EOC claims

**Nothing in this audit is a claim about actual Collatz orbits, `EOC`, or
`CriticalCrossing`.** Every object studied (`W_c(N,s)`, `A_N`, `P_{N,k}`,
rotation orbits) is a purely combinatorial object on formal valuation
words. The dependency chain, as established by the repository's own Lean
files and preserved exactly here:
```
unrestricted compositions
  -> confined formal words           [THIS AUDIT's entire scope]
  -> residue-class realizers         [EOC.Realizer, EOC.Confinement -- untouched]
  -> natural Collatz orbit prefixes  [EOC.Basic, EOC.ValuationWord -- untouched]
  -> hypothetical infinite-orbit claims (EOC, CriticalCrossing)  [OPEN, untouched]
```
No result in this audit crosses from tier 1 (formal words, this audit's
scope) to tier 2 (realizers) or beyond. In particular, "a confined FORMAL
word exists with property X" is never described here as "a Collatz orbit
has property X," and no claim assumes every admissible finite word extends
to a natural infinite orbit (indeed the opposite is already established by
the repository's own `BoundedDrift`/`FinitePrefixPacking` machinery, which
this audit does not touch or contradict).

## 17. Lean formalization recommendations

See `docs/PROMISING_LEMMAS.md` §Lean-suitability for the full mapping. Top
priority: **(a)** actually prove `valuationShell_card` (stars-and-bars) in
a new file `EOC/Combinatorics/PrefixConstrainedCompositions.lean`,
correcting the repeated but false "already proved" claims in the
pre-existing exploration reports (§2); this is the single highest-value,
lowest-risk Lean target identified by this audit. **(b)** the exact
`confined_exact` predicate equivalence (`R_j<=c <-> 2^(S_j-c)<=3^j`) is a
one-line `Nat`/`Real` bridge lemma, immediately formalizable. **(c)** the
Catalan specialization (T1) is a clean, self-contained combinatorial
identity, well suited to a standalone Lean module independent of any
Collatz-specific definitions. No asymptotic theorem (T2-T5) should be
attempted in Lean before its paper proof is complete, per the task's own
explicit instruction and this audit's own findings (T4/T5 are not yet
proof-ready).

## 18. Files created or modified

**Created** (all new, under `~/Desktop/eoc-lean-verification/`):
```
experiments/confined_composition_asymptotics.py
experiments/catalan_barrier_control.py
experiments/prefix_collision_audit.py
experiments/cyclic_rotation_audit.py
tests/test_confined_composition_asymptotics.py
tests/test_catalan_barrier_control.py
tests/test_prefix_collision_audit.py
tests/test_cyclic_rotation_audit.py
results/constrained_word_asymptotics/*.json, *.log
docs/CONSTRAINED_WORD_THEOREM_AUDIT.md   (this file)
docs/CATALAN_CONTROL_AND_LIMITS.md
docs/COLLISION_RATE_PROOF_OBLIGATIONS.md
docs/PROMISING_LEMMAS.md
```
**Modified: none.** No existing Lean, Markdown, or Python file was
altered, renamed, or moved.

## 19. Tests run and complete results

```
$ python3 -m pytest tests/ -q
..........................................
42 passed in 0.06s
```
All 42 tests pass, covering: unrestricted-count hand examples, DP-vs-
brute-force cross-validation, Catalan exact match (0-100), forward/backward
factorization agreement, collision probability vs. brute-force pair
enumeration, `P_{N,0}=1`/`P_{N,N}=1/A_N`, monotonicity in `k`, exact
near-tie barrier decisions, floor/ceiling conventions, cyclic-rotation
orbit accounting (including the imprimitive-word double-counting guard),
and reproducibility of every reported table. **Two real bugs were caught
and fixed by this test suite during development**: (1) the Dyck-path
collision function initially used an unrestricted binomial instead of a
ballot-constrained forward count, producing an impossible probability > 1,
caught by `test_collision_probability_hand_example_n1`; (2) the confined-
word forward DP was initially not exploiting monotonicity of the
confinement test in the digit value, making it intractable past `N~400`
(a performance bug, not a correctness bug, caught by direct benchmarking).

Benchmark (informing the N-ranges used throughout): `confined_count_
forward_dp` at `c=0`: N=100 (0.01s), N=200 (0.11s), N=400 (1.15s), N=800
(12.5s) — roughly 10x per doubling; this bounded the practical ceiling for
the dense regression (N<=400 for the primary sweep) and the coarse
asymptotic table (N<=800/1600/3200 for the unrestricted-shell-only checks,
which do not require the DP).

## 20. Git status confirmation

```
$ git status --short   (AFTER this audit)
?? EOC/TaoLike/CylinderDigitCounting.lean   (pre-existing, untouched)
?? EOC/TaoLike/PersistenceRateCramer.lean   (pre-existing, untouched)
?? experiments/                             (NEW, this audit)
?? explorations/                            (pre-existing, untouched)
?? tests/                                   (NEW, this audit)
?? results/                                 (NEW, this audit)
?? docs/CATALAN_CONTROL_AND_LIMITS.md       (NEW, this audit)
?? docs/COLLISION_RATE_PROOF_OBLIGATIONS.md (NEW, this audit)
?? docs/CONSTRAINED_WORD_THEOREM_AUDIT.md   (NEW, this audit)
?? docs/PROMISING_LEMMAS.md                 (NEW, this audit)
```
**Nothing was committed, pushed, rebased, reset, or cleaned.** All new work
is untracked, in new files, exactly as required.
