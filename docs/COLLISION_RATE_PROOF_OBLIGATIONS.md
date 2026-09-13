# Collision-rate proof obligations

Companion to `docs/CONSTRAINED_WORD_THEOREM_AUDIT.md` §9-10. Full data in
`results/constrained_word_asymptotics/prefix_collision_audit.json`.

## What was measured, exactly

`P_{N,k}` := probability two independent, UNIFORMLY drawn words from
`W_c(N,s_N)` agree on their first `k` digits, computed exactly (Fraction
arithmetic) via
```
P_{N,k} = sum_S [ F(k,S) * B(k,S)^2 ] / A_N^2
```
where `F(k,S)` is the exact forward count of length-`k` confined prefixes
reaching partial sum `S`, and `B(k,S)` is the exact backward count of
confined completions from `(k,S)` to `(N,s_N)`. Both computed by
independent recursions (forward accumulation vs. backward completion),
cross-checked against full brute-force pair enumeration for small `(N,s,c)`
— exact match in every tested case (`test_collision_probability_matches_
brute_force_pair_enumeration`).

**This is explicitly NOT the same object as `round2_verification.py`'s
Doob h-transform section (Part C there)**: that computation is the
GEOMETRIC-cylinder-measure survival probability `B(j,S)` (weighted by
`2^{-digit}` per step, from the Geom(2) product measure); this audit's
`B(k,S)` is an UNWEIGHTED completion COUNT (cardinality), used to define
collision probability under the UNIFORM measure on the finite endpoint-
fixed set `W_c(N,s_N)`. The two are related (dividing the count-based `B`
by `A_N` gives a probability) but are answers to different questions:
"how much cylinder-mass survives" (geometric measure) vs. "how many
completions exist" (uniform measure), and this audit's collision
computation is built entirely from the latter, as the task specifies.

## Result: refutation of a stationary R_2

At `N=40, c=0`: `-log_2(P_{N,k})/k` rises from `0` (`k=0`, trivially) to
`~1.27` (`k=N=40`), passing through `~0.98` at `theta=0.5`, with **no
plateau anywhere in the tested range**. A second check across `N in
{20,30,40,50}` at fixed `theta in {0.25,0.5,0.75}` shows the rate is STILL
increasing with `N` at fixed `theta` (e.g. at `theta=0.5`: `0.83, 0.92,
0.98, 1.02` for `N=20,30,40,50`) — **the finite-N data is not yet in an
asymptotic regime, and no claim of convergence to a specific `I_2(theta)`
value is made.** What IS established: (a) the rate is not flat in `theta`
(refutes stationary `R_2`), and (b) the rate at every tested `theta<1` is
well below the base-digit Renyi-2 rate `alpha=log_2(3)=1.585` (refutes
`R_2=alpha` specifically).

## The base-digit comparison, derived from first principles

For the UNCONDITIONED Geom(2) law `P(q)=2^{-q}`, the collision
(Renyi-2) probability is `sum_q 4^{-q} = 1/3` exactly (geometric series,
ratio `1/4`, first term `1/4`), giving Renyi-2 entropy `-log_2(1/3) =
log_2(3) = alpha` **exactly** — re-derived here independently of
`round2_verification.py`'s own identical derivation (Part G there), which
this audit's finding is fully consistent with as a description of the
*unconditioned single-digit* law. **The measured word-level collision rate
is a DIFFERENT, endpoint-and-confinement-conditioned quantity, and this
audit's data shows it does not equal `alpha` anywhere in the tested
range** — the naive identification "collision rate = base-digit Renyi-2
rate" is refuted, not confirmed, by direct computation.

## The one-digit interior marginal

The exact marginal law of digit `j+1` under uniform sampling from
`W_c(N,s_N)` (computed via the same forward/backward count machinery) has
Renyi-2 entropy growing from `0` (at `j=0`, where the first digit is
forced, since the barrier admits only `d_1=1` at `c=0`) to `~1.53` bits at
`j=35` of `N=40` — approaching but not exceeding `alpha=1.585`. **This
depth (`j=35` of `40`) is close to the FAR endpoint, not a generic
"interior/bulk" point** (only 5 steps remain), so this approach toward
`alpha` cannot be cleanly attributed to a bulk/quasi-stationary
phenomenon without testing a genuinely interior depth at much larger `N`
(e.g. `j=N/2` for `N` in the thousands) — **left as an explicit open
computational task, not resolved here.**

## Five analytic formulations attempted (Phase V.4), and their status

1. **Squared completion-count sums.** Executed exactly (this is the
   collision formula itself); gives exact finite-`N` numbers, not a limit.
2. **Bivariate generating functions.** Not executed; the natural object
   would be `sum_{N,S} A_N(S) x^N y^S` restricted to the confined region —
   setting this up rigorously (the region boundary depends on the
   irrational `alpha`, not a rational slope) is exactly the obstruction
   the pre-existing `docs/RESEARCH_CHECKPOINT_2026-09.md` already
   identifies for a related deficit process. **OPEN.**
3. **Transfer operator for two coupled constrained walks.** Not executed.
   The natural formulation: a Markov chain on pairs of states `(S,S')`
   with transition weight `1` (uniform, not geometric) restricted to
   `S=S'` on the diagonal at collision. **OPEN — the correct next
   computational experiment** (see the main report's proof obligation #3).
4. **Perron-Frobenius/spectral-radius via rational barriers.** Not
   executed at full depth; Phase VI (rational/Sturmian approximation) was
   explicitly time-boxed out of this audit round (see main report §11).
5. **Renewal decomposition at boundary contacts.** Not executed. Since
   `c=0` forces `S_j<=0` whenever `S_j<=c`, i.e. the ONLY way to stay
   confined near the axis is `S_j` tracking `j*alpha` tightly, the natural
   renewal points would be returns to a small deficit — this is a
   plausible route but requires the rational-approximation machinery of
   item 4 to make precise. **OPEN.**

## What additional lemma would turn each into a proof

For (3), the transfer-operator route: a proof that the operator's leading
eigenvalue (restricted to the confined region, uniform weights) equals
`2^{-I_2(theta)}` for a well-defined `I_2` would require (a) showing the
restricted operator has a well-defined leading eigenvalue despite the
region's irrational-slope boundary (a genuine technical obstruction, since
the region is not periodic), and (b) an explicit variational formula for
`I_2(theta)` analogous to the already-proved `I_0` Cramer-rate identity
(`explorations/hypercuboid_transfer/scripts/round2_verification.py` Part
F) but for the UNIFORM (not geometric) measure — a different, harder
variational problem since the uniform measure's "tilt" parameter has no
direct probabilistic interpretation the way the geometric measure's does.

## Labels

- Collision definition, exact formula, brute-force cross-check: **PROVED
  IN THIS AUDIT (as an exact finite computation), REPRODUCED against
  brute force.**
- Monotonicity, `P_{N,0}=1`, `P_{N,N}=1/A_N`: **PROVED IN THIS AUDIT**
  (exact identities, each following directly from the definition).
- Theta-dependence / refutation of stationary `R_2=alpha`: **ROBUST
  COMPUTATIONAL RESULT, new within this audit — a genuine negative
  result.**
- Existence and value of a limiting `I_2(theta)`: **OPEN.**
- Interior-marginal approach to `alpha`: **COMPUTATIONAL, inconclusive**
  (confounded with endpoint proximity at the tested `N`).
