# Catalan control: what transfers and what does not

Companion to `docs/CONSTRAINED_WORD_THEOREM_AUDIT.md` §5-7. Full data in
`results/constrained_word_asymptotics/catalan_barrier_control.json` and
`catalan_run.log`.

## T1 (proved): the generic DP specializes exactly to Catalan numbers

`experiments/catalan_barrier_control.py::dyck_forward_dp` is the SAME
forward-DP architecture as `confined_count_forward_dp`, specialized to
`{-1,+1}` steps, barrier `height>=0`, fixed endpoint `0`. It matches
`catalan_exact(n) = C(2n,n)/(n+1)` exactly for all 25 tested `n` in
`{0,...,20,30,50,75,100}`, including `n=100` (a 60-digit integer, matched
digit-for-digit). **This is an exact combinatorial identity, not an
asymptotic match, and is the cleanest formally-provable result in this
entire audit** — the two counting procedures (Catalan closed form; the
generic prefix-conditioned forward DP) are proved equal by construction
(both count exactly the same set: nonnegative-partial-sum sequences of
`n` up-steps and `n` down-steps).

## Exact survival-fraction law (not merely asymptotic)

`C_n / C(2n,n) = 1/(n+1)` **exactly**, for every `n` (verified via
`Fraction` equality for `n=1..19`). This is the clean closed-form special
case of the general "survival-cost ~ n^-1" phenomenon Phase II asked to
identify — here it is not just an asymptotic rate but an exact rational
identity, because the Catalan formula's denominator `(n+1)` IS the exact
reciprocal survival fraction.

## The three-way decomposition (bridge x positivity = total correction)

| n | bridge correction (vs. `2n`) | positivity-extra correction | total |
|---|---|---|---|
| 10 | -2.505 | -3.459 | -5.964 |
| 20 | -2.996 | -4.392 | -7.388 |
| 40 | -3.491 | -5.358 | -8.849 |
| 80 | -3.989 | -6.340 | -10.329 |

Doubling `n` moves the bridge correction by ≈-0.5 bits (consistent with
`-0.5 log_2 n`, the ordinary bridge/local-limit cost) and the positivity-
extra correction by ≈-1.0 bits (consistent with an ADDITIONAL `-log_2 n`
cost on top of the bridge cost) — their sum moves by ≈-1.5 bits per
doubling, exactly the classical Catalan `n^{-3/2}` correction
(`C_n ~ 4^n/(n^{1.5} sqrt(pi))`). **This numerically confirms the
requested decomposition `n^{-1/2} (bridge) x n^{-1} (positivity) =
n^{-3/2} (total)` for the Dyck-path control model.**

## What does NOT transfer to the valuation-word problem

1. **The classical cycle lemma's exact rotation count.** Dyck steps are
   bounded (`{-1,+1}`); valuation digits are unbounded positive integers.
   `docs/PROMISING_LEMMAS.md` gives the explicit counterexample showing
   the natural generalization fails outright (1.34% success rate, not
   100%).
2. **A single stationary collision rate, even in the CONTROL model
   itself.** The Dyck-path collision computation (`collision_probability_
   exact` in `catalan_barrier_control.py`, corrected after an initial bug
   — see §19 of the main report) shows `-log_2(P)/k` is clearly
   theta-dependent for the Dyck-bridge problem too: it rises from small
   values to a maximum near theta≈0.5-0.67 (≈0.90-0.91 bits) and DECREASES
   again toward theta=1 (≈0.86 bits) — a genuinely non-monotone-in-theta
   rate-function shape for the SYMMETRIC bridge case (different in detail
   from the valuation-word problem's monotone-increasing shape, since the
   Dyck bridge is symmetric around its midpoint while the valuation-word
   problem has no such symmetry). **This means Phase II's own control
   experiment already refutes a "stationary R_2" expectation before the
   harder problem is even reached — an important calibration for how
   surprised to be by the harder problem's own theta-dependence.**
3. **Exact rational survival fraction.** The valuation-word problem's
   `A_N/U_N` shows no sign of an exact rational closed form analogous to
   `1/(n+1)`; its measured exponent (`gamma≈0.78-1.0` depending on `c`)
   does not match Dyck's exact `gamma=1`.

## Labels

- T1 (exact DP-Catalan match): **PROVED IN THIS AUDIT** (exact
  combinatorial identity, exhaustively checked to n=100).
- Survival fraction `1/(n+1)`: **EXACT IDENTITY** (classical, re-derived).
- `n^{-1/2} x n^{-1} = n^{-3/2}` decomposition: **COMPUTATIONALLY
  CONFIRMED** (numerically verified to the precision tested; the classical
  asymptotic itself is a KNOWN STANDARD RESULT, re-derived and verified
  here, not claimed as new).
- Theta-dependence of the Dyck collision rate: **COMPUTATIONALLY
  CONFIRMED, new within this audit's own control experiment** (not found
  stated explicitly in the pre-existing repository material).
- Non-transfer of the cycle lemma and of a stationary collision rate:
  **NEGATIVE RESULT, new within this audit.**
