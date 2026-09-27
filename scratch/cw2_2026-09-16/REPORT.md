# Track A (super-eigenvector) and Track B (realizer floor) — round of 2026-09-16, part 7

Nothing committed or pushed.  No new Lean this round (the CW theorem `val_le_of_superEigen` landed in part 6).
Scripts/data here: `cw2.py`, `cw2env.py`, `dense.py`, `denseenv.py` → `CW2.txt`.

## TRACK A — local super-eigenvector

**A1–A2 (operator, digits).**  One-block operator (killed P* pair chain, tilt `s` at black own odd cells)
`(T_r f)(S) = Σ_{S2} [Σ_{x admissible} s^{black(m−x,2r+2)}] p²q^{S2−S−2} f(S2)`; a K-window is `T_{r}⋯T_{r+K−1}`.
Local state (per start state): `U₀ ∈ [−1/2,1/2]` to precision `3^{−O(K)}` plus the `2K` new digits; measured
depth `L(K) ≈ 3K` ternary digits (16 leading digits sufficed at K = 14–16 to pin `P_K` to 10⁻⁴).

**A3, A7–A9 (analytic h): REFUTED.**  One-block CW with weights that are functions of the predictable black
probability `Q` fails badly (per-step bits, J = 200, s = 3, θ_max = 0.137): `h ≡ 1`: 0.792; `h = exp(aQ)`:
0.770 (a = 0.5) rising to 3.88 (a = 6); `h = 1 + bQ`: 0.768 (b = 1) rising to 1.84 (b = 16).  Reason: inside a
triangle `Q ≈ 1` at every block, so a `Q`-function is constant along the run and cannot pay for the `s` factor
per block; the weight must know **how much longer the black run continues**, i.e. a look-ahead.

**A4–A6, A11–A13 (look-ahead h = M_K, fixed K).**  With `h = M_K` the effective per-window exponent is
`max_S log₂(M_{2K}/M_K)(S)/(2K)`:
| K | J = 200 | 400 | 800 | 1600 |
|---|---|---|---|---|
| 8 | 0.150 | 0.292 | 0.243 | 0.275 |
| 16 | 0.077 | 0.150 | 0.165 | 0.154 |
| 24 | 0.056 | 0.114 (dense 0.117) | 0.107 (dense 0.121) | 0.108 |
| 32 | 0.033 | 0.095 (dense 0.099) | 0.104 (dense 0.097) | 0.106 |
Global pressure for reference: 0.031, 0.041, 0.042, 0.052.  **At fixed K = 32 the CW value stabilizes near
0.10 across J = 200…1600, below θ_max = 0.137** — i.e. numerically K does *not* need to grow with J once CW is
used (COMPUTATIONAL; anchors sampled at stride 2–5, states exhaustive).  This would remove both the `K ≍ log J`
requirement and the `O(J²/K)` union bound of the sup formulation.
Rational certification (A6) was not attempted: see A14, which shows there is nothing universal to certify.

**A10, A14 (worst transitions, environment dependence): the obstruction persists.**  Max CW at K = 32, J = 400:
| environment | max CW |
|---|---|
| ξ = 1 (true) | 0.099 |
| λ = 5 | 0.119 |
| greedy adversary, triangle depth ≤ 3.18 | 0.135 |
| greedy adversary, triangle depth ≤ 8 | **0.374** |
A unit whose triangles are no deeper than the true environment's (depth ≤ 8 vs the true 4.7–6.7) violates the CW
bound by a factor ≈ 3.  So **no fixed-K bound holds for all units, and triangle-depth control still does not
suffice** — consistent with the earlier refutation, now at the level of the CW inequality.  Worst transitions are
always states sitting inside a black run.
Consequence for A11–A13: fixed K works *for the true environment in the tested range* but cannot be universal;
since CW-bad local residues have positive density, a fixed K must eventually fail as J → ∞ unless the true
environment avoids them — which is again the open arithmetic statement, though now at fixed modulus `3^{O(K)}`.

**A15–A19 (skew product, Lean).**  The skew-product formulation (path state × local environment, the environment
evolving deterministically by `ξ ↦ 2^{−Δ}ξ`) is the natural home for a joint certificate, but with bad residues
present its Perron radius is ≥ the adversarial value 0.374, so a joint gap does not exist at K = 32.  Lean status
unchanged: `val_le_of_superEigen` is proved and ready; instantiation awaits an operator with a certified gap.
Best rigorous γ = 0; A > 1/α not proved.

## TRACK B — realizer floor and direct Collatz

**B1–B2, B4–B10 (the weakest sufficient floor) — PROVED (MATH).**  With the repo's identity
`m_n·2^{R_n} = m₀·U_n` (`HarmonicPacking.orbit_mul_two_rpow_R`), `R_n = Σ(a_i − log₂3)`, `U_n = ∏(1+1/(3m_k))`:
* non-descent up to N (`m_i ≥ m₀`) gives `R_i ≤ log₂U_i ≤ N/(3 m₀ ln 2)`;
* hence if `m₀ ≥ N/(3c ln 2)` the length-N word is **c-confined**, so `m₀ ≥ r_min(N,c)`.
Taking `N = ⌊3c ln 2·m₀⌋`, a floor `r_min(N,c) ≥ A·N` forces `m₀ ≥ A·3c ln2·m₀`, a contradiction as soon as
  **A > A_crit(c) = 1/(3c ln 2)**  (A_crit = 0.4809 at c = 1, and 0.481/c in general).
So **a linear realizer floor suffices for descent of all large seeds, hence for Collatz after a finite check** —
exponential growth (B1) is far more than needed, and so is any superlinear polynomial rate (every γ > 1 works).
**Not circular:** confinement is strictly weaker than non-descent (a seed may descend while keeping `R_i ≤ c`),
so `r_min(N,c) ≥ A·N` is a strictly stronger statement than the descent conclusion it implies; the converse does
not hold.  Empirically `log₂ r_min(N,1) ≈ I₀N`, so the target has an enormous margin.

**B6, B16–B17, B39–B46 (do existing results give it?): REFUTED for this sector.**  `logFloor_window_bound'`
(`N^{8/9−B} ≤ 3e^{7/9}2^C·M`) and the Curry/collision-free packing arguments need the orbit values to lie in a
**bounded interval**, which requires a *lower* floor on `R_i` (the divergent sector).  In the non-descent sector
the constraint is the opposite: `R_i ≤ c` gives `m_i ≥ m₀2^{−c}` — the orbit is bounded **below** and completely
unbounded above, so the interval width is not controlled and no packing inequality applies.  The derived
polynomial exponent is therefore *none*, and the promising-looking B43 computation cannot be started.

**B48 (reciprocal sums).**  Non-descent gives `Σ_{i<N} 1/m_i ≤ N/m₀`, which for `N ≍ m₀` is O(1) — no
contradiction with divergent-orbit summability.

**B12–B15, B18–B38 (anchor DP, complexity, minimizers).**  Not run this round (the A-track experiments consumed
the budget); they remain the natural next numerical step, now with the *linear* target rather than exponential.

**B49.** Ranking of direct-Collatz targets by viability: (1) linear realizer floor `r_min(N,c) ≥ 0.49N` — the
weakest sufficient statement and empirically true with an exponential margin; (2) small-realizer ⇒ low symbolic
complexity; (3) finite-state anchor exclusion; (4) exponential floor (unnecessarily strong); (5) collision-free
interval packing — refuted in this sector; (6) Fourier/counting — refuted in part 6 (the `+1` per word).

## Status
* PROVED (MATH) this round: the exact linear threshold `A_crit(c) = 1/(3c ln 2)` and the implication
  linear floor ⇒ descent ⇒ Collatz after a finite check; the strictness (non-circularity) of that target;
  the failure of packing arguments in the non-descent sector.
* COMPUTATIONAL: the fixed-K CW tables; the refutation of Q-only analytic weights; the adversarial CW values.
* REFUTED: analytic `h = f(Q)`; universal fixed-K certification; triangle-depth control for CW; Curry packing
  for non-descent.
* OPEN: a certified local super-eigenvector for the true environment (Track A); the linear realizer floor
  (Track B).
* Best rigorous γ = 0; A > 1/α not proved; Collatz not proved.  LEVEL 1.
