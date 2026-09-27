# Collatz–Wielandt relaxation, and a direct-Collatz audit (round of 2026-09-16, part 6)

Nothing committed or pushed.  Lean: `EOC/LocalWindow.lean` extended (`val_succ`, `val_le_of_superEigen`);
`lake build` 8790 jobs, 0 errors, standard axioms, no sorry.  Scripts/data: `cw.py` → `CW.txt`.

## Goal A — removing the supremum (Parts V–VII, XXV–XXX)

**The relaxation (PROVED (LEAN), `val_le_of_superEigen`).**  The window product bound does not need
`sup_S M_K(S) ≤ 2^{2Kθ}`.  It suffices to exhibit a positive weight `h` with
  ∑_y w(l,x,y)·h(l+1,y) ≤ M·h(l,x)   for all layers `l` and states `x`   (Collatz–Wielandt),
and then `val w l n x ≤ M^n·h(l,x)/c` with `c ≤ h` at the final layer.  `h ≡ 1` recovers the old sup bound.
Adversarial start states are then allowed provided `h` is large there — no state has to satisfy the bound
pointwise.  Crucially `h` may be **local**: `h = M_K` depends on the next window's `O(K)` digits only.

**Numerics (COMPUTATIONAL, `CW.txt`, s = 3, sampled anchors).**  With `h = M_K` the effective per-window
exponent is `max_S log₂(M_{2K}/M_K)(S)/(2K)`:
| J | c₀ | P_K^sup | **P_K^CW** | P_K^bridge (weighted) |
|---|---|---|---|---|
| 200 | 4 | 0.1105 | **0.0464** | 0.0368 |
| 400 | 4 | 0.1048 | **0.0948** | 0.0587 |
| 800 | 4 | 0.1105 | **0.1034** | 0.0823 |
| 200 | 6 | 0.0477 | **0.0338** | 0.0281 |
| 400 | 6 | 0.0775 | **0.0680** | 0.0448 |
| 800 | 6 | 0.0837 | **0.0768** | 0.0666 |
| 400 | 8 | 0.0667 | **0.0592** | 0.0456 |
| 800 | 8 | 0.0790 | **0.0747** | 0.0575 |
The CW value is always below the sup (by a factor 2.4 at J = 200, c₀ = 4; by 5–10 % at J = 800), and the
bridge-weighted value is lower still.  High-pressure states (`M_K > 2^{2K·0.10}`) are absent at c₀ ≥ 6 in every
sampled anchor; at c₀ = 4 there are 2–11 of them out of 273–4035 states, with maximum bridge mass 0 to 4·10⁻².
All three quantities stay below the admissible θ_max = 0.137 (s = 3, β = 0.3), so the payoff (≈ 0.021–0.028
bits/step) survives with either formulation.

**What this does and does not buy.**  It removes the *pointwise* obstruction (Part XX's refutation of arbitrary
local residues no longer blocks the route: bad residues are absorbed into `h`).  It does not reduce the number
of conditions: a super-eigenvector inequality is still required at every state, so the condition count stays
`O(J²/K)`; what changes is that each condition is much weaker.  A genuinely `O(J/K)`-condition version would need
the tilted state distribution to be controlled (Part XXVI), which is not established.

## Goal B — direct-Collatz audit (Parts XXXI–LIII)

**Descent criterion (PROVED (LEAN), existing repo).**  `HarmonicPacking.orbit_mul_two_rpow_R`:
`m_n·2^{R_n} = m_0·U_n`, `U_n = ∏_{k<n}(1 + 1/(3m_k)) ≥ 1`, with `R_n = ∑_{i≤n}(a_i − log₂3)` the **centered**
drift.  Hence `m_n < m_0 ⟺ R_n > log₂U_n` (`UpperEscape.R_gt_iff`, `upper_exit_of_descent`).
**Non-descent = confinement (PROVED (MATH)).**  If `m_i ≥ m_0` for all `i < N` then `R_i ≤ log₂U_i ≤
N/(3 m_0 ln 2)`, which for `N ≤ m_0` is `< 0.5`: the valuation word of the seed is confined under an upper wall
at height O(1) — exactly the confined ensemble this whole program analyses.  So
  descent within N  ⟸  no confined word of length N is realized by a seed ≤ m.
**Why the Fourier route cannot close this (PROVED (MATH) obstruction).**  `SurvivorCounting.card_seeds_le_sum`
bounds the seeds below `X` whose length-`N` prefix is confined by `∑_{w confined}(X·2^{−S_N(w)−1} + 1)`.  The
`+1` per word — each word's realizer progression contributes its smallest element — means the bound is never
below `|W_c(N)| ≥ 1`, no matter how strong the analytic input.  **Counting/Fourier input (hence
LocalWindowPressure, CriticalWhiteCount, WeightedFourier, EOC) yields density statements and cannot by itself
give "every seed descends".**  What direct descent needs instead is a **pointwise realizer floor**
`r_min(N) ≥ 2^{εN}` (the smallest seed realizing any confined word of length `N`), which then gives
`L_c(m) ≤ C log₂ m` and descent within `C log₂ m` steps, and Collatz by minimal-counterexample induction plus a
finite check below `m_*`.
**Where the repo stands on the pointwise side.**  `LogCorridor.logFloor_window_bound'` gives, unconditionally,
`N^{8/9−B} ≤ 3e^{7/9}2^C·M` for orbits with a *lower* floor `R_k ≥ −B log₂(k+1) − C`; `exits_logCorridor`
(B < 8/9, unconditional) and `UpperEscape.exceptional_class` exclude infinite corridor confinement.  These are
polynomial-strength and/or infinite-time statements; the exponential floor needed for logarithmic descent is not
available.  So the gap for direct Collatz is **polynomial → exponential realizer floor**, and it is orthogonal
to the analytic (Fourier) input this program has been building.
**Other endpoints tested.**  Divergent-orbit sparsity (Part XL–XLI): local pressure constrains the valuation
word of a confined prefix, not the arithmetic sizes `m_n`, so no contradiction with García–Tal/Curry sparsity is
produced.  Cycles (Part XLII): a cycle's valuation word is periodic and already covered by
`three_pow_lt_two_pow_of_evPeriodic_orbit`/`R_periodic`; local pressure adds nothing there.  Good windows and
drift (Parts XXXV–XXXIX): the pressure statistic is a function of the *colours* of cells visited, and is
invariant under changing the environment while keeping the word — so it carries no information about the pair
sums `d_{2r+1}+d_{2r+2}` of the word itself.  **Route REFUTED**: good local pressure does not bias drift.

## Status
* PROVED (LEAN) this round: `val_succ`, `val_le_of_superEigen` (Collatz–Wielandt window bound).
* PROVED (MATH): non-descent ⟺ upper-wall confinement; the `+1` obstruction showing counting cannot give
  pointwise descent.
* COMPUTATIONAL: the CW/bridge/sup table above; high-pressure-state masses.
* REFUTED: "good local pressure ⇒ positive drift"; "LocalWindowPressure ⇒ descent" as a direct implication.
* OPEN: LocalWindowPressure for the true orbit (unchanged); exponential realizer floor (for direct Collatz).
* Best rigorous γ = 0; A > 1/α not proved; LEVEL 1.
