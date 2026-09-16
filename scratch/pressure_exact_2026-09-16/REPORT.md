# The exact odd-dark pressure observable (round of 2026-09-16, post-AverageOddDark)

Nothing committed or pushed.  Lean: `EOC/AverageOddDark.lean` extended (§7: `fewGood_le_single`,
`lowFreqDecay_of_shape_and_summedPressure`, `SummedOddDarkPressure`, `summed_of_average`,
`lowFreqDecay_of_summedPressure`); `lake build EOC` = 8800 jobs; standard axioms only.
Scripts: `pexact.py` (engine), `validate.py`, `corpus.py` → `corpus_J.json`, `analyze.py` → `CORPUS_SUMMARY.txt`,
`dscan.py` → `DSCAN_400.txt`, `pareto.py` → `PARETO.txt`, `lam17.py` → `LAM17.txt`, `supereig.py`.

## Formal target
* PROVED (LEAN): `SummedOddDarkPressure ⇒ LowFreqDecay` (no λ-uniformity; `LowFreqDecay` sums over λ ∈ cshell).
* Needed: for even j ≥ max(300, (3C/(θ'−θ))²), every t, every u ≤ U:
  ∑_{λ∈cshell u} ∑_{P∈shellP} 3^{N_odd} ≤ 2^{u+1}·2^{θj + C log₂ j}·|shellP|, θ < 0.1745 (N₀ = 100).

## Observable (PROVED MATH / exact code)
* N_odd(P) = #{r : S_{2r+1} eligible (S_{2r+1}+1 < S_{2r+2}, ≤ b(2r+1)) and ‖λ·3^{−(2r+2)}·2^{S_{2r+1}}/2^m‖ < d}.
* Class DP: Z = e₀ᵀ L₀⋯L_{R−1} e_σ, L_r(x,y) = |B| + (s−1)·#{eligible dark z ∈ B}; exact big integers, O(j·σ).
* Exact telescoping block weights w_r = log₂(Φ_{r+1}/Φ_r), Φ_r = ⟨f_r^{tilted}, g_r^{untilted}⟩, ∑ w_r = log₂(Z_s/Z_1).
  w_r is non-local (bridge + past tilt).
* Reciprocity: Dark(λ, d) ⇔ ‖λ·centered(2^{−(m−z)} mod 3^b)/3^b + ε‖ < d; exact 3-adic switch when 2^{m−σ} > Dλ
  (parity: D|c| ≠ 3^b for even D).  0 mismatches in 3.2·10⁶ cells.
* N_odd(λ, 1/108) ≤ N_Tao-black(ξ=λ, 1/54) for all low λ (PROVED MATH); old measurements are upper bounds (for t = J/6).
  Exact factors at J = 1200, ξ = 1: surrogate 0.0480 → eligibility 0.0183 (d=1/54) → d = 1/108: 0.0093.

## Computation (exact moments; certified comparisons by integer arithmetic)
* 6720 true-family instances (J = 200/400/800/1600, odd λ ≤ 511/511/255/63, t ∈ {0,1,2,3,7,J/6,J/2,J,5J,10⁶+3}):
  **all certified < 17/100 and < 1/6** at d = 1/108 and d = 1/54.  Max P: 0.0343 (J=200), 0.0200, 0.0144, 0.0119
  (d = 1/108); telescoped window rates max 0.103 (K=16), 0.080 (24), 0.062 (32), 0.046 (64), 0.025 (128); none > 0.17.
* d-scan (J = 400): max P ≈ 0.9·2d; below 0.17 up to d = 1/6 (0.158), above at d = 1/4 (0.215).
* λ = 17, J = 1600: Lean observable P = 0.0087, K=64 window 0.015; surrogate exact telescoped K=64 0.071 — the old 0.142
  was a sup-over-states killed-chain artefact.
* REFUTED universality: all-dark pattern gives 0.357–0.363 (certified > 0.17); the 3-adic unit ξ ≡ 2^m gives
  0.32–0.35 (certified); greedy black-adversary gives 0.126 (below).  So no environment-universal window, cycle-mean
  or super-eigenvector certificate below 0.17 exists; state-only h = β^{σ−x} certificate: 0.19 (J=200), 0.24 (J=400).

## Local depth (PROVED MATH)
A K-block window from a start state at distance ≤ h₀ below the barrier reads rows b ∈ [b₀, b₀+2K] and columns spanning
≤ h₀ + 2αK; flags are fixed by the ternary digits of ξ2^{−a₀} in positions [b₀ − L, b₀ + 2K) with
L = ⌈(h₀ + 2αK + log₂ D + g)/log₂ 3⌉ except for a 2^{−g}-fraction of boundary cells, i.e.
D(K) ≈ 4K + 0.63h₀ + 4.3 + 0.63g (not 3K); no finite depth certifies every cell (threshold-boundary cells).

## Classification: C (sparse dangerous set + arithmetic of λ2^{−m}); D-type evidence (global moment ≈ Haar-generic
median 0.009, max 0.034; margin 5× worst case, 18× median).  Dangerous cylinders are non-empty for every K (all-dark cylinder); certified
branch-and-bound was not run.  AverageOddDarkPressure remains OPEN.

---

# Addendum — operator certificates, kernel bridge, dangerous windows (same day, later round)

**Positive stop condition 4 fired: the pressure class-to-kernel bridge is PROVED (LEAN)** (`EOC/PressureBridge.lean`,
imported by `EOC.lean`; `lake build EOC` = 8801 jobs; axioms `propext, Classical.choice, Quot.sound`).
Scripts: `geo.py` (geometric operator, O(σ) recurrences), `geo_validate.py`, `geo_scan.py` → `GEO_SCAN.txt`,
`trend.py` → `TREND.txt`.

## PROVED (LEAN)
* `sum_pow_nodd_eq_class`, `class_prod_le_ker`, `ker_geo_eq` (exact: ker geoW = p^{2n} q^{z−x−2n} ker W),
* `sum_pow_nodd_le_geo`: ∑_P s^{N_odd} ≤ (σj/p)·ker(geoW p q oddW)(0→σ)·|P_σ|, p = (j−1)/(σ−1), q = (σ−j)/(σ−1);
* `sum_pow_nodd_le_windows`: window form via `LocalWindow.val_le_of_window_rem`.
Loss log₂(σj/p) ≈ 2 log₂ j + 1.3 bits (polynomial).

## Route A (super-eigenvector)
* Level 1 (h ≡ 1, geometric): 0.19–0.23 (j = 400), 0.25–0.29 (j = 800) — REFUTED, grows with j.
* Any certificate valid for all phase sequences is valid for ξ ≡ 2^m (exact pressure 0.32–0.35): universal
  phase-aware / K-block / cylinder certificates below 0.17 are REFUTED (PROVED MATH).
* u = 0: cshell = {1, 2^m−1}, identical dark sets ⇒ frequency summation gives no averaging (PROVED MATH).
* Finite-depth reachability: 2 is a primitive root mod 3^D, so every unit residue is reachable by some shift m
  (PROVED MATH); the dark test reads top digits, so reachability pruning does not produce a finite quotient.
* Level 4 per environment (K-window sup-norm, floats): 0.030–0.067 for all 40 true and 8 Haar environments —
  COMPUTATIONAL, not certified.

## Route B (windows)
* Dangerous-window ceiling: one block ≤ 1 + 2q′ ⇒ ≤ ½log₂(1+2q′) < 0.40 bits/step for j ≥ 157 (PROVED MATH).
* Allowed dangerous fraction (asymptotically, θ = 1/6): φ ≤ (1/6 − θ_d)/(0.40 − θ_d):
  θ_d = 0.05: 0.333; 0.08: 0.271; 0.10: 0.222; 0.12: 0.155; minus the bridge loss (2 log₂ j + 1.3)/j.
* Fixed K fails asymptotically (COMPUTATIONAL, `TREND.txt`): fraction of K = 8 windows above 0.10 is
  0.057/0.10/0.16/0.28 at j = 400/800/1600/3200 (∝ j: the sup over start states ranges over ~j columns);
  K = 16: 0/0/0.0025.  So K must grow like log j.
* True and Haar environments are statistically indistinguishable in all window statistics.
* Certified cylinder enumeration, discrete-log statistics: not run (stop condition).
