# Pressure as the single isolated input (round of 2026-09-16, post-ShapeTail)

Nothing committed or pushed.  New Lean: `EOC/AverageOddDark.lean` (imported by `EOC.lean`;
`lake build EOC` = 8800 jobs; axioms `propext, Classical.choice, Quot.sound`; no sorry/native_decide).
Scripts/data: `threshold.py` → `THRESHOLD.txt`, `lowershells.py` → `LOWERSHELLS.txt`.
**Positive stop condition 1 fired** (`AverageOddDarkPressure ⇒ CriticalWhiteCount` PROVED (LEAN));
the arithmetic pressure attack (dangerous cylinders, discrete-log statistics, λ = 17) was not started.

## PROVED (LEAN)
* `shapeTail_allEven_budget` — unconditional ShapeTail for any N₀, K with K + ⌊31j/100⌋ + ⌊σ/(N₀+2)⌋ ≤ j/2.
* `AverageOddDarkPressure b j σ t U d s θ C := OddDarkPressure … (2^{C log₂ j + θ j})`.
* `oddDarkPressure_of_average` (LogAbsorb, j ≥ (3C/(θ'−θ))²).
* `criticalWhiteCount_of_averagePressure`, `criticalWhiteCount_rate`, `criticalWhiteCount_N30`, `_N100`.
* `shellP_nonempty`, `one_sub_cos_ge`, `kappa_pow_le_exp` (κ(d,N₀)^{2k} ≤ exp(−8kd²/N₀)).
* `lowFreqDecay_of_averagePressure` (constant 4, explicit γ).

## Threshold (PROVED MATH from the Lean hypotheses; `THRESHOLD.txt`)
Sufficient: θ(s) < (K_max(N₀) − k/j)·log₂((1+s)/2), K_max = 0.19 − 317/(200(N₀+2)).
At s = 3: 0.058 (N₀=10), 0.1405 (30), 0.1745 (100), → 0.19.  **With the published K = ⌊j/25⌋ it would be 0.04,
below the measured true pressure 0.048 — the budget generalization is what makes the chain usable.**
Measured global true pressure (COMPUTATIONAL, Tao-black, J = 1200): 0.048 at s = 3 → margin ×3–3.6.
γ from the chain at d = 1/108: ≈ 1e-7 – 3e-6 bits/step (tiny, positive).

## Remaining non-pressure inputs downstream (audit)
* `weightedFourier_of_lowFreqDecay_and_sieve`: `Nsplit`, `hN1`, `hNj` (elementary once Nsplit chosen), `hX`
  (elementary estimate on `Xmax`), `hfin` (genuine quantitative sieve/shell inequality).
* `weighted_phi_decay_implies_exceptional_bound` needs WeightedFourier (or the trivial branch) for **all shells
  σ < K at barrier offset U**; ShapeTail is proved only at σ = ⌊jα⌋, U = 0.  The same certificate holds exactly for
  σ ∈ [1.40j, top] at j = 300…2400 (`LOWERSHELLS.txt`, COMPUTATIONAL); lower shells must go to the trivial branch
  via `hweight` (OPEN bookkeeping).
