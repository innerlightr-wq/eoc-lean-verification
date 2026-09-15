# Continuation characteristic function (round of 2026-09-15, eighth)

Nothing committed or pushed. New Lean (in `EOC.lean`, full build 8781 jobs, standard axioms, no sorry):
`EOC/RenyiBarrier.lean` (geometric Rényi identity + closed form of H_R, prefix-sharing Cauchy–Schwarz bound,
phase-alignment sharpness `aligned_attains`, `sum_sq_le_aligned`, `barrier`), `EOC/DecayInterface.lean`
(dyadic kernel summation `sum_sq_le_of_spacingExponent`, `weightedFourier_of_mixed`, `LowFreqDecay`,
`weightedFourier_of_lowFreqDecay_and_sieve`, `weightedFourier_of_spreading_and_sieve`).

## Structure (PROVED MATH)
Γ_S(λ) = φ_Y(ω(λ)): the characteristic function of the continuation's real Syracuse value Y = Σ_k 2^{S'_k}/3^{k+1}
at ω(λ) = (λ·2^{S−m} mod 3^{N+1+L})/3^{N+1}.  Low-frequency λ-averaging randomizes only frac(ω) = U (the N resolved
digits); ⌊ω⌋ (the continuation's frequency digits) follows the Kronecker sequence λβ — Diophantine.

## Numerics (COMPUTATIONAL)
* Controls (j0=60, u=11, 64 λ): log2 E|Γ|² at L = 53/43/33/23/13: true −79.1/−64.4/−51.2/−35.7/−20.7 (rate 0.75–0.80),
  random digits −81.0/−65.0/−52.8/−35.2/−19.0, frozen high digits −7.8/−11.6/−13.8/−15.8/−5.0 (no growth),
  iid tilted continuation −57.7/−47.8/−35.5/−24.7/−13.4 (rate 0.52–0.56 ≈ H_R/2 = 0.559).
* Log-product Z_r = −log₂W_r² (j0=60/100): mean 2.48 bits/block, var 5.1, P(Z=0)=0.256, |corr| ≤ 0.024 at lags 1–8.
* γ → exponent (asymptotic, K=3200→6400 increments; gammaA.txt): model 1 (plain low-frequency mean-square decay of Φ at rate γ) E ≈ H₂ − 0.0301γ; model 2 (decorrelated continuation decay) E ≈ H₂ − 0.0916γ (small γ); at A=0.7 the full exponent 0.944477 needs γ ≈ 0.25 (model 1) / ≈ 0.1 (model 2). Any γ > 0 crosses H₂ (HEURISTIC asymptotics; numerics resolve γ ≥ 0.005–0.01).
