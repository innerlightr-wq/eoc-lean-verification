# Equidistribution horizon beyond the fresh-bit regime (2026-09-14)

Nothing committed or pushed. New Lean: `EOC/ExceptionalPowerBound.lean`, `EOC/SplitPrefix.lean`
(imported in `EOC.lean`; full `lake build` passes, 2280 jobs; standard axioms only).

Data (this directory): complete exit histograms per dyadic scale — c=0 through 2^40
(`hist_U0_2p40.txt`), c=1,2 through 2^38; random-block samples (2^34 seeds each) at scales
2^44–2^60 (c=0) and 2^44–2^52 (c=1,2). Tools: `survivor_hist.c`, `horizon.py`, `horizon2.py`,
`shells_local.py`, `samples.py`, `shell_q.c`, `word_fourier.c`, `cluster_forest.py`,
`onorbit_c.py`.

## Headline

* **No intrinsic horizon detected (COMPUTATIONAL).** `Q_X(N,c)` stays within clustered-Poisson
  noise of 1 at every depth where the expected count `M ≥ 10`, for c=0,1,2, X ≤ 2^40 (exhaustive)
  and 2^44–2^60 (samples): rms `z = E·√M` ≈ 1.2–2.4 (c=0), 1.8–3.9 (c=1), 2–5.5 (c=2), i.e.
  `≈ √D` with D the cluster size; short-block samples are Poisson (rms z 0.6–1.3). The empirical
  `A_ε(X)` grows with X (ε=0.01, c=0: 1.1 at 2^20, 2.6 at 2^26, 4.6 at 2^34, 5.7 at 2^40) and
  the exit from the band happens where the Poisson σ reaches ε — the horizon is noise-limited,
  consistent with `A_ε(X) → 1/I₀ ≈ 12.6` as X → ∞. No collapse in A; collapse in M.
* **No theorem goes beyond 1/α (PROVED MATH + audit).** The exact residue-discrepancy identity
  reduces `Q → 1` to *local* (small-interval) equidistribution of least realizers at scale
  `X/2^{S+1}`. Global star discrepancy of random-like quality only reaches `A ≈ 1.20`; Tao's
  Prop 1.9 (repo hypothesis) reaches only `A ≤ 1/(2+c₀) < 1/2`; ResidueTV/HarmonicAP are
  fresh-bit budgets; pair/Rényi-2 data cannot fix first moments. LEVEL 1.
* **Lean:** baseline `#(E_U ∩ [0,X)) ≤ C_U X^{H₂(1/α)}` with explicit `C_U`
  (`exceptional_count_le_rpow`), the conditional theorem "first moment at depth `A log₂X` ⇒
  exponent `1 − I₀A`" (`exceptional_count_le_of_firstMoment`), and the split-depth bijection
  (`prefix_bijective`, `pair_shared_survival`).
