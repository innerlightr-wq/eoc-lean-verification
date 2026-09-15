# Phase signatures, split-depth covariance, and orbit clustering (2026-09-14)

Nothing committed or pushed. New Lean modules (all imported in `EOC.lean`, full `lake build` passes,
2278 jobs, axioms `propext/Classical.choice/Quot.sound` only):
`EOC/CapacityBounds.lean`, `EOC/SurvivorDensity.lean`, `EOC/EntropyBounds.lean`,
`EOC/SurvivorClusters.lean`. Scratch code/data in this directory.

## Headline

1. **Phase (Q1): LEVEL 1.** The renewal phase leaves no detectable signature in integer realizers
   beyond the ensemble first moment. Integer survivor counts track the phase-modulated `p_N(c)`
   (regression slope on the phase factor `0.000 ± 0.003`, phase-blind alternative `−1`, walls
   c=0,1,2, N=27..150, X up to 2^38 — far beyond the fresh-bit horizon N≈23); per-step hazards
   match in every phase window to 0.2%; least-realizer positions are uniform (even super-uniform);
   normalized pair covariance is phase-free (Haar slope ≤0.065 ⇒ ≤0.6%; empirical 0±0.04); record
   depths' phases match the first-moment law (χ² 11.0/9 on 32768 block maxima).
2. **Split depth (Q2): LEVEL 2.** Exact split-depth survival law (Haar): for `v₂(x−y)=q` the shared
   valuation prefix is **uniform over the 2^{q−1} compositions of sum ≤ q−1**, split digits
   `{g, g+G}` with `G ~ Geom(1/2)`, independent tails. It predicts integer survivor pair
   correlations `C_N(q)` to 0.1–3% (N=60–150, X=2^32, 2^36), beyond the fresh-bit regime.
3. **Clustering is orbit self-overlap, not 2-adic.** survivors/clusters = 2.92 (c=0) universally
   (X ∈ [2^30,2^38], N ∈ [60,250]); 71% of merges are on-orbit (`y = T^i x`), predicted for c=0 by
   `Σ_i W₀(i)/3^i = 1.071` (measured 1.066); 29% are sibling coalescences (`u ↔ 4u+1`). Split depth
   does not predict merging. Extremal index θ=1 for short blocks, θ≈1/2.92 for prefix intervals;
   records follow `exp(−θ(X/2)p_N)` (block maxima: predicted median = observed).
4. **No second-moment obstruction**; quotient-by-merges decays at exactly the ensemble rate.

See the chat report for the 25 numbered answers.
