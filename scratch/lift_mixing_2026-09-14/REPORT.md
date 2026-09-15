# Lift-digit / carry mixing and the first-moment bound (2026-09-14)

Nothing committed or pushed. New Lean: `EOC/LiftDigits.lean`, `EOC/ResidueDiscrepancy.lean`
(in `EOC.lean`; full build passes, 2282 jobs; standard axioms only).

Tools here: `step_stats.c` (per-step survivor S_j / next-digit / orbit-state statistics over all
odd μ < 2^HI), `product_formula.py`, `state_uniformity.py`, `prefix_conditional.py`,
`word_state.c`.

## Headline

* **Exact structure (PROVED MATH; most in LEAN):** append recursion `r_{j+1} = r_j + 2^{S_j+1}τ_j`,
  block expansion `r_N = 1 + Σ 2^{S_j+1}τ_j`, suffix memory `r_N < 2^{S_j+1} ⇔ r_j realizes the
  whole word ⇔ T^j(r_j) ≡ r(σ^j d) mod 2^{S_N−S_j+1}`, exact residue count, exact dyadic
  decomposition, and the Lean plug `exceptional_count_le_of_leastRealizerBound`.
* **Exact product formula (PROVED MATH):** `Q_X(N) = Π_j (1 + ε̄_j)`, `ε̄_j` = h-weighted relative
  error of the survivors' next-digit law; fresh steps give `ε̄_j = 0` exactly (verified to 1e-16).
  Hence a per-step averaged bias `O(1/log X)` would already suffice — the naive `C_0^N` loss is
  an artifact of pointwise bounds.
* **Uniformity is preserved but never created by the algebra (PROVED MATH):** the state update
  along digit d is an exactly 2^d-to-1 measure-preserving map mod 2^{d+a}; multiplication by 3^j
  permutes residues and maps dyadic cylinders to dyadic cylinders. All 2-adic structure is
  permutation-invariant; the only nontrivial input is the archimedean interval [0, X).
* **Data (COMPUTATIONAL):** per-step increments are martingale noise (z rms ≈ 1, no drift, heavy
  cancellation); survivor orbit states are locally uniform mod 2^k (conditional cell z-rms ≈ 1.00);
  prefix-conditional survival is Poisson-exact over 10^3–3·10^5 prefixes (no exceptional prefixes
  beyond Gaussian tails); word-ensemble states are sub-Poissonian but with no exact balance law.
* **Classification: LEVEL 1** — no theorem beyond 1/α; the minimal missing input is a carry /
  least-realizer-state Weyl-sum bound (Mauduit–Rivat-type), stated precisely in the chat report.
