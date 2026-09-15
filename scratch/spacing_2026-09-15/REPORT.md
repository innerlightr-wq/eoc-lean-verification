# Low-shell spacing exponent (round of 2026-09-15, sixth)

Nothing committed or pushed. New Lean (in `EOC.lean`, full build OK, standard axioms, no sorry):
`EOC/PsiSieve.lean` — the rigorous (C3) 3-adic interval sieve for Ψ itself (`reciprocity`, `X_injOn`,
`prefix_phase_grid`, `psi_split`, `sum_sq_norm_Fpre_le`, `psi_shell_sieve`); `EOC/SpacingChain.lean` — `odd_quotient`,
`pairSpacing`, `sum_sq_le_kernel` / `sum_sq_le_pairSpacing` (spacing ⇒ Fourier shell bound),
`spacingExponent_implies_weightedFourier`; `EOC/PsiShellBound.lean` — `psi_cshell_sieve` (centered shells), `weightedFourier_of_psiSieve` (the rigorous sieve plugged into WeightedFourier). Full build 8778 jobs.

## θ → exponent (asymptotic chain formula; COMPUTATIONAL confirmation to 1e-4 at K = 3200→6400)
E(A, θ) = H₂ − (α/2)(A − 1/α)(θ − H₂), H₂ = 1 − I₀/α = 0.949956.  θ = H₂ neutral for all A; θ > H₂: best at max A.
At A = 1: E = H₂ − 0.29248 (θ − H₂): θ = 0.951 → 0.949651; 0.955 → 0.948481; 0.96 → 0.947018; 0.97 → 0.944094; 1 → 0.935319.

## Elementary barrier (PROVED MATH in the tilted model; COMPUTATIONAL for the confined shell)
Minkowski/(C3) exponent = Rényi-2 digit entropy / α: H_R = −log₂ Σ P*(d)² = 2log₂α + log₂(1 − (1 − 1/α)²) = 1.11765,
θ_M = H_R/α = 0.70516 < H₂.  Pairs sharing the first u/α steps have density 2^{−θ_M u}; any argument that bounds the
continuation sums by their size (|G_S| ≤ g_S) is sharp at θ_M (adversarial-phase model).  Confined DP: 0.64–0.80.

## Numerics (COMPUTATIONAL, exact Φ for all λ < 2^18, j0 = 30…120)
* Fejér pair count E(u)/|P|² = 2^{−u}(1 + excess), excess·|P|/2^u ∈ [0.001, 2.4]: θ_eff(u) = 1.00000 for all u ≤ 18,
  margin over H₂ = +0.05004 constant (no decay).  Shell averages a_u·|P| ≲ 1 (at or below random).
* λ = 1: γ₁ = 0.610, 0.763, 0.714, 0.756, 0.791, 0.727, 0.737 bits/step (j0 = 30, 40, 50, 60, 80, 100, 120) ≈ h/2.
* Prefix-sharing pairs (k = u/α) are close at Haar rate (ratio 0.8–1.2); odd-quotient Rényi deficit ≤ 0.5 bit total.
* Additive energy (J = 10…14): 10–62× the random value, explained by exact tail-swap identities.
