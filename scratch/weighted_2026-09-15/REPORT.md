# Weighted Fourier-energy target (round of 2026-09-15, third)

Nothing committed or pushed. New Lean (in `EOC.lean`, full build 3331 jobs, standard axioms,
no sorry): `EOC/WeightedChain.lean` (β_P = −B_P, collision identification, Ψ = Φ path product,
`weighted_phi_decay_implies_exceptional_bound` — the chain now has exactly one analytic hypothesis
`WeightedFourier`), `EOC/FirstDivergence.lean` (v2(q_P − q_Q) = S_i + min(d_i,d'_i); dyadic-shell
orthogonality; resonance count).

## Tools
* `phi_weighted.c` — exact weighted LHS (all λ < 2^20 exhaustively, higher dyadic shells sampled),
  RHS, ratio R, low-shell L² average A2 with v2/v3 breakdown (320-bit).
* `shellopt.py` — shellwise optimization of the required uniform rate at exact finite K.
* `classes.py` — E_P 2^{-r(P)} = #swap classes/|P| (ideal swap-cube L² rate).
* `pairspacing2.c` — pair-spacing E(q)/Haar of ζ_P = y'_P/2^m (320-bit Horner in q_P).

## Headline
* Exact target (repo-native `WeightedFourier`): (1+(σ+1)/2) Σ_{1≤g<2^t} Σ_{k<2^{σ+1}}
  ‖coef(g+2^t k)‖ ‖Ψ(g+2^t k)‖² ≤ ε² |P_σ|² |V_{σ,s}| / 2^t; ‖coef(λ)‖ = |sin(πλ/2^t)|/(2^{σ+1}|sin(πλ/2^m)|).
* Numerical R = LHS/RHS(ε=1) at the A=0.7 geometry: j0=40: 1.1e-10, 60: 4.9e-17, 80: 1.4e-25, 100: 5.8e-33
  (log2 R ≈ −1.2…−1.4 per step); low-shell L² rate 0.67–0.70 bits/step; no v2/v3 anomaly;
  pair spacing E(q)/Haar = 1.0000 ± 2σ for q ≤ 24 at j0 = 30, 50, 70, 100, 120.
* Ideal L² ceilings: swap cube 0.103–0.120; L-block cubes 0.21/0.32/0.38/0.46/0.51 (L=2,3,4,6,8).
* Shellwise optimization raises the finite-K requirement: γ*(C=2) = 0.25/0.19/0.15/0.13 at
  K = 100/200/400/800 (C=K: 0.14/0.13/0.12/0.11) → 0.0911 + O(K^{-1/2}); trivial counting handles
  < 0.1% of Haar mass.
* Swap-cube L² expansion, full-group orthogonality (exact 2^{-r}), interval discrepancy formula;
  large sieve structurally useless (dense set); exact v3-resonance factorization + entropy tradeoff
  (harmless given generic decay, 4^γ < 3); first-divergence helps only high shells.
* Not proved: the weighted inequality. LEVEL 1.
