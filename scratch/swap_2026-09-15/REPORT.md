# Swap-angle nondegeneracy (round of 2026-09-15, second)

Nothing committed or pushed. New Lean (in `EOC.lean`, full build passes, standard axioms,
no sorry): `EOC/ShellwiseChain.lean` (usable chain — fixes the unsatisfiable uniform hypothesis
of `PrefixCollisionBound`), `EOC/SwapBound.lean` (abstract swap / 2-block inequality and
good-block decay), `EOC/SwapCollatz.lean` (instantiation to confined prefix words),
`EOC/TwistExpansion.lean` (exact twist expansion, ‖coef‖ ≤ 2^t/(2 dist(λ,0)), Σ‖coef‖ ≤ 1+r/2, weighted collision bound `collision_le_weighted`); full build 3329 jobs.

## Tools
* `deep_dp.c` — 320-bit exact path-product DP: |Φ(h)|/|P|, swap bound, exact 2-block bound,
  bad-state fraction; `-DLD` long-double build (agrees to all digits at 1e-22, j0=100).
* `bad_geom.c` — bad-cell geometry vs random-angle control (runs, longest all-bad path).
* `check_cells.py` — exact checks of the swap-angle arithmetic (0 failures / 3000 cells).
* `headroom.py` — headroom occupation, swappable pairs, conditional pair probabilities.
* `tradeoff.py` — (ρ, η) and run-length requirement tables.

## Headline
* Exact swap angle: Δ = (g·3^{-n} mod 2^L)/2^L, g = w(2^f−1), n = i+2, L = m−a−S_i−min(d,e),
  h = 2^a w; bad ⟺ ∃x,z: 3^n x − 2^L z = g, |x| < η2^L; no exact degeneracy for h ≤ 2^{t+1};
  3-adic form Δ = ⟨−g2^{-L}/3^n⟩ + g/(3^n2^L), correction ≤ 2^{e+c−σ−1}/9 by confinement.
* Requirement correction: 0.0043 bits/step is the budget of ONE frequency; the bulk (odd g)
  needs 0.0911 (graded by v2: ((2−H2)t − a)/(2j0)). Single-threshold (ρ,η) arguments can reach at
  most 0.093 even under perfect equidistribution — no slack; the full |cos| product (0.176 ideal,
  0.14–0.16 measured) and 2-block weights (0.22–0.25 measured) have slack.
* DP to j0=150 (h ≤ 4095, t = 0.1736 j0): worst-case rates swap 0.144–0.152, 2-block 0.22–0.23,
  exact Φ 0.68–0.71; no persistent worst frequency.
* Resonance: λ = 3^k whitens the first k steps (λ3^{-(i+1)} = 3^{k−i−1} integer); rates degrade
  linearly (swap 0.154 → 0.111 at k=37, j0=100); λ = 3^{j0} has |Φ| ≈ |P|: uniform-in-λ decay is
  REFUTED; only frequency-weighted statements (weights ≲ 2^t/|λ|) can hold.
* Geometry: bad cells random-like (fraction 2η, runs ≤ 11 vs control 11); headroom-1 occupation
  bounded (~1.8 steps total), swappable pairs → 0.539.
* Baker/Yu/Ellison: heights of the relevant rationals are ~L, bounds shave only a 1/log fraction;
  not applicable. Tao triangles: exact parallel (θ ↦ 2θ right, θ ↦ (θ+δ)/3 up).
* No rigorous positive-density theorem; A=0.7 still conditional. LEVEL 1.
