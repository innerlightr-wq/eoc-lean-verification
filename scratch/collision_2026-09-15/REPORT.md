# Prefix end-state collisions (round of 2026-09-15)

Nothing committed or pushed. New Lean (both in `EOC.lean`; full build 3317 jobs, standard axioms,
no sorry): `EOC/PrefixCollision.lean` (word-level gluing + the chain
`exceptional_count_le_of_prefixCollision`), `EOC/PrefixStateFormula.lean` (carry formula,
collision criterion, prefix-state formula, Parseval for collision counts).

## Tools
* `phi_dp.c` — exact path-product characteristic sums Φ(h) = Σ_P e(−h·3^{−j0} q_P / 2^m) by the
  (i,S) transfer recursion, plus the rigorous digit-swap bound B(h) ≥ |Φ(h)|/|P|.
* `check_formula.c` — brute-force check of 2^σ m_P = 3^{j0} r_P + q_P, the m_P formula, r_P formula
  (0 mismatches on 1.4e7 prefixes).
* `mc_collide.c` — Monte Carlo exact collision excess δ_t of m_P mod 2^{t+1} (5e7 samples).
* `split_dp.c` — split-depth decomposition of the smoothed collision sum.
* `block_norm.c`, `block_cert.c` — block transfer norms and the rigorous block-norm certificate.
* `occupation.py` — forced steps, swappable pairs, first-divergence profile (exact).
* `split_opt.py` — split-depth optimization and exact instances.

## Headline
* Chain in Lean: PrefixCollisionBound (δ ≤ ε²|V|/2^t for all fresh σ, post-fresh s) ⇒
  #E_U∩[0,2^K) ≤ ((1+ε)e^{λ*U}/2)(2^K)^{1−I₀A}.
* Smoothed route (Selberg majorant, EXTERNAL): the incidence is ξ_P ∈ J_v with
  ξ_P = {3^{−j0}(2^σ−q_P)/2^m}; needed Σ_{0<|h|≤H}|Φ(h)|²/|P|² ≲ ε²|V|/2^t, Φ a path product
  that closes on the state (i,S): exact O(K²)-state transfer, but one-step norm = 1 exactly
  (unitary diagonal phases).
* A=0.7 at the optimal split j0 = K/α: average rate ≥ 0.0911 bits/step, every-h rate ≥ 0.0043.
* Data: exact |Φ| sub-random (Σ|Φ/P|² = 0.18–0.65× random, j0=30..70); MC δ = 0 within noise
  (j0=30,40,50, t≤26); swap bound rates 0.126–0.16 bits/step (worst h) → would give A ≤ 0.734–0.747
  if made rigorous; block certificate (L=10) ≈ 0.29–0.37 bits/step at j0=40.
* Obstruction: an exponential-rate (tiny but uniform in h ≤ 2^t) decay of the confined 2-adic
  Syracuse characteristic function — by CRT the 3-adic one of Tao's fine-scale mixing, twisted by a
  smooth archimedean phase; Tao's method gives only polylog; the swap/block frameworks reduce it to a
  positive density of non-degenerate phase cells along typical confined paths, uniformly in h.
* No structured collision family; late-split / shared-prefix pairs negligible; h = 3^v whitens only
  ≤ t/(α j0) ≈ 11% of steps. LEVEL 1.
