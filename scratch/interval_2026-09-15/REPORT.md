# Interval averaging for L=3 block cubes (round of 2026-09-15, fifth)

Nothing committed or pushed. New Lean modules (in `EOC.lean`, full build OK, standard axioms, no sorry):
`EOC/ShellRefined.lean` (‖coef‖ ≤ 1, refined shell weights min(2^{u+1},2^t),
`weightedFourier_of_shell_averages_refined`), `EOC/ThreeBlock.lean` (shape set Q_u, injectivity, |Q_u| = C(u−1,2),
q < 2^u, block phase factorization, complete-period orthogonality on any interval of length k·2^M),
`EOC/WhiteRun.lean` ((A′) `cont`, (B′) `exit`, `size_automatic`, `white_step`, `run_length`, `run_dvd`, `cres_rec`,
interval residue count, fibre multiplicity), `EOC/IntervalSieve.lean` (Dirichlet kernel ≤ 1/(2 dZ), pair expansion, `grid_sieve` #T·μ·(H+2q(1+log q)), `minkowski_step`). Full build 8775 jobs.

## Main mathematics
* (T2) 2-adic complete-period tower (PROVED MATH): E_{λ∈I} Q3 ≤ E_P Π_{r: M_r ≤ L} 1/|C_r| for |I| = 2^L.
* (T3) 3-adic block tower (PROVED MATH): reciprocity β_r = f_r/3^{n_r} + λ/(3^{n_r}2^{M_r}), f_r ≡ −λ2^{−M_r} (3^{n_r});
  E_I Q3 ≤ 2 E_P Π_{n_r ≤ L/α} (ρ_r + η), ρ = #{q ≡ q' mod 27}/|Q|², η ≤ 2^{L−m+c+5}.
* (C3) 3-adic interval sieve on the true Φ (PROVED MATH; validated exactly at J = 16, 20): for any split N with
  2·Xmax(N) ≤ 2^m,  √(E_{λ∈I}|Φ|²)/|P| ≤ Σ_S g_S min(p_S, √(κ p_S))/|P|,  κ = μ_N(1 + 2·3^N(1+N ln 3)/|I|),
  μ_N = ⌈Xmax(N)/3^N⌉ ≤ ⌈N2^c/3⌉ (fibres of the injective prefix map X(P₁) = Σ 2^{S_i}3^{N−1−i} mod 3^N).
* 27^k | e_r ⇔ λ ≡ −2^{M_r} f_r (mod 3^{n_r+3k}): the modulus is 3^{n_r+3k}, not 27^k (wrap term).
  Residue counting controls white runs only where 3^{n_r+3k} ≤ |I|, where (T3)/(C3) already give everything.
* Non-white (angle ≥ 2^{−u}/54) gives only κ ≈ 0.9997; only run exits (angle ≥ 1/54) contract, ≈ 0.1 per path.

## Numerics (COMPUTATIONAL)
* Chain constant with rigorous (C3) + refined weights: log2 C = 9.0, 17.3, 24.4, 34.3, 51.5 at K = 100…1600
  (crude Lean weights: 35.2 at K=400, 60.9 at K=800).  Extra deep-step amplitude rate still needed:
  C ≤ 2: 0.235/0.161/0.110/0.077, C ≤ K: 0.111/0.091/0.071/0.055 (K = 100/200/400/800)
  vs uniform requirement 0.252/0.188/0.151/0.126 and 0.138/0.127/0.116/0.107.
* Idealized shell bound a_u = 2^{−θu}: θ = h/α = H₂(1/α): log2 C increments/K → 0.0098, 0.0069, 0.0060 (→ I₀(A−1/α) = 0.0055:
  exactly neutral, exponent 1 − I₀/α for every A); θ = 1: increments 0.0080, 0.0050, 0.0038 (→ (I₀/2)(A−1/α) = 0.0027; exponent 1 − I₀(A+1/α)/2 = 0.9472).
* White runs (j0 = 60/80/100, all/sampled λ < 2^t, 20 sampled paths): white fraction 0.33–0.35%/block;
  P(Rmax ≥ 1,2,3) = 0.067/1.9e-3/0, 0.084/2.5e-3/0, 0.101/3.8e-3/3.7e-5; rigidity violations 0;
  deep blocks P(v27(e_r) ≥ k) ≈ 27^{−k}; per-path worst rate 0.22–0.23, median 0.40–0.42.
* 27 | e_r is not a function of λ mod 27 (all 26 classes mixed, deep and shallow blocks).
* Shell tables SH_J60.txt, SH_J100.txt: rigorous per-shell log2 a_u (T2/T3/C3) vs even-split budget.
