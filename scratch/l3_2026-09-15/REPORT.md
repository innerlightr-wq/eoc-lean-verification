# L = 3 block cubes (round of 2026-09-15, fourth)

Nothing committed or pushed. New Lean (in `EOC.lean`, full build 3333 jobs, standard axioms,
no sorry): `EOC/BlockCube.lean` (class Cauchy–Schwarz, product structure, full-group Parseval
Σ_λ‖Ψ‖² = 2^m|P| via injectivity of y′, interface `weightedFourier_of_blockAverageBound`),
`EOC/ShellDecomposition.lean` (centered dyadic shells, per-shell weight ≤ 2^t/2^{u+1},
`weightedFourier_of_shell_averages`).

## Exact 3-block algebra (PROVED MATH)
* Block at step i, entry S, total u; internal sums S1 = S+d1, S2 = S1+d2. Since
  3^{-(i+2)} = 3·3^{-(i+3)} (2-adic), the block phase is common − h·3^{-(i+3)}(3·2^{S1}+2^{S2})/2^m.
  With a = S1−S−1, b = S2−S−1: shape set Q_u = {3·2^a + 2^b : 0 ≤ a < b ≤ u−2} (admissibility:
  a ≤ b(i+1)−S−1, b ≤ b(i+2)−S−1), single block angle β = h·3^{-(i+3)}·2^{S+1}/2^m mod 1,
  W(β) = |Σ_{q∈Q} e(qβ)|/|Q|, |Q_u| = C(u−1,2).
* Distinct shapes (bits {a,a+1,b} or 5·2^a) ⇒ full-group orthogonality: E_{h∈ℤ/2^m} W² = 1/|Q|;
  whole-cube full-group value = E_P Π 1/|C_r| = #coarse/|P|; ideal L² ceiling
  (3h − H(NB(3,1/α)))/6 = 0.3319 bits/step (confined numerics 0.308–0.318).
* Run rigidity: λψ_r = N_r + e_r/2^{M_r}; ψ_{r+1} = frac(2^{u}(ψ_r + j_r)/27), j_r ≡ −x_r2^{-M_r} (27);
  N_r + λj_r ≡ −e_r2^{-M_r} (mod 27). (A′) 27 | e_r and |e_r| < 27·2^{M_{r+1}−1} ⇒ e_{r+1} = e_r/27;
  (B) |e_r|/2^{M_r} < 2^{-u_r−1}/27 and 27 ∤ e_r ⇒ ‖λψ_{r+1}‖ ≥ 1/54. (Checked: 0 failures in
  81,254 / 9,658 exact big-integer cases.) White-run length ≤ 1 + v27(e_start): Tao triangles.

## Tools
`templates.py` (shape sets, κ_u, analytic ceilings), `phi3.c` (exact Φ, rigorous L=3 bounds Q3 =
E_PΠW² and B3 = E_PΠW per λ; weighted ratio R3; list mode), `blockstats.py`, `rigidity.py`.

## Numerics (COMPUTATIONAL; A=0.7 geometry, top shells, all λ < 2^t exhaustive for the low block)
| j0 | t | true Φ L² rate | L=3 bound Q3 rate (λ-avg) | ideal ceiling | R_true | R3 (rigorous-bound version) |
|---|---|---|---|---|---|---|
| 30 | 5 | 0.610 | 0.292 | ~0.30 | 1.2e-6 | 0.60 |
| 40 | 6 | 0.672 | 0.287 | ~0.30 | 1.5e-10 | 0.077 |
| 60 | 11 | 0.685 | 0.309 | 0.308 | 3.8e-17 | 1.1e-3 |
| 60 (c=1) | 11 | 0.710 | 0.319 | — | 1.0e-17 | 4.9e-4 |
| 80 | 13 | 0.701 | 0.308 | ~0.31 | 4.3e-25 | 1.3e-6 |
| 100 | 17 | 0.692 | 0.303 | ~0.312 | 1.1e-32 | 1.3e-8 |
* The λ-averaged L=3 block-cube bound equals its full-group ideal: no interval loss observed.
* Structured frequencies: λ=3^k whitens ~k/3 blocks (Q3 rate 0.30 → 0.18 at k≈30; no decay only
  for 3^k within a few bits of 2^m, weight ≈ 2^{t−σ}); high v2 harmless (0.31–0.32).
* Exceptional blocks: u=3 (digits 1,1,1; W ≡ 1) ≈ 25%; headroom truncation 21% → 3% (j0 30 → 240).
* Not proved: the interval-averaging lemma. LEVEL 1.
