# Tao's Fourier-decay machinery at λ = 1 (round of 2026-09-15, ninth)

Nothing committed or pushed. Source read directly: arXiv 1909.03562 (`src/collatz.tex`), §1 (Syracuse random variables,
Prop. [f-decay]) and §7 (Decay of Fourier coefficients).  New Lean (in `EOC.lean`, full build 8783 jobs, standard axioms,
no sorry): `EOC/GoodAngles.lean` (`avg_prod_sq_le`, `PositiveDensityGoodAngles`, `lowFreqDecay_of_goodAngles`,
`weightedFourier_of_goodAngles`; `BlockCubeHyp` kept as hypothesis), `EOC/RenyiInstance.lean` (Rényi barrier instantiated
with Fpre/Gsuf: `sum_sq_split_le_aligned`, `aligned_split_attains`, `split_barrier`, `path_sq_le_aligned`, prefix sharing).

## Tao map (labels / TeX lines)
[f-decay] l.421 (uniform n^{−A} decay for units ξ); [key] l.1108; cancellation for white points l.1164 (|f| = cos πθ on
b_j = 3); [jeo-prop] l.1188; [black] l.1212 (black set = union of separated triangles); [Exptail] l.1399 (holding time
mean (4,16)); [stop] l.1423; [mono-prop] l.1505 (induction weight m^{−A}); [rip] l.1660 (#white ≥ ε·#triangles, exponential
tail); [77] l.1702.  Polynomial loss = Case 3 (triangles of size > m/log²m) inside the m^{−A} induction; Tao remarks that
O(exp(−cn)) "could possibly" hold but is not pursued.  Case 3 uses slope 4 > log₂9 (0.8 > log9/(4 log2)); our law is
critical (mean pair total 2α = log₂9): no margin.

## Numerics (COMPUTATIONAL)
* λ=1 rate γ₁ (quad-precision check agrees): 0.706 (j0=60, t=10), 0.737 (120), 0.745 (150), 0.785 (200), 0.796 (250), 0.767 (300).
* Uniformity fails under the critical confined law: −log₂|Φ_ξ/P| at J = 40…240: ξ=1: 6.8→8.1, ξ=2: 9.3→10.8,
  ξ=−1/2: 4.0→5.1 (bounded: no decay); true λ=1 ξ=2^{−(σ+t+1)}: 32→187 (≈0.78/step); random 29→189.
* Environment controls (J=60/120): 1/7, 1/13, Thue–Morse, planted digit runs all decay like random (0.69–0.82);
  archimedean environments (small integers, −1/2) fail; relevant structure = Tao-triangle geometry of ξ·2^S mod 3^{i+1}.
* Lower tail at λ=1: min per-path contraction 0.24/0.28/0.32 amp bits/step (j0=60/100/150; 20000/8000/3000 paths),
  no path below 0.2; weak-block fraction (u≥4) 0.02–0.03, dispersion index 0.57–0.92 (no clustering).
* Literature: Senge–Straus 1971, Stewart 1980 (ternary digit sum of 2^m > log m/(log log m + c) − 3), Lagarias 2009,
  Abram–Bolshakov–Lagarias (3-adic Cantor sets), Stephan 2026 (superlinear complexity of the (3/2)^n steering word):
  all o(L) — none gives positive density.
