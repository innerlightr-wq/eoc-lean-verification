# Tao-black triangles of the universal array along the critical corridor (round of 2026-09-15, tenth)

Nothing committed or pushed.  Lean (in `EOC.lean`, full build OK): `EOC/TriangleArray.lean` (recurrences `y_eq_two_mul`, `y_eq_of_small`, `propagate`, `merge`, `merge_apex`, `black_of_inLargeTriangle`), `EOC/BlockCubeInstance.lean` (`blockCubeHyp_pair`: BlockCubeHyp for Ψ unconditionally with L=2 pair blocks; abstract `ClassProduct`, `norm_sq_le_of_classProduct`).

## Exact geometry (PROVED MATH)
U(a,b) = y(a,b)/3^b, y = centered residue of 2^{−a} mod 3^b.  Black: |U| < η.  Recurrences: U(a−1,b) = 2U(a,b) mod 1,
U(a,b) = 3U(a,b+1) mod 1.  Triangle with apex (a*,b*), size s = ln(η/|U(a*,b*)|): cells (a*−k, b*−l), k log2 + l log3 ≤ s,
with y(a*−k, b*−l) = 2^k y* exactly — the whole triangle is one relation 2^{a*} y* − 3^{b*} z* = 1 (no multi-cell amplification).
Path direction (a,b) → (a−d, b+1): depth Q = k log2 + l log3 changes by d log2 − log3, mean 0 (critical); the path leaves
a triangle at the apex row (≤ s/log3 steps) or through the hypotenuse (mean-zero random walk: survival ≥ c for deep entries).
Merge/spacing: black cells of distinct triangles along a path (b1 ≤ b2, a2 ≤ a1) satisfy |U2|3^{Δb} + 2^{Δa}|U1| ≥ 1, so
max(3^{Δb}, 2^{Δa}) > 1/(2η) (Tao separation); consecutive distinct triangles are separated by white cells.

## Numerics (COMPUTATIONAL, η = 1/54)
* Central corridor, J = 100/400/1600: black fraction 0.043/0.032/0.044 (random 2η = 0.037), max triangle size 3.4/4.4/7.3,
  occupation by size ≥ 6: 0/0/0.002, ≥ 10: 0; identical statistics for slopes α ± 0.05, rational convergents 19/12 … 485/306,
  and random-unit environments (no criticality or continued-fraction resonance).
* Size tail (J = 800 band): P(size ≥ r) ≈ e^{−r} (0.62/0.41/0.12/0.066/0.058/0.022/0.007 at r = 0.5/1/2/3/4/5/6), max 6.8; random env same.
* Paths (J = 200/400, 60 paths): black step fraction 0.032; visits mostly to triangles of size < 3; fraction of visits staying
  ≥ 75% of the available height 0.84–0.97 (no rapid escape).
