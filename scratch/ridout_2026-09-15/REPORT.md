# Ridout / p-adic Subspace audit of R_max(L) (round of 2026-09-15, eleventh)

Nothing committed or pushed.  Backup of all untracked work before the round: `~/eoc-untracked-backup-2026-09-15.tgz`
(440 untracked files + `EOC.lean`).  New Lean: `EOC/MaxTriangle.lean` (imported in `EOC.lean`; `lake build` 8786 jobs,
0 errors, standard axioms only, no sorry).  Source read: `src/evertse8.txt` (J.-H. Evertse, *Diophantine Approximation*
lecture notes, Leiden, Ch. 8 "The p-adic Subspace Theorem", Thm 8.7, p. 162; norm ‖x‖ = max|xᵢ| from Ch. 7, `src/evertse7.txt`).
Exact-arithmetic audit: `check_ridout.py` → `CHECK_300x200.txt`.

**Verdict: VERIFIED.**  R_max(L) = o(L) along the critical corridor (and on any region with a log2 + b log3 = O(L)),
for every fixed threshold η.  Status: EXTERNAL THEOREM (Schlickewei's p-adic Subspace Theorem, n = 2 — Ridout case) +
PROVED (MATH) reduction, the reduction also PROVED (LEAN) with the Subspace instance as an explicit hypothesis.
**Ineffective**: no L₀(ε), no rate.  Stop condition 1 fired.  Consequences for decay / EOC are weak (§ XII–XIII).

## I. Apex relation and size (PROVED MATH; Lean `three_pow_dvd`, `y_ne_zero`, `Y_ne_zero`, `size`)
y = y(a,b) = centered residue of 2^{−a} mod 3^b (−3^b < 2y ≤ 3^b), U = y/3^b, black ⇔ |y| < η3^b.
X := 2^a y, Y := X − 1 = 3^b z, i.e. **2^a y − 3^b z = 1**, gcd(X,Y) = 1; y ≠ 0 (b ≥ 1); z ≠ 0 ⇔ a ≥ 1.
**s(a,b) = ln(η/|U|) = ln(η 3^b/|y|)**; triangle size = s at the apex (a*,b*); its cells are (a*−k, b*−l) with
2^k 3^l |y*| ≤ η 3^{b*} ⇔ k ln2 + l ln3 ≤ s* (`propagate`: y(a*−k, b*−l) = 2^k y*).
Bounds: s ≥ R ⇔ |y| ≤ η3^b e^{−R};  1 ≤ |y| ≤ 3^b/2;  (2^a|y| − 1)/3^b ≤ |z| ≤ 2^{a+1}|y|/3^b;
U = (z + 3^{−b})/2^a ⇒ trivial effective bound **s ≤ min(b ln3 + ln η, a ln2 + ln(3η/2))**.
Degenerate column a = 0: y = 1, z = 0, s = b ln3 + ln η (s/D → 1) — a genuine infinite family; never on the corridor
(a ≥ 1 there, and apexes satisfy a* ≥ a).

## II–III. Target and exact theorem
Corridor/paths: cells (a,b) = (m − S_i, i+1) ⊂ box 1 ≤ a ≤ m, 1 ≤ b ≤ L, m = ⌊αL⌋ + t + 1 (t = L/6 in `rmax.py`), so
D(a,b) := a ln2 + b ln3 ≤ (2 ln3 + (t/L) ln2) L + ln2 = O(L); apex D* ≤ D + s*.  (Fourier angle ξ = 2^{−(σ+t+1)} only shifts a.)
Target: ∀ε ∃L₀: L ≥ L₀ ⇒ s* ≤ εL for every triangle meeting the region; pointwise form: |U(a,b)| ≥ c_δ (2^a3^b)^{−δ} ∀δ > 0.
**Theorem 8.7 (Schlickewei 1976), as in the source:** n ≥ 2, ε > 0, C > 0, K a number field, p₁…p_s distinct primes, for each
p ∈ {∞, p₁…p_s} linearly independent linear forms L_{1,p}…L_{n,p} in X₁…X_n with coefficients in K; then all solutions
x ∈ ℤⁿ of |L_{1,∞}(x)⋯L_{n,∞}(x)|_∞ · ∏_j |L_{1,pj}(x)⋯L_{n,pj}(x)|_{pj} ≤ C‖x‖^{−ε} lie in finitely many proper linear
subspaces T₁…T_t of ℚⁿ.  |·|_p normalized |p|_p = 1/p; ‖x‖ = max|xᵢ|.  Coefficients fixed; x arbitrary in ℤⁿ (no size or
coprimality condition).  Ineffective (Remark after 8.7): T₁…T_t are not computable; quantitative versions bound t only (Ch. 7 remark).
"Finitely many exceptions" here: for n = 2 each T_i is a line ℚv (or {0}), meeting {X − Y = 1} in ≤ 1 point.

## IV. Mapping, forms, hypotheses (PROVED MATH; Lean `subspaceProd`, `SubspaceInstance`, `subspaceProd_le`, `H_bounds`)
n = 2, K = ℚ, S = {∞, 2, 3}, x = (X, Y) = (2^a y, 3^b z), C = 1, ε = δ.
Forms: ∞: X − Y, Y (det 1);  2: X, Y;  3: X, Y.  All coefficients in {0, ±1}: fixed, height 1, independent of a, b, y, z.
P(x) = |X−Y|·|Y|·|X|₂|Y|₂·|X|₃|Y|₃ = 1·3^b|z|·2^{−a}|y|₂|z|₂·|y|₃ 3^{−b}|z|₃ = **y′z′/|X|** (y′, z′ = {2,3}-free parts),
**P ≤ 2|U|**, **1 ≤ H := ‖x‖ ≤ 2^a 3^b**.  Exact check on all 60 000 cells a ≤ 300, b ≤ 200: identities hold, 0 failures.

## V. Varying y, z — the central check (resolved: NOT an obstruction)
y, z are coordinates of the integer point x, not coefficients of the forms.  Thm 8.7 holds uniformly over all x ∈ ℤ²; the
cofactors enter only through ‖x‖ and through |y|_p, |z|_p ≤ 1 (which only help).  The saving is the S-unit structure
2^a | X, 3^b | Y, present in every apex relation whatever y, z are.  The objection is correct for Baker: in
Λ = a log2 + log|y| − b log3 − log|z| the heights of y, z enter the lower bound (≈ exp(−C log|y| log|z| log L)), useless
unless y, z are tiny.  Theorem applies to all cells with a, b ≥ 1 (no restricted subclass; only the off-corridor column a = 0 excluded).

## VI–VII. Inequality and size bound (PROVED MATH from EXTERNAL; Lean `exc_finite`, `apexBound_of_exc_finite`, `apex_size_le`)
If |U| ≤ ½(2^a3^b)^{−δ} then P ≤ 2|U| ≤ (2^a3^b)^{−δ} ≤ H^{−δ}: x solves (8.7).  Solutions lie on finitely many lines, each
line meets X − Y = 1 once, and 2^a ≤ |X|, 3^b ≤ |Y| bound (a, b): **finitely many exceptional cells for each δ > 0**.  Hence
**|U(a,b)| ≥ c_δ (2^a 3^b)^{−δ} for all a, b ≥ 1**, equivalently y′z′ ≥ c′_δ H^{1−δ}, so **|y||z| ≥ c′_δ (2^a|y|)^{1−δ}**
(the recovery-note formula, correct, but only for a ≥ 1).  Size: **s(a,b) ≤ δ(a ln2 + b ln3) + C_δ**, C_δ = ln(η/c_δ).
Apex of a triangle through (a,b): s* ≤ δ(D + s*) + C_δ ⇒ **s* ≤ (δD + C_δ)/(1 − δ)**.  Corridor: R_max(L) ≤ (δKL + C_δ)/(1 − δ),
K = 2 ln3 + (t/L) ln2 + o(1).

## VIII–IX. Order of limits; effectivity
For each fixed δ the exceptional set is finite and C_δ is a constant (independent of L); so limsup R_max(L)/L ≤ δK/(1−δ) for
every δ ∈ (0,1), hence R_max(L)/L → 0 (limsup in L first, then δ → 0; Lean `eventually_maxTriangleLE`, `maxTriangleLE_box`).
**Ineffective**: C_δ and L₀(ε) are not computable; the theorem gives o(L) only, no O(L/log L) or any rate.  Best effective
bound known here: the trivial s ≤ min(a ln2, b ln3) + O(1) ≤ D/2 + O(1).  Quantitative Subspace versions bound the *number* of
exceptional apex relations per δ (not checked against a quantitative source this round), never their location.
(CONJECTURAL aside: abc in ε-form gives the same o(L), effective if abc is; Robert–Stewart–Tenenbaum-strength abc would give
O(√(L/log L)) — citation from memory, not verified.)

## X. Previous report
Item 29 of the triangle round grouped Subspace with Baker ("only near-maximal").  Correct for Baker (single-cell linear forms in
logs with cofactor heights), too pessimistic for Subspace/Ridout, where the cofactors are part of the solution vector.  The
previous conclusion that *occupation* is not controlled stays correct: o(L) says nothing about how often size-εL triangles occur.

## XI. Mahler analogy (legitimate)
Mahler (Mathematika 4 (1957) 122–124): for coprime p > q ≥ 2 and ε > 0, ‖(p/q)ⁿ‖ < e^{−εn} for finitely many n only, via
Ridout; ineffective.  Same mechanism: 3ⁿ = q_n2ⁿ + r_n, the Ridout/Subspace bound "non-S-part of x₁x₂x₃ ≥ H^{1−ε}" gives
|q_n||r_n| ≥ 3^{n(1−ε)}, i.e. |r_n|/2ⁿ ≥ 3^{−εn}; ours: (2^a y)·(3^b z)·1 gives |y||z| ≥ H^{1−ε}.  Ours is the 3-adic analogue
(small-height 3-adic approximations y of 2^{−a}), with two varying cofactors instead of one.

## XII. Consequence for |Γ(1)|
Rigorous: none yet.  Conditional (Lean `lowFreqDecay_of_sublinearMaxTriangle`): SublinearMaxTriangle + **TriangleGapBridge**
(unproved: max triangle size ≤ R₀ ⇒ good-block gaps ≤ G(R₀) ≈ R₀/ln3 + 1) + BlockCubeHyp ⇒ low-frequency mean square
≤ κ^{2⌊R/(G(εL)+1)⌋}, i.e. |Γ(1)| ≲ exp(−cL/(R_max(L)+1)).  With R_max = o(L) at an unknown rate this is **merely e^{−ω(1)} = o(1)**:
not provably super-polynomial, not stretched-exponential.  (R_max = O(L^β) would give e^{−cL^{1−β}}; O(log L) e^{−cL/log L}.)
Bridge obstruction (PROVED MATH from `merge`/`merge_apex`): consecutive path cells (a,b) → (a−d, b+1), both black, lie in distinct
triangles only if 2^d η + 3η ≥ 1 (d ≥ 6 at η = 1/54); such long jumps occur at positive frequency along confined paths, so the
gap bound does not follow pathwise from the maximum alone — a Tao-[rip]-type probabilistic white-count bound under the critical
law is needed.

## XIII. Consequence for A > 1/α
No.  A > 1/α needs LowFreqDecay with a fixed γ > 0 (decay round: E ≈ H₂ − 0.03γ).  κ^{2⌊R/(G+1)⌋} has exponent rate
∝ 1/G → 0 unless R_max = O(1); numerics show R_max growing (≈ log #cells), so the maximum route cannot give exponential decay
even in its ideal O(log L) form (HEURISTIC/COMPUTATIONAL; R_max → ∞ is not proved).  Benefit: at most an o(1) factor at the
same exponent (sub-power improvement), conditional on the bridge.  Exceptional exponent unchanged (A = 1/α).

## XIV. Lean (`EOC/MaxTriangle.lean`, PROVED LEAN; external input only via `SubspaceInstance`)
`y_ne_zero`, `three_pow_dvd`, `Y_ne_zero`, `two_abs_y_le`; `subspaceProd`, `SubspaceInstance δ` (Thm 8.7 instance as a Prop);
`subspaceProd_le`, `H_bounds`, `subspace_ineq_of_exc`, `abs_le_of_line`, **`exc_finite`**; `size`, `D`, `ApexBound`,
**`SublinearMaxTriangle`**, `apexBound_of_exc_finite`, **`sublinearMaxTriangle_of_subspace`**; `InTri`, `apex_size_le`,
`depth_le` (for `TriangleArray.inLargeTriangle`), `MaxTriangleLE`, **`eventually_maxTriangleLE`**, `box`, `maxTriangleLE_box`;
`GoodGap`, `card_good_ge`, `positiveDensityGoodAngles_of_gap`, `lowFreqDecay_of_gap`, `TriangleGapBridge` (hypothesis),
**`lowFreqDecay_of_sublinearMaxTriangle`**.

## XV. Numerics (COMPUTATIONAL) — see `RMAX_J200-6400.txt`
Bug found: `rmax.py`'s random control unit may be divisible by 3 (seed 41: J = 800, 6400), making the apex climb loop forever —
the interrupted run would have hung at J = 800 regardless of the terminal crash.  `rmax.py` and `RMAX.txt` left unchanged;
`rmax_fixed.py` applies the `triangles.py` guard (ξ ≡ 0 mod 3 → ξ + 1; true column unaffected).
```
     J  cells  R_max(true)  R_max/J   R_max/lnJ  apex (a*,b*)   s*/D*    | R_max(random)  R_max/lnJ
   200    800     4.29      0.02145    0.810    ( 153,  128)   0.0174   |     6.39       1.206
   400   1600     3.74      0.00934    0.624    ( 295,  256)   0.0077   |     4.60       0.768
   800   3200     3.54      0.00443    0.530    (1361,   25)   0.0037   |     4.22       0.631
  1600   6400     6.65      0.00416    0.902    (2150,  413)   0.0034   |     4.42       0.599
  3200  12800     6.32      0.00198    0.783    (3825, 1129)   0.0016   |     7.89       0.977
  6400  25600     8.17      0.00128    0.932    (5743, 3449)   0.0011   |     7.25       0.827
```
R_max/J → 0 (consistent with the theorem); R_max/ln J stays in 0.5–0.93 (one realization per J; consistent with O(log L),
not evidence of it); true ≈ random control; R_max − ln(#cells) ≈ −2…−4.5 (random-model Gumbel location ≈ ln(2η) + 0.58 ≈ −2.7).
J = 200, 400 rows reproduce `RMAX.txt` exactly.  Box audit (`CHECK_300x200.txt`): max s/D per dyadic D-shell 0.065, 0.027, 0.016.

## Summary
* Strongest positive: **R_max(L) = o(L)** for Tao-black triangles along the critical corridor, every fixed η (EXTERNAL THEOREM
  + PROVED MATH; reduction PROVED LEAN).  Pointwise: |U(a,b)| ≥ c_δ(2^a3^b)^{−δ} for all a, b ≥ 1.
* Strongest negative: ineffective (no rate); by itself gives only o(1) continuation decay, conditional on an unproved bridge,
  and no change to A = 1/α; uniformity over varying frequency λ (growing shells) not given (constants depend on λ).
* Remaining lemma: TriangleGapBridge (critical-law white-count / good-block lower bound with control of inter-triangle jumps);
  for A > 1/α, an occupation (density) bound, not a maximum bound.
* LEVEL 1 for EOC (convention of recent reports: no A > 1/α), with one new unconditional arithmetic theorem.
