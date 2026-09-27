# Drift bands, shallow recurrence, and the `L₁(m) < 2m` target (round of 2026-09-16, part 10)

Nothing committed or pushed.  Lean: `EOC/DirectDescent.lean` extended (`confined_two_mul_of_nondescent`,
`descent_of_L1_lt_two_mul`); `lake build` 8791 jobs, standard axioms, no sorry.  Data: `bands.py`.

## 1. The target is now explicit in Lean (PROVED (LEAN))
* `confined_two_mul_of_nondescent`: if the orbit of `M` never drops below `M` through step `2M`, its own word is
  `1`-confined to depth `2M` — because `2/(3 ln 2) = 0.9624… < 1`.  **A minimal Collatz counterexample therefore
  satisfies `L₁(m) ≥ 2m` automatically.**
* `descent_of_L1_lt_two_mul`: `L₁(M) < 2M` for all `M ≥ M₀` ⇒ every such odd `M` has a strictly smaller iterate
  (and then Collatz via the part-8 induction).
* Flexibility: the same argument works for any `C < 3 ln 2 = 2.07944`; `C = 2` is what the dyadic route needs.

## 2. Drift bands and value scales (PROVED (MATH))
On a `1`-confined prefix, `m_j = m·U_j·2^{−R_j}` with `U_j ≥ 1`, so
* `R_j ≤ 1` ⇒ `m_j ≥ m/2`;  `R_j ≤ −q` ⇒ `m_j ≥ 2^q·m`;  band `B_q = {j : −q−1 < R_j ≤ −q}` ⇒ `m_j ∈ [2^q m, 2^{q+1}m·U]`.
* Under non-descent (`m_j ≥ m`), `log U_j ≤ j/(3m)`, so for `j ≤ 2m`: **`U_j ≤ e^{2/3} = 1.9477`** (sharpest
  convenient constant; `e^{4/3}` is the version with only `m_j ≥ m/2`).
* Hence the shallow part `{j : R_j > −Q}` lies in the single interval `[m/2, 2^Q·e^{2/3}·m]`.

## 3. Finite collision-free audit (Parts IV–IX)
The repo's finite, injectivity-only tools are **PROVED (LEAN)**:
* `HarmonicPacking.sum_inv_orbit_le`: `∑_{k<N} 1/m_k ≤ 7/3 + (1/3)·log N` for pairwise-distinct states;
* `HarmonicPacking.carryE_le`: `E_N ≤ (1/9)log₂N + 7/(9 ln 2)`;
* `LogCorridor.logFloor_window_bound'`: finite and quantitative, but it assumes a **lower** floor
  `R_k ≥ −B log₂(k+1) − C` for all `k < N`, which a confined prefix does not provide.
The García–Tal/Curry *windowed sparsity* theorem (an interval-occupancy bound with exponent `β* < 1`) is an
EXTERNAL THEOREM, not formalized, and enters the repo only as the hypothesis `LogFloorExclusion`; it is stated
for divergent orbits.  **No finite interval-occupancy lemma with exponent `β < 1` exists in the repo**, and the
harmonic tools above only bite when the orbit values are bounded *above*, which confinement does not give.

## 4. Shallow recurrence: REFUTED as stated (COMPUTATIONAL + HEURISTIC)
Fraction of the `1`-confined prefix with `R_j ≥ −Q` (record seeds):
| m | L₁ | Q=0 | 1 | 2 | 3 | 4 | 6 | 8 | median(−R) | max(−R) |
|---|---|---|---|---|---|---|---|---|---|---|
| 27 | 39 | 0.026 | 0.154 | 0.282 | 0.436 | 0.718 | 0.923 | 1.000 | 3.19 | 6.72 |
| 703 | 50 | 0.000 | 0.020 | 0.080 | 0.280 | 0.440 | 0.920 | 1.000 | 4.36 | 6.89 |
| 35 655 | 85 | 0.012 | 0.082 | 0.165 | 0.247 | 0.329 | 0.694 | 0.965 | 5.04 | 8.59 |
| 270 271 | 102 | 0.000 | 0.020 | 0.059 | 0.127 | 0.167 | 0.225 | 0.333 | 9.76 | 14.89 |
| 1 859 241 | 144 | 0.035 | 0.111 | 0.201 | 0.299 | 0.472 | 0.743 | 0.965 | 4.19 | 9.55 |
| 10 507 503 | 194 | 0.041 | 0.088 | 0.175 | 0.309 | 0.412 | 0.691 | 0.954 | 4.66 | 8.91 |
At fixed `Q` the fraction **decreases with prefix length** (Q = 4: 0.718 at L = 39 → 0.353 at L = 190), matching
the `Q/√L` law expected for a critical walk conditioned to stay below a barrier (local time near the barrier is
`Θ(√L)`).  So the hoped-for statement
> `#{j < N : R_j ≥ −Q} ≥ δN` for fixed `Q, δ`

is **false asymptotically**: the shallow count is `Θ(Q√N)`, not `Θ(N)`.  The two-lemma strategy of Parts
XXXI–XXXIX therefore fails at *both* ends — even a `β < 1` interval-sparsity bound allows
`(2^Q m)^{0.965} ≫ √m` shallow visits, so no contradiction arises.  Required `δ, Q` do not exist.

## 5. Ratio frontier (COMPUTATIONAL, exhaustive odd 3 ≤ m ≤ 2·10⁷)
`sup L₁(m)/m = 1.4444 at m = 27`; the next values are 1.194 (m = 31), 0.927 (41), 0.702 (47), 0.655 (55).
Every seed above 100 has ratio < 0.35, and the record seeds have ratios ≤ 7·10⁻².  **27 remains the global
extremizer**, and the empirical margin to the required `C < 2.07944` is 44%.

## 6. Status
* PROVED (LEAN): minimal counterexample ⇒ `L₁(m) ≥ 2m`; `L₁(m) < 2m` eventually ⇒ eventual descent (⇒ Collatz).
* PROVED (MATH): the band/value-scale dictionary; `U_j ≤ e^{2/3}` for `j ≤ 2m` under non-descent.
* COMPUTATIONAL: `sup_{m ≤ 2·10⁷} L₁(m)/m = 1.4444` at m = 27; band occupancy tables.
* REFUTED: fixed-`Q` positive-density shallow recurrence (and with it the ShallowRecurrence + sparsity strategy).
* OPEN: `L₁(m) < 2m` (equivalently any `C < 3 ln 2`).  No mechanism identified; the finite tools in the repo
  need an upper bound on orbit values, which a confined prefix does not supply.
* Collatz not proved.  LEVEL 1.
