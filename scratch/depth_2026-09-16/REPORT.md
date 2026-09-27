# Ordinary magnitude: depth-vs-seed-size, and why packing still cannot close (round of 2026-09-16, part 12)

Nothing committed or pushed; no new Lean this round.  Data: `depth.py` (exact, exhaustive seeds ≤ 5·10⁶).

## 1. Value/drift conversion (PROVED (MATH))
Under minimal-counterexample non-descent, for `j ≤ 2m`: `1 ≤ U_j ≤ e^{2/3}`, so
  **`m·2^{−R_j} ≤ m_j ≤ e^{2/3}·m·2^{−R_j}`**, i.e. `m_j ≤ m^{1+ε}` iff `−R_j ≤ ε log₂m − log₂U_j`.
So every ordinary-value cutoff is exactly a drift cutoff, and the whole question is how negative `R` can get.

## 2. The excursion-cost frontier (COMPUTATIONAL, exact)
By seed-equivalence (prefix locking) the least realizer of a word is the least seed whose own word it is, so
`r_exc(Q) = min{m : the 1-confined prefix of m reaches R_j ≤ −Q}` is computable by scanning seeds:
| Q | 4 | 5 | 6 | 7 | 8 | 10 | 12 | 14 | 16 |
|---|---|---|---|---|---|---|---|---|---|
| `r_exc(Q)` | 27 | 27 | 27 | 1 819 | 4 255 | 26 623 | 77 671 | 159 487 | 3 041 127 |
| `log₂r_exc/Q` | 1.189 | 0.951 | **0.792** | 1.547 | 1.507 | 1.470 | 1.354 | 1.235 | 1.346 |
* **Minimum over the tested range: `log₂ r_exc(Q)/Q = 0.792` (at Q = 6.72, seed 27)**; for Q ≥ 7 the ratio sits
  in `[1.23, 1.55]`.  Equivalently `max_m Q₁(m)/log₂m = 1.4130`, again attained at m = 27.
* **All-ones family (PROVED (MATH)):** `T₁(x) = (3x+1)/2` gives `T₁^r(m)+1 = (3/2)^r(m+1)`, so
  `d₁ = … = d_r = 1 ⟺ 2^r ∣ m+1`, least seed `b(r) = 2^r − 1`, with `R_r = −(α−1)r`; hence for this family
  `log₂ m / Q = 1/(α−1) = 1.7095`.  It is the cheapest *explicit* family but not the empirical extremizer
  (seed 27 buys depth at ratio 0.79).
So the target inequality `R_j ≤ −Q ⇒ m ≥ 2^{cQ−O(1)}` is **empirically supported with c ≈ 0.79** (CONJECTURAL;
no proof).  It remains the best-shaped intermediate theorem.

## 3. Even granting it, packing does not close — REFUTED (PROVED (MATH) arithmetic)
Suppose the depth theorem holds with constant `c`, so `−R_j ≤ C log₂m`, `C = 1/c`.  Then
`m_j ≤ e^{2/3}·m^{1+C}`, and a `2m`-step confined prefix has `2m` distinct states inside `[m/2, e^{2/3}m^{1+C}]`.
A finite interval-sparsity bound with exponent `β` gives capacity `≈ m^{(1+C)β}`, so a contradiction needs
  **`(1+C)β < 1`.**
* Best available exponent: `β* ≈ 0.9654` (García–Tal/Curry windowed sparsity) — an EXTERNAL THEOREM, not
  formalized, and **stated for divergent orbits**, not finite prefixes; the repo carries it only as the
  hypothesis `LogFloorExclusion`.  The repo's own finite tools (`sum_inv_orbit_le`, `carryE_le`) give `β = 1`.
* Requirement with `β = 0.9654`: `C < 0.0358`, i.e. depth `≤ 0.036 log₂m`.
* Truth: depth reaches `1.41 log₂m` (seed 27), i.e. `C ≈ 1.41` — **too large by a factor ≈ 40**.
Multi-scale aggregation over dyadic bands changes nothing: summing capacities `Σ_q (2^q m)^β` is dominated by
the top band, reproducing the same inequality.  Likewise `θ = 1/2` (√-local time) cannot help, since it would
need `β < 1/2` — far below any known exponent.  **The ordinary-magnitude route is therefore closed with the
sparsity exponents available.**

## 4. The wedge buys nothing (COMPUTATIONAL)
A minimal counterexample satisfies the moving ceiling `R_j ≤ j/(3m ln 2)`, which for `j ≤ m` is `≤ 0.481` —
tighter than `R_j ≤ 1`.  Re-running the whole frontier with barrier `c = 0.5`:
| barrier | deepest `L_c` | `max L_c(m)/m` | `max Q_c(m)/log₂m` | `r_exc` table |
|---|---|---|---|---|
| `c = 1` | 144 | 1.4444 (m = 27) | 1.4130 (m = 27) | as above |
| `c = 0.5` | 141 | 1.4444 (m = 27) | 1.4130 (m = 27) | **identical** |
The extremizers, ratios and excursion costs are unchanged.  So attacking the wedge version is **not** easier
than the `c = 1` version (Parts LIII–LXII), and the extra information in the moving ceiling is empirically worth
about 3 steps of prefix length.

## 5. Status
* PROVED (MATH): value/drift conversion; all-ones burst formula `b(r) = 2^r − 1` and its ratio `1.7095`;
  the exponent arithmetic `(1+C)β < 1` and its failure at the available `β`.
* COMPUTATIONAL: excursion frontier; `max Q/log₂m = 1.4130`; `max L₁(m)/m = 1.4444`; both extremized by 27;
  wedge equivalence.
* CONJECTURAL: `R_j ≤ −Q ⇒ m ≥ 2^{0.79Q}` (the depth theorem) — supported to Q = 16.
* REFUTED this round: depth-theorem + interval-sparsity as a route to `L₁(m) < 2m` (needs `β < 0.44`, have
  `0.965` and only for divergent orbits); the wedge as an easier target.
* OPEN: `L₁(m) < Cm`, `C < 3 ln 2`; the dyadic floor.  Collatz not proved.  LEVEL 1.
