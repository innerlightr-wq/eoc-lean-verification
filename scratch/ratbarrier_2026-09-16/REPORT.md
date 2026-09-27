# Rational barrier models and the limit p/q → α (round of 2026-09-16, part 21)

Nothing committed or pushed.  `lake build EOC` = 8797 jobs, green, HEAD still `317c765`.
Scripts: `cf.py`, `ensembles.py`, `pressure_swap.py`.

## Verdict in one line

The approximation methodology is **sound and quantitatively excellent** — monotone sandwich,
exact agreement for `q > J`, transfer error `O(N·|α−p/q|)` — but it **addresses a
non-obstruction**: the `α`-dependence of EOC is Lipschitz and harmless, while the actual difficulty
(the 3-adic black-cell environment, modulus `3^{2r+2}` growing with the block index) is untouched by
rationalising `α`.  On the ShapeTail side the certificate is already barrier-invariant, so no
approximation is needed there either.

## Parts III–VII — exact barrier data

`α = log₂3 = [1;1,1,2,2,3,1,5,2,23,2,2,1,1,55,…]`.

| p/q | side | ε = \|α−p/q\| | q²ε | first j with `⌊jα⌋ ≠ ⌊jp/q⌋` | L_agree | L_agree/q |
|---|---|---|---|---|---|---|
| 8/5 | above | 1.504e-2 | 0.376 | **5** | 4 | 0.80 |
| 19/12 | below | 1.629e-3 | 0.235 | 53 | 52 | 4.33 |
| 65/41 | above | 4.034e-4 | 0.678 | **41** | 40 | 0.98 |
| 84/53 | below | 5.684e-5 | 0.160 | 359 | 358 | 6.75 |
| 485/306 | above | 4.820e-6 | 0.451 | **306** | 305 | 1.00 |
| 1054/665 | below | 9.471e-8 | 0.042 | 16266 | 16265 | 24.46 |
| 24727/15601 | above | 1.683e-9 | 0.410 | **15601** | 15600 | 1.00 |

* **`L_agree ≍ q`**, not `q²` and not `1/ε`.  For an *above*-convergent the first disagreement is at
  `j = q` exactly (there `jp/q = p ∈ ℤ` while `jα < p`).  Below-convergents agree longer (up to `24q`).
* Disagreement density: `|D(N)|/N ≈ Nε/2`, i.e. **`|D(N)| ≍ N²ε/2`** (e.g. 485/306 at `N = 6·10⁴`:
  density 0.1462 against `Nε/2 = 0.1446`).
* **PROVED (MATH), Part VII.**  If `⌊jα⌋ ≠ ⌊jβ⌋` then an integer lies weakly between `jα` and `jβ`,
  hence `‖jα‖ ≤ |jα − jβ| = j|α−β|`.  Verified on every convergent tested (implication held in all
  cases, no exceptions).  So barrier disagreement happens **only at Diophantine contact times**.

## Parts XX, XXX–XXXII — monotone sandwich

**PROVED (MATH) (immediate).**  Confinement is `S_j ≤ b(j)`, so `b₁ ≤ b₂` pointwise gives
`W_{b₁} ⊆ W_{b₂}`.  Hence for `β⁻ < α < β⁺`:  `W_{β⁻} ⊆ W_α ⊆ W_{β⁺}` — the sandwich of Part XXXII
holds with no hypotheses.

**COMPUTATIONAL (exact big-int DP), `σ = ⌊Jα⌋`:**

| J | 8/5 | 19/12 | 65/41 | 84/53 | 485/306 | 1054/665 |
|---|---|---|---|---|---|---|
| 40 | 2.0954 | 1.000000 | 1.000000 | 1.000000 | 1.000000 | 1.000000 |
| 80 | 2.1231 | 0.905667 | 1.004623 | 1.000000 | 1.000000 | 1.000000 |
| 120 | 4.2743 | 0.832667 | 1.010595 | 1.000000 | 1.000000 | 1.000000 |

(ratio `|W_β|/|W_α|`.)  **The symmetric difference is exactly zero whenever `q > J`** — the rational
ensemble *is* the true ensemble, not an approximation of it.

## Parts XVII–XIX — transfer error

*Combinatorial:* `E(J,p,q) = log₂|W_β| − log₂|W_α|` is `0` for `q > J`; for `65/41` it grows
super-linearly once `J ≫ q` (`+0.013` at `J=60` → `+0.605` bits at `J=300`).

*Pressure-level (the observable that matters, Part XIV):* swapping the barrier while holding the
3-adic environment and chain weights fixed, at `J = 400`, over `λ ∈ {1,5,7,11}`:

| p/q | max\|Δrate\| | Δrate/ε | mean\|Δw\| per block | mean\|Δw\|/ε |
|---|---|---|---|---|
| 8/5 | 3.7e-3 | 0.247 | 2.7e-2 | 1.80 |
| 19/12 | 1.7e-4 | 0.104 | 2.2e-3 | 1.36 |
| 65/41 | 5.0e-5 | 0.124 | 7.1e-4 | 1.75 |
| 485/306 | < 1e-6 | ≈0 | 5e-6 | 1.04 |

**`E ≤ C·N·|α−p/q|` with `C ≈ 1–2` per block — Part XIX's best case, measured.**  The rate
perturbation is `≈ 0.1·ε`, four orders of magnitude below the available margin at `485/306`.

## Parts XII–XIII — contraction constants and the uniform margin

Long-run exact rates at `J = 400` (max over the `λ` sample), against `θ_max = 0.137`:

| barrier | α | 8/5 | 19/12 | 65/41 | 485/306 |
|---|---|---|---|---|---|
| `Θ` | 0.03536 | 0.03659 | 0.03523 | 0.03541 | 0.03536 |
| margin `δ = θ_max − Θ` | 0.1016 | 0.1004 | 0.1018 | 0.1016 | 0.1016 |

**The margin is uniform across convergents and equals the true one to 4 decimals from `65/41` on**
— no shrinkage, no oscillation (COMPUTATIONAL, 4 λ's at one J).

## Parts X–XI, XXXIV–XXXV — why this buys nothing

1. **The ShapeTail certificate is already barrier-invariant — PROVED (LEAN).**
   `blockW_superEigen : ∀ (b : ℕ → ℕ) (σ l : ℕ) (x : Fin (σ+1)), ∑_y blockW b 3 σ l x y · hcert σ (l+1) y ≤ (3/2)·hcert σ l x`
   has **no hypothesis on `b`**; instantiating at `b(j) = ⌊485j/306⌋` and at a generic `b` both
   type-check.  Part XXXV's "invariant certificate" already exists, so the limit argument is
   unnecessary on this side.
2. **Rationalising `α` does not finitize the pressure model — REFUTED.**  Blackness of the cell of
   block `r` is tested modulo `3^{2r+2}`, a depth that grows with `r` and does **not** involve `α`.
   `α` enters only through `σ = ⌊Jα⌋`, `top[·]` and the chain weight `p = 1/α`.  A rational barrier
   makes `top` periodic and the weights rational, but the environment stays aperiodic and of
   unbounded 3-adic depth, so no finite state space appears.
3. **The two requirements are contradictory anyway.**  Faithfulness needs `q ≳ J` (exact for
   `q > J`); a period-`q` model only offers a finite-state advantage when `J ≫ q`.

## Status

* PROVED (LEAN): barrier-invariance of the ShapeTail certificate.
* PROVED (MATH): monotone sandwich `W_{β⁻} ⊆ W_α ⊆ W_{β⁺}`; the contact implication
  `⌊jα⌋ ≠ ⌊jβ⌋ ⇒ ‖jα‖ ≤ j|α−β|`.
* COMPUTATIONAL: `L_agree ≍ q`; `|D(N)| ≍ N²ε/2`; zero symmetric difference for `q > J`;
  `E ≈ C N ε` with `C ≈ 1–2`; uniform margin `δ ≈ 0.1016` across convergents.
* REFUTED: "rational barrier ⇒ finite-state pressure model"; the usefulness of the approximation
  route for the open problem.
* OPEN (unchanged): `OddDarkPressure` / `AverageOddDarkPressure`; the ShapeTail entropy comparison.
