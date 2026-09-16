# Round 18 — back to the density route: `ShapeTail` formalized down to a transfer-operator inequality

Nothing committed or pushed.  New Lean: `EOC/ShapeTail.lean` (imported from `EOC.lean`), plus
`EOC.LocalWindow.val_ge_of_subEigen`.  `lake build EOC` = **8794 jobs**, no `sorry`/`axiom`/`opaque`,
all new theorems on `[propext, Classical.choice, Quot.sound]`.
Data: `tight.py` (→ `tight400.txt`), `budget.py`.  Adversarial-realizability work is in
`scratch/oddpressure_2026-09-16/`.

## Part I — exact definitions (from the repo, not from memory)

| object | exact definition | file |
|---|---|---|
| `shellP b j0 σ` | confined words: `P.Positive ∧ BarrierConfined b P ∧ P.total = σ` (`mem_shellP_iff`) | `PrefixCollision.lean:162` |
| `BarrierConfined K w` | `∀ j ∈ Icc 1 N, S_j ≤ K j` | `CapacityBounds.lean:67` |
| `pairκ j0 P` | coarse class = **even prefix sums** `j ↦ if j even then S_j else 0` | `BlockCubeInstance.lean:320` |
| `pairπ j0 P` | internal config = odd prefix sums `r ↦ S_{2r+1}` | `BlockCubeInstance.lean:324` |
| `pairB c r` | `(Ioo (c_{2r}) (c_{2r+2})).filter (· ≤ b(2r+1))` — admissible `S_{2r+1}` | `BlockCubeInstance.lean:331` |
| `nCls T κ c` | `|{i ∈ T : κ i = c}|` (class size, as a real) | `BlockCubeInstance.lean:42` |
| `Elig b c r` | `{x ∈ pairB : x+1 ∈ pairB}` | `OddBlack.lean:79` |
| `ShapeGood b N0 c r` | `|pairB c r| ≤ N0 ∧ (Elig c r).Nonempty` | `OddBlack.lean:120` |
| `Dark m d lam r x` | `distZ(pairPhase lam m (2r+1) x − pairPhase lam m (2r+1) (x+1)) < d` | `OddBlack.lean:116` |
| `Nodd m d lam P` | `#{r < j0/2 : own choice S_{2r+1} ∈ Elig ∧ Dark}` | `OddBlack.lean:161` |
| `GoodPair b m N0 d lam c r` | `|pairB| ≤ N0 ∧ ∃x, x,x+1 ∈ pairB, d ≤ distZ(phase diff)` | `WhiteContraction.lean:303` |
| `CriticalWhiteCount b j0 σ t U N0 d k ρ` | `∀u ≤ U, ∀λ ∈ cshell (σ+1) t u`: class-weighted mass of classes with `#good < k` is `≤ ρ·(total)` | `WhiteContraction.lean:373` |
| `ShapeTail b j0 σ N0 K ρ₁` | class-weighted mass with `#ShapeGood < K` is `≤ ρ₁·|shellP|` | `OddBlack.lean:248` |
| `OddDarkPressure b j0 σ t U d s M` | `∀u ≤ U, ∀λ ∈ cshell`: `∑_{P∈shellP} s^{Nodd λ P} ≤ M·|shellP|` | `OddBlack.lean:258` |
| `λ` | frequency, ranging over `ShellDecomposition.cshell (σ+1) t u`, `u ≤ U` | `ShellDecomposition.lean:114` |
| `ξ = λ2^{−m}`, `m = σ+1+t` | **not a Lean object**; enters only through `pairPhase`/`collatzPhase` | — |
| local window, local environment, triangle depth, admissible/adversarial unit | **not Lean objects** — they exist only in the Python experiments (`scratch/cw*`); `LocalWindow.lean` has the abstract kernel `ker`/`val` over an abstract finite state type and `val_le_of_superEigen` | — |

**Important correction to the working picture:** the *only* Lean content of the "local window" is the
abstract layered kernel.  The bridge from the confined-word ensemble to that kernel is explicitly
not formalized (`LocalWindow.lean` docstring).  That same missing bridge is what blocks *both*
remaining inputs.

## Part II — exact dependency graph

```
  tilted class-sum inequality        (finite transfer-operator statement, OPEN)
      │  ShapeTailRed.tightTail_of_tilted            [PROVED (LEAN), new]
      ▼
  TightTail b j0 σ T ρ₁              (def, new)
      │  ShapeTailRed.shapeTail_of_tightTail         [PROVED (LEAN), new]
      │     side condition  K + T + σ/(N0+2) ≤ j0/2
      ▼
  ShapeTail b j0 σ N0 K ρ₁   +   OddDarkPressure b j0 σ t U d s M   (OPEN)
      │  OddBlack.criticalWhiteCount_of_shape_and_oddPressure        [PROVED (LEAN)]
      │  ShapeTailRed.criticalWhiteCount_of_tight_and_oddPressure    [PROVED (LEAN), new wrapper]
      │     side condition  M ≤ ρ₂((1+s)/2)^n
      ▼
  CriticalWhiteCount b j0 σ t U N0 d k (ρ₁+ρ₂)
      │  WhiteContraction.lowFreqDecay_of_criticalWhiteCount         [PROVED (LEAN)]
      │     side condition  κ(d,N0)^{2k} + ρ ≤ C·2^{−γ j0}
      ▼
  DecayInterface.LowFreqDecay b j0 σ t U C γ
      │  WhiteContraction.weightedFourier_of_criticalWhiteCount      [PROVED (LEAN)]
      │     (via DecayInterface.weightedFourier_of_lowFreqDecay_and_sieve + PsiSieve (C3))
      ▼
  WeightedChain.WeightedFourier b N j0 s σ ε
      │  WeightedChain.weighted_phi_decay_implies_exceptional_bound  [PROVED (LEAN)]
      ▼
  EOC exceptional-set count
```
Every arrow is a proved Lean theorem; the only hypotheses are the two boxes marked OPEN.

## Part III–VI — `ShapeTail` in Lean

**Not fully proved — but reduced, in Lean, to a single finite transfer-operator inequality.**
The full large-deviation proof of the pressure round (cycle lemma + generating function + contact
martingale) was *not* formalized; instead the statement was decomposed, and one of its two failure
modes was discharged **deterministically**.

1. **`shapeGood_iff` [PROVED (LEAN)]** — `ShapeGood ↔ 2 ≤ |B_r| ≤ N₀`.  (`Elig` is nonempty iff
   `|B_r| ≥ 2`, because `pairB` is an interval.)  So a block fails for exactly two reasons:
   **tight** (`|B_r| ≤ 1`) or **big** (`|B_r| > N₀`).
2. **`tight_iff` [PROVED (LEAN)]** — tight ⟺ `S_{2r+2} ≤ S_{2r}+2` (the digit pair is `(1,1)`) or
   `b(2r+1) ≤ S_{2r}+1` (the barrier cuts the block).
3. **`sum_card_pairB_add_le` [PROVED (LEAN)]** — the exact **block budget**
   `∑_{r<R} (|B_r| + 1) ≤ σ`, by `|B_r| + 1 ≤ S_{2r+2} − S_{2r}` and telescoping.
4. **`card_big_mul_le` [PROVED (LEAN)]** — hence `#big · (N₀+2) ≤ σ`: **big blocks are
   deterministically few**, with no counting input whatsoever.
5. **`shapeTail_of_tightTail` [PROVED (LEAN)]** — if `K + T + σ/(N₀+2) ≤ j₀/2` then
   `TightTail(T,ρ₁) ⇒ ShapeTail(N₀,K,ρ₁)`.
6. **`card_class_eq_prod` [PROVED (LEAN)]** — a coarse class has size `∏_r |B_r|` (from the
   repo's `pairDecomposition` fibre bijection).
7. **`sum_pow_tight_eq_class_sum` [PROVED (LEAN)]** — `∑_{P∈shellP} u^{#tight(P)} =
   ∑_c (∏_r |B_r|)·u^{#tight(c)}`: the word-level tilted sum **is** the class-level partition
   function that every DP/transfer-operator computation in this project evaluates.
8. **`tightTail_of_tilted` [PROVED (LEAN)]** — Chernoff: if `∑_c (∏_r|B_r|) u^{#tight(c)} ≤
   ρ₁ u^T |shellP|` for some `u ≥ 1`, then `TightTail`.
9. **`criticalWhiteCount_of_tight_and_oddPressure` [PROVED (LEAN)]** — the single-hypothesis
   wrapper asked for in Part LV, with `ShapeTail` discharged internally.
10. **`LocalWindow.val_ge_of_subEigen` [PROVED (LEAN)]** — dual of `val_le_of_superEigen`; the
    lower-bound certificate form needed for the denominator `|shellP|` of the tilted ratio.

So `ShapeTail` is **not yet unconditional**, but its remaining content is now exactly:
`∑_c (∏_r |B_r|)·u^{#tight(c)} ≤ ρ₁ u^T |shellP|` — a statement about one finite nonnegative
transfer operator (state = even prefix sum, block weight `|B_r|·u^{[|B_r| ≤ 1]}`), for which the
repo already has both certificate directions.

## Part IV/V/LII — constants, finite base, and the `N₀` trade-off (**new constraint found**)

Exact confined-ensemble DP (`tight.py`, uniform law on `C_J`; `J = 200` and `J = 400` agree):

* **mean `#tight` = 0.4005 per block (J=200), 0.3993 (J=400)** — matching `p² = 0.398`, `p = 1/α`.
* Chernoff rate for `P(#tight ≥ T)` (bits per digit):

| `T/R` | 0.42 | 0.45 | 0.48 | 0.50 | 0.55 | 0.60 |
|---|---|---|---|---|---|---|
| J = 200 | 0.0011 | 0.0070 | 0.0185 | 0.0287 | 0.0652 | 0.1177 |
| J = 400 | 0.0013 | 0.0073 | 0.0191 | — | — | — |

* **The deterministic big-block bound costs `σ/((N₀+2)R) ≈ 2α/(N₀+2)`**, so the reduction needs
  `T/R ≤ 1 − K/R − 2α/(N₀+2)`:

| `N₀` | 4 | 6 | 10 | 14 | 20 | 30 |
|---|---|---|---|---|---|---|
| loss `2α/(N₀+2)` | 0.5283 | 0.3962 | 0.2642 | 0.1981 | 0.1441 | 0.0991 |
| max `T/R` at `K/R = 0.1` | **0.3717** | 0.5038 | 0.6358 | 0.7019 | 0.7559 | 0.8009 |
| margin over mean tight | **−0.027** | +0.104 | +0.236 | +0.302 | +0.356 | +0.401 |

  **At `N₀ = 4` — the parameter used by the earlier pressure round — this reduction route fails**
  (the admissible `T/R = 0.372` lies *below* the mean 0.40, so no exponential rate exists).  It
  works from `N₀ ≥ 6`, comfortably from `N₀ ≥ 10`.  *(This constrains the reduction route only; the
  pressure round's own LD proof at `N₀ = 4` is untouched.)*
* **Robust interior point (Part L):** `N₀ = 10`, `T/R = 0.55`, `K/R = k/R + n/R ≤ 0.186`,
  `ρ₁ = 2^{−0.065 J}`, and the contraction side (`κ = 1 − 2(1−cos πd)/N₀ = 0.9999154` at
  `d = η/2 = 1/108`) then admits `γ ≈ 1.1·10⁻⁵ > 0`.  Since only `γ > 0` is needed and
  `rate = 0.065 ≫ γ`, the budget is not tight anywhere except at `N₀ = 4`.
* **Finite base (Part V):** none is needed for the reduction — items 1–10 hold for all `j₀ ≥ 1`.
  A finite base would be needed only for the remaining transfer-operator inequality.

## Part LI — what the chain actually demands of the constants

`lowFreqDecay_of_criticalWhiteCount` requires `κ(d,N₀)^{2k} + ρ ≤ C·2^{−γ j₀}` with `ρ = ρ₁+ρ₂`.
So **`ρ₁` must be exponentially small in `j₀`** — a crude constant-`ρ₁` bound is useless, which is
why the LD structure cannot be avoided.  Conversely `γ` may be arbitrarily small, which is what
gives the `N₀`/`k` trade-off its slack.

## The denominator was already in the repo; the certificate for the numerator

The remaining obligation of `tightTail_of_tilted` is a ratio.  Its **denominator is already
formalized**: `CapacityBounds.shell_choose_le_mul_card` (chord rotation = cycle lemma, with
`ChordRotation.chord_rotation_nat`) gives `C(σ−1, j₀−1) ≤ j₀·|P_σ|`.  New wrapper
**`choose_le_mul_card_shellP`** and **`tightTail_of_tilted_choose`** [PROVED (LEAN)] put the
obligation in fully explicit form:

  `j₀ · ∑_c (∏_r |B_r|)·u^{#tight(c)}  ≤  ρ₁ · u^T · C(σ−1, j₀−1)`.

**Exact integer verification** (`exact.py`, Python big-ints, `u = 3`, `T = 0.55R`):

| J | 40 | 80 | 120 | 160 | 200 |
|---|---|---|---|---|---|
| `log₂ Z(1) = log₂|P_σ|` | 50.85 | 109.86 | 169.06 | 228.88 | 288.40 |
| `log₂ C(σ−1,j₀−1)` | 55.73 | 114.88 | 175.67 | 235.12 | 294.61 |
| chord-rotation slack `log₂[C/(j₀Z(1))]` | −0.44 | −1.30 | −0.30 | −1.08 | −1.43 |
| resulting `log₂ ρ₁` | −1.60 | −3.73 | −7.22 | −9.28 | −11.61 |
| rate (bits/digit) | 0.040 | 0.047 | 0.060 | 0.058 | **0.058** |

So the cycle lemma costs **only 0.3–1.4 bits in total** — negligible — and the inequality the Lean
theorem needs holds with a stable exponential rate ≈ 0.058 bits/digit.  Best tilt is `u = 3` or `4`
(`u = 2`: 0.046, `u = 6`: 0.046).

**Is there a finite certificate?** `LocalWindow.ker_le_of_superEigen` (new, pinned form) turns the
obligation into: find `h > 0` with `∑_y w_l(x,y)h_{l+1}(y) ≤ M·h_l(x)`, then `Z(u) ≤ M^R·h/h`.

* **Budget:** at `T/R = 0.60`, `M` may be as large as **3.82–3.87 bits/block**.
* **True pinned growth:** 3.564 / 3.625 / 3.661 bits/block at `J = 120 / 200 / 300`.
* **Best possible certificate value** (free-endpoint growth, the Collatz–Wielandt optimum):
  **3.597 / 3.643 / 3.674** — margin **≈ 0.19 bits/block, stable in `J`** [COMPUTATIONAL].
* **A naive geometric `h(v) = λ^v` (headroom `v`) is NOT enough**: best `log₂M = 4.516` at `λ = 1.8`
  (worst state: reachable, large headroom, barrier-increment type `(inc₁,inc) = (2,4)`), margin
  −0.70 [REFUTED].  A *phase-blind* certificate is in fact invalid — with `inc = 4` taken at every
  layer the headroom drifts and the operator is unbounded.
* **The certificate must be layer-dependent** (which `ker_le_of_superEigen` allows: `h : ℕ → σ → ℝ`),
  absorbing the quasi-periodic barrier increments `inc ∈ {3,4}` (frequencies 0.83 / 0.17).  Phase-
  averaging a geometric `h` already gives ≈ 3.81 vs budget 3.82 (marginal); the optimal layer-
  dependent `h` reaches 3.64 with the full 0.19-bit margin.
* **Periodic relaxation is free** (`periodic.py`): replacing `⌊iα⌋` by `⌊i·p/q⌋` with `p/q > α`
  dominates the true barrier (so it only increases `Z`) and makes the operator genuinely periodic,
  hence the certificate finite.  Cost at `J = 200`: `p/q = 65/41` → **+0.04 bits total**;
  `485/306` → **+0.000**; (`8/5` → +1.8 bits, still inside the 11.7-bit margin).

**Conclusion for the shape side [Tier C]:** the remaining content of `ShapeTail` is one finite
rational super-eigenvector certificate on the state space (headroom, barrier phase mod `q`), for a
periodic barrier `p/q > α`, and such a certificate exists with ≈ 0.19 bits/block of margin.  The
Lean consumer for it is already proved.

## Status of this half

* Tier A (PROVED (LEAN)): items 1–10 above; the whole chain from the tilted class-sum inequality to
  the EOC exceptional-set count.
* Tier B (PROVED (MATH), Lean-ready): the pressure round's shape LD at `N₀ = 4`
  (`scratch/pressure_2026-09-16`), rate `c(0.1) = 0.073` — still not formalized.
* Tier D (COMPUTATIONAL): the tight-block mean and Chernoff rates above; the `N₀` trade-off table.
* OPEN: the tilted class-sum inequality (equivalently `TightTail`), and `OddDarkPressure`.
