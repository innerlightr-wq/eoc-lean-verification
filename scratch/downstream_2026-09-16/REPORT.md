# Downstream EOC chain conditional on the arithmetic frontier (research round, 2026-09-16)

Nothing committed or pushed.

**New Lean** (imported by `EOC.lean`; `lake build EOC` = 8806 jobs; every theorem below uses only `propext`,
`Classical.choice`, `Quot.sound`; no sorry/native_decide):
* `EOC/ShapeRegion.lean`: `arith_down`, `arith_up`, `arith_mono`, `barrier_offset`, `lower_barrier`,
  `arith_region`, **`shapeTail_region`**, `shapeTail_lowerShell`.
* `EOC/FrontierRegion.lean`: `PowerOfTwoDangerousWindowSparsityAt` (OPEN), `ofAt`, `q_le_of`,
  `logb_bridge_le_of`, `summedPressure_at`, `summedPressure_of_sparsityAt`, `shellP_nonempty_of`,
  **`lowFreqDecay_of_sparsityAt`**.
* `EOC/ConditionalChain.lean`: `min_mul_pow_le`, **`hfin_of_split`**, **`weightedFourier_of_sparsityAt`**,
  `PairInputs`, `weightedFourier_of_pairInputs`, **`exceptional_bound_of_pairInputs`**.

**Scripts.**
* `shellregion.c` → `SHELLREGION.txt`: Haar-weight profile over prefix shells.
* `gamma.py` → `GAMMA.txt`: best γ allowed by the Lean hypotheses, and the heuristic exponent.

## 1. Final theorem and hypotheses (PROVED (MATH) audit of the Lean statements)

`WeightedChain.weighted_phi_decay_implies_exceptional_bound U K j0 A C c` gives
#(E_U ∩ [0, 2^K)) ≤ (C e^{λ*U}/2)(2^K)^{1 − I₀A}. Its hypotheses, after this round
(`exceptional_bound_of_pairInputs`):

| hypothesis | content | class | status |
|---|---|---|---|
| hC, hj1, hjN, hbK, hNA | 1 ≤ C, 1 ≤ j0 < N, b_U(j0) < K, AK ≤ N | B | parameter choice |
| trivial branch | 2^{s+1−K} ≤ c s σ | A | PROVED (LEAN) |
| ShapeTail on the shell | inside `lowFreqDecay_of_sparsityAt` | A (was C) | **PROVED (LEAN)** on b₀(j) − j/300 ≤ σ ≤ b_U(j), σ + 2 ≤ 2j |
| pressure → LowFreqDecay on the shell | `lowFreqDecay_of_sparsityAt` | A | PROVED (LEAN) for any U, σ with 63σ + 37 ≤ 100j |
| arithmetic input on the shell | `PowerOfTwoDangerousWindowSparsityAt U j0 σ t Us K d a b` | E | **OPEN** (σ-, U-parametric form of the frontier) |
| rate/budget conditions | budget, k+n ≤ Kb, N0, d, θ′ > 1/6, (3C/(θ′−1/6))² ≤ j, n ≥ νj, θ′+γ ≤ ν, γj ≤ j/300 − δ, γj ln2 ≤ 8kd²/N0 | B | finite arithmetic (§5) |
| sieve split | N_u, 1 ≤ N_u < j0, 2·Xmax(N_u) ≤ 2^{σ+1+t} | B | not yet instantiated |
| hfin, low shells u ≤ Us | (Us+1)·2^t·4·2^{−γj0}|P_σ|²·(1+(σ+1)/2) part of `hsplit` | A + B | reduction PROVED (LEAN) (`hfin_of_split`); needs a lower bound on |V_{σ,s}| (binomial counting, not yet in Lean) |
| hfin, high shells u > Us | Σ_{u>Us} min(1, 2^t/2^{u+1})·2·sieveBound(N_u, 2^u)² | D | quantitative (C3) sieve exponent on confined shells: θ_M = H_R/α = 0.70516 PROVED (MATH) in the tilted model, COMPUTATIONAL (0.64–0.80) on the confined shell; not proved |
| hweight | Σ c·haarShare ≤ C·HaarMass | D (counting) | reduces to (i) ε = O(1) on pairs with hfin and (ii) exponential smallness of Haar weight × 2^{s+1−K} outside; large-deviation counting of confined lattice paths, COMPUTATIONAL (§2), not proved |

No new obstacle (class F) was found. The only arithmetic assumption is the frontier Prop, now on a family of shells.
The remaining non-arithmetic inputs are two quantitative counting/sieve estimates (hfin high part, hweight) and one
binomial lower bound.

**Dependency graph (Lean).**
```
ShapeRegion.shapeTail_region ──┐
PowerOfTwoDangerousWindowSparsityAt (OPEN) → FrontierRegion.summedPressure_of_sparsityAt
  → AverageOddDark.lowFreqDecay_of_shape_and_summedPressure   = FrontierRegion.lowFreqDecay_of_sparsityAt
  → DecayInterface.weightedFourier_of_lowFreqDecay_and_sieve  (+ hfin via ConditionalChain.hfin_of_split)
  → ConditionalChain.weightedFourier_of_sparsityAt / PairInputs
  → WeightedChain.weighted_phi_decay_implies_exceptional_bound (+ hweight)
  = ConditionalChain.exceptional_bound_of_pairInputs
```
The route uses the frequency-summed white-count split; the per-frequency `CriticalWhiteCount` Prop is not
instantiated.

## 2. Required shell region (COMPUTATIONAL + HEURISTIC scaling)

With x = b(j0) − σ and L = N − j0, the trivial branch outside x > x* adds at most 1 to C exactly when
x* ≈ 2.1·L (x*/L = 1.89–2.14 at K = 1500, 3000; A = 0.635 … 0.70). The Haar-weight median of x is 6–20 and the 99%
quantile is 15–48 (`SHELLREGION.txt`). HEURISTIC scaling: the trivial cost 2^{(αA−1)K} = 2^{αL} must be beaten by a
Gaussian-in-x tail of width ≈ √L, so x* = Θ(L).

In the regime where an improvement is possible, A − 1/α ≈ γ/((2−H)α²) (§5), so L ≈ 0.6γ·j0 and
x* ≈ 1.3γ·j0 ≪ j0/300. The Lean region δ ≤ j/300 therefore covers the needed shells.

Offsets:
* ShapeTail is monotone upward in σ while σ ≤ 2j − 2 (`arith_up`, PROVED (LEAN)), so a fixed U > 0 costs nothing
  for the shape tail.
* The pressure side needs 63σ + 37 ≤ 100j, i.e. U ≲ 0.0023j (fine for fixed U).
* The arithmetic Prop at U > 0 is a different environment statement (the Bset caps move with the barrier); no
  monotonicity in U is known for it.

## 3. hfin and hweight

* hfin (`DecayInterface.weightedFourier_of_lowFreqDecay_and_sieve`):
  (1+(σ+1)/2) Σ_{u<σ+1+t} min(1, 2^t/(2·2^u))·mixedBound(u) ≤ ε²|P_σ|²|V_{σ,s}|/2^t.
  * mixedBound(u) = min(2^{u+1}·C·2^{−γj0}|P_σ|², 2·sieve²) for u ≤ Us, and 2·sieve² otherwise.
  * It controls the full frequency range of the twist expansion: the low/high split plus the weight
    min(1, 2^t/2^{u+1}).
  * Low part: exactly bookkeeping (`hfin_of_split`, PROVED (LEAN)), cost (Us+1)·2^t per unit decay bound.
  * Solving the inequality needs γ j0 ≥ 2t − log₂|V_{σ,s}| + O(log) ≈ (2 − H₂(1/α))·t (HEURISTIC evaluation of
    |V| ≈ 2^{H₂ t}).
  * High part: needs Σ_{u>Us} a_u ≲ 2^{−(2−H)t} with a_u the normalized sieve bound. This holds with Us ≈ 1.49t if
    a_u ≈ 2^{−0.705u} (HEURISTIC/COMPUTATIONAL). Not bookkeeping.
* hweight (`ShellwiseChain`): Haar-weight large deviations over (s, σ). Not bookkeeping, not an open conjecture;
  not yet proved.

## 4. Kill conditions

* 1 (certificate fails off top shell): not fired; the certificate is PROVED (LEAN) on the region.
* 2 (offset destroys monotonicity): not fired for ShapeTail; the pressure Prop has no U-monotonicity.
* 3 (hfin/hweight encode a genuine estimate): **partially fired**. The low part of hfin is bookkeeping (proved); the
  high part and hweight are genuine quantitative counting/sieve estimates, not unsolved conjectures.
* 5 (nonpositive exponent): not fired (heuristically positive, §5).

## 5. Quantitative (γ: PROVED (MATH) from the Lean constraints; ε: HEURISTIC)

**Rate budget.** Per unit j: k/j + γ ≤ 1/2 − 31/100 (ShapeTail certificate) − α/(N0+2) (class loss) − 1/6 (pressure
rate) = 0.0116 at N0 = 133. The rate is γ ≤ 8(k/j)d²/(N0 ln 2):

| d | γ_max | heuristic ε |
|---|---|---|
| 1/108 | 8.6·10⁻⁸ | 1.1–2.6·10⁻⁹ |
| 1/2 (formal maximum; hypothesis plausibility at such d unknown) | 2.5·10⁻⁴ | 3.2–7.4·10⁻⁶ |

**Exponent.** E = 1 − I₀A with A − 1/α limited by hfin:
* model t = αL: ε = (1−H)γ/((2−H)α) = 0.0301γ, matching `scratch/decay_2026-09-15` model 1;
* conservative, t up to (α + 2.1)L: 0.0129γ.

Baseline H₂(1/α) = 0.9499555. Conditional exponent ≤ 0.9499555 − O(10⁻⁹) at d = 1/108.

**Dominant loss.** White contraction κ(d, N0)^{2k} ≤ exp(−8kd²/N0): the factor d²/N0 ≈ 6.4·10⁻⁷ at d = 1/108. Then
the pressure rate 1/6 consumes 0.167 of the 0.19 budget, and the Fourier conversion γ → A costs a factor
0.013–0.030.

**Most valuable constant.** The white-contraction strength (dark threshold d and the per-block κ). The pressure rate
1/6 vs budget 0.19 is second.
