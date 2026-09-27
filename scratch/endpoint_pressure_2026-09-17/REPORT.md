# Frequency-summed endpoint-pressure audit — 2026-09-17

Status vocabulary: **PROVED (LEAN)**, **PROVED (MATH)**, **EXTERNAL THEOREM**,
**COMPUTATIONAL**, **HEURISTIC**, **CONJECTURAL**, **REFUTED**, **OPEN**, and
**REQUIRES ADDITIONAL JUSTIFICATION**.

## Executive result

The previous audit's central logical claim is correct, with one important refinement.

* The weakest pressure hypothesis used by the current multi-white chain is exactly the existing
  `AverageOddDark.SummedOddDarkPressure`. I gave it the arithmetic-facing, rate-parameterized name
  `EndpointPressure.PowerOfTwoSummedPressureAt`. It sums over the complete frequency shell before
  imposing the bound and contains no windows, no per-frequency assertion, and no start-state norm.
  **PROVED (LEAN)**.
* A more concrete arithmetic sufficient condition is
  `PowerOfTwoPinnedKernelPressureAt`. It bounds the shell sum of the actual pinned matrix
  coefficient `ker ... 0 ... σ`, including exactly the bridge prefactor. It has neither
  `sup_λ` nor `sup_x`. **PROVED (LEAN)** to imply the weakest summed pressure.
* The weakest summed hypothesis now implies `LowFreqDecay`, `WeightedFourier`, the generic final
  bound, and the same explicit infinite-family bound
  `H₂(1/α) - I₀/2,000,000`. **PROVED (LEAN)**.
* The old dangerous-window frontier implies the new weakest frontier at `θ=1/6`, both locally and
  for the explicit family. **PROVED (LEAN)**.

The refinement is essential: the pinned-kernel proposition is not literally the weakest condition.
`PressureBridge.sum_pow_nodd_le_geo` is one-sided, so the summed odd-dark moment may hold even when
the geometric-kernel majorant does not. The mathematically honest architecture is therefore

```text
old dangerous-window frontier
              │
              ▼
PowerOfTwoSummedPressureAt  ──► LowFreqDecay ──► multi-white/final chain
              ▲
              │
PowerOfTwoPinnedKernelPressureAt
```

The highest-value next theorem is a propagated-state pinned-kernel pressure theorem. The focused
experiment below shows an exponential gap between the actual pinned product and the product of
independent window sup norms. This is **COMPUTATIONAL**, not an arithmetic proof.

## Repository

### 1–6. State, builds, changed files

1. Branch: `research-sparse-visits-2026-09-16`.
2. HEAD: `14dea46ae5af816754cf3883475fa73dea598130`.
3. Starting `lake build EOC`: successful, 8,813 jobs; the pre-existing tree emitted 648 counted
   warning lines in the prior fresh audit. **PROVED (LEAN)** build result.
4. Final `lake build EOC`: successful, 8,815 jobs, 657 `warning:` lines. The additional warnings
   are lint/style warnings (header, long line, scoped-classical, heartbeat option), not proof
   failures. **PROVED (LEAN)**.
5. Files added this round: `EOC/EndpointPressure.lean`,
   `EOC/EndpointPressureFamily.lean`, `scratch/endpoint_pressure_2026-09-17/propagated_state.py`,
   its JSON output, and this report. `EOC.lean` was extended with two imports. Existing dirty work
   was preserved. The initially modified docs remained modified; the initially untracked Lean
   modules remained untracked. No file was discarded.
6. No commit, push, merge, rebase, checkout, reset, or public-branch mutation was performed.

The final source scan finds no proof-hole occurrence of `sorry` or `admit`, no `native_decide`, and
no custom `axiom` in the EOC Lean sources; search hits are explanatory prose. Fresh `#print axioms`
on all six new key theorems returns exactly `[propext, Classical.choice, Quot.sound]`.
**PROVED (LEAN)** under standard Mathlib foundations.

## Old frontier

### 7–13. Exact definition and artifacts

For naturals `U,j,σ,t,Us,K` and reals `d,a,b`, the old proposition is

```text
∀ u ≤ Us, ∀ λ ∈ cshell(σ+1,t,u), ∃ bad ⊂ ℕ,
  #bad ≤ (2/9) floor((j/2)/K) + (a log₂j+b)/K,
  ∀ i < floor((j/2)/K), i ∉ bad → ∀ y : Fin(σ+1),
    val(geoW(p,q,oddW(b_U,m,d,3,λ),σ), iK,K,y) ≤ 2^(2K/10),
```

where `m=σ+1+t`, `p=(j-1)/(σ-1)`, and `q=(σ-j)/(σ-1)`.

7. This is the exact Lean definition of `PowerOfTwoDangerousWindowSparsityAt`.
8. It is universal in shell index `u`, frequency `λ`, window index `i`, and every admissible start
   state `y`; the bad set may depend on `u,λ`.
9. There is no syntactic `sup_λ`, but the universal per-`λ` assertion is logically the same
   worst-frequency requirement for the downstream estimate.
10. `∀ y` is the row-sum/`L∞→L∞` window norm requirement.
11. The binary safe threshold is `θ_d=1/10` per valuation step (`2K` steps per pair window).
12. The dangerous fraction is `φ=2/9`, plus `(a log₂j+b)/K`.
13. A bad window is replaced by the universal rate `2/5`, obtained from the geometric ceiling.
   Thus `1/10+(2/9)(2/5-1/10)=1/6`. **PROVED (LEAN)** in
   `FrontierRegion.summedPressure_of_sparsityAt`.

## Actual downstream need

### 14–17. Quantity, sums, endpoints, norm

14. The exact consumed quantity is, for every `u≤Us`,

```text
Σ_{λ∈cshell(σ+1,t,u)} Σ_{P∈shellP(b_U,j,σ)}
  3 ^ Nodd(b_U,σ+1+t,d,λ,P)
≤ 2^(u+1) 2^(C log₂j + θj) #shellP(b_U,j,σ).
```

This is `SummedOddDarkPressure`; all summands are nonnegative.

15. The frequency sum is inside the hypothesis. No individual-frequency upper bound is used after
this boundary. **PROVED (LEAN)** by tracing `MultiWhite.lowFreqDecay_multi`.
16. At kernel level a sufficient quantity is

```text
A(j,σ) Σ_{λ∈cshell} ker(geoW(...,oddW(...,λ),σ), 0,j/2,0,σ)
≤ 2^(u+1) 2^(C log₂j+θj),
A(j,σ)=σj / ((j-1)/(σ-1)).
```

Both start and endpoint are pinned: `0→σ`. There is no endpoint maximum.
17. The weakest norm is therefore no operator norm at all: it is the positive shell-summed odd-dark
moment. Among kernel formulations, the pinned matrix coefficient is sufficient and strictly better
aligned than an `L∞` row norm. **PROVED (LEAN)** sufficiency; literal equivalence is **REFUTED** by
the one-sided pressure bridge.

## New frontier

### 18–23. Definition and quantifiers

18. The core definition is

```lean
abbrev PowerOfTwoSummedPressureAt (U j σ t Us : ℕ) (d θ C : ℝ) : Prop :=
  AverageOddDark.SummedOddDarkPressure (collatzBarrier U) j σ t Us d 3 θ C
```

The provisional name `PowerOfTwoEndpointPressureAt` was not used for this weakest boundary because
its actual expression is a path moment, not an exposed endpoint kernel. The concrete endpoint object
is named `PowerOfTwoPinnedKernelPressureAt`.

19. Both propositions are parameterized by `θ` and `C`; `1/6` is not built into the interface.
20. `λ` is summed inside each inequality. Per-`λ` control is gone.
21. The core moment has no start state. The concrete kernel has the single actual start state `0`.
22. The kernel endpoint is the single actual endpoint `σ`. Summing endpoints would be stronger here,
because all coefficients are nonnegative; no max is needed.
23. Shell index `u` remains universal because `LowFreqDecay` requires the bound for every shell.
Within a shell, frequencies are summed. Good `(s,σ)` pairs remain universal because final shell
counting applies `WeightedFourier` pairwise.

## Logic

### 24–29. Formal implications and strictness

24. `summedPressure_of_pinnedKernel`: pinned shell-summed kernel pressure implies the exact summed
odd-dark pressure. **PROVED (LEAN)**.
25. `lowFreqDecay_of_summedPressure`: arbitrary `θ<C`-loss pressure plus the current shape and
multi-white numerical hypotheses implies `LowFreqDecay`. It imports no dangerous-window argument.
**PROVED (LEAN)**.
26. `exceptional_bound_of_summedPressure_and_scalar` is the generic final theorem, and
`EndpointPressureFamily.exceptional_bound_family_of_summedPressure` proves the same explicit family
and exponent from summed pressure alone. **PROVED (LEAN)**.
27. `summedPressure_of_dangerousWindowSparsity` proves the legacy frontier implies the new frontier
at `θ=1/6`. `exceptional_bound_family_of_dangerousWindowSparsity` verifies backward compatibility
through the new path. **PROVED (LEAN)**.
28. The converse between the actual power-of-two propositions is **OPEN**; no realizable kernel
counterexample was constructed.
29. Strict weakness of the abstract aggregate-pressure requirement is **PROVED (LEAN)** by
`aggregate_rate_counterexample`: three windows of rate `11/100` have average below `1/6`, while all
three exceed `1/10`, far above a `2/9` dangerous fraction. A second abstract separation is immediate:
one arbitrarily bad frequency with arbitrarily small weight can obey a weighted aggregate bound.
These prove the aggregation schemes are not logically equivalent in general, but do not by
themselves prove nonimplication on the restricted family of actual power-of-two kernels.

## Removed artifacts

### 30–35

30. `1/10` is absent from the core new theorem: **YES, PROVED (LEAN)**.
31. `2/9` is absent: **YES, PROVED (LEAN)**.
32. `2/5` is absent: **YES, PROVED (LEAN)**.
33. Per-`λ` control is absent: **YES, PROVED (LEAN)**.
34. Start-state supremum is absent: **YES, PROVED (LEAN)**.
35. Binary safe/danger classification is absent: **YES, PROVED (LEAN)**.

All three numerical artifacts remain only in the optional legacy implication.

## Computation

### 36–41. Focused propagated-state experiment

The one permitted focused experiment used the exact existing geometric transfer code, `d=1/108`,
`s=3`, `λ=1`, `t=floor(j/6)`, and `K=floor(7log₂j)` pair blocks. Floating-point results are
**COMPUTATIONAL**:

| `j` | pinned `0→σ` rate / `j` | unpinned propagated rate / `j` | product-of-window-sups / `j` | max window rate | dangerous fraction | log₂(sup product / pinned) |
|---:|---:|---:|---:|---:|---:|---:|
| 400 | -0.024390 | -0.004044 | 0.005555 | 0.053438 | 0 | 11.98 |
| 800 | -0.010166 | 0.001896 | 0.008974 | 0.023325 | 0 | 15.31 |
| 1600 | 0.000275 | 0.006636 | 0.015851 | 0.035038 | 0 | 24.92 |
| 3200 | 0.004925 | 0.008202 | 0.018044 | 0.026054 | 0 | 41.98 |
| 6400 | 0.006911 | 0.008834 | 0.020251 | 0.035924 | 0 | 85.38 |

36. These max-window rates are the old all-start-state sup rates at the family window length.
37. The actual pinned endpoint rates are much smaller. This is not a uniform theorem.
38. Full shell-summed rates were not computed: the relevant complete shells are enormous and the
requested focused experiment was spent on the propagated-state mechanism. Status: **OPEN**.
39. The λ=1 data have about `0.160` rate units of slack below `1/6` at `j=6400`, before polynomial
bridge loss. **COMPUTATIONAL**.
40. No claim about full frequency shells follows. **REQUIRES ADDITIONAL JUSTIFICATION**.
41. Available full-shell slack below `1/6` is therefore **OPEN**.

The negative rates at small `j` are possible because the geometric operator is substochastic. The
bridge prefactor contributes only `O(log j)/j`, but the full λ shell cardinality/weight cannot be
ignored.

## Operator analysis

### 42–47. Products, moments, and Parseval

42. The old proof bounds a product by products of independent `L∞` window norms. Each window may
choose a different worst start state.
43. The propagated coefficient `e₀ᵀK₁⋯K_We_σ` is the concrete object in the new wrapper. The table
shows an exponential total gap: the log₂ ratio grows from 12 to 85 over the tested range.
**COMPUTATIONAL**. An asymptotic exponential gap is **CONJECTURAL**.
44. The first positive moment—the L1 shell sum—is exactly the weakest current frontier.
**PROVED (LEAN)**.
45. A start-state or frequency second moment may prove it via Cauchy–Schwarz, but it is a stronger
input than necessary. No such estimate was proved. **OPEN**.
46. Summing λ after `Nodd` does not produce exact character cancellation: `3^Nodd` and all geometric
kernel terms are already nonnegative. Thus a direct Parseval identity at this endpoint is
**REFUTED**. Orthogonality would have to be used upstream, before absolute values/dark majorization.
47. An L2 shell frontier gives L1 by Cauchy–Schwarz with `sqrt(#shell)` loss. Since
`#cshell≤2^(u+1)`, a naively unnormalized L2 theorem pays `2^((u+1)/2)` and is not the weakest
interface. Whether upstream Fourier structure can more than repay this loss is **OPEN**.

Additive rates `r_i=(2K)⁻¹log₂ mass_i` describe products of scalar window bounds. The actual kernels
compose as matrices and sums occur before logs. Consequently `Σr_i` is valid only after a
submultiplicative norm reduction; it is not equal to the log of the propagated pinned coefficient.
This is why the new formal Prop is multiplicative/linear in masses, not a sum of local logarithms.

## Quantitative payoff

### 48–53. Current theorem and θ sensitivity

48. At `θ=1/6`, the existing explicit family remains exactly
`H₂(1/α)-I₀/2,000,000`; numerically the exponent saving is
`3.9659306387×10⁻⁸`. **PROVED (LEAN)**.

Lowering `θ` alone does not change that fixed theorem: its `P=1,080,000` and certified final exponent
were deliberately retained. The following table is a **HEURISTIC** one-pass family re-optimization,
not a Lean theorem. It keeps `q=Kb/j=205198/1080000`, takes `θ'=θ+0.001`, uses the exact contraction
cap

```text
γ ≤ κ(q-θ')/(ln 2+κ),   κ=(4/3)(1-cos(π/108)),
```

then sets the counting-scale estimate `P≈18/γ` and scales the existing certified exponent margin.

| `θ` | allowed `γ` | estimated `P` | estimated final exponent saving |
|---:|---:|---:|---:|
| 1/6 | 1.816e-5 | 991,296 | 4.32e-8 |
| 0.15 | 3.171e-5 | 567,645 | 7.55e-8 |
| 0.14 | 3.984e-5 | 451,795 | 9.48e-8 |
| 0.13 | 4.797e-5 | 375,217 | 1.14e-7 |
| 0.12 | 5.610e-5 | 320,836 | 1.34e-7 |
| 0.10 | 7.237e-5 | 248,737 | 1.72e-7 |

49–51. The requested `0.15`, `0.14`, and `0.13` values appear above. They require rebuilding and
formally checking a new family. **HEURISTIC**.
52. With the current block budget, the asymptotic critical value is
`θ_max≈Kb/j=0.189998148...`; strictly below it is required to choose `θ'>θ` and positive `γ`.
Finite log-absorption and counting impose additional margin. **PROVED (MATH)** from the displayed
contraction inequality; not packaged as a Lean optimization theorem.
53. At fixed `θ=1/6`, the dominant unresolved bottleneck is arithmetic endpoint pressure, not white
contraction. If substantially smaller `θ` is proved, the `γP≥18` final counting scale becomes the
next optimization target.

## Arithmetic difficulty

### 54–58. Calibration

54. The old frontier remains Type III: it asks for uniform short-orbit control for every frequency
and every start state, a digit-distribution style assertion beyond generic `×2` mixing.
55. The new frontier removes genuine analytic artifacts and is plausibly Type II/III boundary rather
than clearly Type III. That reclassification is **HEURISTIC**, not a theorem: the λ=1 calculation is
encouraging, but uniform full-shell control is still open.
56. The arithmetic content is a positive moment along short powers-of-two phase orbits in the
ternary/reciprocal representation. It is weaker than pointwise digit equidistribution because it
allows compensation across frequencies and paths, but still probes structured short orbits.
57. The new statement does not visibly imply the Erdős ternary-powers conjecture or full
Lagarias-style normality: it is an upper bound on an averaged positive dark-visit moment, not a
claim that every power has (or omits) specified ternary digits. Status: **PROVED (MATH)** at the
level of logical form; a formal model-theoretic nonimplication is **OPEN**.
58. A sufficient external input would be a uniform shell-averaged large-deviation theorem for the
dark-visit count along the relevant short `×2` orbits, with moment generating function at `log 3`
bounded by `2^(θj+O(log j))`, including the actual path weights. This is much weaker than full
normality but stronger and more tailored than currently quoted generic exponential-sum bounds.
No known theorem in the audited literature supplies it. **OPEN**.

## Recommendation

### 59–66. Decisive next step

59. Strongest new **PROVED (LEAN)** theorem:
`EndpointPressureFamily.exceptional_bound_family_of_summedPressure`. It gives the current explicit
exceptional-set bound from the frequency-summed moment, with no `1/10`, `2/9`, `2/5`, per-λ bound,
start-state supremum, or binary window split.
60. Strongest new **PROVED (MATH)** conclusion: the genuine downstream frontier is an L1 positive
moment; pinned propagated kernel coefficients are sufficient, while independent window norms are
not logically required.
61. Strongest **COMPUTATIONAL** observation: at λ=1 the product-of-window-sups/pinned-product ratio
has log₂ size `85.38` by `j=6400`, while the pinned rate is only `0.00691`.
62. Strongest negative: λ summation at this endpoint cannot itself create Fourier cancellation,
because absolute values/dark weights have already made every summand nonnegative. A naive Parseval
route is therefore not the next theorem.
63. Best next arithmetic theorem:

> **Propagated pinned-pressure theorem.** For each downstream good pair `(j,σ,t)` and shell `u`, the
> actual positive initial vector propagated through the full sequence of power-of-two geometric
> transfer matrices, pinned at endpoint `σ` and summed over `λ∈cshell`, is at most
> `2^(u+1)2^(θj+C log₂j)/A(j,σ)` for some `θ<θ_max` (first target `θ=1/6`).

The first proof step should derive a compressed recursion for the shell-summed propagated vector
and test whether λ-pairs or state bands close under one pair block. This attacks the norm-of-product
directly and preserves the exact formal interface already proved sufficient.
64. Preferred route: **propagated state (Route B)**. Start-state second moments are the fallback.
Do not lead with L2/Parseval, because positivity kills direct cancellation; do not attack the old
per-window frontier directly.
65. The old frontier should now be treated as legacy sufficient-condition and diagnostic
infrastructure. **PROVED (LEAN)** backward compatibility makes retaining it cost-free.
66. Updated EOC assessment: **LEVEL 3 conditional programme**—the analytic/combinatorial/final chain
and the weaker interface are formal, while the decisive arithmetic moment is open. Continue
cautiously and aggressively on the single propagated-state theorem; do not present the result as
an unconditional Collatz advance.

## Exact new dependency graph

```text
PowerOfTwoPinnedKernelPressureAt
  └─ summedPressure_of_pinnedKernel
       └─ PowerOfTwoSummedPressureAt (= SummedOddDarkPressure)
            └─ lowFreqDecay_of_summedPressure
                 └─ MultiWhite.lowFreqDecay_multi
                      └─ weightedFourier_of_explicitSummed
                           └─ exceptional_bound_of_summedPressure_and_scalar
                                └─ exceptional_bound_family_of_summedPressure

PowerOfTwoDangerousWindowSparsityAt
  └─ FrontierRegion.summedPressure_of_sparsityAt
       └─ summedPressure_of_dangerousWindowSparsity
            └─ the same new chain
```

No source theorem in the new core imports a dangerous-window hypothesis. The module import graph
still reaches legacy files through `MultiWhiteChain`, but the theorem dependency graph does not.
