# Independent EOC audit — 2026-09-17

Status vocabulary used throughout: **PROVED (LEAN)**, **PROVED (MATH)**, **EXTERNAL THEOREM**,
**COMPUTATIONAL**, **HEURISTIC**, **CONJECTURAL**, **REFUTED**, **OPEN**, and
**REQUIRES ADDITIONAL JUSTIFICATION**.

## Executive verdict

EOC currently contains a substantial and internally coherent formal conditional theorem, but not an
unconditional improvement for Collatz. The analytic, combinatorial, shell-counting, and final-counting chain is
**PROVED (LEAN)**, with only Lean's standard classical/quotient axioms. Its sole substantive unproved input in the
latest explicit family is arithmetic: a very strong uniform short-orbit pressure assertion called
`PowerOfTwoDangerousWindowSparsityAt`.

The latest multi-white contraction is valid. It removes the artificial `1/N₀` contraction loss, and the claimed
family and exponent are correctly formalized. The remaining frontier, however, is stronger than the downstream
argument intrinsically needs: it asks for every individual frequency, every disjoint window, and every start state,
although downstream ultimately needs only a frequency-summed endpoint pressure moment. This is the central finding
of this audit.

**Recommendation: Route B/E hybrid, beginning with Route B.** Formulate and prove the exact endpoint,
frequency-summed pressure interface described in §Candidate next theorems, then attack it by propagated-state or
multi-path averaging (Route E). Do not attack the present sup-norm frontier directly, and do not spend the next round
on overlapping white pairs or family-constant polishing.

## Repository

### 1–6. State, build, axioms, and uncommitted work

* Branch: `research-sparse-visits-2026-09-16`.
* HEAD: `14dea46ae5af816754cf3883475fa73dea598130` (`Isolate power-of-two digit sparsity frontier in Lean`).
* `lake build EOC`: **PROVED (LEAN)** successful, **8,813 jobs**, no errors. A fresh counted build emitted 648
  `warning:` lines. They are lint/style/deprecation/unused-variable warnings; no theorem failure occurred.
* Modified tracked files: `EOC.lean`, `docs/LITERATURE_CONTEXT.md`, `docs/RESEARCH_STATUS.md`.
* Untracked Lean modules:
  `BinomialTail`, `ConditionalChain`, `FinalChain`, `FrontierFamily`, `FrontierFamilyMulti`, `FrontierRegion`,
  `MultiWhiteChain`, `MultiWhiteContraction`, `ShapeRegion`, `ShellCounts`.
* Relevant latest scratch trees include `multiwhite_2026-09-17`, `frontier_family_2026-09-17`,
  `multipath_hfin_2026-09-17`, `erdos_eoc_bridge_2026-09-17`, `pressure_exact_2026-09-16`,
  `logwindows_2026-09-16`, `codimension_2026-09-16`, and `sparsevisits_2026-09-16`.
* Source search found no declaration of `axiom` or `opaque`, no proof hole `sorry` or `admit`, and no
  `native_decide` in the audited EOC chain. Occurrences returned by broad searches were explanatory comments.
* Fresh `#print axioms` checks for the headline theorem, both final-chain theorems, the multi-white contraction and
  class split, pressure wrapper, and ShapeTail returned exactly
  `[propext, Classical.choice, Quot.sound]`. Status: **PROVED (LEAN)** under standard Mathlib foundations.
* No commit, push, merge, rebase, or branch mutation was performed. The only files created by this audit are in this
  scratch directory (`AuditAxioms.lean`, `constants.py`, and this report).

### Actual dependency graph

The operative chain, reconstructed from theorem bodies rather than comments, is:

```text
ShapeCertificate -> ShapeUnconditional -> ShapeRegion.shapeTail_region

OddBlack + PressureBridge + DangerousWindows
  -> FrontierRegion.summedPressure_of_sparsityAt
  -> SummedOddDarkPressure(theta = 1/6)

ShapeTail + SummedOddDarkPressure
  -> MultiWhite.class_split / avg_prod_sq_le_multi
  -> MultiWhite.lowFreqDecay_multi
  -> MultiWhiteChain.lowFreqDecay_of_sparsityAt_multi
  -> WeightedFourier

ShellCounts + BinomialTail + FinalChain counting
  -> MultiWhiteChain.exceptional_bound_of_frontier_and_scalar_multi
  -> FrontierFamilyMulti.exceptional_bound_of_frontier_family
  -> FrontierFamilyMulti.exceptional_bound_family_exponent
```

`ArithmeticFrontier`/`FrontierRegion` do not prove the arithmetic assertion; they name it and prove its analytic
consequences. `TaoExternal.I0` and `lambdaStar` are definitions/results formalized from the probabilistic model, not
unproved Lean axioms in this chain.

## Current theorem

### 7–11. Exact statement, family, exponent, and assumptions

The exact headline is:

```lean
EOC.FrontierFamilyMulti.exceptional_bound_family_exponent
```

For every natural `m` with `1000 ≤ m`, assume that for all naturals `σ,t` satisfying

```text
b₀(Pm) ≤ σ + 4m,
σ ≤ b₀(Pm),
m ≤ t,
t ≤ b₀(Pm+m) − σ,
```

the proposition

```lean
PowerOfTwoDangerousWindowSparsityAt
  0 (P*m) σ t (σ+t) (Kwin m) (1/108) 2 2
```

holds. Then the number of odd `μ < 2^(b₀(Pm)+1)` whose accelerated orbit is `0`-confined for every length is at most

```text
(3/2) (2^(b₀(Pm)+1))^(H₂(1/α) − I₀/2,000,000).
```

Here `α = log₂ 3`, and Lean writes `H₂(1/α)` as
`Real.binEntropy alpha⁻¹ / Real.log 2`. Numerically, `I₀ = 0.07931861277…`, the entropy baseline is
`0.94995552719…`, and the proved conditional saving is `I₀/2,000,000 = 3.96593×10⁻⁸`.

The exact family is:

| quantity | exact Lean value | role |
|---|---:|---|
| `P` | `1,080,000` | `j₀ = Pm`; large enough for all scalar inequalities |
| `j₀` | `Pm` | prefix length |
| `L=N-j₀` | `m` | suffix length |
| `N` | `(P+1)m` | final depth |
| deficit cutoff `x*` | `4m` | declares good shell pairs |
| `Kwin` | `⌊7 log₂(Pm)⌋` | dangerous-window length |
| `N₀` | `1,079,998=P−2` | only the ShapeTail budget; no contraction denominator |
| `K_b` | `205,198m` | shape-good block threshold |
| `d` | `1/108` | dark/white angular threshold |
| `a,b` | `2,2` | logarithmic exceptional-window constants |
| `θ'` | `1/6+1/1000` | absorbed pressure exponent |
| `γ` | `1/60,000` | Fourier decay rate |
| `ε,κ` | `1,1` | good-pair Fourier and bad-mass constants |

Structurally necessary are: positive slack `θ'−θ`, positive suffix ratio `L/j₀`, a positive dark threshold `d`, a
ShapeTail budget, and enough `γj₀` to pay final shell counting. The literal integers `P`, `205198`, `7`, `4`, and the
round rational slack `1/1000` are proof conveniences/nonoptimal. `P` is chosen to make `γP=18` exactly and to clear
integer/divisibility inequalities. `d=1/108` is inherited from the clean comparison with Tao-black at `η=1/54` and
its three-balanced-digit description; it is not analytically optimal.

All non-arithmetic inputs of this particular family are discharged in Lean: ShapeTail, shell lower bounds, the
high-shell elimination by taking all shells as low, Haar/bad-pair counting, scalar binomial tail, and the numerical
family inequalities. Status: **PROVED (LEAN)**. The universally quantified frontier displayed above is **OPEN**.
Thus the conclusion is genuinely stronger than the entropy baseline, but only conditionally.

## White contraction

### 12–16. Old proof, new proof, density inequality, and exact gain

The old argument selected one white adjacent edge in a block `B`, obtained

```text
W ≤ 1 − 2(1−cos(πd))/|B|,
```

then used `|B|≤N₀` and `1−cos(πd)≥2d²`. Its exponential rate per credited block was
`8d²/N₀`. With `d=1/108`, `N₀=133`, this is `5.1569×10⁻⁶`.

The new argument is correct from first principles. `whiteSet` consists of eligible adjacent edges that are not dark,
split by the parity of their left endpoint. Same-parity edges cannot overlap. For either parity set `S`, triangle
inequality after partitioning the block into its disjoint pairs and unused points gives

```text
||Σ_{z∈B} e(φ_z)|| ≤ |B| − 2|S|(1−cos(πd)).
```

Taking `M=max(#white_even,#white_odd)` and dividing by nonzero `|B|` proves

```text
W ≤ 1 − 2(1−cos(πd)) M/|B|.
```

Normalization, disjointness, and the cosine factor are exact. The proof assumes only `d≥0`; positivity of the final
contraction follows from the already nonnegative normalized norm and the proved upper bound. Status:
**PROVED (LEAN)** (`norm_sum_le_pairs`, `wfac_le_parity`, `wfac_le_multi`).

White and dark eligible edges partition `Elig`. The block differs from eligible edges by at most one endpoint. Hence
`|B|≤2M+D+1`. If `D+2≤|B|`, at least one white edge exists, so `M≥1` and the spare `M+D−1` absorbs the `+1`; if not,
`|B|≤D+1≤2D`. Therefore, for `|B|≥2`, exactly

```text
|B| ≤ 3M + 2D.
```

Status: **PROVED (LEAN)** (`three_M_add_two_D_ge`). It yields

```text
exp(ln 2 · (1−3M/|B|)) ≤ 1+2D/|B|
```

with a separate harmless branch for `|B|<2`. The right side is precisely the normalized per-block factor in
`Σ_P 3^{N_odd}`: `(|B|+2D)/|B|`. The identities `block_sum_eq` and `class_moment_eq` prove that the factors multiply
and sum to the existing odd-dark pressure moment. No independent white-density hypothesis has been introduced.

Logical chain:

```text
current frontier -> summed dark pressure -> pressure/white exchange
                 -> many white pairs on pressure-light classes -> strong contraction.
```

Every arrow is **PROVED (LEAN)** except the first premise itself, which is **OPEN**.

At `d=1/108`, `c₀=1−cos(πd)=0.000423049918…` and the new rate is
`4c₀/3=0.000564066557…`, 109.38 times the old per-block rate. The exact family permits
`γ≤1.8158×10⁻⁵` and uses `1.6667×10⁻⁵`; the old cap was about `4.85×10⁻⁸`, a factor 374.4.
The extra factor beyond 109 comes from eliminating `N₀`, using the exact cosine, and reclaiming the old split between
Markov blocks and separately credited contraction blocks. The final exponent improves by 1000 because the usable
`γ` permits `P` to fall from `675,000,000` to `1,080,000` (factor 625), while the shell-counting proof improves its
required `γP` from 27 to 18 and the new rational family rounds the depth gain to `1/(2·10⁶)` rather than
`1/(2·10⁹)`.

Crediting overlapping white edges could at best double `M` relative to the larger parity class. A spectral/cluster
proof may recover part of that factor, but it cannot change the present bottleneck. Status: **OPEN**, worthwhile later
as cleanup, not as the next main direction.

## Bottleneck audit

### 17–21. Budgets and sensitivity

For the explicit family,

```text
K_b/j = 205198/1080000 = 0.1899981481…
θ' = 0.1676666667…
γ = 0.0000166667…
K_b/j − (θ'+γ) = 0.0223148148… .
```

Thus the reported `≈0.19`, `≈0.168`, and `≈0.022–0.023` are correct. The `0.19` originates in the ShapeTail budget
`K_b + 0.31j + σ/(N₀+2) ≤ j/2`. The last term is made tiny by the huge convenience choice `N₀=P−2`.
The `≈0.168` is not a raw observed pressure; it is the absorbed exponent `Λ/j=θ'+γ`, where `θ'` must exceed the
frontier-produced `θ=1/6`. Current ordering: (1) pressure/shape slack, (2) small `d`, (3) final condition `γP≥18`.

| Parameter/change | Effect on `γ` | Effect on final saving | Arithmetic cost | Analytic cost |
|---|---:|---:|---|---|
| Prove lower pressure rate `θ` | large; increases `K_b/j−θ'` linearly | large via smaller `P` | potentially large | modest once pressure supplied |
| Reduce dangerous fraction `φ` | `θ=.1+.3φ`; strong | strong | much harder sparse-hit theorem | none |
| Improve safe rate `.1` | linear improvement weighted by `1−φ` | useful | requires rigorous window bound | none |
| Improve universal `.4` ceiling | weighted only by `φ`; modest | modest | none if true | likely impossible in sup norm |
| Enlarge `d` | approximately quadratic initially | potentially 2–38× in table below | dark target gets larger | easy in contraction, hard in pressure |
| Improve ShapeTail rate `1/300` | little unless it binds `γ`; current family has ample shape-tail rate | small now | none | substantial certificate work |
| Count overlapping white pairs | at most ≈2× local | <2× likely | none | major spectral complexity |
| Improve final shell counting (`γP≥18`) | permits proportional decrease of `P` | proportional | none | combinatorial optimization |
| Optimize family constants | tens of percent, possibly a few-fold | same | none | tedious, low conceptual value |

For `φ=1/5,1/6,1/7,1/9,1/10`, the effective rates are respectively
`0.1600, 0.1500, 0.142857, 0.133333, 0.1300`. These improve analytic slack, but demanding fewer dangerous windows is
strictly stronger arithmetically. No current evidence justifies recommending it over weakening the norm.

## Pressure-rate audit

The theorem uses safe-window exponent `θ_d=1/10`, dangerous fraction `φ=2/9`, and the universal ceiling `2/5`:

```text
θ = θ_d + φ(2/5−θ_d) = 1/6.
```

The `2/5` comes from the row-sum bound `1+2q≤1.74≤2^(4/5)` over `j/2` blocks, hence `2/5` per original step.
It is close to the exact adversarial sup-norm ceiling and is approached by computed adversarial phases.

* **A:** `1/6` is not close to the observed endpoint pressure, but it is a natural consequence of the present binary
  sup-norm wrapper. It is not demonstrably optimal for the actual arithmetic path.
* **B:** the most realistic quantity to improve is not one of the three constants separately; it is the use of a
  supremum/binary split. Lowering `θ_d` rigorously or `φ` arithmetically is essentially the frontier again. Lowering
  `2/5` uniformly is **REFUTED** by adversarial phases.
* **C:** an average local rate would beat the convex combination if proved. This is **COMPUTATIONAL** with large slack,
  not yet a theorem.
* **D:** the ceiling is sharp for adversarial phases. The actual power-of-two orbit appears not to realize those
  phases often, but proving that is the arithmetic content, not an analytic free gain.
* **E:** separating window classes can lower an effective rate only if one proves different occupation weights. No
  such deterministic theorem is present; otherwise it is a restatement of the frontier.

Earlier `1/3` and `3/8` universal ceilings are **REFUTED** by exact/adversarial computations; `2/5` is essentially
sharp in the universal norm. Restricting to ShapeTail-good states does not rigorously lower it: ShapeTail constrains
block cardinality/classes, while the ceiling's bad phase and start state remain available. A restricted ceiling below
`2/5` is therefore **OPEN**, and the naive implication from ShapeTail is **REFUTED**.

The sampled worst safe-window rate `≈0.09124` supports thresholds `.095` or `.092` only
**COMPUTATIONALLY**. The Haar theorem bounds the measure of dangerous environments; it does not certify the fixed
power-of-two orbit. Lowering `.10` without new arithmetic is **REQUIRES ADDITIONAL JUSTIFICATION**.

## Larger `d`

Holding the current shape/pressure slack fixed and solving the multi-white rate inequality gives the following
optimistic analytic caps. `P_min` uses only the current counting requirement `γP≥18`; it does not certify the enlarged
dark-pressure frontier.

| `d` | `c₀=1−cos πd` | potential `γ_max` | optimistic `P_min` | expected saving `I₀·0.54/P_min` | arithmetic assessment |
|---:|---:|---:|---:|---:|---|
| `1/108` | .00042305 | 1.816e-5 | 991k | 4.32e-8 | current, proved conditional family |
| `1/72` | .00095178 | 4.081e-5 | 441k | 9.71e-8 | larger interval; awkward denominator |
| `1/54` | .00169184 | 7.244e-5 | 248k | 1.72e-7 | about twice dark density |
| `1/36` | .00380530 | 1.623e-4 | 111k | 3.86e-7 | clean `1/(4·3²)` cylinder scale |
| `1/27` | .00676164 | 2.867e-4 | 62.8k | 6.82e-7 | larger finite interval union |
| `1/18` | .01519225 | 6.341e-4 | 28.4k | 1.51e-6 | clean `1/(2·3²)`, but much harder pressure |

The repository's exact `j=400` scan reports global pressure below `.17` through `d=1/6` and above it by `d=1/4`.
That is **COMPUTATIONAL**, not a window theorem. Every rational `d` still has a finite residue-interval description;
denominators `2·3^k` or `4·3^k` give especially simple leading balanced-digit conditions. Thus `d>1/108` does not
destroy finite describability, but it enlarges the target and can qualitatively harden sparse visits. `d=1/36` is the
best later tradeoff to test. It is not the first theorem to formalize because the current frontier is already open.

## Frontier audit

### 22. Exact proposition

For fixed `U,j,σ,t,Us,K,d,a,b`, `PowerOfTwoDangerousWindowSparsityAt` says:

* for every frequency shell `u≤Us`;
* for every individual `λ∈cshell(σ+1,t,u)`;
* there exists a set `bad` of window indices with
  `#bad ≤ (2/9) floor((j/2)/K) + (a log₂j+b)/K`;
* for every disjoint window `i<floor((j/2)/K)` outside `bad`;
* for every start state `y∈{0,…,σ}`;
* the length-`K` geometric odd-dark transfer mass from `y` is at most `2^(2K/10)`.

For the explicit family this is required for asymptotically `O(m²)` good integer pairs `(σ,t)` in a strip of
deficit `≤4m` and suffix length range `m≤t≤B−σ`; for each pair it covers `σ+t+1=Θ(Pm)` frequency shells. Shell `u`
contains up to `2^(u+1)` frequencies, there are `Θ(j/log j)` disjoint windows, and `σ+1=Θ(j)` start states. These are
quantifiers, not a feasible enumeration.

### 23–27. Minimum statement and necessity audit

The minimum non-tautological arithmetic object already visible in the proof is
`AverageOddDark.SummedOddDarkPressure`, or equivalently a frequency-summed endpoint-kernel bound before the
`PressureBridge` polynomial loss. This is strictly weaker than the named frontier:

* per-`λ` control is **not necessary**; `MultiWhite.lowFreqDecay_multi` accepts a sum over `λ` in each shell;
* per-window binary control is **not necessary**; only the product/endpoint kernel or total log pressure matters;
* a supremum over all start states is **not necessary**; it enters only when `val_le_prod_windows_rem` propagates a
  worst-case norm between windows;
* every shell individually is required by the current `LowFreqDecay` interface, but a single correctly weighted sum
  over shells would also suffice at the `WeightedFourier` level. That weakening is not packaged in the final family;
* every good `(σ,t)` pair is required by the present pointwise good-pair branch. A Haar-weighted average over pairs
  could suffice if integrated with `hweight`, but no such theorem is currently proved.

Thus the earlier conclusion that exponential moments force per-`λ` control is **REFUTED as a logical claim**. They
force control of the frequency-summed moment, which may still be difficult, but do not force a supremum. The new
multi-white engine does not by itself create this fact; `SummedOddDarkPressure` and the summed low-frequency route
already expose it.

## Alternative formulations

### 28. Weighted/continuous pressure

Define an endpoint pressure assertion (schematically):

```lean
PowerOfTwoEndpointPressureAt U j σ t Us d θ C :=
  ∀ u ≤ Us,
    ∑ λ ∈ cshell (σ+1) t u,
      ker (geoW p q (oddW (collatzBarrier U) (σ+1+t) d 3 λ) σ)
          0 (j/2) 0 σ
      ≤ 2^(u+1 + θ*j + C*log₂ j)
```

with the exact polynomial normalization chosen to feed `PressureBridge.sum_pow_nodd_le_geo`.
This assertion is **strictly weaker** than `PowerOfTwoDangerousWindowSparsityAt` and is sufficient for the downstream
chain after adjusting `C`. It removes `2/9`, `.10`, the binary safe/danger split, per-window worst cases, and per-`λ`
control. This is a genuine weakening, not merely new notation.

A sum of local sup rates `Σ_i log₂ ||T_i||∞` is weaker than binary danger but still retains the main start-state
artifact. It is useful as an intermediate theorem, not the final target.

### 29. Average start states

If `v_i` is the actual nonnegative propagated row vector before window `i`, the exact replacement for the max is

```text
||v_i T_i||₁ / ||v_i||₁,
```

not `sup_y val_i(y)`. Products telescope to the endpoint mass. This makes start-state averaging natural and creates
changing relative offsets among paths. The repository's multi-path data show that constant offsets add little rank,
whereas changing offsets add fresh ternary constraints. That is a plausible bridge, but presently
**HEURISTIC/COMPUTATIONAL**.

### 30. Operator norms

* `L∞→L∞`: current wrapper; robust, loses propagated distribution, supports the sharp `2/5` adversary.
* `L1→L1`: controls column sums, not naturally matched to the pinned start/end kernel without weights.
* `L2→L2`: could exploit average cancellation/correlation, but entries are nonnegative pressure weights, so the gain
  is concentration/geometry rather than sign cancellation.
* weighted stationary/projective norm: best aligned with the geometric bridge; a positive left/right weight can
  follow the actual state profile and telescope.

A hybrid using sup norm only at the first/last `O(log j)` boundary layers and a weighted `L2` or projective norm in
the interior is mathematically plausible. No rigorous exponent below `1/6` has yet been derived. Status: **OPEN**.

### 31. Larger `d`

Analytically attractive, as quantified above, but it strengthens the arithmetic pressure observable. Test `1/36`
after the endpoint-pressure interface exists; do not rebuild the full Lean family first.

### 32. Restricted `2/5`

No rigorous restricted improvement was found. Actual endpoint rates are much lower, but the restricted sup ceiling
is not the right abstraction. Status: **OPEN**; not recommended as the primary route.

### Computational pressure evidence

For `λ=1`, exact disjoint-window computations give mean sup-window rates (already a pessimistic average of maxima):

| `(j,K)` | mean rate | max rate | dangerous fraction at `.10` |
|---|---:|---:|---:|
| `(1600,12)` | .0515–.0531 | .0963 | 0 |
| `(3200,12)` | .0625–.0637 | .1149–.1376 | .023–.030 |
| `(1600,8)` | .0713–.0727 | .1306–.1445 | .13–.16 |

The exact full endpoint moments in the broader corpus peak near `.0119` at `j=1600,d=1/108`; all 6,720 tested
instances were below `1/6`. These are **COMPUTATIONAL**. They strongly motivate endpoint pressure but prove nothing
for the asymptotic fixed power-of-two orbit.

## Arithmetic difficulty

### 33–36. Powers of two, Erdős/Lagarias, exponential sums, accessibility

The frontier concerns short ranges of the orbit of powers of two in 3-adic digit space, at digit depth comparable to
the orbit length, with moving finite-digit targets and many path/start-state offsets. Lagarias's fixed-`λ` theorem
`#{n≤X: λ2^n omits ternary digit 2} ≤ 2X^{log₃2}` is an **EXTERNAL THEOREM**, but it obtains only `O(log X)` digits
from a full residue period. Abram–Lagarias path-set dimensions concern whole-expansion Cantor restrictions for fixed
multipliers. Neither supplies the required short-range pressure.

Known Korobov/Bourgain-type exponential-sum regimes cited in the repository require ranges much longer than
`N≈depth`; they do not reach this frontier. A theorem giving uniform weighted equidistribution of
`{λ2^n mod 3^B: n in an interval of length cB}` against the EOC moving cylinder observables, with exponential moment
rate `<1/6`, would imply the endpoint frontier. This is the weakest honest external theorem presently identifiable;
it is itself a major new short-orbit digit-distribution theorem.

The current frontier does not visibly imply Erdős's conjecture that powers of two eventually contain ternary digit
2: it permits a positive fraction of bad windows and concerns local moving dark patterns, not global omission of a
digit. Conversely, even a strong fixed-multiplier Cantor-dimension result does not directly imply the needed uniform
short-window moment. A sufficiently strong short-orbit normality/equidistribution theorem would imply it.

Classification: **Type III — comparable to major open digit-distribution problems**, not Type IV on current evidence.
It appears substantially weaker than Collatz itself because it is a finite-scale statistical assertion about a
specific power orbit and would yield only an exceptional-set improvement, not extinction of every exceptional
orbit. But existing tools do not access its `length≈depth` uniform regime. Failed experiments alone are not the
reason for this rating; the obstruction is the quantitative range of known exponential-sum/digit theorems.

Literature comparison:

* Terras/Everett density/stopping-time results supply the classical entropy/counting baseline; EOC's formal shell and
  confined-word bookkeeping refines this architecture.
* Tao's almost-bounded theorem uses logarithmic density, entropy decrement, and 3-adic mixing inputs to show almost
  all orbits attain almost bounded values. EOC instead seeks a power-saving count for forever-confined exceptional
  seeds through Fourier pressure. The goals and measures are different.
* Lagarias and Abram–Lagarias calibrate the ternary-power digit barrier but do not prove the EOC frontier.
* If the endpoint frontier were proved, the new mathematical content would be a quantitative short-orbit 3-adic
  pressure theorem plus the resulting conditional-to-unconditional exceptional exponent. Novelty beyond the local
  repository was not established by a comprehensive publication search, so any novelty claim remains
  **REQUIRES ADDITIONAL JUSTIFICATION**.

## Candidate next theorems

### Candidate A — restricted ceiling

**Exact target:** prove `val(T_window,y)≤2^(2K θ_bad)` with `θ_bad<2/5` for all states actually reached with positive
weight by the pinned endpoint kernel on ShapeTail-good classes.

* Payoff: replaces `.4` in the convex combination.
* Obstacle: reachability can include adversarial phases; ShapeTail alone does not restrict them.
* Route: characterize reachable weighted support, not merely class geometry.
* Assessment: low/medium provability, modest impact, high arithmetic dependence, awkward Lean formalization.

### Candidate B — endpoint frequency-summed pressure (**primary**)

**Exact target:** formalize `PowerOfTwoEndpointPressureAt` above and prove that rate `θ<θ'` plus polynomial loss
implies `LowFreqDecay` and the final family theorem; first aim for `θ=1/6`.

* Payoff: strictly weakens the only open hypothesis and deletes per-`λ`, danger-count, threshold, window-max, and
  start-state-sup requirements.
* Obstacle: proving the endpoint estimate for the actual power orbit remains hard.
* Route: use `PressureBridge.sum_pow_nodd_le_geo` directly, telescope propagated vectors, sum over `λ` before applying
  Hölder/second moments, and retain the current multi-white class split.
* Assessment: high formal provability of the reduction, highest conceptual impact, best reuse of machinery.

### Candidate C — average-start window theorem

**Exact target:** for each window and incoming probability vector `μ`, bound the weighted amplification
`||μT_i||₁/||μ||₁`, with the product averaged over frequencies, rather than `sup_y val_i(y)`.

* Payoff: attacks the observed main artifact directly.
* Obstacle: incoming `μ` depends on all preceding windows and on `λ`.
* Route: positive-operator/projective contraction or a two-replica second moment.
* Assessment: medium provability, high impact, moderate Lean difficulty after mathematics is settled.

### Candidate D — weighted `L²` operator contraction

**Exact target:** construct positive weights `h_i` and prove a shell-summed bound for
`Σ_λ ||h_i^{-1/2}T_{i,λ}h_{i+1}^{1/2}||_{2→2}²` whose cumulative exponent is `<1/6`.

* Payoff: could exploit changing-offset rank and eliminate worst states.
* Obstacle: nonnegative kernels offer no elementary cancellation; replica state grows with offset.
* Route: prove a locality/cluster lemma for joint dark cells before building a finite operator.
* Assessment: medium/low near-term provability, very high upside, significant new theory.

### Candidate E — larger-`d` family

**Exact target:** rebuild `pairData_fam` at `d=1/36` under an endpoint pressure assumption at that `d`, with an
explicit `P≈1.2×10⁵` and saving around `4×10⁻⁷`.

* Payoff: about 9× current exponent saving if arithmetic pressure survives.
* Obstacle: larger dark target may sharply raise pressure and arithmetic difficulty.
* Route: exact computations first; only then formalize constants.
* Assessment: easy analytic/Lean work, uncertain arithmetic premise, secondary priority.

## Independent assessment

### 42–50. What EOC is and is not

* Strongest aspect: a long, explicit, axiom-audited Lean chain converts one named arithmetic pressure input into a
  genuine power saving, including shell counts and all final scalar bookkeeping.
* Weakest aspect: the named frontier is a uniform short-orbit digit-distribution assertion far beyond current proved
  methods, and its sup-norm formulation contains avoidable strength.
* Strongest proved theorem: conditionally, `exceptional_bound_family_exponent`; unconditionally, the multi-white
  pressure-to-decay machinery and explicit ShapeTail/shell-counting theorems.
* Most important unproved claim: any asymptotic arithmetic pressure theorem for the actual powers-of-two phases;
  specifically the current `PowerOfTwoDangerousWindowSparsityAt` family.
* Biggest conceptual risk: the actual fixed 3-adic orbit may have rare structured resonances invisible to Haar and
  finite sampling, so averaged numerical slack may not yield a uniform asymptotic theorem.
* Biggest opportunity: sum frequencies and propagate start-state weights inside the operator before taking norms.
* How much is rigorous? Nearly all implications after an appropriate pressure hypothesis are **PROVED (LEAN)**.
  None of the decisive fixed-orbit arithmetic input is proved.
* Is the current exceptional-set theorem nontrivial? Yes as a conditional theorem: it gives an explicit strict
  exponent improvement and eliminates numerous formerly abstract analytic/counting inputs. It is not unconditional
  progress on Collatz.
* Is the programme credible? **Cautiously yes** as a rigorous research programme for exceptional-set bounds. It is
  not currently close to a Collatz proof.
* Maturity: mature conditional analytic/combinatorial framework; early-stage arithmetic core.
* Frontier difficulty: **Type III**.

What would seriously weaken or falsify the programme: an explicit sequence of family parameters/frequencies whose
endpoint pressure has limsup `≥K_b/j` or at least cannot be kept below the ShapeTail budget; a proof that the endpoint
frontier implies a recognized open digit theorem of equal or greater difficulty with no exploitable averaging; or a
failure of the claimed bridge under independent exact reproduction. No such flaw was found in the Lean chain.

## Recommendation

### 51–56. Decisive next move

Pursue **Candidate B: the endpoint frequency-summed pressure theorem**.

The first concrete step is to add a scratch-only mathematical prototype—not a production Lean module—that computes,
for the existing exact environments, all three quantities side by side:

```text
product of per-window L∞ norms,
actual pinned endpoint kernel,
frequency-summed pinned endpoint kernel by shell.
```

Then prove on paper the exact reduction
`PowerOfTwoEndpointPressureAt -> SummedOddDarkPressure -> LowFreqDecay`, including constants. The reduction should be
straightforward from `PressureBridge.sum_pow_nodd_le_geo` and will satisfy the positive stop condition of a strictly
weaker sufficient frontier. Only after this reduction is fixed should multi-path/second-moment machinery be aimed at
the arithmetic estimate.

Do **not** work next on overlapping white pairs, a universal `2/5` improvement, small family optimizations, or direct
formalization at larger `d`; each either offers under 2× payoff or preserves the main sup-norm barrier. Do not relabel
the same per-window supremum as “weighted pressure.”

Keep the Erdős side thread active at low intensity for calibration and reusable automata/short-orbit results, but do
not make it the main line. Existing Cantor-dimension theorems do not bridge the required short-range regime.

Overall posture: **continue EOC cautiously**, with an explicit checkpoint. If endpoint/frequency averaging cannot
produce a theorem materially weaker than the present frontier after a focused round, freeze aggressive Lean
expansion and treat the remaining problem as a Type III arithmetic programme rather than as near-term Collatz work.

