# Research status

This file records the current state of the analytic program in this repository: what is proved in Lean, what is
proved on paper, what rests on an external theorem, what is only computational, and what is open.  It complements
[`RESEARCH_CHECKPOINT_2026-09.md`](RESEARCH_CHECKPOINT_2026-09.md) (the earlier, pointwise-oriented audit) and the
[README](../README.md).  Literature used here is documented, with its limits, in
[`LITERATURE_SUBSPACE_TRIANGLES.md`](LITERATURE_SUBSPACE_TRIANGLES.md).  Reproduction instructions for all computations
are in [`../scratch/README.md`](../scratch/README.md).

**Labels.**

| Label | Meaning |
|---|---|
| PROVED (LEAN) | Compiles in this repository (`lake build`), no `sorry`, standard axioms only. Hypotheses, if any, are explicit Lean `Prop`s and are named below. |
| PROVED (MATH) | Derived by hand and audited; not (fully) packaged as a Lean theorem. |
| EXTERNAL THEOREM | A published theorem used as input, entering Lean (if at all) only as an explicit hypothesis. |
| COMPUTATIONAL | Exact or numerical experiment. Evidence, not proof. |
| HEURISTIC | Supported by a random model or informal argument only. |
| CONJECTURAL | Stated as a conjecture; no proof. |
| REFUTED | A proposed route or claim shown false or unworkable (by proof, exact identity, or decisive computation, as stated). |
| OPEN | No proof known in this project. |

The README's older labels map as follows: FORMALLY VERIFIED = PROVED (LEAN) without hypotheses; CONDITIONAL FORMAL
RESULT = PROVED (LEAN) with an explicit external hypothesis; PROVED MATHEMATICALLY = PROVED (MATH); COMPUTATION =
COMPUTATIONAL.

---

# Milestone — 2026-09-16: Unconditional ShapeTail closed

**Headline.** **ShapeTail is now unconditional in Lean for every even j ≥ 300.** The pressure side remains open; this
is not a proof of Collatz.

* **PROVED (LEAN)** — `EOC.ShapeUnconditional.shapeTail_allEven`: for every even j ≥ 300,
  `ShapeTail (collatzBarrier 0) j (collatzBarrier 0 j) 10 (j / 25) (2 ^ (j / 300))⁻¹`.
* **PROVED (LEAN)** — `EOC.ShapeUnconditional.shapeTail_allEven_rate`: the same with some ρ₁ ≤ 2·2^{−j/300}. The
  exponential rate is 1/300 bits per unit of word length; the factor 2 comes from the floor ⌊j/300⌋.
* **PROVED (LEAN)** — `EOC.ShapeUnconditional.shapeTail_cofinal`: j = 300(q+1), K = 12(q+1), ρ₁ = 2^{−(q+1)} exactly.
* Axioms: `propext`, `Classical.choice`, `Quot.sound` (`#print axioms`); no `sorry`, no `native_decide`. The 150
  base certificates j = 300, …, 598 are one `decide +kernel` statement (`bases_ok`).
* Full account: [`SHAPETAIL_UNCONDITIONAL.md`](SHAPETAIL_UNCONDITIONAL.md). Literature context:
  [`LITERATURE_CONTEXT.md`](LITERATURE_CONTEXT.md).

Lean state: 94 modules imported by `EOC.lean`; `lake build EOC` completes with 8802 jobs.

**Pressure-only wrapper — PROVED (LEAN), `EOC/AverageOddDark.lean`.**

* `shapeTail_allEven_budget`: the same unconditional ShapeTail holds for any N₀ and K with
  K + ⌊31j/100⌋ + ⌊σ/(N₀+2)⌋ ≤ j/2. The certificate does not involve N₀ or K.
* `AverageOddDarkPressure b j σ t U d s θ C` is `OddDarkPressure` with M = 2^{θj + C log₂ j}.
* `criticalWhiteCount_of_averagePressure` / `criticalWhiteCount_rate` (concrete schedules
  `criticalWhiteCount_N30`, `_N100`): for even j ≥ max(300, (3C/(θ'−θ))²), averaged pressure alone gives
  `CriticalWhiteCount` with ρ ≤ 2·2^{−j/300} + 2^{−γj}, whenever θ' + γ ≤ ν log₂((1+s)/2) and ν j ≤ n, k + n ≤ K.
* `lowFreqDecay_of_averagePressure`: the same hypothesis gives `LowFreqDecay` with constant 4. Its side conditions
  (nonempty shell, κ(d,N₀)^{2k} ≤ exp(−8kd²/N₀)) are proved.
* Sufficient threshold (PROVED (MATH) from these hypotheses): θ(s) < (K_max(N₀) − k/j)·log₂((1+s)/2), with
  K_max = 0.19 − 317/(200(N₀+2)); at s = 3 this is 0.1405 (N₀ = 30) and 0.1745 (N₀ = 100). With K = ⌊j/25⌋ it would
  be 0.04, below the measured true pressure 0.048 (COMPUTATIONAL). Details:
  `scratch/avgpressure_2026-09-16/REPORT.md`.

**Pressure interface and bridge (PROVED (LEAN), later on 2026-09-16).**

* `AverageOddDark.lowFreqDecay_of_summedPressure`: the pressure hypothesis need not be uniform in λ.
  `LowFreqDecay` sums over each frequency shell, so `SummedOddDarkPressure` (the moment summed over
  λ ∈ cshell u, bounded by 2^{u+1}·2^{θj + C log₂ j}·|P_σ|) suffices.
* `PressureBridge.sum_pow_nodd_le_geo`: ∑_P s^{N_odd} ≤ (σj/p)·ker(geometric kernel)(0 → σ)·|P_σ| with
  p = (j−1)/(σ−1), a polynomial loss. `sum_pow_nodd_le_windows` turns K-block window mass bounds into moment bounds.
* COMPUTATIONAL (`scratch/pressure_exact_2026-09-16/REPORT.md`, exact integer DP of the Lean observable):
  6720 true low-frequency environments (J ≤ 1600) are all certified below θ = 1/6. The worst global rate
  is 0.034 and the median about 0.009.
* REFUTED: environment-universal certificates. A 3-adic unit ξ ≡ 2^m realises 0.32–0.35, and the
  state-only super-eigenvector gives 0.19–0.29. Fixed-K dangerous-window fractions grow linearly in j.
* OPEN: `SummedOddDarkPressure` for λ·2^{−m} (λ = 1 at every shift is unavoidable, since cshell(0) = {1, 2^m − 1}).

**Dangerous windows (PROVED (LEAN), `EOC/DangerousWindows.lean`).**

* `summedPressure_of_tenth_twoNinths`: split the pair blocks into windows of K ≤ k₁ log₂ j + k₀ blocks. Suppose, for
  every low frequency, all but (2/9)·W + (a log₂ j + b)/K windows have geometric mass ≤ 2^{K/5} from every state.
  Then `SummedOddDarkPressure` holds with θ = 1/6 and an explicit C. Dangerous windows are paid for by the proved
  universal ceiling 2^{(4/5)K} (`val_le_ceiling`; 2/5 bits per step for j ≥ 300).
* `nodd_companion`: λ and 2^m − λ have identical odd-dark counts, so the u = 0 shell reduces to λ = 1.
* COMPUTATIONAL (`scratch/logwindows_2026-09-16/REPORT.md`): with K = ⌈2 log₂ j⌉ every window is safe in all 36
  environments scanned (j ≤ 6400). 1602 windows in 30 distinct environments (λ = 1 at five shifts and λ = 17, per j)
  are certified by exact integer arithmetic; the worst exact rate is 0.0908 < 1/10. The per-state danger density
  decays like ≈ 3^{−(2.2 + 0.5K)} (HEURISTIC fit), which explains why K ≍ log j is the right scale.
* OPEN: the arithmetic local-window statement for λ·2^{−m} at every shift and every j.
* PROVED (MATH), `scratch/codimension_2026-09-16/REPORT.md`: dark (d = 1/108) implies Tao-black at η = 1/54, i.e. three
  leading balanced-ternary digits of the phase vanish; each block adds two fresh digits and consecutive rows share one.
  A 2-state digit operator then gives, for a Haar-random 3-adic environment and any start state,
  P(K-window mass > 2^{K/5}) ≤ 1.055·3^{−0.100K} (exponent 0.136 with the second moment).  This covers
  K ≳ 4.6–6.3·log₂ j after a union over start states, not yet K = 2 log₂ j, and it is a Haar statement, not a
  statement about the orbit λ·2^{−m}.

## Arithmetic frontier — power-of-two digit sparsity (2026-09-16)

Full account: [`ARITHMETIC_FRONTIER.md`](ARITHMETIC_FRONTIER.md). Lean: `EOC/ArithmeticFrontier.lean`.

### PROVED (LEAN)

* `ArithmeticFrontier.summedPressure_of_powerOfTwoSparsity`: `PowerOfTwoDangerousWindowSparsity ⇒
  SummedOddDarkPressure` (θ = 1/6, C = 2 + (3/5)a + (4/5)A + (2 + (3/5)b + 4/5)/8, any window size K ≤ A log₂ j + 1).
* `ArithmeticFrontier.lowFreqDecay_of_powerOfTwoSparsity`: `PowerOfTwoDangerousWindowSparsity ⇒ LowFreqDecay`. The
  route goes through summed pressure, the proved `ShapeTail`, and the frequency-summed white-count split
  `AverageOddDark.lowFreqDecay_of_shape_and_summedPressure` (the summed form of the `CriticalWhiteCount` argument).
* Helpers: `dark_iff_distZ`, `uInv_modEq_shift`, `dark_shift` (shift translation: only a = m − z matters), and
  `black_fiftyfourth_iff` (black at η = 1/54 iff the three leading balanced-ternary digits vanish).
* Axioms of all of these: `propext`, `Classical.choice`, `Quot.sound`.

### OPEN

`PowerOfTwoDangerousWindowSparsity` itself is unproved. It asserts that, for the true low-frequency arithmetic
environments, logarithmic windows whose geometric odd-dark pressure exceeds the dangerous threshold (rate 1/10 per
step) cannot occupy more than the allowed 2/9 fraction plus the explicit logarithmic allowance (a log₂ j + b)/K. The
u = 0 shell {1, 2^m − 1} is present at every shift and reduces to λ = 1 (`DangerousWindows.nodd_companion`). There the
hypothesis is a restriction on leading ternary digit patterns of 2^{−a} mod 3^b along the EOC diagonal. This lies in
the same general family as classical unresolved digit-distribution questions for powers of 2. No equivalence with any
named conjecture is claimed.

### PROVED (MATH) — negative audit of the current architecture

* Pointwise control in the shift t is essentially required by `weighted_phi_decay_implies_exceptional_bound`. A bad
  shift costs ≳ 2^{t/2} (trivial branch, or ε from the collision bound) against a Haar share of ≈ N^{−1/2}.
* Averaging over t does not remove the arithmetic blocker. Full-period averages need ≈ 3^{4K} = j^{O(1)} shifts, and
  bad shifts cannot be paid for.
* Averaging over u, λ or j does not substantially weaken the needed input. Uniformity in u is only an API convenience;
  the exponential moments tolerate only exponentially rare bad λ; one j₀ per K gives no new environments.
* u = 0 reduces to the λ = 1 dark environment by the proved companion symmetry.
* The exponent lift 2^{Q_D} ≡ 1 + c·3^D (mod 3^{D+1}) is triangular, but the digit tests admit no finite transducer
  (`scratch/sparsevisits_2026-09-16/REPORT.md`).

These are results about the **current proof architecture**, not impossibility theorems for every conceivable future
EOC approach.

### COMPUTATIONAL

`scratch/shiftaudit_2026-09-16/REPORT.md`: 1230 environments (j = 400, 800, 1600; K = ⌈2 log₂ j⌉; consecutive and
scattered shifts up to t = 77702; Haar controls; 40 shifts at K = ⌈5 log₂ j⌉).
* No window has rate above the formal threshold 1/10, so there are zero dangerous windows.
* The nine worst λ = 1 shifts (201 windows) were certified by exact integer arithmetic. Worst exact rate **0.09124**,
  about 9% below 1/10.
* Worst Haar-control rates are 0.0874 / 0.0779 / 0.0776.

These finite computations support the hypothesis but do not prove it.

## Chain after this milestone

    PowerOfTwoDangerousWindowSparsity (OPEN)  ⇒  SummedOddDarkPressure   ArithmeticFrontier.summedPressure_of_powerOfTwoSparsity (PROVED (LEAN))
    SummedOddDarkPressure + ShapeTail  ⇒  LowFreqDecay   AverageOddDark.lowFreqDecay_of_summedPressure (PROVED (LEAN))
    ShapeTail (PROVED, LEAN)  +  OddDarkPressure (OPEN)
        ⇒ CriticalWhiteCount        OddBlack.criticalWhiteCount_of_shape_and_oddPressure   (implication PROVED (LEAN))
        ⇒ LowFreqDecay              WhiteContraction.lowFreqDecay_of_criticalWhiteCount     (implication PROVED (LEAN))
        ⇒ WeightedFourier           WhiteContraction.weightedFourier_of_criticalWhiteCount  (implication PROVED (LEAN))
        ⇒ exceptional-set bound     WeightedChain.weighted_phi_decay_implies_exceptional_bound

* `criticalWhiteCount_of_shape_and_oddPressure` takes `ShapeTail` at K = k + n, together with `OddDarkPressure` and
  the numerical condition M ≤ ρ₂((1+s)/2)ⁿ. The parameter compatibility of these with the proved K = ⌊j/25⌋, N₀ = 10
  has not been checked (OPEN).
* **White-point contraction**, listed as OPEN in Lean in §10 of the 2026-09-15 checkpoint below, is now PROVED (LEAN)
  in `WhiteContraction` (`pair_factor_le_of_good`, `goodPair_of_white_step`).

## Current status of the main statements

| statement | status |
|---|---|
| `ShapeTail` (Collatz barrier, every even j ≥ 300, rate 2·2^{−j/300}) | PROVED (LEAN) |
| `PowerOfTwoDangerousWindowSparsity` (named arithmetic input, `ArithmeticFrontier`) | OPEN — **the current blocker** |
| `SummedOddDarkPressure` / `OddDarkPressure` for the true environment | OPEN (follows from `PowerOfTwoDangerousWindowSparsity` by a PROVED (LEAN) implication) |
| `CriticalWhiteCount`, `LowFreqDecay` | OPEN (`LowFreqDecay` follows by a PROVED (LEAN) implication from the OPEN `PowerOfTwoDangerousWindowSparsity`; both follow from `AverageOddDarkPressure`) |
| lower shells σ < ⌊jα⌋ and barrier offsets U > 0 for ShapeTail (needed by the exceptional-set chain) | OPEN (the certificate holds exactly for σ ≥ ~1.40j at j = 300…2400, COMPUTATIONAL) |
| `WeightedFourier` beyond the fresh-bit boundary (A > 1/α) | OPEN |
| exceptional-set exponent below H₂(1/α) ≈ 0.949956 | OPEN (baseline H₂(1/α) is PROVED (LEAN)) |
| EOC; the Collatz conjecture | OPEN |

## Modules added 2026-09-16

All compile, contain no `sorry`, and are imported by `EOC.lean`.

* ShapeTail chain: `ShapeTail`, `ShapeBridge`, `ShapeCertificate`, `ShapeUnconditional`, `LocalWindow` (layered
  kernels and super-eigenvector bounds).
* White-count interface: `WhiteContraction`, `OddBlack` (the `OddDarkPressure` hypothesis is an explicit `Prop`).
* Pressure-only wrapper: `AverageOddDark`.
* Auxiliary: `BinomialEntropy` (C(n,k) ≥ 2^{nH(k/n)}/(n+1)), `LogAbsorb` (absorbing an O(log n) surplus into the rate).
* Pointwise-descent side results: `DirectDescent` (its descent theorems assume the OPEN `LinearRealizerFloor`),
  `HarmonicFloor` (a logarithmic drift ceiling along a non-descending orbit), `LiftGap` (least-realizer
  stabilization). None of them is a pointwise Collatz result.

Round reports: `scratch/shapetail_2026-09-16/` (bridge and certificate), `scratch/pressure_2026-09-16/` (shape-only
large deviations, PROVED (MATH)), `scratch/shapetail_allEven_2026-09-16/` (residue audit, COMPUTATIONAL guidance
only). Other 2026-09-16 exploratory rounds are not part of this milestone and are not in git.

---

# Research checkpoint — 2026-09-15

**Headline.**

* **R_max(L) = o(L)** for Tao-black triangles along the critical corridor, for every fixed threshold η. This is a
  mathematical consequence of the p-adic Subspace Theorem (EXTERNAL THEOREM, Schlickewei) together with this
  repository's reduction. The reduction is PROVED (LEAN), with the Subspace Theorem entering as the explicit hypothesis
  `SubspaceInstance`. The result is **ineffective**.
* R_max(L) = o(L) does **not** imply positive-density good angles, and nothing here proves **A > 1/α**.
* The current analytic bottleneck is **exponentially concentrated control of Tao-black triangle occupation under the
  critical confined law** (§10). It is OPEN.

Lean state at this checkpoint: 79 modules imported by `EOC.lean`, `lake build` completes with **8787 jobs** (clean
rebuild of the project outputs). A metaprogram over all 1529 declarations of the 79 `EOC.*` modules found no
axiom other than `propext`, `Classical.choice` and `Quot.sound` (in particular no `sorryAx`). Textual occurrences of
`sorry`/`admit` in the sources are all inside comments or docstrings ("No `sorry`, …").

## 1. Current objective

The Lean chain in `WeightedChain.lean` ends in
`weighted_phi_decay_implies_exceptional_bound`: under the analytic hypothesis `WeightedFourier` on the relevant shells
(plus a finite Haar-weight condition), the exceptional confined seeds satisfy

    #(E_U ∩ [0, 2^K)) ≤ (C e^{λ* U} / 2) · (2^K)^{1 − I₀ A}      (N ≥ A K),

with I₀ = α(1 − H₂(1/α)) ≈ 0.0793186 and α = log₂3 ≈ 1.5849625. The unconditional baseline is the fresh-bit boundary
**A = 1/α**, giving the exponent

    1 − I₀/α = H₂(1/α) ≈ 0.949956      (ExceptionalPowerBound.lean; PROVED (LEAN)).

The objective of the recent rounds was to prove `WeightedFourier` beyond the fresh-bit boundary, i.e. some A > 1/α,
through low-frequency decay of the continuation characteristic function. **No improved exponent is claimed: the
exceptional exponent remains H₂(1/α) ≈ 0.949956.**

## 2. Exact triangle geometry — PROVED (LEAN), `EOC/TriangleArray.lean`

For a, b ∈ ℕ let y(a,b) ∈ ℤ be the centered representative of 2^{−a} mod 3^b (`y`, via `ZMod.valMinAbs`, so
−3^b < 2y ≤ 3^b), and

    U(a,b) = y(a,b) / 3^b.

A cell is **black** at threshold η if |U(a,b)| < η (`black`). Moving a ↦ a − 1 doubles U mod 1, moving b ↦ b − 1
triples it mod 1. Proved exact integer statements:

* `cast_y`, `cast_two_pow_mul_y` — reduction of y modulo smaller powers of 3;
* `y_succ_modEq`, `y_eq_two_mul` — horizontal recurrence 2y(a+1,b) ≡ y(a,b) (mod 3^b), with equality when small;
* `y_modEq_succ`, `y_eq_of_small` — vertical recurrence y(a,b+1) ≡ y(a,b) (mod 3^b), with equality when small;
* `propagate` — **triangle propagation**: if 2·2^k|y(a+k, b+l)| < 3^b then y(a,b) = 2^k·y(a+k, b+l);
* `merge`, `merge_apex` — two black cells (a+k, b), (a, b+l) with |y(a,b+l)| + 2^k|y(a+k,b)| < 3^b lie in one
  triangle with apex (a+k, b+l);
* `black_of_inLargeTriangle` — a cell deep inside a triangle is black and carries the apex value.

A triangle with apex (a*, b*) and size s consists of the cells (a*−k, b*−l) with k log 2 + l log 3 ≤ s, all carrying
y = 2^k·y(a*,b*): the whole triangle is **one** arithmetic relation (no multi-cell amplification).

## 3. Apex Diophantine relation — PROVED (LEAN), `EOC/MaxTriangle.lean`

With X = 2^a·y(a,b) and Y = X − 1 one has 3^b | Y (`three_pow_dvd`), i.e.

    2^a y − 3^b z = 1,     z = Y / 3^b,

with y ≠ 0 for b ≥ 1 (`y_ne_zero`) and z ≠ 0 for a ≥ 1 (`Y_ne_zero`). The **size** of a cell is

    s(a,b) = log(η / |U(a,b)|) = log(η · 3^b / |y(a,b)|)      (`size`),

and a triangle's size is the size of its apex. All cells of one triangle share the same X = 2^{a*}y*, so each triangle
determines a single integer point (X, X − 1).

## 4. Ridout / p-adic Subspace result

**PROVED (MATH), conditional only on the cited EXTERNAL THEOREM; the reduction is PROVED (LEAN).**
For every fixed η > 0,

    R_max(L) = o(L),

where R_max(L) is the largest apex size of a triangle meeting the corridor/path region of depth L (any region with
a log 2 + b log 3 = O(L), in particular the box 1 ≤ a ≤ m, 1 ≤ b ≤ L with m = O(L)).

Argument:

* Use x = (X, Y) ∈ ℤ² with X = 2^a·y and Y = 3^b·z = X − 1.
* Apply the p-adic Subspace Theorem (Schlickewei; Evertse's notes, Ch. 8, Thm 8.7) with n = 2, K = ℚ, places ∞, 2, 3,
  and the **fixed** linear forms X − Y, Y at ∞ and X, Y at 2 and at 3 (coefficients in {0, ±1}).
* The varying cofactors y, z are **coordinates of the integer point x, not coefficients** of the forms; the theorem is
  uniform over all x ∈ ℤ². (This is where Baker-type single-cell bounds fail and the Subspace Theorem does not.)
* The Subspace product equals y′z′/|X| (y′, z′ the {2,3}-free parts) and is ≤ 2|U(a,b)| (`subspaceProd_le`), while
  1 ≤ max(|X|, |Y|) ≤ 2^a·3^b (`H_bounds`). So a cell with |U| ≤ ½(2^a 3^b)^{−δ} solves the Subspace inequality
  (`subspace_ineq_of_exc`).
* The solutions lie on finitely many lines through 0; each line meets X − Y = 1 at most once, and 2^a ≤ |X|,
  3^b ≤ |Y|. Hence, for every fixed δ > 0, the exceptional set is finite (`exc_finite`), and

      |U(a,b)| ≥ c_δ (2^a 3^b)^{−δ}      for all a, b ≥ 1      (`apexBound_of_exc_finite`),

  i.e. s(a,b) ≤ δ(a log 2 + b log 3) + C_δ (`SublinearMaxTriangle`, `sublinearMaxTriangle_of_subspace`).
* For an apex over a cell with D = a log 2 + b log 3: s* ≤ (δD + C_δ)/(1 − δ) (`apex_size_le`); for any region with
  D ≤ K·L this gives R_max(L)/L → 0 (`eventually_maxTriangleLE`, `maxTriangleLE_box`).

The column a = 0 (y = 1, z = 0) is a genuine infinite exception; it never meets the corridor (a ≥ 1 there and apexes
satisfy a* ≥ a). Every inequality of the reduction was also checked in exact integer arithmetic on all 60 000 cells
with a ≤ 300, b ≤ 200 (COMPUTATIONAL, `scratch/ridout_2026-09-15/CHECK_300x200.txt`).

> **The result is ineffective: it gives no explicit rate and no computable threshold L₀(ε).**

The mechanism is analogous to Mahler's 1957 bound ‖(p/q)ⁿ‖ > e^{−εn} (also via Ridout); the EOC statement itself does
not appear in Mahler's work (see the literature file).

## 5. Triangle hopping theorem — PROVED (LEAN), `EOC/TriangleHop.lean`

For consecutive path cells (a, b) → (a − d, b + 1), both black: they lie in the same triangle exactly when
y(a−d, b+1) = 2^d·y(a,b) (`SameTri`; `sameTri_of_common_corner`, `corner_eq`). If they lie in **distinct** triangles
(`DistinctTriangleHop`), then

    (2^d + 3) η > 1      (`black_distinct_imp_large_digit`, `distinct_hop_pow_gt`),

so the least possible digit is

    d_min(η) = ⌊log₂(1/η − 3)⌋ + 1      (η < 1/4).

At **η = 1/54** this gives **d ≥ 6** (`distinct_hop_digit_ge_six`). The bound is **sharp**: the cells
**(160, 5) → (154, 6)** (y = 4, y′ = 13, 13 − 64·4 = −3⁵) form a distinct-triangle hop with d = 6, checked by the Lean
kernel (`distinct_hop_witness_d6`, via `decide`; no `native_decide`). Exact witnesses at d_min for η = 1/20, 1/100,
1/200 are in `scratch/hop_2026-09-15/WITNESS.txt` (COMPUTATIONAL). In one row, distinct black triangles are at least
6 columns apart at η = 1/54 (`sameRow_of_small_gap`).

## 6. Deterministic run decomposition — PROVED (LEAN), `EOC/TriangleHop.lean`

Path cells are (a i, b0 + i) with a (i+1) + d i = a i. A linked run of r steps from a black cell has a corner generator
of size > r log 3 (`chain_value`, `corner_eq`, `run_offset_lt`). For every path of n steps with b0 ≥ 1
(`run_decomposition`):

    n ≤ W + Occ(R₁) + H₁ · (1 + W + W′ + J),

and, at η = 1/54, using W′ ≤ W + 1 (`card_white_next_le`) and J ≤ N₆ (`run_decomposition_54`):

    n ≤ (2H₁ + 1)·W + Occ(R₁) + H₁·N₆ + 2H₁,

where W = #white cells, W′ = #{i : cell i+1 white}, J = #distinct-triangle hops, N₆ = #{i < n : d_i ≥ 6},
Occ(R₁) = #black cells lying in a triangle of size ≥ R₁, and H₁ = ⌊R₁/log 3⌋ + 1. If R_max ≤ R₀ < R₁ on the path,
then Occ(R₁) = 0 (`occ_eq_zero_of_maxTriangleLE`).

## 7. Why the obvious large-jump route fails — REFUTED (as a strategy)

Under the tilted law P*(d = k) = (1/α)(1 − 1/α)^{k−1}, large digits have positive density:

    p₆ = P*(d ≥ 6) = (1 − 1/α)⁵ ≈ 0.00685.

Keeping white density low on an interval requires only about n/H₁ hops, and H₁ grows with the triangle height. So the
required hop density tends to 0, below the typical density p₆: there is no large-deviation penalty. **Large-deviation
control of N₆ alone cannot prove positive-density good angles.** (The large-deviation bound itself holds: under the
confined law P_conf(N₆ ≥ qn) ≤ C n^{3/2} 2^{−n I(q‖p₆)} — PROVED (MATH), given the Θ(n^{−3/2}) confinement asymptotic,
which is a paper-level result of the author's ScalesConfinement note and is not contained in this repository.)

## 8. Why maximum triangle size is insufficient — PROVED (MATH), structural negative result

    R_max = o(L)   does NOT imply positive-density good angles.

Even with no hops, maximum control alone gives white density only ≳ 1/(2H + 1) with H = ⌊R_max/log 3⌋ + 1, and this is
combinatorially sharp: runs of height H separated by single white cells satisfy every proved local constraint. Many
moderate triangles can still occupy a positive density. Maximum control plus the large-deviation bound gives positive
density only if H·p₆ < 1, i.e. R_max ≲ 165 — true in every computation (R_max(6400) ≈ 8.2, §9) but not provable as
L → ∞.

## 9. Computational observations — COMPUTATIONAL

All numbers in this section are COMPUTATIONAL; none is a theorem.

**Maximum triangle size** along the critical corridor band (η = 1/54, t = J/6, offsets 0–3;
`scratch/ridout_2026-09-15/RMAX_J200-6400.txt`):

| J    | R_max | R_max/J | R_max/log J |
| ---- | ----: | ------: | ----------: |
| 200  |  4.29 |  0.021  |  0.81 |
| 400  |  3.74 |  0.0093 |  0.62 |
| 800  |  3.54 |  0.0044 |  0.53 |
| 1600 |  6.65 |  0.0042 |  0.90 |
| 3200 |  6.32 |  0.0020 |  0.78 |
| 6400 |  8.17 |  0.0013 |  0.93 |

These are consistent with R_max = O(log L) but do not prove it (one realization per J). A random-unit environment
gives comparable values.

**Triangle sizes** (`scratch/triangle_2026-09-15/`): P(size ≥ r) ≈ e^{−r} on a J = 800 band
(0.62 / 0.41 / 0.12 / 0.066 / 0.058 / 0.022 / 0.007 at r = 0.5 / 1 / 2 / 3 / 4 / 5 / 6); no slope or continued-fraction
resonance; true environment ≈ random-unit environment.

**Black occupation and hopping** (`scratch/hop_2026-09-15/HOPS.txt`, sampled confined paths, J = 100…1600):

* black fraction 0.032–0.038, close to 2η ≈ 0.037; white density ≥ 0.90 on every sampled path;
* distinct-triangle hops are rare: 2 among ≈ 11 000 black steps (true environment), consistent with the random-model
  rate p₆·2η ≈ 2.5·10⁻⁴;
* same-triangle runs average 1.35–1.44 steps (max 8); a black episode is almost always a single triangle;
* the behavior resembles a random-unit environment.

**Large digits** (`scratch/hop_2026-09-15/LD_TABLES.txt`, exact DP): E[N₆]/n = 0.0059–0.0066 under the confined law
(n = 60…300) against 0.00685 iid; confined tails are lighter than iid; n^{3/2}·P*(C_n) ∈ [0.43, 1.12].

**Low frequency** (`scratch/tao_2026-09-15/`): the λ = 1 continuation decays at ≈ 0.71–0.80 bits/step for j0 = 60…300.
Uniform decay fails under the critical confined law for small integer ξ, and no rigorous γ > 0 is known.

## 10. Current remaining analytic lemma — OPEN

### OPEN — Triangle occupation / critical white-count theorem

Find a theorem giving, for some fixed R, θ < 1, c > 0,

    Pr_conf( Occ_{≥R}(L) > θ L ) ≤ 2^{−cL},

where Occ_{≥R}(L) is the number of steps of a confined path of length L lying in Tao-black triangles of size ≥ R.
An equivalent positive-density-good-angle statement would also do. The run decomposition (§6) shows what suffices:
θ' := 1 − θ must exceed q·(⌊R/log 3⌋ + 1), where q is the large-deviation cutoff for N₆ (≈ p₆). For example,
R = 3, Occ ≤ L/2 and N₆ ≤ 0.02 L give white density ≥ 0.063 (PROVED (LEAN) glue:
`positiveDensityGoodAngles_of_runBound`, with `LargeJumpLD` and `TriangleOccupation` as hypotheses). The size
requirement is weak; the difficulty is the **exponential concentration**. Triangle size is the length of a run of
equal 3-adic digits (all 0 or all 2) of 2^{−a}, sampled along the path, so this is a digit-statistics problem for
powers of 2. The incomplete sums involved (windows of length O(√b) against period 2·3^{b−1}) are far outside the
Kloosterman/Burgess/Korobov range.

A second, smaller missing lemma is **white-point contraction** for the pair-block factors of `BlockCubeInstance`
(white cell ⇒ block factor ≤ κ < 1). It is OPEN in Lean.

## 11. Formal chain

    TriangleOccupation  ⇒  PositiveDensityGoodAngles  ⇒  LowFreqDecay  ⇒  WeightedFourier  ⇒  A > 1/α

* **First arrow — still requires analytic input.** In Lean it is `positiveDensityGoodAngles_of_runBound` together with
  the per-path bound of `run_decomposition_54`. It assumes `TriangleOccupation` (OPEN), `LargeJumpLD`
  (PROVED (MATH) given the confinement asymptotic, not yet in Lean) and white-point contraction (OPEN). The identification of path cells with the
  block indices of `GoodAngles` is not yet formalized.
* **Second arrow:** `lowFreqDecay_of_goodAngles`, assuming `BlockCubeHyp`. `BlockCubeHyp` is instantiated
  unconditionally for L = 2 pair blocks by `blockCubeHyp_pair` (PROVED (LEAN)).
* **Third arrow:** `weightedFourier_of_lowFreqDecay_and_sieve` (PROVED (LEAN)). It combines the (C3) sieve on high
  shells with a finite numerical shell condition.
* **Fourth arrow:** `weighted_phi_decay_implies_exceptional_bound` (PROVED (LEAN)) gives exponent 1 − I₀A.
  - That a fixed low-frequency rate γ > 0 yields some A > 1/α comes from the chain formula evaluated asymptotically
    (COMPUTATIONAL; `scratch/decay_2026-09-15/`, `scratch/spacing_2026-09-15/`).
  - A merely subexponential rate (e.g. from R_max = o(L)) gives no exponent improvement.

## 12. Refuted / closed routes

Each item points to the round report under `scratch/` where it is documented; labels as stated there.

* **Uniform-in-frequency Tao decay** — REFUTED. λ = 3^{j0} gives |Φ| ≈ |P| (swap round). Under the critical confined
  law, ξ = 1, 2, −1/2 give |Φ_ξ/P| ≈ const (Tao round). Tao's uniform estimate uses a supercritical slope and has no
  margin at criticality.
* **Shell (m) averaging** — REFUTED as a route (PROVED (MATH)). |Φ_{m−1}(λ)| = |Φ_m(2λ)|, so averaging W shells is
  frequency dilation and adds at most log₂W bits of frequency entropy (orbit round).
* **Power-of-two short-orbit averaging** — closed. The effective shell window is bounded or logarithmic
  (COMPUTATIONAL, orbit round). Korobov and Bourgain–Glibichuk–Konyagin need superpolynomial windows. LTE controls
  only 3-adic, not archimedean, closeness.
* **Additive-energy route** — closed.
  - The relevant additive energy is 10–62× the random value (COMPUTATIONAL), explained by exact tail-swap identities
    (spacing round).
  - The prefix-sharing Cauchy–Schwarz bound is attained under adversarial phase alignment (PROVED (LEAN)
    `RenyiBarrier.aligned_attains`, `RenyiInstance.aligned_split_attains`). So arguments that bound continuation sums
    by their size cannot beat the Rényi-2 exponent θ_M = H_R/α ≈ 0.705 < H₂ (spacing and decay rounds).
* **Frequency-tree / resonance entropy counting** — no gain. The v3-resonance factorization and its entropy tradeoff are
  harmless but give no saving (weighted round). Shell averaging adds only log₂W bits (orbit round).
* **Probabilistic rapid escape from large triangles** — REFUTED at criticality. The depth drift is zero, so paths ride to
  the apex row (triangle round).
* **Maximum-size-only route** — REFUTED as a strategy (§8, PROVED (MATH)).
* **Large-d-count-only route** — REFUTED as a strategy (§7).
* **Baker-type bounds on single triangle cells** — not applicable. The heights of the relevant rationals are ~L, so
  such bounds shave only a 1/log fraction (swap round). For the maximum this is superseded by §4, which does not use
  Baker.

## Module inventory for this checkpoint

The 44 modules below were added in the 2026-09-14/15 rounds. All compile and are imported by `EOC.lean`. Where a
module's main theorem carries an analytic hypothesis, that hypothesis is an explicit `Prop` named in the module
docstring (e.g. `WeightedFourier`, `BlockCubeHyp`, `PositiveDensityGoodAngles`, `LowFreqDecay`, `SubspaceInstance`,
`TriangleGapBridge`, `LargeJumpLD`, `TriangleOccupation`). The round report for each module is in `scratch/<round>/`.

* Realizer/transport layer (2026-09-14): `PairValuation`, `SuffixTransport`, `TransportCollapse`, `PrescribedMatching`,
  `LogCorridor`, `UpperEscape`, `UpperCertificates`, `SurvivorCounting`, `CapacityBounds`, `SurvivorDensity`,
  `EntropyBounds`, `SurvivorClusters`, `ExceptionalPowerBound`, `SplitPrefix`, `LiftDigits`, `ResidueDiscrepancy`.
* Fourier/exponent chain: `ShellWeyl`, `PrefixSuffixBilinear`, `PrefixCollision`, `PrefixStateFormula`,
  `ShellwiseChain`, `SwapBound`, `SwapCollatz`, `TwistExpansion`, `WeightedChain`, `FirstDivergence`, `BlockCube`,
  `ShellDecomposition`, `ShellRefined`, `ThreeBlock`, `WhiteRun`, `IntervalSieve`, `SpacingChain`, `PsiSieve`,
  `PsiShellBound`, `PowerOrbit`, `RenyiBarrier`, `DecayInterface`, `RenyiInstance`, `GoodAngles`.
* Triangle layer: `TriangleArray`, `BlockCubeInstance`, `MaxTriangle`, `TriangleHop`.

The round reports' header line "Nothing committed or pushed" describes the state at the end of each round. All of
them were committed together at this checkpoint.
