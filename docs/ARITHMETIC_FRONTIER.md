# Arithmetic frontier — power-of-two digit sparsity (2026-09-16)

Labels as in [`RESEARCH_STATUS.md`](RESEARCH_STATUS.md). Lean source: `EOC/ArithmeticFrontier.lean`. Round reports:
[`../scratch/shiftaudit_2026-09-16/REPORT.md`](../scratch/shiftaudit_2026-09-16/REPORT.md),
[`../scratch/sparsevisits_2026-09-16/REPORT.md`](../scratch/sparsevisits_2026-09-16/REPORT.md),
[`../scratch/codimension_2026-09-16/REPORT.md`](../scratch/codimension_2026-09-16/REPORT.md).

**Summary.** `PowerOfTwoDangerousWindowSparsity ⇒ LowFreqDecay` is PROVED (LEAN).
`PowerOfTwoDangerousWindowSparsity` itself is OPEN. Nothing here proves `LowFreqDecay` unconditionally, improves the
exceptional-set exponent, or proves EOC or the Collatz conjecture.

## 1. The hypothesis (definition, Lean)

```lean
def PowerOfTwoDangerousWindowSparsity (j t U K : ℕ) (d a b : ℝ) : Prop :=
  ∀ u ≤ U, ∀ lam ∈ ShellDecomposition.cshell (collatzBarrier 0 j + 1) t u,
    ∃ bad : Finset ℕ,
      (bad.card : ℝ) ≤ 2 / 9 * ((j / 2 / K : ℕ) : ℝ) + (a * Real.logb 2 j + b) / K ∧
      ∀ i < j / 2 / K, i ∉ bad → ∀ y : Fin (collatzBarrier 0 j + 1),
        val (geoW (((j : ℝ) - 1) / ((collatzBarrier 0 j : ℝ) - 1))
            (((collatzBarrier 0 j : ℝ) - j) / ((collatzBarrier 0 j : ℝ) - 1))
            (oddW (collatzBarrier 0) (collatzBarrier 0 j + 1 + t) d 3 lam)
            (collatzBarrier 0 j)) (i * K) K y ≤ (2 : ℝ) ^ (2 * (K : ℝ) * (1 / 10))
```

In words: split the j/2 pair blocks into W = ⌊(j/2)/K⌋ disjoint windows of K blocks. For every low-frequency shell
u ≤ U and every frequency λ in it, at most (2/9)·W + (a log₂ j + b)/K windows may be *dangerous*. A window is dangerous
when its geometric odd-dark kernel mass (tilt s = 3), from some start state, exceeds 2^{2K/10}. That is a rate above
**1/10 per step**, since a window has 2K steps.

## 2. What it implies (PROVED (LEAN))

* `EOC.ArithmeticFrontier.summedPressure_of_powerOfTwoSparsity`: for even j ≥ 300, 0 < K ≤ A log₂ j + 1 and b ≥ 0,
  the hypothesis gives `AverageOddDark.SummedOddDarkPressure` at rate θ = 1/6 with
  C = 2 + (3/5)a + (4/5)A + (2 + (3/5)b + 4/5)/8. Any logarithmic A is allowed.
* `EOC.ArithmeticFrontier.lowFreqDecay_of_powerOfTwoSparsity`: under the parameter inequalities of
  `AverageOddDark.lowFreqDecay_of_summedPressure` (block budget, θ′ > 1/6, the cutoff (3C/(θ′ − 1/6))² ≤ j, and the
  conditions on γ), the hypothesis gives `DecayInterface.LowFreqDecay (collatzBarrier 0) j (collatzBarrier 0 j) t U 4 γ`.
* The route is: dangerous-window count ⇒ summed pressure (`DangerousWindows.summedPressure_of_tenth_twoNinths`) ⇒
  `LowFreqDecay`. The last step combines the proved `ShapeTail` with the frequency-summed white-count split
  (`AverageOddDark.lowFreqDecay_of_shape_and_summedPressure`). This split is the summed form of the
  `CriticalWhiteCount` argument; the per-frequency `CriticalWhiteCount` `Prop` is not instantiated on this route.
* `#print axioms` for both theorems, the definition, and the helpers below: `propext`, `Classical.choice`,
  `Quot.sound`. No `sorry`, `axiom` or `native_decide`.

## 3. Why λ = 1 is unavoidable (PROVED (LEAN) + PROVED (MATH))

The u = 0 shell is cshell(σ+1, t, 0) = {1, 2^m − 1} with m = σ + 1 + t, and this shell is present at every shift.
`DangerousWindows.nodd_companion` (PROVED (LEAN)) shows that λ and 2^m − λ have identical odd-dark counts. So the u = 0
case of the hypothesis is exactly the λ = 1 environment, with no frequency averaging available.

## 4. The three-zero-digit characterization (PROVED (LEAN) + PROVED (MATH))

* `dark_iff_distZ` (PROVED (LEAN)): the dark predicate is ‖λ·u·2^z/2^m‖ < d with u = 3^{−(2r+2)} mod 2^m.
* By reciprocity, for λ = 1 at low frequency this is a condition on the centered residue of 2^{−a} mod 3^b, with
  a = m − z and b = 2r + 2 (PROVED (MATH); the exact scan engine checks the parity condition that makes both tests agree).
* `black_fiftyfourth_iff` (PROVED (LEAN)): Tao-black at η = 1/54 holds iff 2|y| < 3^{b−3}, i.e. the three leading
  balanced-ternary digits of y vanish. Dark at d = 1/108 implies black at η = 1/54 (PROVED (MATH)).

For λ = 1, the hypothesis is therefore a statement about how often certain leading ternary digit patterns of
2^{−a} mod 3^b can occur along the EOC diagonal. This lies in the same general family as classical unresolved
digit-distribution questions for powers of 2, such as Erdős's question on the ternary digits of 2^n. No equivalence
with any such conjecture is claimed or known.

## 5. Shift translation (PROVED (LEAN))

`dark_shift`: `Dark (m + t) d λ r (z + t) ↔ Dark m d λ r z` (via `uInv_modEq_shift`). Only a = m − z matters. Moving
the shift t by one is absorbed by moving the column, so the supremum over start states makes neighbouring shifts very
similar. The observed autocorrelation is 0.92–1.00 at j = 400 (COMPUTATIONAL).

## 6. Haar codimension (PROVED (MATH))

For a Haar-random 3-adic environment and any start state, P(K-window mass > 2^{2K/10}) ≤ 1.055·3^{−0.100K}. The
exponent improves to 0.136 with a second-moment operator. After a union over start states this covers
K ≳ 4.6–6.3·log₂ j.

## 7. Why Haar rarity does not imply deterministic rarity

The bound in §6 is about a random environment. The hypothesis concerns the single deterministic orbit 2^{−a} mod 3^b.
* Consecutive exponents do not act like Haar samples: short exponent intervals over-visit black cylinders
  (COMPUTATIONAL, `sparsevisits` report).
* The exponent lift 2^{Q_D} ≡ 1 + c·3^D (mod 3^{D+1}), with Q_D = 2·3^{D−1} (PROVED (MATH)), is triangular, but the
  digit tests admit no finite transducer (REFUTED as a route).
* Full-period averaging would need about Q_D ≈ 3^{4K} = j^{O(1)} consecutive shifts.

## 8. Why shift averaging does not help in the present architecture (PROVED (MATH), architecture-level)

Audit of `WeightedChain.weighted_phi_decay_implies_exceptional_bound` and `ShellwiseChain`:
* **Shift t.** A shell pair (s, σ) with t = s − σ that fails the hypothesis must use the trivial branch
  c ≥ 2^{s+1−K}, or an ε from the collision bound with ε² ≳ 2^t. Its Haar share is only about N^{−1/2} in the bulk
  (a local limit estimate for the negative-binomial shift profile). A bad shift can therefore be paid for only when
  t = O(log C). **Pointwise control in t is essentially required.**
* **u.** Uniformity in u is only an API convenience (the sieve step sums over u with weights), but this does not
  weaken the λ = 1 requirement.
* **λ.** Frequencies are summed, but because the moments are exponential, only exponentially rare bad λ are
  tolerated. λ = 1 must be good.
* **j.** Only one j₀ per K is needed. This gives no new environments, because the phase depends on m = s + 1.

These are statements about the **current proof architecture**. They are not impossibility theorems for every
conceivable future EOC approach.

## 9. Computational evidence (COMPUTATIONAL)

`scratch/shiftaudit_2026-09-16/`: 1230 environments, dark threshold d = 1/108, tilt s = 3, K = ⌈2 log₂ j⌉ (and
K = ⌈5 log₂ j⌉ on 40 shifts). The windows are the Lean windows, with the supremum over start states.

| j | K | W | λ = 1 shifts | Haar controls | worst λ = 1 window rate | worst Haar window rate |
|---|---|---|---|---|---|---|
| 400 | 18 | 11 | 306 consecutive + 294 scattered | 100 | 0.0912 (t = 1502) | 0.0874 |
| 800 | 20 | 20 | 153 + 147 (+ 40 at K = 49) | 50 | 0.0865 (t = 4353); 0.0259 at K = 49 | 0.0779 |
| 1600 | 22 | 36 | 60 + 60 | 20 | 0.0841 (t = 56430) | 0.0776 |

* The rate threshold for a dangerous window is **1/10**, the formal threshold of the hypothesis. No sampled window
  exceeded it, so every sampled environment has 0 dangerous windows. The allowance of 2/9·W bad windows was never used.
* The three worst λ = 1 shifts per j (nine environments, 201 windows) were certified by exact integer arithmetic
  (G⁵ ≤ 2^K·D^{5(T−x)}). Worst exact rate: **0.09124 < 1/10**. The margin is only about 9%.
* The larger margin reported for K = 49 matches the danger density decaying with K (HEURISTIC).

These finite computations support the hypothesis but do not prove it.

## 10. Open mathematical target (OPEN)

Prove `PowerOfTwoDangerousWindowSparsity` for all sufficiently large even j, every shift t in the relevant range, and
some logarithmic K ≤ A log₂ j + 1. The λ = 1 case (§3) is the essential core. Separately OPEN, and needed by the
exceptional-set chain: lower shells σ < ⌊jα⌋ and barrier offsets U > 0.

## 11. Non-claims

* `PowerOfTwoDangerousWindowSparsity` is **not** proved.
* It is **not** known to follow from any equidistribution theorem.
* It is **not** claimed equivalent to Erdős's conjecture or to any other named conjecture.
* `SummedOddDarkPressure`, `CriticalWhiteCount` and `LowFreqDecay` for the true environment remain conditional.
* The Haar bound (§6) is not a statement about powers of 2.
* The negative audit (§8) concerns the current architecture only.
* EOC and the Collatz conjecture remain OPEN.
