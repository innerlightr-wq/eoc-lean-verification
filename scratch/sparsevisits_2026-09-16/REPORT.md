# Deterministic sparse visits for 2^{-a} mod 3^D (research round, 2026-09-16)

Committed to the PR #9 branch together with the shift audit (parent 1895557).  No Lean changes.  Scripts: `lift.py` (exponent-lift structure, occupancy), `largeA.py` →
`LARGE_A.txt`, `FORMAL_A.txt`.  No positive stop condition fired; kill condition 1 fired for the transducer route.

## Target (PROVED LEAN, unchanged)
`summedPressure_of_tenth_twoNinths`: for every u ≤ U and λ ∈ cshell(σ+1, t, u) there is a Finset `bad` with
`(bad.card : ℝ) ≤ (2/9)·W + (a log₂ j + b)/K` such that every window i < W, i ∉ bad, has geometric mass ≤ 2^{2K/10}
from every state; j/2 = W·K + ρ, ρ ≤ K, K ≤ k₁ log₂ j + k₀.

## Exponent walk (PROVED MATH)
* Dark at block r, column z (λ = 1, low frequencies) is, up to the reciprocity term, a condition on the top balanced
  digits of 2^{−a} mod 3^b with **a = σ + 1 + t − z** and **b = 2r + 2**.
* Shift t translates every exponent by t.  A window from start state x₀ reads a ∈ [σ+1+t−cap, σ+t−x₀] (length
  ≤ h₀ + 2αK) at rows b ∈ [2r₀+2, 2r₀+2K]: as the window index grows, b increases by 2K and a decreases by ≈ 2αK —
  a diagonal, not an interval at fixed modulus.
* Common-depth lift: every test in the window is a function of v = 2^{−(σ+1+t−x₀)} mod 3^{2r₀+2K} (row b, column z
  reads the top digits of v·2^{z−x₀} mod 3^b), so E_{K,x₀} ⊆ (ℤ/3^{2r₀+2K})^× is well defined; its relative size is
  ≤ 1.055·3^{−0.100K} by the Haar codimension bound.  Because of carries from v·2^{z−x₀}, E is not a union of cylinders
  at bounded depth (only margin-resolved): no symbolic finite-depth representation was built.
* Equivalently, for fixed t the windows read successive digit blocks of the single 3-adic unit 2^{−(σ+1+t)} (twisted by
  multiplications by 2^{z−x₀}).  The λ = 1 sparse-visit statement is therefore a digit-pattern frequency statement for
  the 3-adic expansions of powers of 2 — the same family as Erdős's conjecture on ternary digits of 2^n
  (J. C. Lagarias, "Ternary expansions of powers of 2", J. London Math. Soc. 79(3) (2009) 562–588,
  doi:10.1112/jlms/jdn080), for which only weak unconditional results are known.  (Context, not a claim of equivalence.)

## Lift recursion (PROVED MATH, verified exactly at D = 9, 11)
2^{Q_D} ≡ 1 + c·3^D (mod 3^{D+1}), 3 ∤ c.  Hence for 0 ≤ a < Q_D and k ∈ {0,1,2}:
2^{−(a+kQ_D)} ≡ 2^{−a} − k·c·2^{−a}·3^D, i.e. the lower D digits are unchanged and digit D shifts by k·s(a mod 2) (mod 3).
Consequences: full-period counts are exact (every unit once per Q_D; a cylinder of codimension q has exactly
|units|/3^q exponents); digit D is a bijective function of the exponent digit k_D **offset by all lower exponent digits**.

## Transducer (REFUTED — kill condition 1)
Minimal memory for digit i as a function of (e₀, k_{i−w..i}): w = i − 1 at every tested depth (digits 3, 8, 10 at
D = 9, 11) — the offset depends on all lower exponent digits; no finite-state transducer.

## Short-interval occupancy along consecutive exponents (COMPUTATIONAL, exact full scans)
Top digits evolve by the halving map u ↦ (u + ε)/2 (ε = parity), so small-u starts produce clusters of length
≈ 1.585·D.  Black cylinder (density 1/27): M(L)/L = 1.00 (L ≤ 10), 0.50 (L = 30), 0.21 (L = 100), 0.11 (L = 300)
at D = 11; one digit (density 1/3): 1.0, 0.8, 0.56, 0.43.  Worst-case short intervals over-visit by 3–27×; a
uniform "M(L) ≤ ρL + C" with ρ < 2/9 fails for cylinders at the scale L ≲ 100 unless C ≳ 1.585 D.  (This is the
fixed-modulus walk; EOC uses the diagonal family above.)

## Frequency shells (PROVED MATH)
* u = 0: cshell = {1, 2^m − 1}, identical dark sets (PROVED LEAN, `nodd_companion`): no averaging.
* Window danger depends on λ through ξ = λ·2^{x₀−m} mod 3^{2r₀+2K} (3-adic side; the reciprocity term needs
  2^{t+1} > 108λ) or through λ mod 2^{m−x₀} (2-adic side).  Consecutive λ give exact full-period equidistribution only
  when 2^u ≥ 3^{2r₀+2K} (resp. 2^{m−x₀}).  Hence elementary averaging covers window r₀ only for
  u ≳ 1.585(2r₀ + 2K): **u*(j) ≈ 1.585 j + O(log j)** for all windows — linear, not O(log j).  For u ≥ t − 6 the
  3-adic form also loses the reciprocity smallness.  Small-u shells are not logarithmically many.

## Codimension refinement (secondary; COMPUTATIONAL estimate)
The exact annealed β = 1 rate implied by the Haar Monte Carlo (mean per-state mass 1.096 at K = 8) is c ≈ 0.116,
so the 2-state LP (0.100) is near-optimal at β = 1; gains need higher moments with a resolved phase state (the
compact-fiber θ operator), whose ceiling is the empirical LD rate ≈ 0.5.  No richer matrix was certified.
A_min = 1/(c log₂ 3): c = 0.100 → 6.31; 0.116 → 5.44; 0.136 → 4.64; 0.5 → 1.26.

## Larger A (PROVED MATH / COMPUTATIONAL)
The wrapper accepts any K ≤ k₁ log₂ j + k₀: A = 5 gives C = 6.35 (cutoff 6.8·10⁶ at θ' = 0.174), A = 7 gives
C = 7.95 (1.1·10⁷).  Floats (`LARGE_A.txt`): A = 5, 7 at j = 400…3200, λ = 1, t ∈ {1, j/6}: 0 dangerous windows,
max rates 0.014–0.040, W ≥ 3.  Larger A is formally usable; it only raises the finite cutoff.
