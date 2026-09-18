import EOC.DangerousWindows

/-!
# The arithmetic frontier of the pressure chain

Everything between the confined-word combinatorics and `LowFreqDecay` is now proved, except one
arithmetic count.  This file names that count and proves the end-to-end implication.

* `PowerOfTwoDangerousWindowSparsity j t U K d a b` — **the explicit arithmetic input.**  For every
  low-frequency shell `u ≤ U` and every frequency `λ` in it, at most `(2/9) W + (a log₂ j + b)/K` of
  the `W = ⌊(j/2)/K⌋` disjoint `K`-block windows of the geometric odd-dark kernel have mass above
  `2^{K/5}` from some start state.  For `λ = 1` (the `u = 0` shell, see
  `DangerousWindows.nodd_companion`) the dark cells are top-ternary-digit conditions on the
  residues `2^{-(m-z)} mod 3^{2r+2}`, so the hypothesis asserts that certain top ternary digit
  patterns of powers of `2` do not occur too often along the EOC diagonal.  It is **not** known to
  follow from any equidistribution theorem, and it is **not** claimed to be equivalent to Erdős's
  conjecture on the ternary digits of `2^n`; it belongs to the same general family of open
  digit-distribution questions.
* `lowFreqDecay_of_powerOfTwoSparsity` — **the hypothesis implies `LowFreqDecay`** (through
  `SummedOddDarkPressure` at rate `1/6`, the proved `ShapeTail`, and the frequency-summed
  white-count split `AverageOddDark.lowFreqDecay_of_shape_and_summedPressure`; the per-frequency
  `CriticalWhiteCount` `Prop` is not instantiated), for any logarithmic window size
  `K ≤ A log₂ j + 1`, with the explicit constant `C = 2 + (3/5)a + (4/5)A + (2 + (3/5)b + 4/5)/8`.
  The hypothesis itself is OPEN, so `LowFreqDecay` remains conditional.
* Stable helpers: `dark_iff_distZ` (the dark predicate is `‖λ u 2^z / 2^m‖ < d`), `dark_shift`
  (**shift translation**: raising `m` and the column `z` by the same `t` leaves the dark predicate
  unchanged, so only `a = m − z` matters), `black_fiftyfourth_iff` (Tao-black at `η = 1/54` is
  `2|y| < 3^{b−3}`, i.e. the three leading balanced-ternary digits of `y` vanish).

No `sorry`, `admit`, `axiom`, `opaque`, or `native_decide`.
-/

namespace EOC
namespace ArithmeticFrontier

open Finset LocalWindow PressureBridge CapacityBounds DangerousWindows

/-! ## 1. Stable helpers -/

/-- The dark predicate is a distance-to-integer condition on `λ u 2^z / 2^m`. -/
theorem dark_iff_distZ {m : ℕ} {d : ℝ} {lam r z : ℕ} :
    OddBlack.Dark m d lam r z ↔
      WhiteContraction.distZ
        (((lam * WeightedChain.uInv m (2 * r + 1) * 2 ^ z : ℕ) : ℝ) / 2 ^ m) < d := by
  unfold OddBlack.Dark WhiteContraction.pairPhase
  obtain ⟨k, hk⟩ :=
    WhiteContraction.collatzPhase_sub_succ lam m (WeightedChain.uInv m) (2 * r + 1) z
  rw [hk, WhiteContraction.distZ_add_int]

theorem uInv_modEq_shift (m t i : ℕ) :
    (WeightedChain.uInv (m + t) i : ℤ) ≡ WeightedChain.uInv m i [ZMOD 2 ^ m] := by
  have h1 := PsiSieve.uInv_modEq (m + t) i
  have h2 := PsiSieve.uInv_modEq m i
  have h1' : (WeightedChain.uInv (m + t) i : ℤ) * 3 ^ (i + 1) ≡ 1 [ZMOD 2 ^ m] :=
    Int.ModEq.of_mul_right (2 ^ t) (by rw [← pow_add]; exact h1)
  have hcop : IsCoprime ((2 : ℤ) ^ m) (3 ^ (i + 1)) := by
    apply IsCoprime.pow; rw [Int.isCoprime_iff_gcd_eq_one]; rfl
  have hdiv : (2 : ℤ) ^ m ∣ ((WeightedChain.uInv (m + t) i : ℤ) - WeightedChain.uInv m i) *
      3 ^ (i + 1) := by
    have := (h1'.trans h2.symm).symm.dvd
    simpa [sub_mul] using this
  have := hcop.dvd_of_dvd_mul_right hdiv
  exact (Int.ModEq.symm ((Int.modEq_iff_dvd).mpr this))

/-- **Shift translation.**  Raising the modulus exponent `m` and the column `z` by the same `t`
leaves the dark predicate unchanged: only `a = m − z` matters. -/
theorem dark_shift {m t : ℕ} {d : ℝ} {lam r z : ℕ} :
    OddBlack.Dark (m + t) d lam r (z + t) ↔ OddBlack.Dark m d lam r z := by
  rw [dark_iff_distZ, dark_iff_distZ]
  obtain ⟨k, hk⟩ := (Int.modEq_iff_dvd).mp (uInv_modEq_shift m t (2 * r + 1)).symm
  -- uInv (m+t) = uInv m + 2^m k
  have hu : (WeightedChain.uInv (m + t) (2 * r + 1) : ℝ) =
      WeightedChain.uInv m (2 * r + 1) + 2 ^ m * k := by
    have : (WeightedChain.uInv (m + t) (2 * r + 1) : ℤ) =
        WeightedChain.uInv m (2 * r + 1) + 2 ^ m * k := by linarith
    exact_mod_cast this
  have hval :
      (((lam * WeightedChain.uInv (m + t) (2 * r + 1) * 2 ^ (z + t) : ℕ) : ℝ) / 2 ^ (m + t)) =
      (((lam * WeightedChain.uInv m (2 * r + 1) * 2 ^ z : ℕ) : ℝ) / 2 ^ m) +
        ((lam * 2 ^ z * k : ℤ) : ℝ) := by
    push_cast [hu]
    rw [pow_add, pow_add]
    field_simp
  rw [hval, WhiteContraction.distZ_add_int]

/-- **Tao-black at `η = 1/54` is a three-digit condition.**  `black a b (1/54)` holds iff
`2|y| < 3^{b−3}`, i.e. (for the centered representative `y`, `|y| ≤ (3^b − 1)/2`) iff the three
leading balanced-ternary digits of `y` vanish. -/
theorem black_fiftyfourth_iff {a b : ℕ} (hb : 3 ≤ b) :
    TriangleArray.black a b (1 / 54) ↔ 2 * |(TriangleArray.y a b : ℝ)| < 3 ^ (b - 3) := by
  unfold TriangleArray.black
  have h3 : (3 : ℝ) ^ b = 27 * 3 ^ (b - 3) := by
    have : (3 : ℝ) ^ b = 3 ^ (b - 3) * 3 ^ 3 := by rw [← pow_add]; congr 1; omega
    rw [this]; ring
  rw [h3]
  constructor <;> intro h <;> linarith

/-! ## 2. The named arithmetic hypothesis -/

/-- **`PowerOfTwoDangerousWindowSparsity`** — the explicit arithmetic input of the pressure chain.
For every shell `u ≤ U` and frequency `λ ∈ cshell (σ+1) t u` (σ = ⌊jα⌋), all but
`(2/9) W + (a log₂ j + b)/K` of the `W = ⌊(j/2)/K⌋` disjoint `K`-block windows have geometric
odd-dark mass at most `2^{2K/10}` from every start state.  For `λ = 1` this asserts that certain top
ternary digit patterns of powers of `2` cannot occur with sufficient frequency along the EOC
diagonal.  OPEN: not known to follow from equidistribution; not claimed equivalent to Erdős's
ternary-digit conjecture. -/
def PowerOfTwoDangerousWindowSparsity (j t U K : ℕ) (d a b : ℝ) : Prop :=
  ∀ u ≤ U, ∀ lam ∈ ShellDecomposition.cshell (collatzBarrier 0 j + 1) t u,
    ∃ bad : Finset ℕ,
      (bad.card : ℝ) ≤ 2 / 9 * ((j / 2 / K : ℕ) : ℝ) + (a * Real.logb 2 j + b) / K ∧
      ∀ i < j / 2 / K, i ∉ bad → ∀ y : Fin (collatzBarrier 0 j + 1),
        val (geoW (((j : ℝ) - 1) / ((collatzBarrier 0 j : ℝ) - 1))
            (((collatzBarrier 0 j : ℝ) - j) / ((collatzBarrier 0 j : ℝ) - 1))
            (oddW (collatzBarrier 0) (collatzBarrier 0 j + 1 + t) d 3 lam)
            (collatzBarrier 0 j)) (i * K) K y ≤ (2 : ℝ) ^ (2 * (K : ℝ) * (1 / 10))

/-! ## 3. End-to-end: the hypothesis implies `LowFreqDecay` -/

/-- **`PowerOfTwoDangerousWindowSparsity ⇒ SummedOddDarkPressure (1/6)`** for logarithmic
windows. -/
theorem summedPressure_of_powerOfTwoSparsity {j t U K : ℕ} {d a b A : ℝ}
    (hj : 300 ≤ j) (hev : 2 ∣ j) (hK : 0 < K) (hKlog : (K : ℝ) ≤ A * Real.logb 2 j + 1)
    (hb : 0 ≤ b) (h : PowerOfTwoDangerousWindowSparsity j t U K d a b) :
    AverageOddDark.SummedOddDarkPressure (collatzBarrier 0) j (collatzBarrier 0 j) t U d 3
      (1 / 6) (2 + 3 / 5 * a + 4 / 5 * A + (2 + 3 / 5 * b + 4 / 5 * 1) / 8) := by
  have hR : j / 2 = (j / 2 / K) * K + (j / 2) % K := by
    have := Nat.div_add_mod (j / 2) K; rw [mul_comm] at this; omega
  have hρ : (j / 2) % K ≤ K := (Nat.mod_lt _ hK).le
  exact summedPressure_of_tenth_twoNinths hj hev hR hρ hK hb (by norm_num) hKlog h

/-- **End to end: `PowerOfTwoDangerousWindowSparsity ⇒ LowFreqDecay`.**  The only non-arithmetic
inputs are the parameter inequalities of `AverageOddDark.lowFreqDecay_of_summedPressure` (block
budget for `N₀`, split `k + n`, dark threshold `d`, rate `θ' > 1/6`, finite cutoff
`(3C/(θ' − 1/6))² ≤ j`, and the rate conditions for `γ`). -/
theorem lowFreqDecay_of_powerOfTwoSparsity {j t U K N0 Kb k n : ℕ} {d a b A θ' ν γ : ℝ}
    (hj : 300 ≤ j) (hev : 2 ∣ j) (hK : 0 < K) (hKlog : (K : ℝ) ≤ A * Real.logb 2 j + 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : 0 ≤ A)
    (hbudget : Kb + 31 * j / 100 + collatzBarrier 0 j / (N0 + 2) ≤ j / 2) (hkn : k + n ≤ Kb)
    (hN : 2 ≤ N0) (hd0 : 0 ≤ d) (hd1 : d ≤ 1 / 2) (hθ : 1 / 6 < θ')
    (hlarge :
      (3 * (2 + 3 / 5 * a + 4 / 5 * A + (2 + 3 / 5 * b + 4 / 5 * 1) / 8) / (θ' - 1 / 6)) ^ 2 ≤ j)
    (hn : ν * j ≤ n) (hγ : θ' + γ ≤ ν * Real.logb 2 ((1 + 3) / 2)) (hγ300 : γ ≤ 1 / 300)
    (hγk : γ * j * Real.log 2 ≤ 8 * k * d ^ 2 / N0)
    (h : PowerOfTwoDangerousWindowSparsity j t U K d a b) :
    DecayInterface.LowFreqDecay (collatzBarrier 0) j (collatzBarrier 0 j) t U 4 γ :=
  AverageOddDark.lowFreqDecay_of_summedPressure hj hev hbudget hkn hN hd0 hd1 (by norm_num)
    (by positivity) hθ hlarge hn hγ hγ300 hγk
    (summedPressure_of_powerOfTwoSparsity hj hev hK hKlog hb h)

end ArithmeticFrontier
end EOC
