import EOC.ShapeCertificate
import EOC.CapacityBounds
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Log

/-!
# Unconditional ShapeTail for the Collatz barrier

`ShapeCertificate.shapeTail_of_arith` reduces `ShapeTail` to one arithmetic inequality.  This file
discharges it, with every side condition, for the zero-offset Collatz barrier `σ = ⌊j log₂ 3⌋`:

* `shapeTail_cofinal` — `j₀ = 300(q+1)`, `K = 12(q+1)`, `ρ₁ = 2^{-(q+1)}`;
* `shapeTail_allEven` — every even `j₀ ≥ 300`, `K = ⌊j₀/25⌋`, `ρ₁ = 2^{-⌊j₀/300⌋}`;
* `shapeTail_allEven_rate` — the same with `ρ₁ ≤ 2 · 2^{-j₀/300}`.

Schedule: `N₀ = 10`, `T = ⌊31 j₀/100⌋`.

## Architecture (chosen to keep proof terms small)

1. `collatzBarrier 0 j = Nat.log 2 (3^j)` is the only lemma that touches `ℝ`; the `+300` barrier
   recurrences are then pure `ℕ` consequences of `2^475 < 3^300 < 2^476`.
2. The induction step `step_core` is proved with **all exponents abstract**, then instantiated; the
   elaborator never normalizes a literal such as `2^477`.
3. The block binomial uses `C(95,60)^5 ≤ C(475,300)` (Vandermonde) and `2^86 ≤ C(95,60)`.
4. The 150 even base cases `j = 300, 302, …, 598` are one finite statement checked by the kernel
   (`decide +kernel`, GMP arithmetic, binomials via the factorial formula).  The checker
   verifies its own floor witness, so no specification of the bit-length helper is needed.
5. The real inequality `harith` is obtained from the `ℕ` one by the abstract lemma `real_of_nat`.

No `sorry`, `admit`, `axiom`, `opaque`, or `native_decide`.
-/

namespace EOC
namespace ShapeUnconditional

open Finset CapacityBounds OddBlack ShapeCertificate

/-! ## 1. The barrier as an integer logarithm -/

theorem alpha_mul_ge_of_pow_le (j s : ℕ) (h : 2 ^ s ≤ 3 ^ j) : (s : ℝ) ≤ j * alpha := by
  have hcast : (2 : ℝ) ^ s ≤ (3 : ℝ) ^ j := by exact_mod_cast h
  have hl := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hcast
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at hl
  simpa [alpha] using hl

theorem barrier_eq_of_pow {j s : ℕ} (h1 : 2 ^ s ≤ 3 ^ j) (h2 : 3 ^ j < 2 ^ (s + 1)) :
    collatzBarrier 0 j = s := by
  unfold collatzBarrier
  rw [Nat.floor_eq_iff (barrier_arg_nonneg 0 j)]
  have hlo := alpha_mul_ge_of_pow_le j s h1
  have hhi := alpha_mul_lt_of_pow_lt j (s + 1) h2
  push_cast at hhi ⊢
  constructor <;> linarith

theorem barrier_eq_log (j : ℕ) : collatzBarrier 0 j = Nat.log 2 (3 ^ j) :=
  barrier_eq_of_pow (Nat.pow_log_le_self 2 (pow_pos (by norm_num) j).ne')
    (Nat.lt_pow_succ_log_self (by norm_num) _)

theorem barrier_pow_bounds (j : ℕ) :
    2 ^ collatzBarrier 0 j ≤ 3 ^ j ∧ 3 ^ j < 2 ^ (collatzBarrier 0 j + 1) := by
  rw [barrier_eq_log]
  exact ⟨Nat.pow_log_le_self 2 (pow_pos (by norm_num) j).ne',
    Nat.lt_pow_succ_log_self (by norm_num) _⟩

/-! ## 2. The `+300` barrier recurrence, in `ℕ` -/

theorem lt_of_two_pow_lt {a b : ℕ} (h : 2 ^ a < 2 ^ b) : a < b := by
  by_contra hc
  exact absurd h (not_lt.mpr (Nat.pow_le_pow_right (by norm_num) (by omega)))

theorem add_le_of_pow {A s s' u v : ℕ} (h1 : 2 ^ s ≤ A) (hk : 2 ^ u < 3 ^ v)
    (h2 : A * 3 ^ v < 2 ^ (s' + 1)) : s + u ≤ s' := by
  have h : 2 ^ (s + u) < 2 ^ (s' + 1) := by
    rw [pow_add]
    exact lt_of_le_of_lt (Nat.mul_le_mul h1 hk.le) h2
  have := lt_of_two_pow_lt h
  omega

theorem lt_add_of_pow {A s s' u v : ℕ} (h1 : 2 ^ s' ≤ A * 3 ^ v) (hA : A < 2 ^ (s + 1))
    (hk : 3 ^ v < 2 ^ u) : s' < s + 1 + u := by
  have h : 2 ^ s' < 2 ^ (s + 1 + u) := by
    rw [pow_add]
    exact lt_of_le_of_lt h1 (mul_lt_mul'' hA hk (Nat.zero_le _) (Nat.zero_le _))
  exact lt_of_two_pow_lt h

theorem pow_475_lt : 2 ^ 475 < 3 ^ 300 := by decide +kernel
theorem pow_476_gt : 3 ^ 300 < 2 ^ 476 := by decide +kernel

theorem barrier_add_lower (j : ℕ) : collatzBarrier 0 j + 475 ≤ collatzBarrier 0 (j + 300) :=
  add_le_of_pow (barrier_pow_bounds j).1 pow_475_lt
    (by rw [← pow_add]; exact (barrier_pow_bounds (j + 300)).2)

theorem barrier_add_upper (j : ℕ) : collatzBarrier 0 (j + 300) ≤ collatzBarrier 0 j + 476 := by
  have h := lt_add_of_pow (by rw [← pow_add]; exact (barrier_pow_bounds (j + 300)).1)
    (barrier_pow_bounds j).2 pow_476_gt
  omega

/-- `200 σ < 317 j`, i.e. `σ < 1.585 j` (from `3^200 < 2^317`). -/
theorem barrier_lt (j : ℕ) (hj : 1 ≤ j) : 200 * collatzBarrier 0 j < 317 * j := by
  have h1 := (barrier_pow_bounds j).1
  have hk : 3 ^ 200 < 2 ^ 317 := by decide +kernel
  apply lt_of_two_pow_lt
  calc 2 ^ (200 * collatzBarrier 0 j) = (2 ^ collatzBarrier 0 j) ^ 200 := by
        rw [← pow_mul, mul_comm]
    _ ≤ (3 ^ j) ^ 200 := Nat.pow_le_pow_left h1 _
    _ = (3 ^ 200) ^ j := by rw [← pow_mul, ← pow_mul, mul_comm]
    _ < (2 ^ 317) ^ j := Nat.pow_lt_pow_left hk (by omega)
    _ = 2 ^ (317 * j) := by rw [← pow_mul, mul_comm]

/-! ## 3. Block binomial growth (Vandermonde) -/

theorem choose_mul_le_choose_add (n m k l : ℕ) :
    n.choose k * m.choose l ≤ (n + m).choose (k + l) := by
  rw [Nat.add_choose_eq]
  have hm : (k, l) ∈ antidiagonal (k + l) := by simp
  exact Finset.single_le_sum
    (fun (ij : ℕ × ℕ) (_ : ij ∈ antidiagonal (k + l)) =>
      Nat.zero_le (n.choose ij.1 * m.choose ij.2)) hm

/-- Vandermonde block product with the sums supplied as equations, so that literal targets such as
`C(190,120)` are never matched against `C(95+95,60+60)` by unfolding `Nat.choose`. -/
theorem choose_mul_le_choose_of_eq {n m k l N L : ℕ} (hN : n + m = N) (hL : k + l = L) :
    n.choose k * m.choose l ≤ N.choose L := by
  subst hN hL
  exact choose_mul_le_choose_add n m k l

theorem choose95_lower : 2 ^ 86 ≤ Nat.choose 95 60 := by
  rw [Nat.choose_eq_factorial_div_factorial (by decide)]
  decide +kernel

theorem choose94_lower : 2 ^ 85 ≤ Nat.choose 94 59 := by
  rw [Nat.choose_eq_factorial_div_factorial (by decide)]
  decide +kernel

/-- Abstract five-fold product chain (no literals, so `calc` is safe here). -/
theorem pow5_le_of_chain {c x2 x3 x4 x5 : ℕ} (h2 : c * c ≤ x2) (h3 : x2 * c ≤ x3)
    (h4 : x3 * c ≤ x4) (h5 : x4 * c ≤ x5) : c ^ 5 ≤ x5 := by
  calc c ^ 5 = (((c * c) * c) * c) * c := by ring
    _ ≤ ((x2 * c) * c) * c :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h2))
    _ ≤ (x3 * c) * c := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h3)
    _ ≤ x4 * c := Nat.mul_le_mul_right _ h4
    _ ≤ x5 := h5

/-- Abstract four-fold product chain with a different last factor. -/
theorem pow4_mul_le_of_chain {c d x2 x3 x4 x5 : ℕ} (h2 : c * c ≤ x2) (h3 : x2 * c ≤ x3)
    (h4 : x3 * c ≤ x4) (h5 : x4 * d ≤ x5) : c ^ 4 * d ≤ x5 := by
  calc c ^ 4 * d = (((c * c) * c) * c) * d := by ring
    _ ≤ ((x2 * c) * c) * d :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h2))
    _ ≤ (x3 * c) * d := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h3)
    _ ≤ x4 * d := Nat.mul_le_mul_right _ h4
    _ ≤ x5 := h5

/-- `C(95,60)^5 ≤ C(475,300)`. -/
theorem choose475_ge : Nat.choose 95 60 ^ 5 ≤ Nat.choose 475 300 :=
  pow5_le_of_chain
    (choose_mul_le_choose_of_eq (n := 95) (m := 95) (k := 60) (l := 60)
      (N := 190) (L := 120) rfl rfl)
    (choose_mul_le_choose_of_eq (n := 190) (m := 95) (k := 120) (l := 60)
      (N := 285) (L := 180) rfl rfl)
    (choose_mul_le_choose_of_eq (n := 285) (m := 95) (k := 180) (l := 60)
      (N := 380) (L := 240) rfl rfl)
    (choose_mul_le_choose_of_eq (n := 380) (m := 95) (k := 240) (l := 60)
      (N := 475) (L := 300) rfl rfl)

/-- `C(95,60)^4 · C(94,59) ≤ C(474,299)`. -/
theorem choose474_ge : Nat.choose 95 60 ^ 4 * Nat.choose 94 59 ≤ Nat.choose 474 299 :=
  pow4_mul_le_of_chain
    (choose_mul_le_choose_of_eq (n := 95) (m := 95) (k := 60) (l := 60)
      (N := 190) (L := 120) rfl rfl)
    (choose_mul_le_choose_of_eq (n := 190) (m := 95) (k := 120) (l := 60)
      (N := 285) (L := 180) rfl rfl)
    (choose_mul_le_choose_of_eq (n := 285) (m := 95) (k := 180) (l := 60)
      (N := 380) (L := 240) rfl rfl)
    (choose_mul_le_choose_of_eq (n := 380) (m := 94) (k := 240) (l := 59)
      (N := 474) (L := 299) rfl rfl)

/-- **Block constant.** `2 · 3^150 · 2^477 ≤ 2^150 · 3^93 · C(475,300)`. -/
theorem block_constant : 2 * 3 ^ 150 * 2 ^ 477 ≤ 2 ^ 150 * 3 ^ 93 * Nat.choose 475 300 := by
  have hn : 2 * 3 ^ 150 * 2 ^ 477 ≤ 2 ^ 150 * 3 ^ 93 * (2 ^ 86) ^ 5 := by decide +kernel
  exact hn.trans (Nat.mul_le_mul_left _
    ((Nat.pow_le_pow_left choose95_lower 5).trans choose475_ge))

theorem choose_step (j s s' : ℕ) (hj : 1 ≤ j) (hs1 : 1 ≤ s) (hs : s + 475 ≤ s') :
    (s - 1).choose (j - 1) * Nat.choose 475 300 ≤ (s' - 1).choose (j + 300 - 1) := by
  rw [show j + 300 - 1 = j - 1 + 300 by omega]
  exact (choose_mul_le_choose_add (s - 1) 475 (j - 1) 300).trans (Nat.choose_le_choose _ (by omega))

/-! ## 4. The arithmetic certificate and its `+300` induction -/

/-- The denominator-cleared ShapeTail certificate at scale `j`, shell `s`, rate exponent `e`:
`j · 3^(j/2) · 2^(s+e) ≤ 2^(j/2) · 3^⌊31j/100⌋ · C(s-1, j-1)`. -/
def Arith (j s e : ℕ) : Prop :=
  j * 3 ^ (j / 2) * 2 ^ (s + e) ≤ 2 ^ (j / 2) * 3 ^ (31 * j / 100) * (s - 1).choose (j - 1)

/-- The induction step with every exponent abstract (no literal powers are ever normalized). -/
theorem step_core {j j' m t s s' e e' C C' B a c d : ℕ}
    (hj : j' ≤ 2 * j) (hs : s' + e' ≤ s + e + c) (hC : C * B ≤ C')
    (hblock : 2 * 3 ^ a * 2 ^ c ≤ 2 ^ a * 3 ^ d * B)
    (ih : j * 3 ^ m * 2 ^ (s + e) ≤ 2 ^ m * 3 ^ t * C) :
    j' * 3 ^ (m + a) * 2 ^ (s' + e') ≤ 2 ^ (m + a) * 3 ^ (t + d) * C' := by
  calc j' * 3 ^ (m + a) * 2 ^ (s' + e')
      ≤ (2 * j) * 3 ^ (m + a) * 2 ^ (s + e + c) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ hj) (Nat.pow_le_pow_right (by norm_num) hs)
    _ = (j * 3 ^ m * 2 ^ (s + e)) * (2 * 3 ^ a * 2 ^ c) := by ring
    _ ≤ (2 ^ m * 3 ^ t * C) * (2 ^ a * 3 ^ d * B) := Nat.mul_le_mul ih hblock
    _ = 2 ^ (m + a) * 3 ^ (t + d) * (C * B) := by ring
    _ ≤ 2 ^ (m + a) * 3 ^ (t + d) * C' := Nat.mul_le_mul_left _ hC

/-- **The residue-independent `+300` step.**  Each block gains `≥ 11` bits
(`log₂` of `2^150 3^93 2^430 / (2 · 3^150 · 2^477)`), which pays one extra bit of rate. -/
theorem arith_step {j e : ℕ} (hj : 300 ≤ j) (h : Arith j (collatzBarrier 0 j) e) :
    Arith (j + 300) (collatzBarrier 0 (j + 300)) (e + 1) := by
  unfold Arith at h ⊢
  have hlo := barrier_add_lower j
  have hhi := barrier_add_upper j
  have hsj := le_collatzBarrier 0 j
  rw [show (j + 300) / 2 = j / 2 + 150 by omega,
    show 31 * (j + 300) / 100 = 31 * j / 100 + 93 by omega]
  exact step_core (a := 150) (c := 477) (d := 93) (by omega) (by omega)
    (choose_step j _ _ (by omega) (by omega) hlo) block_constant h

theorem arith_of_base {r : ℕ} (hbase : Arith (300 + r) (collatzBarrier 0 (300 + r)) 1) (q : ℕ) :
    Arith (300 + r + 300 * q) (collatzBarrier 0 (300 + r + 300 * q)) (q + 1) := by
  induction q with
  | zero => exact hbase
  | succ q ih =>
    have h := arith_step (by omega) ih
    rwa [show 300 + r + 300 * q + 300 = 300 + r + 300 * (q + 1) by ring] at h

/-! ## 5. Cofinal base `j = 300` (block-product constants only) -/

theorem barrier_300 : collatzBarrier 0 300 = 475 :=
  barrier_eq_of_pow (by decide +kernel) (by decide +kernel)

theorem arith_base_300 : Arith 300 (collatzBarrier 0 300) 1 := by
  unfold Arith
  rw [barrier_300, show (300 : ℕ) / 2 = 150 from rfl, show 31 * 300 / 100 = 93 from rfl,
    show (475 : ℕ) - 1 = 474 from rfl, show (300 : ℕ) - 1 = 299 from rfl]
  have hn : 300 * 3 ^ 150 * 2 ^ (475 + 1) ≤ 2 ^ 150 * 3 ^ 93 * ((2 ^ 86) ^ 4 * 2 ^ 85) := by
    decide +kernel
  exact hn.trans (Nat.mul_le_mul_left _
    ((Nat.mul_le_mul (Nat.pow_le_pow_left choose95_lower 4) choose94_lower).trans choose474_ge))

theorem arith_cofinal (q : ℕ) :
    Arith (300 * (q + 1)) (collatzBarrier 0 (300 * (q + 1))) (q + 1) := by
  have h := arith_of_base (r := 0) arith_base_300 q
  rwa [show 300 + 0 + 300 * q = 300 * (q + 1) by ring] at h

/-! ## 6. All even bases `300 ≤ j < 600`: one kernel-checked finite statement -/

/-- Bit length with fuel (only used to *propose* the floor; `checkAt` verifies it). -/
def bitLen : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, n => if n = 0 then 0 else bitLen f (n / 2) + 1

/-- Checks `j ≤ s`, `2^s ≤ 3^j < 2^(s+1)` and the certificate at rate exponent `1`, with the
binomial written by the factorial formula. -/
def checkAt (j s : ℕ) : Bool :=
  decide (1 ≤ j) && decide (j ≤ s) && decide (2 ^ s ≤ 3 ^ j) && decide (3 ^ j < 2 ^ (s + 1)) &&
  decide (j * 3 ^ (j / 2) * 2 ^ (s + 1) ≤
    2 ^ (j / 2) * 3 ^ (31 * j / 100) *
      ((s - 1).factorial / ((j - 1).factorial * (s - j).factorial)))

def baseOK (j : ℕ) : Bool := checkAt j (bitLen (2 * j + 2) (3 ^ j) - 1)

theorem arith_of_checkAt {j s : ℕ} (h : checkAt j s = true) : Arith j (collatzBarrier 0 j) 1 := by
  simp only [checkAt, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hj1, hjs⟩, h1⟩, h2⟩, h3⟩ := h
  rw [barrier_eq_of_pow h1 h2]
  unfold Arith
  rwa [Nat.choose_eq_factorial_div_factorial (by omega), show s - 1 - (j - 1) = s - j by omega]

theorem arith_of_baseOK {j : ℕ} (h : baseOK j = true) : Arith j (collatzBarrier 0 j) 1 :=
  arith_of_checkAt h

set_option maxRecDepth 100000 in
/-- **The 150 even base certificates**, `j = 300, 302, …, 598`, checked by the kernel. -/
theorem bases_ok : ∀ i < 150, baseOK (300 + 2 * i) = true := by decide +kernel

theorem arith_allEven {j : ℕ} (hj : 300 ≤ j) (hev : 2 ∣ j) :
    Arith j (collatzBarrier 0 j) (j / 300) := by
  obtain ⟨i, hi, q, rfl⟩ : ∃ i < 150, ∃ q, j = 300 + 2 * i + 300 * q :=
    ⟨j % 300 / 2, by omega, j / 300 - 1, by omega⟩
  have h := arith_of_base (arith_of_baseOK (bases_ok i hi)) q
  rwa [show (300 + 2 * i + 300 * q) / 300 = q + 1 by omega]

/-! ## 7. Side conditions and the real-valued certificate -/

theorem budget (j : ℕ) (hj : 300 ≤ j) :
    j / 25 + 31 * j / 100 + collatzBarrier 0 j / (10 + 2) ≤ j / 2 := by
  have := barrier_lt j (by omega)
  omega

/-- Clearing denominators, with all quantities abstract. -/
theorem real_of_nat {j m s e t C : ℕ} (h : j * 3 ^ m * 2 ^ (s + e) ≤ 2 ^ m * 3 ^ t * C) :
    (j : ℝ) * ((3 / 2 : ℝ) ^ m * (2 : ℝ) ^ s) ≤ ((2 : ℝ) ^ e)⁻¹ * 3 ^ t * (C : ℝ) := by
  have hr : (j : ℝ) * 3 ^ m * 2 ^ (s + e) ≤ 2 ^ m * 3 ^ t * C := by exact_mod_cast h
  have hpos : (0 : ℝ) < 2 ^ m * 2 ^ e := by positivity
  have e1 : (j : ℝ) * ((3 / 2 : ℝ) ^ m * (2 : ℝ) ^ s)
      = ((j : ℝ) * 3 ^ m * 2 ^ (s + e)) / (2 ^ m * 2 ^ e) := by
    rw [div_pow, pow_add]
    field_simp
  have e2 : ((2 : ℝ) ^ e)⁻¹ * 3 ^ t * (C : ℝ) = (2 ^ m * 3 ^ t * C) / (2 ^ m * 2 ^ e) := by
    field_simp
  rw [e1, e2]
  exact div_le_div_of_nonneg_right hr hpos.le

/-- ShapeTail from the certificate at any rate exponent `e`, all other hypotheses discharged. -/
theorem shapeTail_of_Arith {j e : ℕ} (hj : 300 ≤ j) (hev : 2 ∣ j)
    (h : Arith j (collatzBarrier 0 j) e) :
    ShapeTail (collatzBarrier 0) j (collatzBarrier 0 j) 10 (j / 25) ((2 : ℝ) ^ e)⁻¹ := by
  unfold Arith at h
  exact shapeTail_of_arith (collatzBarrier 0) (t := 0) (T := 31 * j / 100)
    (by omega) (by positivity) (by omega) (collatz_chord 0 (by omega))
    (le_collatzBarrier 0 j) le_rfl (budget j hj) (real_of_nat h)

/-! ## 8. Main theorems -/

/-- **Cofinal unconditional ShapeTail.** `j₀ = 300(q+1)`, `σ = ⌊j₀ log₂ 3⌋`, `N₀ = 10`,
`K = 12(q+1)`, `ρ₁ = 2^{-(q+1)}` (with `T = 93(q+1)` in the certificate). -/
theorem shapeTail_cofinal (q : ℕ) :
    ShapeTail (collatzBarrier 0) (300 * (q + 1)) (collatzBarrier 0 (300 * (q + 1))) 10
      (12 * (q + 1)) ((2 : ℝ) ^ (q + 1))⁻¹ := by
  have h := shapeTail_of_Arith (by omega) (by omega) (arith_cofinal q)
  rwa [show 300 * (q + 1) / 25 = 12 * (q + 1) by omega] at h

/-- **All-even unconditional ShapeTail.** For every even `j₀ ≥ 300`: `σ = ⌊j₀ log₂ 3⌋`,
`N₀ = 10`, `K = ⌊j₀/25⌋`, `ρ₁ = 2^{-⌊j₀/300⌋}` (with `T = ⌊31 j₀/100⌋` in the certificate). -/
theorem shapeTail_allEven {j : ℕ} (hj : 300 ≤ j) (hev : 2 ∣ j) :
    ShapeTail (collatzBarrier 0) j (collatzBarrier 0 j) 10 (j / 25) ((2 : ℝ) ^ (j / 300))⁻¹ :=
  shapeTail_of_Arith hj hev (arith_allEven hj hev)

theorem rho_le_rate (j : ℕ) : ((2 : ℝ) ^ (j / 300))⁻¹ ≤ 2 * (2 : ℝ) ^ (-(j : ℝ) / 300) := by
  have hn : (j : ℝ) < 300 * ((j / 300 : ℕ) : ℝ) + 300 := by
    have : j < 300 * (j / 300) + 300 := by omega
    exact_mod_cast this
  rw [← Real.rpow_natCast, ← Real.rpow_neg (by norm_num)]
  calc (2 : ℝ) ^ (-((j / 300 : ℕ) : ℝ)) ≤ (2 : ℝ) ^ (1 + -(j : ℝ) / 300) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = 2 * (2 : ℝ) ^ (-(j : ℝ) / 300) := by
        rw [Real.rpow_add (by norm_num), Real.rpow_one]

/-- **All-even ShapeTail with an explicit exponential rate** `ρ₁ ≤ 2 · 2^{-j₀/300}`. -/
theorem shapeTail_allEven_rate :
    ∀ j : ℕ, 300 ≤ j → 2 ∣ j →
      ∃ ρ₁ : ℝ, ρ₁ ≤ 2 * (2 : ℝ) ^ (-(j : ℝ) / 300) ∧
        ShapeTail (collatzBarrier 0) j (collatzBarrier 0 j) 10 (j / 25) ρ₁ :=
  fun j hj hev => ⟨_, rho_le_rate j, shapeTail_allEven hj hev⟩

end ShapeUnconditional
end EOC
