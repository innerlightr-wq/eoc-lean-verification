import EOC.TriangleHop
import EOC.BlockCubeInstance
import EOC.PsiSieve

/-!
# White-cell contraction for the pair-block factor, and the critical white-count interface

The pair-block factor of `BlockCubeInstance.blockCubeHyp_pair` is
`W λ c r = ‖∑_{x ∈ B} e(φ_{2r+1}(x))‖ / |B|`, `B = pairB b c r` (the admissible internal prefix sums
of pair-block `r`), `φ_i(x) = collatzPhase λ m (uInv m) i x`.

* **Local contraction** (`wfac_le_of_pair`, `pair_factor_le_of_good`): if `x, x+1 ∈ B` and the phase
  difference `φ(x) − φ(x+1)` is at distance `≥ d` from `ℤ` (`0 ≤ d ≤ 1/2`), then
  `W ≤ 1 − 2(1 − cos(π d))/|B|`; for `|B| ≤ N₀` this is `≤ κ(d, N₀) = 1 − 2(1 − cos(π d))/N₀ < 1`.
  (Tao's white-point cancellation `|f(x,3)| = cos(πθ)` is the case `|B| = 2`.)
* **Phase identification** (`collatzPhase_sub_succ`, `phase_reciprocity`, `distZ_phase_ge`): the
  phase difference is `λ u_i 2^x / 2^m ≡ −λ·y(m−x, i+1)/3^{i+1} + λ 2^x/(2^m 3^{i+1})` (mod 1),
  i.e. minus `λ` times Tao's cell value `U(m − x, i + 1)` up to a tiny correction; at `λ = 1` a
  Tao-white cell (`¬ black`) gives distance `≥ η − 2^x/(2^m 3^{i+1})` (`distZ_phase_ge_of_white`),
  and `goodPair_of_white_step` turns a white odd step of a confined word into a good pair block.
* **Interface** (`GoodPair`, `CriticalWhiteCount`, `lowFreqDecay_of_criticalWhiteCount`,
  `weightedFourier_of_criticalWhiteCount`): a lower-tail bound on the number of good pair blocks
  (weighted by class size, i.e. uniformly over the confined prefix shell) gives `LowFreqDecay` and
  `WeightedFourier` with the exact pair-block factor.  `CriticalWhiteCount` itself is NOT proved.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace WhiteContraction

open Finset TriangleArray MaxTriangle SwapBound ShellDecomposition PrefixCollision Real

noncomputable section

/-! ## 1. Distance to the nearest integer -/

/-- Distance of `t` to the nearest integer. -/
def distZ (t : ℝ) : ℝ := |t - round t|

theorem distZ_nonneg (t : ℝ) : 0 ≤ distZ t := abs_nonneg _

theorem distZ_le (t : ℝ) (z : ℤ) : distZ t ≤ |t - z| := round_le t z

theorem distZ_le_half (t : ℝ) : distZ t ≤ 1 / 2 := abs_sub_round t

theorem distZ_add_int (t : ℝ) (z : ℤ) : distZ (t + z) = distZ t := by
  unfold distZ; rw [round_add_intCast]; push_cast; ring_nf

theorem distZ_neg (t : ℝ) : distZ (-t) = distZ t := by
  apply le_antisymm
  · calc distZ (-t) ≤ |-t - ((-round t : ℤ) : ℝ)| := distZ_le _ _
      _ = distZ t := by unfold distZ; push_cast; rw [← abs_neg]; ring_nf
  · calc distZ t ≤ |t - ((-round (-t) : ℤ) : ℝ)| := distZ_le _ _
      _ = distZ (-t) := by unfold distZ; push_cast; rw [← abs_neg]; ring_nf

/-- `distZ` is 1-Lipschitz. -/
theorem distZ_le_add (t s : ℝ) : distZ t ≤ distZ s + |t - s| := by
  calc distZ t ≤ |t - (round s : ℝ)| := distZ_le t (round s)
    _ = |(t - s) + (s - round s)| := by ring_nf
    _ ≤ |t - s| + |s - round s| := abs_add_le _ _
    _ = distZ s + |t - s| := by unfold distZ; ring

theorem distZ_eq_abs {t : ℝ} (ht : |t| ≤ 1 / 2) : distZ t = |t| := by
  apply le_antisymm
  · simpa using distZ_le t 0
  · unfold distZ
    by_cases h0 : round t = 0
    · rw [h0]; simp
    · have h1 : (1 : ℝ) ≤ |((round t : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs h0
      have h2 : |((round t : ℤ) : ℝ)| ≤ |t - round t| + |t| := by
        calc |((round t : ℤ) : ℝ)| = |-(t - round t) + t| := by ring_nf
          _ ≤ |-(t - round t)| + |t| := abs_add_le _ _
          _ = |t - round t| + |t| := by rw [abs_neg]
      linarith

/-- `|cos(π t)| ≤ cos(π d)` when `t` is at distance `≥ d` from `ℤ` (`d ≥ 0`). -/
theorem abs_cos_pi_le {t d : ℝ} (hd0 : 0 ≤ d) (hdt : d ≤ distZ t) :
    |Real.cos (π * t)| ≤ Real.cos (π * d) := by
  set s := t - round t with hs
  have hsabs : |s| = distZ t := rfl
  have hs2 : |s| ≤ 1 / 2 := distZ_le_half t
  have hcos : Real.cos (π * t) = (-1) ^ (round t) * Real.cos (π * s) := by
    rw [← Real.cos_add_int_mul_pi]; congr 1; rw [hs]; ring
  have hpi := Real.pi_pos
  have heven : Real.cos (π * s) = Real.cos (π * |s|) := by
    rcases abs_choice s with h | h <;> rw [h]
    rw [mul_neg, Real.cos_neg]
  have hnn : 0 ≤ Real.cos (π * |s|) := by
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    · nlinarith [abs_nonneg s]
    · nlinarith
  have hpow : |((-1 : ℝ) ^ (round t))| = 1 := by rw [abs_zpow, abs_neg, abs_one, one_zpow]
  rw [hcos, abs_mul, hpow, one_mul, heven, abs_of_nonneg hnn]
  apply Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by nlinarith)
  rw [hsabs]; exact mul_le_mul_of_nonneg_left hdt hpi.le

/-- Two consecutive terms: `‖e(a) + e(b)‖ ≤ 2 cos(π d)` if `distZ (a − b) ≥ d ≥ 0`. -/
theorem norm_ee_add_ee_le {a b d : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ distZ (a - b)) :
    ‖ee a + ee b‖ ≤ 2 * Real.cos (π * d) := by
  rw [norm_ee_add_ee]
  have := abs_cos_pi_le hd0 hd
  linarith

/-! ## 2. The block factor bound -/

theorem norm_sum_le_pair (B : Finset ℕ) (φ : ℕ → ℝ) {x : ℕ} (hx : x ∈ B) (hx1 : x + 1 ∈ B) :
    ‖∑ z ∈ B, ee (φ z)‖ ≤ ((B.card : ℕ) : ℝ) - 2 + ‖ee (φ x) + ee (φ (x + 1))‖ := by
  have hx1' : x + 1 ∈ B.erase x := mem_erase.mpr ⟨by omega, hx1⟩
  have hsplit : ∑ z ∈ B, ee (φ z) =
      (ee (φ x) + ee (φ (x + 1))) + ∑ z ∈ (B.erase x).erase (x + 1), ee (φ z) := by
    rw [← add_sum_erase B _ hx, ← add_sum_erase (B.erase x) _ hx1', add_assoc]
  have hcard : (((B.erase x).erase (x + 1)).card : ℝ) = (B.card : ℝ) - 2 := by
    rw [card_erase_of_mem hx1', card_erase_of_mem hx]
    have h2 : 2 ≤ B.card := by
      have : ({x, x + 1} : Finset ℕ) ⊆ B := by
        intro z hz; simp only [mem_insert, mem_singleton] at hz
        rcases hz with rfl | rfl <;> assumption
      have := card_le_card this
      rw [card_pair (by omega)] at this; exact this
    push_cast [Nat.sub_sub, show 1 + 1 = 2 from rfl]
    rw [Nat.cast_sub h2]; push_cast; ring
  have hrest : ‖∑ z ∈ (B.erase x).erase (x + 1), ee (φ z)‖ ≤
      (((B.erase x).erase (x + 1)).card : ℝ) := by
    calc ‖∑ z ∈ (B.erase x).erase (x + 1), ee (φ z)‖
        ≤ ∑ z ∈ (B.erase x).erase (x + 1), ‖ee (φ z)‖ := norm_sum_le _ _
      _ = _ := by simp [norm_ee]
  rw [hsplit]
  calc ‖(ee (φ x) + ee (φ (x + 1))) + ∑ z ∈ (B.erase x).erase (x + 1), ee (φ z)‖
      ≤ ‖ee (φ x) + ee (φ (x + 1))‖ + ‖∑ z ∈ (B.erase x).erase (x + 1), ee (φ z)‖ :=
        norm_add_le _ _
    _ ≤ _ := by rw [hcard] at hrest; linarith

/-- **Block-factor contraction.** `x, x+1 ∈ B`, `distZ (φ x − φ (x+1)) ≥ d ≥ 0` ⇒
`‖∑_B e(φ)‖/|B| ≤ 1 − 2(1 − cos(π d))/|B|`. -/
theorem wfac_le_of_pair {B : Finset ℕ} {φ : ℕ → ℝ} {x : ℕ} (hx : x ∈ B) (hx1 : x + 1 ∈ B)
    {d : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ distZ (φ x - φ (x + 1))) :
    ‖∑ z ∈ B, ee (φ z)‖ / (B.card : ℝ) ≤ 1 - 2 * (1 - Real.cos (π * d)) / (B.card : ℝ) := by
  have hpos : (0 : ℝ) < B.card := Nat.cast_pos.mpr (card_pos.mpr ⟨x, hx⟩)
  have h1 := norm_sum_le_pair B φ hx hx1
  have h2 := norm_ee_add_ee_le hd0 hd
  rw [div_le_iff₀ hpos, sub_mul, div_mul_cancel₀ _ hpos.ne', one_mul]
  linarith

/-- The explicit contraction constant `κ(d, N₀) = 1 − 2(1 − cos(π d))/N₀`. -/
def kappa (d : ℝ) (N0 : ℕ) : ℝ := 1 - 2 * (1 - Real.cos (π * d)) / N0

theorem kappa_le_one (d : ℝ) (N0 : ℕ) : kappa d N0 ≤ 1 := by
  unfold kappa
  have : 0 ≤ 2 * (1 - Real.cos (π * d)) / (N0 : ℝ) := by
    have := Real.cos_le_one (π * d); positivity
  linarith

theorem kappa_nonneg {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1 / 2) {N0 : ℕ} (hN : 2 ≤ N0) :
    0 ≤ kappa d N0 := by
  unfold kappa
  have hpi := Real.pi_pos
  have hN' : (2 : ℝ) ≤ N0 := by exact_mod_cast hN
  have hc : 0 ≤ Real.cos (π * d) :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by nlinarith) (by nlinarith)
  have : 2 * (1 - Real.cos (π * d)) / (N0 : ℝ) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  linarith

theorem kappa_lt_one {d : ℝ} (hd0 : 0 < d) (hd1 : d ≤ 1 / 2) {N0 : ℕ} (hN : 1 ≤ N0) :
    kappa d N0 < 1 := by
  unfold kappa
  have hpi := Real.pi_pos
  have hc : Real.cos (π * d) < 1 := by
    have : Real.cos (π * d) < Real.cos 0 :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) (by nlinarith) (by positivity)
    rwa [Real.cos_zero] at this
  have hN' : (0 : ℝ) < N0 := by exact_mod_cast hN
  have : 0 < 2 * (1 - Real.cos (π * d)) / (N0 : ℝ) := by
    apply div_pos _ hN'; linarith
  linarith

/-- `‖∑_B e(φ)‖ / |B| ∈ [0, 1]`. -/
theorem wfac_mem_unit (B : Finset ℕ) (φ : ℕ → ℝ) :
    0 ≤ ‖∑ z ∈ B, ee (φ z)‖ / (B.card : ℝ) ∧ ‖∑ z ∈ B, ee (φ z)‖ / (B.card : ℝ) ≤ 1 := by
  refine ⟨by positivity, ?_⟩
  rcases B.eq_empty_or_nonempty with h | h
  · subst h; simp
  · have hpos : (0 : ℝ) < B.card := Nat.cast_pos.mpr (card_pos.mpr h)
    rw [div_le_one hpos]
    calc ‖∑ z ∈ B, ee (φ z)‖ ≤ ∑ z ∈ B, ‖ee (φ z)‖ := norm_sum_le _ _
      _ = B.card := by simp [norm_ee]

/-! ## 3. Phase identification with Tao cells -/

/-- The pair-block phase at internal prefix sum `x`. -/
def pairPhase (lam m i x : ℕ) : ℝ := SwapCollatz.collatzPhase lam m (WeightedChain.uInv m) i x

/-- Consecutive phases differ by `λ u_i 2^x / 2^m` modulo `ℤ`. -/
theorem collatzPhase_sub_succ (h m : ℕ) (u : ℕ → ℕ) (i x : ℕ) :
    ∃ z : ℤ, SwapCollatz.collatzPhase h m u i x - SwapCollatz.collatzPhase h m u i (x + 1) =
      ((h * u i * 2 ^ x : ℕ) : ℝ) / 2 ^ m + z := by
  unfold SwapCollatz.collatzPhase
  set A : ℝ := ((h * u i * 2 ^ x : ℕ) : ℝ) / 2 ^ m
  have hA2 : ((h * u i * 2 ^ (x + 1) : ℕ) : ℝ) / 2 ^ m = 2 * A := by
    simp only [A]; push_cast; ring
  rw [hA2]
  refine ⟨⌊A⌋ - ⌊2 * A⌋, ?_⟩
  unfold Int.fract; push_cast; ring

/-- **Reciprocity at a cell.**  For `x ≤ m`:
`λ u_i 2^x/2^m + λ y(m−x, i+1)/3^{i+1} − λ 2^x/(2^m 3^{i+1}) ∈ ℤ`. -/
theorem phase_reciprocity (lam m i x : ℕ) (hx : x ≤ m) :
    ∃ z : ℤ, ((lam * WeightedChain.uInv m i * 2 ^ x : ℕ) : ℝ) / 2 ^ m +
        (lam : ℝ) * (y (m - x) (i + 1) : ℝ) / 3 ^ (i + 1) -
        (lam : ℝ) * 2 ^ x / (2 ^ m * 3 ^ (i + 1)) = z := by
  set u : ℤ := (WeightedChain.uInv m i : ℤ)
  set k := i + 1
  set yy : ℤ := y (m - x) k
  have hu : u * 3 ^ k ≡ 1 [ZMOD 2 ^ m] := PsiSieve.uInv_modEq m i
  have hy : (3 : ℤ) ^ k ∣ 2 ^ (m - x) * yy - 1 := three_pow_dvd (m - x) k
  have hm : (2 : ℤ) ^ m = 2 ^ x * 2 ^ (m - x) := by rw [← pow_add]; congr 1; omega
  set N : ℤ := u * 2 ^ x * 3 ^ k + yy * 2 ^ m - 2 ^ x
  have h2 : (2 : ℤ) ^ m ∣ N := by
    have e : N = 2 ^ x * (u * 3 ^ k - 1) + 2 ^ m * yy := by simp only [N]; ring
    rw [e]
    have hd : (2 : ℤ) ^ m ∣ u * 3 ^ k - 1 := hu.symm.dvd
    exact dvd_add (Dvd.dvd.mul_left hd _) (dvd_mul_right _ _)
  have h3 : (3 : ℤ) ^ k ∣ N := by
    have e : N = 2 ^ x * (2 ^ (m - x) * yy - 1) + 3 ^ k * (u * 2 ^ x) := by
      simp only [N]; rw [hm]; ring
    rw [e]; exact dvd_add (Dvd.dvd.mul_left hy _) (dvd_mul_right _ _)
  have hcop : IsCoprime ((2 : ℤ) ^ m) ((3 : ℤ) ^ k) :=
    IsCoprime.pow (by norm_num [Int.isCoprime_iff_gcd_eq_one])
  obtain ⟨z, hz⟩ := hcop.mul_dvd h2 h3
  refine ⟨lam * z, ?_⟩
  have hN : (N : ℝ) = (2 ^ m * 3 ^ k : ℝ) * z := by exact_mod_cast hz
  have hNexp : (N : ℝ) = (u : ℝ) * 2 ^ x * 3 ^ k + (yy : ℝ) * 2 ^ m - 2 ^ x := by
    simp only [N]; push_cast; ring
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  have h3k : (0 : ℝ) < 3 ^ k := by positivity
  have key : (u : ℝ) * 2 ^ x / 2 ^ m + (yy : ℝ) / 3 ^ k - 2 ^ x / (2 ^ m * 3 ^ k) = z := by
    have : (u : ℝ) * 2 ^ x / 2 ^ m + (yy : ℝ) / 3 ^ k - 2 ^ x / (2 ^ m * 3 ^ k) =
        (N : ℝ) / (2 ^ m * 3 ^ k) := by
      rw [hNexp]; field_simp
    rw [this, hN]; field_simp
  have hucast :
      ((lam * WeightedChain.uInv m i * 2 ^ x : ℕ) : ℝ) = (lam : ℝ) * ((u : ℝ) * 2 ^ x) := by
    simp only [u]; push_cast; ring
  rw [hucast]
  push_cast
  calc (lam : ℝ) * ((u : ℝ) * 2 ^ x) / 2 ^ m + (lam : ℝ) * (yy : ℝ) / 3 ^ k -
        (lam : ℝ) * 2 ^ x / (2 ^ m * 3 ^ k)
      = (lam : ℝ) * ((u : ℝ) * 2 ^ x / 2 ^ m + (yy : ℝ) / 3 ^ k - 2 ^ x / (2 ^ m * 3 ^ k)) := by
        ring
    _ = (lam : ℝ) * z := by rw [key]

/-- **Phase difference vs. Tao cell.**  For `x ≤ m`:
`distZ(φ(x) − φ(x+1)) ≥ distZ(λ y(m−x, i+1)/3^{i+1}) − λ 2^x/(2^m 3^{i+1})`. -/
theorem distZ_phase_ge (lam m i x : ℕ) (hx : x ≤ m) :
    distZ ((lam : ℝ) * (y (m - x) (i + 1) : ℝ) / 3 ^ (i + 1)) -
        (lam : ℝ) * 2 ^ x / (2 ^ m * 3 ^ (i + 1)) ≤
      distZ (pairPhase lam m i x - pairPhase lam m i (x + 1)) := by
  obtain ⟨z1, hz1⟩ := collatzPhase_sub_succ lam m (WeightedChain.uInv m) i x
  obtain ⟨z2, hz2⟩ := phase_reciprocity lam m i x hx
  set T : ℝ := (lam : ℝ) * (y (m - x) (i + 1) : ℝ) / 3 ^ (i + 1)
  set ε : ℝ := (lam : ℝ) * 2 ^ x / (2 ^ m * 3 ^ (i + 1))
  have hε : 0 ≤ ε := by positivity
  have hdiff :
      pairPhase lam m i x - pairPhase lam m i (x + 1) = (-T + ε) + ((z1 + z2 : ℤ) : ℝ) := by
    unfold pairPhase; rw [hz1]; push_cast at hz2 ⊢; linarith
  rw [hdiff, distZ_add_int]
  have := distZ_le_add T (T - ε)
  have h2 : distZ (T - ε) = distZ (-T + ε) := by rw [← distZ_neg]; ring_nf
  rw [h2] at this
  have h3 : |T - (T - ε)| = ε := by rw [sub_sub_cancel, abs_of_nonneg hε]
  linarith

/-- **At `λ = 1`: a Tao-white cell gives a large phase difference.**  If `(m − x, i+1)` is not black
at threshold `η` then `distZ(φ(x) − φ(x+1)) ≥ η − 2^x/(2^m 3^{i+1})`. -/
theorem distZ_phase_ge_of_white {m i x : ℕ} (hx : x ≤ m) {η : ℝ}
    (hwhite : ¬ black (m - x) (i + 1) η) :
    η - 2 ^ x / (2 ^ m * 3 ^ (i + 1)) ≤ distZ (pairPhase 1 m i x - pairPhase 1 m i (x + 1)) := by
  have h := distZ_phase_ge 1 m i x hx
  have hy2 : 2 * |y (m - x) (i + 1)| ≤ 3 ^ (i + 1) := two_abs_y_le (m - x) (i + 1)
  have h3 : (0 : ℝ) < 3 ^ (i + 1) := by positivity
  have habs : |(y (m - x) (i + 1) : ℝ) / 3 ^ (i + 1)| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos h3, div_le_iff₀ h3]
    have : (2 : ℝ) * |(y (m - x) (i + 1) : ℝ)| ≤ 3 ^ (i + 1) := by exact_mod_cast hy2
    linarith
  have hd : distZ ((y (m - x) (i + 1) : ℝ) / 3 ^ (i + 1)) =
      |(y (m - x) (i + 1) : ℝ)| / 3 ^ (i + 1) := by
    rw [distZ_eq_abs habs, abs_div, abs_of_pos h3]
  unfold black at hwhite
  push Not at hwhite
  have hw : η ≤ |(y (m - x) (i + 1) : ℝ)| / 3 ^ (i + 1) := by rw [le_div_iff₀ h3]; exact hwhite
  simp only [Nat.cast_one, one_mul] at h
  rw [hd] at h
  linarith

/-! ## 4. Good pair blocks and the critical white-count interface -/

variable (b : ℕ → ℕ)

/-- Pair block `r` of class `c` is **good** at frequency `λ` (parameters `m`, `N₀`, `d`): the block
has at most `N₀` internal choices and contains consecutive choices `x, x+1` whose phase difference
is at distance `≥ d` from `ℤ`. -/
def GoodPair (m N0 : ℕ) (d : ℝ) (lam : ℕ) {j0 : ℕ} (c : Fin (j0 + 1) → ℕ) (r : ℕ) : Prop :=
  (BlockCubeInstance.pairB b c r).card ≤ N0 ∧
    ∃ x, x ∈ BlockCubeInstance.pairB b c r ∧ x + 1 ∈ BlockCubeInstance.pairB b c r ∧
      d ≤ distZ (pairPhase lam m (2 * r + 1) x - pairPhase lam m (2 * r + 1) (x + 1))

/-- **White-cell contraction for the actual pair-block factor.** -/
theorem pair_factor_le_of_good {m N0 : ℕ} {d : ℝ} (hd0 : 0 ≤ d) {lam j0 : ℕ}
    {c : Fin (j0 + 1) → ℕ} {r : ℕ} (hg : GoodPair b m N0 d lam c r) :
    BlockCubeInstance.Wfac (BlockCubeInstance.pairB b)
        (fun _ r x => SwapCollatz.collatzPhase lam m (WeightedChain.uInv m) (2 * r + 1) x) c r ≤
      kappa d N0 := by
  obtain ⟨hN, x, hx, hx1, hdist⟩ := hg
  unfold BlockCubeInstance.Wfac
  have h := wfac_le_of_pair (φ := fun z => pairPhase lam m (2 * r + 1) z) hx hx1 hd0 hdist
  have hcardpos : (0 : ℝ) < (BlockCubeInstance.pairB b c r).card :=
    Nat.cast_pos.mpr (card_pos.mpr ⟨x, hx⟩)
  have hN' : ((BlockCubeInstance.pairB b c r).card : ℝ) ≤ N0 := by exact_mod_cast hN
  have hnn : 0 ≤ 2 * (1 - Real.cos (π * d)) := by linarith [Real.cos_le_one (π * d)]
  have hmono : 2 * (1 - Real.cos (π * d)) / (N0 : ℝ) ≤
      2 * (1 - Real.cos (π * d)) / ((BlockCubeInstance.pairB b c r).card : ℝ) :=
    div_le_div_of_nonneg_left hnn hcardpos hN'
  unfold kappa
  simp only [pairPhase] at h
  linarith

theorem prefixSum_le_prefixSum {N : ℕ} (w : FiniteValuationWord N) {j : ℕ} :
    ∀ k, j ≤ k → k ≤ N → w.prefixSum j ≤ w.prefixSum k := by
  intro k
  induction k with
  | zero => intro h _; rw [Nat.le_zero.mp h]
  | succ k ih =>
    intro hjk hkN
    rcases Nat.eq_or_lt_of_le hjk with h | h
    · rw [h]
    · have := ih (by omega) (by omega)
      rw [BlockCubeInstance.prefixSum_succ' w (by omega)]
      omega

/-- **Bridge from the path's own Tao cell to a good pair block (`λ = 1`).**  For a confined prefix
word `P` (total `σ`, `m = σ + 1 + t`), pair block `r`: if the word's cell at odd step `2r+1`,
namely `(m − S_{2r+1}, 2r+2)`, is Tao-white at threshold `η`, the next internal choice
`S_{2r+1} + 1` is admissible, the block has at most `N₀` choices, and the correction
`2^{S_{2r+1}}/(2^m 3^{2r+2}) ≤ η/2`, then the block of `P`'s class is good with `d = η/2`. -/
theorem goodPair_of_white_step {j0 σ t N0 : ℕ} (hj : 1 ≤ j0) {P : FiniteValuationWord j0}
    (hP : P ∈ shellP b j0 σ) {r : ℕ} (hr : r < j0 / 2) {η : ℝ}
    (hcard : (BlockCubeInstance.pairB b (BlockCubeInstance.pairκ j0 P) r).card ≤ N0)
    (hnext :
      P.prefixSum (2 * r + 1) + 1 ∈ BlockCubeInstance.pairB b (BlockCubeInstance.pairκ j0 P) r)
    (hwhite : ¬ black (σ + 1 + t - P.prefixSum (2 * r + 1)) (2 * r + 2) η)
    (hsmall : (2 : ℝ) ^ (P.prefixSum (2 * r + 1)) / (2 ^ (σ + 1 + t) * 3 ^ (2 * r + 2)) ≤ η / 2) :
    GoodPair b (σ + 1 + t) N0 (η / 2) 1 (BlockCubeInstance.pairκ j0 P) r := by
  have hmem :
      P.prefixSum (2 * r + 1) ∈ BlockCubeInstance.pairB b (BlockCubeInstance.pairκ j0 P) r := by
    have := Fintype.mem_piFinset.mp (BlockCubeInstance.pairπ_mem b hj hP) ⟨r, hr⟩
    simpa [BlockCubeInstance.pairπ] using this
  have htot : P.total = σ := ((BlockCubeInstance.mem_shellP_iff b hj).mp hP).2.2
  have hxm : P.prefixSum (2 * r + 1) ≤ σ + 1 + t := by
    have h1 := prefixSum_le_prefixSum P (j := 2 * r + 1) j0 (by omega) le_rfl
    rw [FiniteValuationWord.total] at htot
    omega
  refine ⟨hcard, P.prefixSum (2 * r + 1), hmem, hnext, ?_⟩
  have h := distZ_phase_ge_of_white (m := σ + 1 + t) (i := 2 * r + 1) hxm hwhite
  have e : 2 * r + 1 + 1 = 2 * r + 2 := by omega
  rw [e] at h
  linarith

open Classical in
/-- **`CriticalWhiteCount`** (analytic hypothesis, NOT proved): for every low frequency, the
confined prefix shell (classes weighted by size) has at most a `ρ` fraction with fewer than `k` good
pair blocks. -/
def CriticalWhiteCount (j0 σ t U N0 : ℕ) (d : ℝ) (k : ℕ) (ρ : ℝ) : Prop :=
  ∀ u ≤ U, ∀ lam ∈ cshell (σ + 1) t u,
    ∑ c ∈ ((shellP b j0 σ).image (BlockCubeInstance.pairκ j0)).filter
        (fun c => ((range (j0 / 2)).filter (GoodPair b (σ + 1 + t) N0 d lam c)).card < k),
      BlockCubeInstance.nCls (shellP b j0 σ) (BlockCubeInstance.pairκ j0) c ≤
    ρ * ∑ c ∈ (shellP b j0 σ).image (BlockCubeInstance.pairκ j0),
      BlockCubeInstance.nCls (shellP b j0 σ) (BlockCubeInstance.pairκ j0) c

/-- The class-weighted bad mass is the number of confined prefix words with few good blocks. -/
theorem sum_nCls_filter_eq_card {ι β : Type*} [DecidableEq β] (T : Finset ι) (κ : ι → β)
    (p : β → Prop) [DecidablePred p] :
    ∑ c ∈ (T.image κ).filter p, BlockCubeInstance.nCls T κ c =
      ((T.filter (fun i => p (κ i))).card : ℝ) := by
  unfold BlockCubeInstance.nCls
  rw [← Nat.cast_sum]
  congr 1
  rw [card_eq_sum_card_fiberwise (f := κ) (t := (T.image κ).filter p)]
  · refine sum_congr rfl fun c hc => ?_
    rw [filter_filter]
    congr 1
    ext i
    simp only [mem_filter]
    constructor
    · rintro ⟨hi, hk⟩; exact ⟨hi, by rw [hk]; exact (mem_filter.mp hc).2, hk⟩
    · rintro ⟨hi, _, hk⟩; exact ⟨hi, hk⟩
  · intro i hi
    rw [mem_coe, mem_filter] at hi ⊢
    exact ⟨mem_image_of_mem κ hi.1, hi.2⟩

open Classical in
/-- **`CriticalWhiteCount ⇒ LowFreqDecay`**, with the actual pair-block factor and contraction
`κ(d, N₀)`: if `κ^{2k} + ρ ≤ C·2^{−γ j0}` then `LowFreqDecay b j0 σ t U C γ`. -/
theorem lowFreqDecay_of_criticalWhiteCount {j0 σ t U N0 k : ℕ} {d ρ C γ : ℝ} (hj : 1 ≤ j0)
    (hne : (shellP b j0 σ).Nonempty) (hd0 : 0 ≤ d) (hd1 : d ≤ 1 / 2) (hN : 2 ≤ N0)
    (hcw : CriticalWhiteCount b j0 σ t U N0 d k ρ) (hC0 : 0 ≤ C)
    (hrate : kappa d N0 ^ (2 * k) + ρ ≤ C * (2 : ℝ) ^ (-(γ * j0))) :
    DecayInterface.LowFreqDecay b j0 σ t U C γ := by
  refine GoodAngles.lowFreqDecay_of_goodAngles b j0 σ t U
    ((shellP b j0 σ).image (BlockCubeInstance.pairκ j0))
    (BlockCubeInstance.nCls (shellP b j0 σ) (BlockCubeInstance.pairκ j0))
    (fun lam => BlockCubeInstance.Wfac (BlockCubeInstance.pairB b)
      (fun _ r x => SwapCollatz.collatzPhase lam (σ + 1 + t) (WeightedChain.uInv (σ + 1 + t))
        (2 * r + 1) x))
    (fun lam c r => GoodPair b (σ + 1 + t) N0 d lam c r) (j0 / 2) k
    (kappa_nonneg hd0 hd1 hN) (kappa_le_one d N0)
    (fun c _ => by unfold BlockCubeInstance.nCls; positivity)
    (BlockCubeInstance.blockCubeHyp_pair b j0 σ t U hj hne) ?_ hC0 hrate
  intro u hu lam hlam
  refine ⟨fun c _ r => ?_, fun c _ r hg => pair_factor_le_of_good b hd0 hg, ?_⟩
  · unfold BlockCubeInstance.Wfac
    exact wfac_mem_unit _ _
  · have := hcw u hu lam hlam
    convert this using 2

/-- **`CriticalWhiteCount ⇒ WeightedFourier`** (through `LowFreqDecay` and the (C3) sieve). -/
theorem weightedFourier_of_criticalWhiteCount {N j0 s σ U N0 k : ℕ} {ε d ρ C γ : ℝ}
    (Nsplit : ℕ → ℕ) (hj : 1 ≤ j0) (hne : (shellP b j0 σ).Nonempty) (hd0 : 0 ≤ d) (hd1 : d ≤ 1 / 2)
    (hN : 2 ≤ N0)
    (hcw : CriticalWhiteCount b j0 σ (s - σ) U N0 d k ρ) (hC0 : 0 ≤ C)
    (hrate : kappa d N0 ^ (2 * k) + ρ ≤ C * (2 : ℝ) ^ (-(γ * j0)))
    (hN1 : ∀ u ∈ range (σ + 1 + (s - σ)), 1 ≤ Nsplit u)
    (hNj : ∀ u ∈ range (σ + 1 + (s - σ)), Nsplit u < j0)
    (hX : ∀ u ∈ range (σ + 1 + (s - σ)), 2 * PsiSieve.Xmax b (Nsplit u) ≤ 2 ^ (σ + 1 + (s - σ)))
    (hfin : (1 + ((σ + 1 : ℕ) : ℝ) / 2) * ∑ u ∈ range (σ + 1 + (s - σ)),
        min 1 (2 ^ (s - σ) / (2 * 2 ^ u)) *
          DecayInterface.mixedBound b j0 σ Nsplit (fun u => u ≤ U)
            (fun u => 2 ^ (u + 1) * C * (2 : ℝ) ^ (-(γ * j0)) * ((shellP b j0 σ).card : ℝ) ^ 2) u ≤
      ε ^ 2 * ((shellP b j0 σ).card : ℝ) ^ 2 * (shellV b N j0 σ (s - σ)).card / 2 ^ (s - σ)) :
    WeightedChain.WeightedFourier b N j0 s σ ε :=
  DecayInterface.weightedFourier_of_lowFreqDecay_and_sieve b N j0 s σ U ε C γ Nsplit hN1 hNj hX
    (lowFreqDecay_of_criticalWhiteCount b hj hne hd0 hd1 hN hcw hC0 hrate) hfin

end

end WhiteContraction
end EOC
