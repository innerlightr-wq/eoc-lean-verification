import EOC.ShapeUnconditional
import EOC.LogAbsorb

/-!
# Pressure is the only open input of `CriticalWhiteCount`

`OddBlack.criticalWhiteCount_of_shape_and_oddPressure` needs `ShapeTail`, `OddDarkPressure` and a
numerical compatibility condition.  `ShapeTail` is now PROVED (LEAN) for the Collatz barrier
(`EOC.ShapeUnconditional`).  This file removes it, and every other non-pressure hypothesis, from
the chain up to `LowFreqDecay`:

* `shapeTail_allEven_budget` — the unconditional ShapeTail holds for **any** `N₀` and `K` satisfying
  the block budget `K + ⌊31j/100⌋ + ⌊σ/(N₀+2)⌋ ≤ j/2`.  The arithmetic certificate does not involve
  `N₀` or `K`, so enlarging `N₀` enlarges the admissible `K` for free (`K/j → 0.19`).
* `AverageOddDarkPressure b j σ t U d s θ C` — the whole-word exponential moment bound
  `∑_P s^{N_odd(P)} ≤ 2^{θ j + C log₂ j} · |P_σ|` for every low frequency.  It is an instance of
  `OddDarkPressure` with an explicit exponent; nothing is window-wise or pointwise in blocks.
* `oddDarkPressure_of_average` — logarithmic absorption (`LogAbsorb.rpow_log_absorb`) for
  `j ≥ (3C/(θ'−θ))²`.
* `criticalWhiteCount_of_averagePressure` — **`AverageOddDarkPressure ⇒ CriticalWhiteCount`** for
  every even `j ≥ 300` above the absorption threshold, with
  `ρ = 2^{−⌊j/300⌋} + 2^{θ'j}((1+s)/2)^{−n}`.
* `criticalWhiteCount_rate` — the same with `ρ ≤ 2·2^{−j/300} + 2^{−γ j}` when
  `θ' + γ ≤ ν log₂((1+s)/2)` and `n ≥ ν j`.
* `shellP_nonempty`, `kappa_pow_le_exp` — the elementary side conditions of `LowFreqDecay`.
* `lowFreqDecay_of_averagePressure` — **`AverageOddDarkPressure ⇒ LowFreqDecay`** with `C = 4`
  and an explicit rate `γ`.
* `N0 = 30, K = ⌊7j/50⌋` and `N0 = 100, K = ⌊17j/100⌋` are packaged as concrete schedules.
* `SummedOddDarkPressure`, `lowFreqDecay_of_summedPressure` — uniformity in `λ` is not needed:
  `LowFreqDecay` sums over the frequencies of each shell, so a bound on the **summed** moment
  `∑_{λ ∈ cshell u} ∑_P s^{N_odd} ≤ 2^{u+1}·2^{θj + C log₂ j}·|P_σ|` suffices (`summed_of_average`).

The pressure bound itself is a hypothesis; nothing here claims it.

No `sorry`, `admit`, `axiom`, `opaque`, or `native_decide`.
-/

namespace EOC
namespace AverageOddDark

open Finset CapacityBounds OddBlack WhiteContraction ShapeUnconditional

/-! ## 1. ShapeTail with a free budget -/

open Classical in
/-- `ShapeTail` is monotone in the required number `K` of shape-good blocks. -/
theorem shapeTail_mono {b : ℕ → ℕ} {j σ N0 K K' : ℕ} {ρ : ℝ} (hK : K' ≤ K)
    (h : ShapeTail b j σ N0 K ρ) : ShapeTail b j σ N0 K' ρ := by
  unfold ShapeTail at h ⊢
  refine le_trans (sum_le_sum_of_subset_of_nonneg ?_ fun c _ _ => ?_) h
  · intro c hc
    simp only [mem_filter] at hc ⊢
    exact ⟨hc.1, lt_of_lt_of_le hc.2 hK⟩
  · unfold BlockCubeInstance.nCls; positivity

/-- **Unconditional ShapeTail with a free block budget.**  For every even `j ≥ 300`, every `N₀` and
every `K` with `K + ⌊31j/100⌋ + ⌊σ/(N₀+2)⌋ ≤ j/2`. -/
theorem shapeTail_allEven_budget {j N0 K : ℕ} (hj : 300 ≤ j) (hev : 2 ∣ j)
    (hK : K + 31 * j / 100 + collatzBarrier 0 j / (N0 + 2) ≤ j / 2) :
    ShapeTail (collatzBarrier 0) j (collatzBarrier 0 j) N0 K ((2 : ℝ) ^ (j / 300))⁻¹ := by
  have h := arith_allEven hj hev
  unfold Arith at h
  exact ShapeCertificate.shapeTail_of_arith (collatzBarrier 0) (t := 0) (T := 31 * j / 100)
    (by omega) (by positivity) (by omega) (collatz_chord 0 (by omega))
    (le_collatzBarrier 0 j) le_rfl hK (real_of_nat h)

/-- Budget for `N₀ = 30`, `K = ⌊7j/50⌋` (uses `200σ < 317j`). -/
theorem budget_30 (j : ℕ) (hj : 1 ≤ j) :
    7 * j / 50 + 31 * j / 100 + collatzBarrier 0 j / (30 + 2) ≤ j / 2 := by
  have := barrier_lt j hj
  omega

/-- Budget for `N₀ = 100`, `K = ⌊17j/100⌋`. -/
theorem budget_100 (j : ℕ) (hj : 1 ≤ j) :
    17 * j / 100 + 31 * j / 100 + collatzBarrier 0 j / (100 + 2) ≤ j / 2 := by
  have := barrier_lt j hj
  omega

/-! ## 2. Averaged pressure and logarithmic absorption -/

/-- **Averaged odd dark pressure.**  For every shell `u ≤ U` and frequency `λ` in it, the whole-word
exponential moment of the own dark odd cells is at most `2^{θ j + C log₂ j}` times the shell size:
exponent `θ` per step with a logarithmic surplus `C`. -/
def AverageOddDarkPressure (b : ℕ → ℕ) (j σ t U : ℕ) (d s θ C : ℝ) : Prop :=
  OddDarkPressure b j σ t U d s ((2 : ℝ) ^ (C * Real.logb 2 j + θ * j))

/-- `OddDarkPressure` is monotone in `M`. -/
theorem oddDarkPressure_mono {b : ℕ → ℕ} {j σ t U : ℕ} {d s M M' : ℝ} (hM : M ≤ M')
    (h : OddDarkPressure b j σ t U d s M) : OddDarkPressure b j σ t U d s M' :=
  fun u hu lam hlam => (h u hu lam hlam).trans
    (mul_le_mul_of_nonneg_right hM (Nat.cast_nonneg _))

/-- **Logarithmic absorption.**  Beyond `j ≥ (3C/(θ'−θ))²` the logarithmic surplus disappears into
the slightly larger exponent `θ'`. -/
theorem oddDarkPressure_of_average {b : ℕ → ℕ} {j σ t U : ℕ} {d s θ θ' C : ℝ}
    (hj : 1 ≤ j) (hC : 0 ≤ C) (hθ : θ < θ') (hlarge : (3 * C / (θ' - θ)) ^ 2 ≤ j)
    (h : AverageOddDarkPressure b j σ t U d s θ C) :
    OddDarkPressure b j σ t U d s ((2 : ℝ) ^ (θ' * j)) :=
  oddDarkPressure_mono (LogAbsorb.rpow_log_absorb hC hθ (by exact_mod_cast hj) hlarge) h

/-! ## 3. `AverageOddDarkPressure ⇒ CriticalWhiteCount` -/

/-- **Pressure-only `CriticalWhiteCount`.**  For every even `j ≥ 300` beyond the absorption
threshold, every `N₀, K` within the block budget and every split `k + n ≤ K`:
`AverageOddDarkPressure` with exponent `θ < θ'` gives `CriticalWhiteCount` at level `k` with
`ρ = 2^{−⌊j/300⌋} + 2^{θ' j} / ((1+s)/2)^n`.  No `ShapeTail` hypothesis remains. -/
theorem criticalWhiteCount_of_averagePressure {j t U N0 K k n : ℕ} {d s θ θ' C : ℝ}
    (hj : 300 ≤ j) (hev : 2 ∣ j)
    (hK : K + 31 * j / 100 + collatzBarrier 0 j / (N0 + 2) ≤ j / 2) (hkn : k + n ≤ K)
    (hs : 1 ≤ s) (hC : 0 ≤ C) (hθ : θ < θ') (hlarge : (3 * C / (θ' - θ)) ^ 2 ≤ j)
    (hpress : AverageOddDarkPressure (collatzBarrier 0) j (collatzBarrier 0 j) t U d s θ C) :
    CriticalWhiteCount (collatzBarrier 0) j (collatzBarrier 0 j) t U N0 d k
      (((2 : ℝ) ^ (j / 300))⁻¹ + (2 : ℝ) ^ (θ' * j) / ((1 + s) / 2) ^ n) := by
  have hshape := shapeTail_mono hkn (shapeTail_allEven_budget (N0 := N0) hj hev hK)
  have hodd := oddDarkPressure_of_average (by omega) hC hθ hlarge hpress
  have hpos : (0 : ℝ) < ((1 + s) / 2) ^ n := pow_pos (by linarith) n
  exact criticalWhiteCount_of_shape_and_oddPressure (collatzBarrier 0) (by omega) hs hshape hodd
    (le_of_eq (div_mul_cancel₀ _ hpos.ne').symm)

/-- The pressure term is exponentially small once `θ' + γ ≤ ν log₂((1+s)/2)` and `n ≥ ν j`. -/
theorem pressure_term_le {j n : ℕ} {s θ' ν γ : ℝ} (hs : 1 ≤ s) (hn : ν * j ≤ n)
    (hθ : θ' + γ ≤ ν * Real.logb 2 ((1 + s) / 2)) :
    (2 : ℝ) ^ (θ' * j) / ((1 + s) / 2) ^ n ≤ (2 : ℝ) ^ (-(γ * j)) := by
  have ha : (1 : ℝ) ≤ (1 + s) / 2 := by linarith
  have ha0 : (0 : ℝ) < (1 + s) / 2 := by linarith
  set L := Real.logb 2 ((1 + s) / 2) with hL
  have hL0 : 0 ≤ L := Real.logb_nonneg one_lt_two ha
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  -- ((1+s)/2)^n = 2^(n L) ≥ 2^(ν j L)
  have hpowL : ((1 + s) / 2 : ℝ) ^ n = (2 : ℝ) ^ ((n : ℝ) * L) := by
    rw [show (n : ℝ) * L = L * n by ring, Real.rpow_mul (by norm_num), hL,
      Real.rpow_logb (by norm_num) (by norm_num) ha0, Real.rpow_natCast]
  have hden : (2 : ℝ) ^ ((ν * j) * L) ≤ ((1 + s) / 2) ^ n := by
    rw [hpowL]
    exact Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_right hn hL0)
  have hpos : (0 : ℝ) < (2 : ℝ) ^ ((ν * j) * L) := by positivity
  calc (2 : ℝ) ^ (θ' * j) / ((1 + s) / 2) ^ n
      ≤ (2 : ℝ) ^ (θ' * j) / (2 : ℝ) ^ ((ν * j) * L) :=
        div_le_div_of_nonneg_left (by positivity) hpos hden
    _ = (2 : ℝ) ^ (θ' * j - (ν * j) * L) := by rw [← Real.rpow_sub (by norm_num)]
    _ ≤ (2 : ℝ) ^ (-(γ * j)) := by
        apply Real.rpow_le_rpow_of_exponent_le one_le_two
        nlinarith

/-- **Pressure-only `CriticalWhiteCount` with explicit rates.** -/
theorem criticalWhiteCount_rate {j t U N0 K k n : ℕ} {d s θ θ' C ν γ : ℝ}
    (hj : 300 ≤ j) (hev : 2 ∣ j)
    (hK : K + 31 * j / 100 + collatzBarrier 0 j / (N0 + 2) ≤ j / 2) (hkn : k + n ≤ K)
    (hs : 1 ≤ s) (hC : 0 ≤ C) (hθ : θ < θ') (hlarge : (3 * C / (θ' - θ)) ^ 2 ≤ j)
    (hn : ν * j ≤ n) (hγ : θ' + γ ≤ ν * Real.logb 2 ((1 + s) / 2))
    (hpress : AverageOddDarkPressure (collatzBarrier 0) j (collatzBarrier 0 j) t U d s θ C) :
    ∃ ρ ≤ 2 * (2 : ℝ) ^ (-(j : ℝ) / 300) + (2 : ℝ) ^ (-(γ * j)),
      CriticalWhiteCount (collatzBarrier 0) j (collatzBarrier 0 j) t U N0 d k ρ :=
  ⟨_, add_le_add (rho_le_rate j) (pressure_term_le hs hn hγ),
    criticalWhiteCount_of_averagePressure hj hev hK hkn hs hC hθ hlarge hpress⟩

/-! ## 4. The elementary side conditions of `LowFreqDecay` -/

/-- The Collatz shell is nonempty (chord rotation: `1 ≤ C(σ−1, j−1) ≤ j·|P_σ|`). -/
theorem shellP_nonempty {j : ℕ} (hj : 1 ≤ j) :
    (PrefixCollision.shellP (collatzBarrier 0) j (collatzBarrier 0 j)).Nonempty := by
  have hjs := le_collatzBarrier 0 j
  have h := shell_choose_le_mul_card hj (collatzBarrier 0) (collatz_chord 0 (by omega)) hjs le_rfl
  have hc : 1 ≤ (collatzBarrier 0 j - 1).choose (j - 1) := Nat.choose_pos (by omega)
  rw [← Finset.card_pos]
  have : 0 < j * (PrefixCollision.shellP (collatzBarrier 0) j (collatzBarrier 0 j)).card :=
    lt_of_lt_of_le hc h
  exact Nat.pos_of_mul_pos_left this

/-- `1 − cos(π d) ≥ 2 d²` for `0 ≤ d ≤ 1/2` (via `sin y ≥ 2y/π`). -/
theorem one_sub_cos_ge {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1 / 2) :
    2 * d ^ 2 ≤ 1 - Real.cos (Real.pi * d) := by
  have hy0 : 0 ≤ Real.pi * d / 2 := by have := Real.pi_pos; positivity
  have hy1 : Real.pi * d / 2 ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hsin := Real.mul_le_sin hy0 hy1
  have hsin' : d ≤ Real.sin (Real.pi * d / 2) := by
    have : 2 / Real.pi * (Real.pi * d / 2) = d := by field_simp
    linarith
  have hcos : Real.cos (Real.pi * d) = 1 - 2 * Real.sin (Real.pi * d / 2) ^ 2 := by
    have h := Real.cos_two_mul' (Real.pi * d / 2)
    rw [show 2 * (Real.pi * d / 2) = Real.pi * d by ring] at h
    rw [h]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * d / 2)]
  rw [hcos]
  nlinarith

/-- **The good-block factor decays.**  `κ(d,N₀)^{2k} ≤ exp(−8 k d²/N₀)` for `0 ≤ d ≤ 1/2` and
`N₀ ≥ 2`. -/
theorem kappa_pow_le_exp {d : ℝ} {N0 : ℕ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1 / 2) (hN : 2 ≤ N0) (k : ℕ) :
    kappa d N0 ^ (2 * k) ≤ Real.exp (-(8 * k * d ^ 2 / N0)) := by
  have hN0 : (2 : ℝ) ≤ N0 := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N0 := by linarith
  have hc := one_sub_cos_ge hd0 hd1
  have hcos0 : 0 ≤ Real.cos (Real.pi * d) := Real.cos_nonneg_of_mem_Icc
    ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  have hcos1 : Real.cos (Real.pi * d) ≤ 1 := Real.cos_le_one _
  -- 0 ≤ κ ≤ 1 − 4d²/N₀
  have hk0 : 0 ≤ kappa d N0 := by
    unfold kappa
    rw [sub_nonneg, div_le_one hNpos]
    linarith
  have hk1 : kappa d N0 ≤ 1 - 4 * d ^ 2 / N0 := by
    unfold kappa
    have : 4 * d ^ 2 / (N0 : ℝ) ≤ 2 * (1 - Real.cos (Real.pi * d)) / N0 :=
      div_le_div_of_nonneg_right (by linarith) hNpos.le
    linarith
  have hexp : 1 - 4 * d ^ 2 / N0 ≤ Real.exp (-(4 * d ^ 2 / N0)) := by
    have := Real.add_one_le_exp (-(4 * d ^ 2 / N0))
    linarith
  calc kappa d N0 ^ (2 * k) ≤ Real.exp (-(4 * d ^ 2 / N0)) ^ (2 * k) :=
        pow_le_pow_left₀ hk0 (hk1.trans hexp) _
    _ = Real.exp (-(8 * k * d ^ 2 / N0)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring

/-! ## 5. `AverageOddDarkPressure ⇒ LowFreqDecay` -/

/-- **Pressure-only `LowFreqDecay`.**  With `γ ≤ 1/300`, `θ' + γ ≤ ν log₂((1+s)/2)`, `n ≥ ν j` and
`γ j ln 2 ≤ 8 k d²/N₀`, the averaged pressure bound gives `LowFreqDecay` with constant `4` and rate
`γ`.  All remaining hypotheses are parameter inequalities. -/
theorem lowFreqDecay_of_averagePressure {j t U N0 K k n : ℕ} {d s θ θ' C ν γ : ℝ}
    (hj : 300 ≤ j) (hev : 2 ∣ j)
    (hK : K + 31 * j / 100 + collatzBarrier 0 j / (N0 + 2) ≤ j / 2) (hkn : k + n ≤ K)
    (hN : 2 ≤ N0) (hd0 : 0 ≤ d) (hd1 : d ≤ 1 / 2)
    (hs : 1 ≤ s) (hC : 0 ≤ C) (hθ : θ < θ') (hlarge : (3 * C / (θ' - θ)) ^ 2 ≤ j)
    (hn : ν * j ≤ n) (hγ : θ' + γ ≤ ν * Real.logb 2 ((1 + s) / 2))
    (hγ300 : γ ≤ 1 / 300) (hγk : γ * j * Real.log 2 ≤ 8 * k * d ^ 2 / N0)
    (hpress : AverageOddDarkPressure (collatzBarrier 0) j (collatzBarrier 0 j) t U d s θ C) :
    DecayInterface.LowFreqDecay (collatzBarrier 0) j (collatzBarrier 0 j) t U 4 γ := by
  obtain ⟨ρ, hρ, hcwc⟩ := criticalWhiteCount_rate (N0 := N0) hj hev hK hkn hs hC hθ hlarge hn hγ
    hpress
  refine lowFreqDecay_of_criticalWhiteCount (collatzBarrier 0) (by omega)
    (shellP_nonempty (by omega)) hd0 hd1 hN hcwc (by norm_num) ?_
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have e1 : (2 : ℝ) ^ (-(γ * j)) = Real.exp (-(γ * j * Real.log 2)) := by
    rw [Real.rpow_def_of_pos (by norm_num)]; ring_nf
  have hkap : kappa d N0 ^ (2 * k) ≤ (2 : ℝ) ^ (-(γ * j)) := by
    rw [e1]
    exact (kappa_pow_le_exp hd0 hd1 hN k).trans (Real.exp_le_exp.mpr (by linarith))
  have h300 : (2 : ℝ) ^ (-(j : ℝ) / 300) ≤ (2 : ℝ) ^ (-(γ * j)) :=
    Real.rpow_le_rpow_of_exponent_le one_le_two (by nlinarith)
  have hp : (0 : ℝ) ≤ (2 : ℝ) ^ (-(γ * j)) := by positivity
  nlinarith

/-! ## 6. Concrete schedules -/

/-- **`N₀ = 30`, `K = ⌊7j/50⌋`.** -/
theorem criticalWhiteCount_N30 {j t U k n : ℕ} {d s θ θ' C ν γ : ℝ}
    (hj : 300 ≤ j) (hev : 2 ∣ j) (hkn : k + n ≤ 7 * j / 50)
    (hs : 1 ≤ s) (hC : 0 ≤ C) (hθ : θ < θ') (hlarge : (3 * C / (θ' - θ)) ^ 2 ≤ j)
    (hn : ν * j ≤ n) (hγ : θ' + γ ≤ ν * Real.logb 2 ((1 + s) / 2))
    (hpress : AverageOddDarkPressure (collatzBarrier 0) j (collatzBarrier 0 j) t U d s θ C) :
    ∃ ρ ≤ 2 * (2 : ℝ) ^ (-(j : ℝ) / 300) + (2 : ℝ) ^ (-(γ * j)),
      CriticalWhiteCount (collatzBarrier 0) j (collatzBarrier 0 j) t U 30 d k ρ :=
  criticalWhiteCount_rate hj hev (budget_30 j (by omega)) hkn hs hC hθ hlarge hn hγ hpress

/-- **`N₀ = 100`, `K = ⌊17j/100⌋`.** -/
theorem criticalWhiteCount_N100 {j t U k n : ℕ} {d s θ θ' C ν γ : ℝ}
    (hj : 300 ≤ j) (hev : 2 ∣ j) (hkn : k + n ≤ 17 * j / 100)
    (hs : 1 ≤ s) (hC : 0 ≤ C) (hθ : θ < θ') (hlarge : (3 * C / (θ' - θ)) ^ 2 ≤ j)
    (hn : ν * j ≤ n) (hγ : θ' + γ ≤ ν * Real.logb 2 ((1 + s) / 2))
    (hpress : AverageOddDarkPressure (collatzBarrier 0) j (collatzBarrier 0 j) t U d s θ C) :
    ∃ ρ ≤ 2 * (2 : ℝ) ^ (-(j : ℝ) / 300) + (2 : ℝ) ^ (-(γ * j)),
      CriticalWhiteCount (collatzBarrier 0) j (collatzBarrier 0 j) t U 100 d k ρ :=
  criticalWhiteCount_rate hj hev (budget_100 j (by omega)) hkn hs hC hθ hlarge hn hγ hpress

/-! ## 7. Frequency-summed pressure suffices

`GoodAngles.lowFreqDecay_of_goodAngles` bounds each frequency separately and then **sums** over
`λ ∈ cshell`.  Hence the pressure hypothesis need not be uniform in `λ`: a bound on the moment
summed over each shell, `∑_{λ ∈ cshell u} ∑_P s^{N_odd} ≤ 2^{u+1}·M·|P_σ|`, feeds `LowFreqDecay`
directly. -/

section Summed

variable (b : ℕ → ℕ)

open Classical in
/-- **Per-frequency few-good bound.**  For a single `λ`, the class-weighted mass with fewer than `k`
good blocks is at most `ρ₁|P_σ| + (∑_P s^{N_odd}) / ((1+s)/2)^n`. -/
theorem fewGood_le_single {j σ t N0 k n : ℕ} {d s ρ₁ : ℝ} (lam : ℕ) (hj : 1 ≤ j) (hs : 1 ≤ s)
    (hshape : ShapeTail b j σ N0 (k + n) ρ₁) :
    ∑ c ∈ (PrefixCollision.shellP b j σ).image (BlockCubeInstance.pairκ j) with
        ((range (j / 2)).filter (GoodPair b (σ + 1 + t) N0 d lam c)).card < k,
        BlockCubeInstance.nCls (PrefixCollision.shellP b j σ) (BlockCubeInstance.pairκ j) c ≤
      ρ₁ * ((PrefixCollision.shellP b j σ).card : ℝ) +
        (∑ P ∈ PrefixCollision.shellP b j σ, s ^ Nodd b (σ + 1 + t) d lam P) /
          ((1 + s) / 2) ^ n := by
  set T := PrefixCollision.shellP b j σ
  set κ := BlockCubeInstance.pairκ j
  set C := T.image κ
  set w := BlockCubeInstance.nCls T κ
  set good := fun c => ((range (j / 2)).filter (GoodPair b (σ + 1 + t) N0 d lam c)).card
  set shp := fun c => ((range (j / 2)).filter (ShapeGood b N0 c)).card
  set bad := fun c => ((range (j / 2)).filter (BadPair b (σ + 1 + t) N0 d lam c)).card
  have hw0 : ∀ c, 0 ≤ w c := fun c => by unfold w BlockCubeInstance.nCls; positivity
  have ha : (0 : ℝ) < (1 + s) / 2 := by linarith
  have hsplit : ∑ c ∈ C.filter (fun c => good c < k), w c ≤
      ∑ c ∈ C.filter (fun c => shp c < k + n), w c + ∑ c ∈ C.filter (fun c => n ≤ bad c), w c := by
    rw [sum_filter, sum_filter, sum_filter, ← sum_add_distrib]
    refine sum_le_sum fun c _ => ?_
    have hgc := goodCount_ge b (m := σ + 1 + t) (N0 := N0) (d := d) (lam := lam) c (range (j / 2))
    split_ifs with h1 h2 h3 h2 h3 <;> linarith [hw0 c]
  have hbad : (∑ c ∈ C.filter (fun c => n ≤ bad c), w c) * ((1 + s) / 2) ^ n ≤
      ∑ P ∈ T, s ^ Nodd b (σ + 1 + t) d lam P := by
    rw [sum_mul]
    calc ∑ c ∈ C.filter (fun c => n ≤ bad c), w c * ((1 + s) / 2) ^ n
        ≤ ∑ c ∈ C.filter (fun c => n ≤ bad c), w c * ((1 + s) / 2) ^ bad c :=
          sum_le_sum fun c hc => mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ (by linarith) (mem_filter.mp hc).2) (hw0 c)
      _ ≤ ∑ c ∈ C, w c * ((1 + s) / 2) ^ bad c :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            (fun c _ _ => mul_nonneg (hw0 c) (pow_nonneg ha.le _))
      _ ≤ ∑ c ∈ C, ∑ P ∈ T.filter (fun P => κ P = c), s ^ Nodd b (σ + 1 + t) d lam P :=
          sum_le_sum fun c hc => sum_class_pow_nodd_ge b (t := t) hj hs hc
      _ = ∑ P ∈ T, s ^ Nodd b (σ + 1 + t) d lam P :=
          sum_fiberwise_of_maps_to (fun P hP => mem_image_of_mem κ hP) _
  have hpos : (0 : ℝ) < ((1 + s) / 2) ^ n := pow_pos ha n
  have hbad2 : ∑ c ∈ C.filter (fun c => n ≤ bad c), w c ≤
      (∑ P ∈ T, s ^ Nodd b (σ + 1 + t) d lam P) / ((1 + s) / 2) ^ n := by
    rw [le_div_iff₀ hpos]; exact hbad
  have hsh : ∑ c ∈ C.filter (fun c => shp c < k + n), w c ≤ ρ₁ * (T.card : ℝ) := hshape
  exact hsplit.trans (add_le_add hsh hbad2)

open Classical in
/-- **`ShapeTail` + frequency-summed pressure ⇒ `LowFreqDecay`.** -/
theorem lowFreqDecay_of_shape_and_summedPressure {j σ t U N0 k n : ℕ} {d s ρ₁ M C γ : ℝ}
    (hj : 1 ≤ j) (hne : (PrefixCollision.shellP b j σ).Nonempty) (hd0 : 0 ≤ d) (hd1 : d ≤ 1 / 2)
    (hN : 2 ≤ N0) (hs : 1 ≤ s) (hρ₁ : 0 ≤ ρ₁) (hshape : ShapeTail b j σ N0 (k + n) ρ₁)
    (hpress : ∀ u ≤ U, ∑ lam ∈ ShellDecomposition.cshell (σ + 1) t u,
        ∑ P ∈ PrefixCollision.shellP b j σ, s ^ Nodd b (σ + 1 + t) d lam P ≤
      2 ^ (u + 1) * M * ((PrefixCollision.shellP b j σ).card : ℝ))
    (hrate : kappa d N0 ^ (2 * k) + ρ₁ + M / ((1 + s) / 2) ^ n ≤ C * (2 : ℝ) ^ (-(γ * j))) :
    DecayInterface.LowFreqDecay b j σ t U C γ := by
  intro u hu
  set T := PrefixCollision.shellP b j σ
  set Cl := T.image (BlockCubeInstance.pairκ j)
  set w := BlockCubeInstance.nCls T (BlockCubeInstance.pairκ j)
  set P2 : ℝ := (T.card : ℝ) ^ 2
  set a : ℝ := ((1 + s) / 2) ^ n
  have ha : 0 < a := pow_pos (by linarith) n
  have hT : (0 : ℝ) < T.card := by exact_mod_cast hne.card_pos
  have hP2 : 0 ≤ P2 := by positivity
  have hwsum : ∑ c ∈ Cl, w c = (T.card : ℝ) := BlockCubeInstance.sum_nCls T _
  have hκ0 := kappa_nonneg hd0 hd1 hN
  obtain ⟨hwpos, hbd⟩ := BlockCubeInstance.blockCubeHyp_pair b j σ t U hj hne
  -- per-frequency bound
  have hpt : ∀ lam ∈ ShellDecomposition.cshell (σ + 1) t u,
      ‖TwistExpansion.Psi T (σ + 1) t (WeightedChain.yPrime j σ t) lam‖ ^ 2 ≤
        P2 * (kappa d N0 ^ (2 * k) + ρ₁) +
          P2 * ((∑ P ∈ T, s ^ Nodd b (σ + 1 + t) d lam P) / a / T.card) := by
    intro lam hlam
    set ρl := ρ₁ + (∑ P ∈ T, s ^ Nodd b (σ + 1 + t) d lam P) / a / T.card
    have hdens : GoodAngles.PositiveDensityGoodAngles Cl w
        (BlockCubeInstance.Wfac (BlockCubeInstance.pairB b) fun _ r x =>
          SwapCollatz.collatzPhase lam (σ + 1 + t) (WeightedChain.uInv (σ + 1 + t)) (2 * r + 1) x)
        (fun c r => GoodPair b (σ + 1 + t) N0 d lam c r) (j / 2) k ρl (kappa d N0) := by
      refine ⟨fun c _ r => ?_, fun c _ r hg => pair_factor_le_of_good b hd0 hg, ?_⟩
      · unfold BlockCubeInstance.Wfac; exact wfac_mem_unit _ _
      · have h := fewGood_le_single b (t := t) (d := d) lam hj hs hshape
        rw [hwsum]
        have e : ρl * (T.card : ℝ) =
            ρ₁ * T.card + (∑ P ∈ T, s ^ Nodd b (σ + 1 + t) d lam P) / a := by
          simp only [ρl]; field_simp
        rw [e]; convert h using 2
    have havg := GoodAngles.avg_prod_sq_le_of_goodAngles Cl w _ _ (j / 2) k hκ0 (kappa_le_one d N0)
      (fun c _ => by unfold w BlockCubeInstance.nCls; positivity) hdens
    have hdiv : (∑ c ∈ Cl, w c * ∏ r ∈ range (j / 2),
        (BlockCubeInstance.Wfac (BlockCubeInstance.pairB b) (fun _ r x =>
          SwapCollatz.collatzPhase lam (σ + 1 + t) (WeightedChain.uInv (σ + 1 + t)) (2 * r + 1) x)
          c r) ^ 2) / ∑ c ∈ Cl, w c ≤ kappa d N0 ^ (2 * k) + ρl := (div_le_iff₀ hwpos).mpr havg
    calc _ ≤ P2 * _ := hbd u hu lam hlam
      _ ≤ P2 * (kappa d N0 ^ (2 * k) + ρl) := mul_le_mul_of_nonneg_left hdiv hP2
      _ = _ := by simp only [ρl]; ring
  have hcard : ((ShellDecomposition.cshell (σ + 1) t u).card : ℝ) ≤ 2 ^ (u + 1) := by
    exact_mod_cast ShellDecomposition.card_cshell_le (σ + 1) t u
  have hconst : 0 ≤ P2 * (kappa d N0 ^ (2 * k) + ρ₁) := by
    have := pow_nonneg hκ0 (2 * k); positivity
  have hsumS := hpress u hu
  calc ∑ lam ∈ ShellDecomposition.cshell (σ + 1) t u,
        ‖TwistExpansion.Psi T (σ + 1) t (WeightedChain.yPrime j σ t) lam‖ ^ 2
      ≤ ∑ lam ∈ ShellDecomposition.cshell (σ + 1) t u, (P2 * (kappa d N0 ^ (2 * k) + ρ₁) +
          P2 * ((∑ P ∈ T, s ^ Nodd b (σ + 1 + t) d lam P) / a / T.card)) := sum_le_sum hpt
    _ = ((ShellDecomposition.cshell (σ + 1) t u).card : ℝ) * (P2 * (kappa d N0 ^ (2 * k) + ρ₁)) +
          P2 / a / T.card * ∑ lam ∈ ShellDecomposition.cshell (σ + 1) t u,
            ∑ P ∈ T, s ^ Nodd b (σ + 1 + t) d lam P := by
        rw [sum_add_distrib, sum_const, nsmul_eq_mul, mul_sum]
        congr 1; refine sum_congr rfl fun lam _ => ?_; ring
    _ ≤ 2 ^ (u + 1) * (P2 * (kappa d N0 ^ (2 * k) + ρ₁)) +
          P2 / a / T.card * (2 ^ (u + 1) * M * T.card) := by
        gcongr
    _ = 2 ^ (u + 1) * P2 * (kappa d N0 ^ (2 * k) + ρ₁ + M / a) := by
        field_simp
    _ ≤ 2 ^ (u + 1) * P2 * (C * (2 : ℝ) ^ (-(γ * j))) := by gcongr
    _ = _ := by simp only [P2]; ring

end Summed

/-- **Frequency-summed averaged pressure.**  For every shell `u ≤ U`, the moment summed over the
frequencies of the shell is at most `2^{u+1} · 2^{θ j + C log₂ j} · |P_σ|`.  Implied by
`AverageOddDarkPressure` (`|cshell u| ≤ 2^{u+1}`), and strictly weaker in general. -/
def SummedOddDarkPressure (b : ℕ → ℕ) (j σ t U : ℕ) (d s θ C : ℝ) : Prop :=
  ∀ u ≤ U, ∑ lam ∈ ShellDecomposition.cshell (σ + 1) t u,
      ∑ P ∈ PrefixCollision.shellP b j σ, s ^ Nodd b (σ + 1 + t) d lam P ≤
    2 ^ (u + 1) * (2 : ℝ) ^ (C * Real.logb 2 j + θ * j) * ((PrefixCollision.shellP b j σ).card : ℝ)

theorem summed_of_average {b : ℕ → ℕ} {j σ t U : ℕ} {d s θ C : ℝ}
    (h : AverageOddDarkPressure b j σ t U d s θ C) : SummedOddDarkPressure b j σ t U d s θ C := by
  intro u hu
  have hcard : ((ShellDecomposition.cshell (σ + 1) t u).card : ℝ) ≤ 2 ^ (u + 1) := by
    exact_mod_cast ShellDecomposition.card_cshell_le (σ + 1) t u
  have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ (C * Real.logb 2 j + θ * j) *
      ((PrefixCollision.shellP b j σ).card : ℝ) := by positivity
  calc _ ≤ ∑ lam ∈ ShellDecomposition.cshell (σ + 1) t u,
        (2 : ℝ) ^ (C * Real.logb 2 j + θ * j) * ((PrefixCollision.shellP b j σ).card : ℝ) :=
        sum_le_sum fun lam hlam => h u hu lam hlam
    _ = _ * _ := by rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_right hcard hnn

/-- **Frequency-summed pressure ⇒ `LowFreqDecay` for the Collatz barrier.**  Same parameters as
`lowFreqDecay_of_averagePressure`, with the λ-uniform hypothesis replaced by the summed one. -/
theorem lowFreqDecay_of_summedPressure {j t U N0 K k n : ℕ} {d s θ θ' C ν γ : ℝ}
    (hj : 300 ≤ j) (hev : 2 ∣ j)
    (hK : K + 31 * j / 100 + collatzBarrier 0 j / (N0 + 2) ≤ j / 2) (hkn : k + n ≤ K)
    (hN : 2 ≤ N0) (hd0 : 0 ≤ d) (hd1 : d ≤ 1 / 2)
    (hs : 1 ≤ s) (hC : 0 ≤ C) (hθ : θ < θ') (hlarge : (3 * C / (θ' - θ)) ^ 2 ≤ j)
    (hn : ν * j ≤ n) (hγ : θ' + γ ≤ ν * Real.logb 2 ((1 + s) / 2))
    (hγ300 : γ ≤ 1 / 300) (hγk : γ * j * Real.log 2 ≤ 8 * k * d ^ 2 / N0)
    (hpress : SummedOddDarkPressure (collatzBarrier 0) j (collatzBarrier 0 j) t U d s θ C) :
    DecayInterface.LowFreqDecay (collatzBarrier 0) j (collatzBarrier 0 j) t U 4 γ := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (by omega : 1 ≤ j)
  have habs := LogAbsorb.rpow_log_absorb hC hθ (by linarith) hlarge
  refine lowFreqDecay_of_shape_and_summedPressure (collatzBarrier 0) (k := k) (n := n)
    (M := (2 : ℝ) ^ (θ' * j)) (by omega) (shellP_nonempty (by omega)) hd0 hd1 hN hs
    (by positivity) (shapeTail_mono hkn (shapeTail_allEven_budget (N0 := N0) hj hev hK))
    (fun u hu => (hpress u hu).trans ?_) ?_
  · have hP : (0 : ℝ) ≤ ((PrefixCollision.shellP (collatzBarrier 0) j
        (collatzBarrier 0 j)).card : ℝ) := Nat.cast_nonneg _
    gcongr
  · have h1 := rho_le_rate j
    have h2 := pressure_term_le hs hn hγ
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have e1 : (2 : ℝ) ^ (-(γ * j)) = Real.exp (-(γ * j * Real.log 2)) := by
      rw [Real.rpow_def_of_pos (by norm_num)]; ring_nf
    have hkap : kappa d N0 ^ (2 * k) ≤ (2 : ℝ) ^ (-(γ * j)) := by
      rw [e1]
      exact (kappa_pow_le_exp hd0 hd1 hN k).trans (Real.exp_le_exp.mpr (by linarith))
    have h300 : (2 : ℝ) ^ (-(j : ℝ) / 300) ≤ (2 : ℝ) ^ (-(γ * j)) :=
      Real.rpow_le_rpow_of_exponent_le one_le_two (by nlinarith)
    have hp : (0 : ℝ) ≤ (2 : ℝ) ^ (-(γ * j)) := by positivity
    nlinarith

end AverageOddDark
end EOC
