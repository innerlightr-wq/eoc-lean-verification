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

end AverageOddDark
end EOC
