import EOC.UpperEscape

/-!
# Upper-exit certificates, the divergence equivalence, and the exceptional class

**Divergence equivalence.** `injective_of_sublinear_upper_wall`: an odd seed whose drift stays below
a sublinear wall (`SublinearWall W`: eventually `W n ≤ ε n` for every `ε > 0`) has an injective
orbit, because an eventually periodic orbit gains `Δ > 0` drift per period. `logWall_sublinear`:
`a log₂ n + C` is sublinear. Together with `UpperEscape.rebased_upper_log_wall`:

* `divergence_iff_upperLogAnchor` — an injective (hence divergent) accelerated orbit exists **iff**
  some odd seed satisfies `R_n ≤ (1/9) log₂ n + 7/(9 ln 2)` for every `n`. Fully verified.

**Certificates.**

* `R_add_block` — `R_{t+ℓ} = R_t + (S_{t+ℓ} − S_t − ℓ log₂3)` (exact block drift formula).
* `block_certificate` — a block whose gain exceeds the headroom `U − R_t` forces `R_{t+ℓ} > U`.
* `run_certificate` — the run `1^r q` has gain `r + q − (r+1) log₂3`;
  `q > (U − R_t) + (r+1) log₂3 − r` forces exit at step `t + r + 1`.
* `contraction_drift_gain` — `2^H m_{t'} < m_t` (`t ≤ t'`) forces `R_{t'} − R_t > H`.

**Exceptional class.** For a forever `U`-confined odd seed:

* `exceptional_window` — every window satisfies `S_{t+ℓ} − S_t ≤ ℓ log₂3 + (U − R_t)`;
* `exceptional_headroom_unbounded` — the headroom `U − R_t` exceeds every bound infinitely often
  (from the unconditional lower-wall theorem), so **no fixed block is excluded at all times**:
  every certificate is compatible with permanent confinement after infinitely many dips.

None of this proves EOC, `CriticalCrossing`, or the Collatz conjecture.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace UpperCertificates

open Filter HarmonicPacking PeriodicCore UpperEscape

/-! ## 1. Sublinear upper walls force injectivity -/

/-- A wall `W : ℕ → ℝ` is sublinear if, for every `ε > 0`, eventually `W n ≤ ε n`. -/
def SublinearWall (W : ℕ → ℝ) : Prop := ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, W n ≤ ε * n

/-- **Sublinear upper wall ⇒ injective orbit.** -/
theorem injective_of_sublinear_upper_wall (M : ℕ) (hM : Odd M) (W : ℕ → ℝ)
    (hW : SublinearWall W) (hup : ∀ n, R (orbWord M) n ≤ W n) :
    ∀ i j, orbit M i = orbit M j → i = j := by
  rcases orbit_dichotomy M with hinj | ⟨j0, L, hL, hper⟩
  · exact hinj
  · exfalso
    set Δ := (blockSum (orbWord M) j0 L : ℝ) - alpha * L with hΔ
    have hΔpos : 0 < Δ := cycle_gain_pos M j0 L hM hL hper
    have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
    obtain ⟨N, hN⟩ := hW (Δ / (2 * L)) (by positivity)
    set X := Δ * j0 / (2 * L) - R (orbWord M) j0 with hX
    obtain ⟨k, hk⟩ := exists_nat_gt (max (N : ℝ) (X * 2 / Δ))
    have hkN : N ≤ j0 + k * L := by
      have hNk : N < k := by exact_mod_cast lt_of_le_of_lt (le_max_left _ _) hk
      have : k ≤ k * L := Nat.le_mul_of_pos_right k hL
      omega
    have h1 := hN (j0 + k * L) hkN
    have h2 := hup (j0 + k * L)
    rw [R_periodic (orbWord M) j0 L hper k] at h2
    push_cast at h1
    have e1 : Δ / (2 * L) * ((j0 : ℝ) + k * L) = Δ * j0 / (2 * L) + k * Δ / 2 := by
      field_simp
    have e2 : X < k * Δ / 2 := by
      have h := lt_of_le_of_lt (le_max_right _ _) hk
      rw [div_lt_iff₀ hΔpos] at h
      linarith
    rw [← hΔ] at h2
    linarith

/-- `a log₂ n + C` is a sublinear wall. -/
theorem logWall_sublinear (a C : ℝ) : SublinearWall (fun n => a * Real.logb 2 n + C) := by
  intro ε hε
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set A := |a| / Real.log 2 with hA
  have hA0 : 0 ≤ A := by positivity
  set c := ε / (2 * (A + 1)) with hc
  have hcpos : 0 < c := by positivity
  have hev := (Real.isLittleO_log_id_atTop.def hcpos)
  have hev' := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hev
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp hev'
  obtain ⟨N2, hN2⟩ := exists_nat_gt (2 * |C| / ε)
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have h1 := hN1 n (le_of_max_le_left hn)
  simp only [id, Real.norm_eq_abs] at h1
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlog : a * Real.logb 2 n ≤ A * (c * n) := by
    unfold Real.logb
    calc a * (Real.log n / Real.log 2) ≤ |a * (Real.log n / Real.log 2)| := le_abs_self _
      _ = |a| * |Real.log n| / Real.log 2 := by
          rw [abs_mul, abs_div, abs_of_pos hlog2]; ring
      _ ≤ |a| * (c * |(n : ℝ)|) / Real.log 2 := by gcongr
      _ = A * (c * n) := by rw [abs_of_nonneg hn0, hA]; ring
  have hfrac : A / (A + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have heq : A * (c * n) = (A / (A + 1)) * (ε / 2 * n) := by
    rw [hc]; field_simp
  have hB : A * (c * n) ≤ ε / 2 * n := by
    rw [heq]; exact mul_le_of_le_one_left (by positivity) hfrac
  have hCn : C ≤ ε / 2 * n := by
    have hN2n : (N2 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
    have h' : 2 * |C| / ε < n := lt_of_lt_of_le hN2 hN2n
    rw [div_lt_iff₀ hε] at h'
    have := le_abs_self C
    nlinarith
  change a * Real.logb 2 n + C ≤ ε * n
  linarith

/-- **Divergence equivalence (fully verified).** An injective accelerated orbit exists iff some odd
seed stays under the upper logarithmic wall `(1/9) log₂ n + 7/(9 ln 2)` forever. -/
theorem divergence_iff_upperLogAnchor :
    (∃ M, Odd M ∧ ∀ i j, orbit M i = orbit M j → i = j) ↔
      ∃ μ, Odd μ ∧ ∀ n, R (orbWord μ) n ≤ (1 / 9) * Real.logb 2 (n : ℝ) + 7 / (9 * Real.log 2) := by
  constructor
  · rintro ⟨M, hM, hinj⟩
    obtain ⟨n₀, h⟩ := rebased_upper_log_wall M hM hinj
    exact ⟨orbit M n₀, odd_orbit hM n₀, h⟩
  · rintro ⟨μ, hμ, h⟩
    exact ⟨μ, hμ, injective_of_sublinear_upper_wall μ hμ _ (logWall_sublinear _ _) h⟩

/-! ## 2. Upper-exit certificates -/

/-- **Exact block drift formula.** `R_{t+ℓ} = R_t + (S_{t+ℓ} − S_t − ℓ log₂3)`. -/
theorem R_add_block (d : ℕ → ℕ) (t ℓ : ℕ) :
    R d (t + ℓ) = R d t + (((s d (t + ℓ) : ℝ) - s d t) - (ℓ : ℝ) * alpha) := by
  unfold R
  push_cast
  ring

/-- **Block certificate.** A block whose gain exceeds the current headroom `U − R_t` forces an
upper exit after it. -/
theorem block_certificate (d : ℕ → ℕ) (t ℓ : ℕ) (U : ℝ)
    (h : U - R d t < ((s d (t + ℓ) : ℝ) - s d t) - (ℓ : ℝ) * alpha) :
    U < R d (t + ℓ) := by
  rw [R_add_block]
  linarith

/-- **Run certificate.** A run `1^r` followed by `q` starting at `t` has gain
`r + q − (r+1) log₂3`; if `q > (U − R_t) + (r+1) log₂3 − r`, the drift exceeds `U` at
step `t + r + 1`. -/
theorem run_certificate (d : ℕ → ℕ) (t r q : ℕ) (U : ℝ)
    (hones : ∀ i < r, d (t + i) = 1) (hq : d (t + r) = q)
    (h : (U - R d t) + ((r : ℝ) + 1) * alpha - r < q) :
    U < R d (t + (r + 1)) := by
  have hs : ∀ i ≤ r, s d (t + i) = s d t + i := by
    intro i hi
    induction i with
    | zero => simp
    | succ i ih =>
      rw [← add_assoc, s_succ, ih (by omega), hones i (by omega)]
      ring
  apply block_certificate
  rw [← add_assoc, s_succ, hs r le_rfl, hq]
  push_cast
  linarith

/-- **Contraction certificate.** If `2^H · m_{t'} < m_t` with `t ≤ t'`, then `R_{t'} − R_t > H`. -/
theorem contraction_drift_gain (M t t' : ℕ) (hM : Odd M) (htt' : t ≤ t') (H : ℝ)
    (h : (2 : ℝ) ^ H * (orbit M t' : ℝ) < (orbit M t : ℝ)) :
    H < R (orbWord M) t' - R (orbWord M) t := by
  have hw := window_drift_gain M t t' hM htt'
  have hpos : (0 : ℝ) < (orbit M t' : ℝ) := by exact_mod_cast (odd_orbit hM t').pos
  have h2 : (2 : ℝ) ^ H * (orbit M t' : ℝ)
      < (2 : ℝ) ^ (R (orbWord M) t' - R (orbWord M) t) * (orbit M t' : ℝ) := by
    linarith
  exact (Real.rpow_lt_rpow_left_iff (by norm_num)).mp (lt_of_mul_lt_mul_right h2 hpos.le)

/-! ## 3. The exceptional class: windows and headroom -/

/-- **Sliding-window constraint.** A forever `U`-confined seed satisfies
`S_{t+ℓ} − S_t ≤ ℓ log₂3 + (U − R_t)` on every window. -/
theorem exceptional_window (M : ℕ) (U : ℝ) (hE : UpperConfinedForever U M) (t ℓ : ℕ) :
    ((s (orbWord M) (t + ℓ) : ℝ) - s (orbWord M) t)
      ≤ (ℓ : ℝ) * alpha + (U - R (orbWord M) t) := by
  have h := hE (t + ℓ)
  rw [R_add_block] at h
  linarith

/-- **Headroom is unbounded infinitely often.** For a forever `U`-confined odd seed, for every
bound `H` there are arbitrarily late times with headroom `U − R_t > H`. Hence any fixed block,
however large its gain, is compatible with confinement after infinitely many times. -/
theorem exceptional_headroom_unbounded (M : ℕ) (hM : Odd M) (U : ℝ)
    (hE : UpperConfinedForever U M) (H : ℝ) (N₀ : ℕ) :
    ∃ t ≥ N₀, H < U - R (orbWord M) t := by
  obtain ⟨-, -, -, hdip⟩ := exceptional_class M hM U hE
  obtain ⟨t, ht, hlt⟩ := hdip 0 (by norm_num) (H - U) N₀
  refine ⟨t, ht, ?_⟩
  simp only [neg_zero, zero_mul, zero_sub] at hlt
  linarith

end UpperCertificates
end EOC
