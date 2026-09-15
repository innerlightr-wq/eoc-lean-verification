import EOC.LogCorridor

/-!
# Upper-wall escape: returning anchors cross every upper drift wall

Complement to `EOC.LogCorridor` (lower-wall escape for divergent anchors). Everything here is
unconditional except where `LogFloorExclusion` (the external García–Tal/Curry interface) appears as
an explicit hypothesis.

**Orbit types.** Every accelerated orbit is either injective or eventually periodic
(`orbit_dichotomy`); injective orbits tend to infinity (`injective_orbit_tendsto`); bounded orbits
are not injective (`bounded_orbit_not_injective`). There is no third, bounded-but-aperiodic type.

**Size–drift identity.** `m_n · 2^{R_n} = m_0 · U_n` with `U_n = ∏_{k<n} (1 + 1/(3 m_k)) ≥ 1`
(`HarmonicPacking.orbit_mul_two_rpow_R`). Consequences:

* `R_gt_iff` — **upper exit is a modified stopping time**: `c < R_n ↔ 2^c · m_n < m_0 · U_n`.
* `upper_exit_of_descent` — `2^c · m_n < m_0` forces `c < R_n`.
* `orbit_mul_two_rpow_R_mono` / `window_drift_gain` — `m_t 2^{R_t}` is nondecreasing, so a
  contraction `m_{t'} ≤ m_t 2^{−c}` between times `t ≤ t'` raises the drift by at least `c`.

**Periodic anchors.** The repository already has the positive cycle gain
(`three_pow_lt_two_pow_of_evPeriodic_orbit`) and the exact law `R_periodic`. Added here:

* `evPeriodic_orbit_exit_at` / `evPeriodic_orbit_exit` — explicit upper-wall exit time
  `j0 + (⌈(c − R_{j0})/Δ⌉ + 1)·L`, `Δ = blockSum − L·log₂3 > 0`.
* `bounded_orbit_not_upper_confined` — bounded orbits cross every upper wall.
* `R_after_one`, `two_rpow_R_at_one`, `reach_one_upper_exit` — after reaching `1` the drift grows
  by exactly `2 − log₂3` per step, and `m_0 ≤ 2^{R_h}` already holds at the hitting time `h`.

**Exceptional class.** `exceptional_class` / `exceptional_class_of_exclusion`: an odd seed whose
drift stays `≤ U` forever has an injective, divergent orbit that never descends below `m_0 2^{−U}`
and crosses every lower wall `−B log₂ n − K` infinitely often for `B < 8/9` (and for `B < Bstar`
under `LogFloorExclusion Bstar`).

**Rebasing.** `rebased_upper_log_wall`: an injective orbit, rebased at its global minimum, stays
under the upper logarithmic wall `R_n ≤ (1/9) log₂ n + 7/(9 ln 2)` forever (unconditional).

**Prescribed matching.** `descent_prescribed_matching_le` / `reach_one_prescribed_matching_le` —
upper exit of the anchor bounds the matching of every `U`-confined prescribed future.

None of this proves EOC, `CriticalCrossing`, or the Collatz conjecture.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace UpperEscape

open Finset HarmonicPacking PrescribedMatching TransportCollapse LogCorridor PeriodicCore

/-! ## 1. Orbit types -/

/-- A bounded orbit repeats a value (pigeonhole on `K + 2` times into `K + 1` values). -/
theorem bounded_orbit_not_injective (M K : ℕ) (hb : ∀ n, orbit M n ≤ K) :
    ∃ i j, i ≠ j ∧ orbit M i = orbit M j := by
  obtain ⟨x, _, y, _, hxy, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (s := range (K + 2)) (t := range (K + 1))
      (by simp) (fun n _ => by simpa [Nat.lt_succ_iff] using hb n)
  exact ⟨x, y, hxy, heq⟩

/-- An injective orbit tends to infinity: each value bound is exceeded from some time on. -/
theorem injective_orbit_tendsto (M : ℕ) (hinj : ∀ i j, orbit M i = orbit M j → i = j) (K : ℕ) :
    ∃ N₀, ∀ n ≥ N₀, K < orbit M n := by
  have hfin : (orbit M ⁻¹' Set.Iic K).Finite :=
    Set.Finite.preimage (fun x _ y _ h => hinj x y h) (Set.finite_Iic K)
  obtain ⟨B, hB⟩ := hfin.bddAbove
  refine ⟨B + 1, fun n hn => ?_⟩
  by_contra h
  push Not at h
  have := hB (show n ∈ orbit M ⁻¹' Set.Iic K from h)
  omega

/-- **Orbit dichotomy.** Every orbit is injective or has an eventually periodic word. -/
theorem orbit_dichotomy (M : ℕ) :
    (∀ i j, orbit M i = orbit M j → i = j) ∨
      ∃ j0 L, 1 ≤ L ∧ EvPeriodic (orbWord M) j0 L := by
  by_cases hinj : ∀ i j, orbit M i = orbit M j → i = j
  · exact Or.inl hinj
  · right
    push Not at hinj
    obtain ⟨i, j, heq, hne⟩ := hinj
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact ⟨i, j - i, by omega, evPeriodic_of_noninj M i j h heq⟩
    · exact ⟨j, i - j, by omega, evPeriodic_of_noninj M j i h heq.symm⟩

/-! ## 2. Size–drift identity consequences -/

theorem carryU_mono (M t : ℕ) : ∀ k, carryU M t ≤ carryU M (t + k) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, carryU_succ]
    have hf : (1 : ℝ) ≤ 1 + 1 / (3 * (orbit M (t + k) : ℝ)) := by
      have : (0 : ℝ) ≤ 1 / (3 * (orbit M (t + k) : ℝ)) := by positivity
      linarith
    nlinarith [carryU_pos M (t + k)]

theorem R_zero (d : ℕ → ℕ) : R d 0 = 0 := by simp [R]

/-- `m_t · 2^{R_t}` is nondecreasing along the orbit. -/
theorem orbit_mul_two_rpow_R_mono (M t t' : ℕ) (hM : Odd M) (h : t ≤ t') :
    (orbit M t : ℝ) * (2 : ℝ) ^ R (orbWord M) t
      ≤ (orbit M t' : ℝ) * (2 : ℝ) ^ R (orbWord M) t' := by
  rw [orbit_mul_two_rpow_R M t hM, orbit_mul_two_rpow_R M t' hM]
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := by positivity
  obtain ⟨k, rfl⟩ : ∃ k, t' = t + k := ⟨t' - t, by omega⟩
  exact mul_le_mul_of_nonneg_left (carryU_mono M t k) hM0

/-- `m_0 ≤ m_n · 2^{R_n}` for every `n`. -/
theorem seed_le_orbit_mul_two_rpow_R (M n : ℕ) (hM : Odd M) :
    (M : ℝ) ≤ (orbit M n : ℝ) * (2 : ℝ) ^ R (orbWord M) n := by
  have h := orbit_mul_two_rpow_R_mono M 0 n hM (Nat.zero_le n)
  rwa [R_zero, orbit_zero, Real.rpow_zero, mul_one] at h

/-- **Window drift gain.** For `t ≤ t'`, `m_t ≤ m_{t'} · 2^{R_{t'} − R_t}`: a contraction of the
orbit by a factor `2^c` raises the drift by at least `c`. -/
theorem window_drift_gain (M t t' : ℕ) (hM : Odd M) (h : t ≤ t') :
    (orbit M t : ℝ) ≤ (orbit M t' : ℝ) * (2 : ℝ) ^ (R (orbWord M) t' - R (orbWord M) t) := by
  have hmono := orbit_mul_two_rpow_R_mono M t t' hM h
  have hpos : (0 : ℝ) < (2 : ℝ) ^ R (orbWord M) t := by positivity
  rw [Real.rpow_sub (by norm_num)]
  rw [mul_div_assoc', le_div_iff₀ hpos]
  exact hmono

/-- **Upper exit is a modified stopping time.** `c < R_n ↔ 2^c · m_n < m_0 · U_n`. -/
theorem R_gt_iff (M n : ℕ) (hM : Odd M) (c : ℝ) :
    c < R (orbWord M) n ↔ (2 : ℝ) ^ c * (orbit M n : ℝ) < (M : ℝ) * carryU M n := by
  have hid := orbit_mul_two_rpow_R M n hM
  have hmpos : (0 : ℝ) < (orbit M n : ℝ) := by exact_mod_cast (odd_orbit hM n).pos
  rw [← hid, mul_comm ((orbit M n : ℝ)), mul_lt_mul_iff_left₀ hmpos,
    Real.rpow_lt_rpow_left_iff (by norm_num)]

/-- **Descent forces upper exit.** If `2^c · m_n < m_0` then `c < R_n`. -/
theorem upper_exit_of_descent (M n : ℕ) (hM : Odd M) (c : ℝ)
    (h : (2 : ℝ) ^ c * (orbit M n : ℝ) < (M : ℝ)) : c < R (orbWord M) n := by
  have hle := seed_le_orbit_mul_two_rpow_R M n hM
  have hmpos : (0 : ℝ) < (orbit M n : ℝ) := by exact_mod_cast (odd_orbit hM n).pos
  have h2 : (2 : ℝ) ^ c * (orbit M n : ℝ) < (2 : ℝ) ^ R (orbWord M) n * (orbit M n : ℝ) := by
    linarith
  have h3 := lt_of_mul_lt_mul_right h2 hmpos.le
  exact (Real.rpow_lt_rpow_left_iff (by norm_num)).mp h3

/-! ## 3. Periodic anchors: explicit upper-wall exit -/

/-- The per-period drift gain of an eventually periodic genuine orbit is positive. -/
theorem cycle_gain_pos (m0 j0 L : ℕ) (hm0 : Odd m0) (hL : 1 ≤ L)
    (hper : EvPeriodic (orbWord m0) j0 L) :
    0 < (blockSum (orbWord m0) j0 L : ℝ) - alpha * L := by
  have := alpha_mul_lt_of_pow_lt L _ (three_pow_lt_two_pow_of_evPeriodic_orbit m0 j0 L hm0 hL hper)
  linarith

/-- Exit at any `k` with `k · Δ > c − R_{j0}`. -/
theorem evPeriodic_orbit_exit_at (m0 j0 L : ℕ) (hper : EvPeriodic (orbWord m0) j0 L) (c : ℝ)
    (k : ℕ) (hk : c - R (orbWord m0) j0
      < (k : ℝ) * ((blockSum (orbWord m0) j0 L : ℝ) - alpha * L)) :
    c < R (orbWord m0) (j0 + k * L) := by
  rw [R_periodic (orbWord m0) j0 L hper k]
  linarith

/-- **Explicit upper-wall exit for eventually periodic anchors.** With
`Δ = blockSum − L·log₂3 > 0`, the drift exceeds `c` at step `j0 + (⌈(c − R_{j0})/Δ⌉ + 1)·L`. -/
theorem evPeriodic_orbit_exit (m0 j0 L : ℕ) (hm0 : Odd m0) (hL : 1 ≤ L)
    (hper : EvPeriodic (orbWord m0) j0 L) (c : ℝ) :
    c < R (orbWord m0)
      (j0 + (Nat.ceil ((c - R (orbWord m0) j0)
        / ((blockSum (orbWord m0) j0 L : ℝ) - alpha * L)) + 1) * L) := by
  set Δ := (blockSum (orbWord m0) j0 L : ℝ) - alpha * L with hΔ
  have hΔpos : 0 < Δ := cycle_gain_pos m0 j0 L hm0 hL hper
  apply evPeriodic_orbit_exit_at m0 j0 L hper c
  have hceil := Nat.le_ceil ((c - R (orbWord m0) j0) / Δ)
  have h1 : (c - R (orbWord m0) j0) / Δ
      < ((Nat.ceil ((c - R (orbWord m0) j0) / Δ) + 1 : ℕ) : ℝ) := by
    push_cast; linarith
  rwa [div_lt_iff₀ hΔpos] at h1

/-- **Bounded orbits cross every upper wall.** -/
theorem bounded_orbit_not_upper_confined (M K : ℕ) (hM : Odd M) (hb : ∀ n, orbit M n ≤ K)
    (c : ℝ) : ∃ N, ¬ Confined c (orbWord M) N := by
  obtain ⟨i, j, hne, heq⟩ := bounded_orbit_not_injective M K hb
  exact noninjective_orbit_not_upper_confined c M hM ⟨i, j, hne, heq⟩

/-! ## 4. Anchors reaching 1 -/

theorem a_one : a 1 = 2 := by
  change padicValNat 2 (3 * 1 + 1) = 2
  rw [show 3 * 1 + 1 = 2 ^ 2 by norm_num, padicValNat.prime_pow]

theorem T_one : T 1 = 1 := by
  unfold T
  rw [a_one]
  norm_num

theorem orbit_one (t : ℕ) : orbit 1 t = 1 := by
  induction t with
  | zero => rfl
  | succ t ih => rw [orbit_succ, ih, T_one]

/-- After hitting `1`, every valuation is `2`. -/
theorem word_after_one (m0 h : ℕ) (hh : orbit m0 h = 1) (t : ℕ) : orbWord m0 (h + t) = 2 := by
  change a (orbit m0 (h + t)) = 2
  rw [orbit_add, hh, orbit_one, a_one]

/-- After hitting `1` at time `h`, `R_{h+t} = R_h + t·(2 − log₂3)`. -/
theorem R_after_one (m0 h : ℕ) (hh : orbit m0 h = 1) (t : ℕ) :
    R (orbWord m0) (h + t) = R (orbWord m0) h + (t : ℝ) * (2 - alpha) := by
  have hs : ∀ t, s (orbWord m0) (h + t) = s (orbWord m0) h + 2 * t := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [← add_assoc, s_succ, ih, word_after_one m0 h hh t]; ring
  unfold R
  rw [hs t]
  push_cast
  ring

/-- At the hitting time of `1`, the drift already satisfies `m_0 ≤ 2^{R_h}`. -/
theorem two_rpow_R_at_one (m0 h : ℕ) (hm0 : Odd m0) (hh : orbit m0 h = 1) :
    (m0 : ℝ) ≤ (2 : ℝ) ^ R (orbWord m0) h := by
  have := seed_le_orbit_mul_two_rpow_R m0 h hm0
  rwa [hh, Nat.cast_one, one_mul] at this

/-- **Reach-1 upper exit.** If the orbit hits `1` at time `h`, the drift exceeds `c` at every
`h + t` with `t·(2 − log₂3) > c − R_h`; if moreover `2^c < m_0`, already at `h`. -/
theorem reach_one_upper_exit (m0 h : ℕ) (hm0 : Odd m0) (hh : orbit m0 h = 1) (c : ℝ) :
    (∀ t : ℕ, c - R (orbWord m0) h < (t : ℝ) * (2 - alpha) → c < R (orbWord m0) (h + t)) ∧
    ((2 : ℝ) ^ c < (m0 : ℝ) → c < R (orbWord m0) h) := by
  refine ⟨fun t ht => ?_, fun hc => ?_⟩
  · rw [R_after_one m0 h hh t]; linarith
  · have := two_rpow_R_at_one m0 h hm0 hh
    exact (Real.rpow_lt_rpow_left_iff (by norm_num)).mp (lt_of_lt_of_le hc this)

/-! ## 5. The exceptional class of forever upper-confined anchors -/

/-- The drift of `M` stays at most `U` forever. -/
def UpperConfinedForever (U : ℝ) (M : ℕ) : Prop := ∀ n, R (orbWord M) n ≤ U

/-- **Exceptional-class characterization (conditional form).** Under `LogFloorExclusion Bstar`, a
forever `U`-confined odd seed has an injective, divergent orbit that never descends below
`m_0 · 2^{−U}` and crosses every lower wall `−B log₂ n − K` (`B < Bstar`) infinitely often. -/
theorem exceptional_class_of_exclusion {Bstar : ℝ} (hX : LogFloorExclusion Bstar)
    (M : ℕ) (hM : Odd M) (U : ℝ) (hE : UpperConfinedForever U M) :
    (∀ i j, orbit M i = orbit M j → i = j) ∧
    (∀ K, ∃ N₀, ∀ n ≥ N₀, K < orbit M n) ∧
    (∀ n, (M : ℝ) ≤ (2 : ℝ) ^ U * (orbit M n : ℝ)) ∧
    (∀ B < Bstar, ∀ K : ℝ, ∀ N₀ : ℕ, ∃ n ≥ N₀,
      R (orbWord M) n < -B * Real.logb 2 (n : ℝ) - K) := by
  have hinj : ∀ i j, orbit M i = orbit M j → i = j := by
    by_contra h
    push Not at h
    obtain ⟨i, j, heq, hne⟩ := h
    obtain ⟨N, hN⟩ := noninjective_orbit_not_upper_confined U M hM ⟨i, j, hne, heq⟩
    exact hN (fun k _ => hE k)
  refine ⟨hinj, injective_orbit_tendsto M hinj, fun n => ?_, fun B hB K N₀ => ?_⟩
  · have h1 := seed_le_orbit_mul_two_rpow_R M n hM
    have h2 : (2 : ℝ) ^ R (orbWord M) n ≤ (2 : ℝ) ^ U :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (hE n)
    have hm : (0 : ℝ) ≤ (orbit M n : ℝ) := by positivity
    nlinarith
  · have h := hX M hM hinj B hB K
    push Not at h
    obtain ⟨n, hn, hlt⟩ := h N₀
    exact ⟨n, hn, hlt⟩

/-- **Exceptional-class characterization (unconditional, `B < 8/9`).** -/
theorem exceptional_class (M : ℕ) (hM : Odd M) (U : ℝ) (hE : UpperConfinedForever U M) :
    (∀ i j, orbit M i = orbit M j → i = j) ∧
    (∀ K, ∃ N₀, ∀ n ≥ N₀, K < orbit M n) ∧
    (∀ n, (M : ℝ) ≤ (2 : ℝ) ^ U * (orbit M n : ℝ)) ∧
    (∀ B < (8 : ℝ) / 9, ∀ K : ℝ, ∀ N₀ : ℕ, ∃ n ≥ N₀,
      R (orbWord M) n < -B * Real.logb 2 (n : ℝ) - K) :=
  exceptional_class_of_exclusion logFloorExclusion_eight_ninths M hM U hE

/-- **Rebasing an injective orbit at its minimum.** If `orbit M` is injective, then from the time
`n₀` of its global minimum the rebased seed `μ = orbit M n₀` has drift under the upper logarithmic
wall `R_n ≤ (1/9)·log₂ n + 7/(9 ln 2)` for every `n` (unconditional; from the carry budget
`carryE_le`). So a divergent orbit, if one exists, produces a forever upper-log-confined anchor. -/
theorem rebased_upper_log_wall (M : ℕ) (hM : Odd M)
    (hinj : ∀ i j, orbit M i = orbit M j → i = j) :
    ∃ n₀, ∀ n,
      R (orbWord (orbit M n₀)) n ≤ (1 / 9) * Real.logb 2 (n : ℝ) + 7 / (9 * Real.log 2) := by
  have hne : (Set.range (orbit M)).Nonempty := ⟨_, 0, rfl⟩
  obtain ⟨n₀, hn₀⟩ := Nat.sInf_mem hne
  refine ⟨n₀, fun n => ?_⟩
  have hμ : Odd (orbit M n₀) := odd_orbit hM n₀
  have hmin : orbit M n₀ ≤ orbit (orbit M n₀) n := by
    rw [← orbit_add, hn₀]
    exact Nat.sInf_le ⟨_, rfl⟩
  have hinj' : ∀ i < n, ∀ j < n, orbit (orbit M n₀) i = orbit (orbit M n₀) j → i = j := by
    intro i _ j _ h
    rw [← orbit_add, ← orbit_add] at h
    have := hinj _ _ h
    omega
  have hid := orbit_mul_two_rpow_R (orbit M n₀) n hμ
  rw [carryU_eq_two_rpow_carryE] at hid
  have hE := carryE_le (orbit M n₀) n hμ hinj'
  have hpos : (0 : ℝ) < (orbit (orbit M n₀) n : ℝ) := by exact_mod_cast (odd_orbit hμ n).pos
  have h1 : (orbit (orbit M n₀) n : ℝ) * (2 : ℝ) ^ R (orbWord (orbit M n₀)) n
      ≤ (orbit (orbit M n₀) n : ℝ) * (2 : ℝ) ^ carryE (orbit M n₀) n := by
    rw [hid]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hmin) (by positivity)
  have h2 := le_of_mul_le_mul_left h1 hpos
  have hR := (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp h2
  linarith

/-! ## 6. Upper exit and prescribed matching -/

/-- **Descent bounds prescribed matching.** If the anchor orbit has contracted by more than `2^U`
at step `L` (`2^U · m_L < μ_j`), every prescribed block `e` (length `m ≥ L`) with `R ≤ U` through
`m` has prescribed matching at most `U + L·log₂3`. -/
theorem descent_prescribed_matching_le (d e : ℕ → ℕ) (j m L : ℕ) (U : ℝ) (hLm : L ≤ m)
    (he_pos : ∀ i < m, 1 ≤ e i) (hU : ∀ n ≤ m, R e n ≤ U) (hodd : Odd (anchorState d j))
    (hdesc : (2 : ℝ) ^ U * (orbit (anchorState d j) L : ℝ) < (anchorState d j : ℝ)) :
    ((padicValInt 2 ((leastRealizer e m : ℤ) - anchorState d j) : ℕ) : ℝ)
      ≤ U + (L : ℝ) * alpha := by
  apply matching_le_of_R_ne d e j m L U hLm he_pos hU
  intro heq
  have hup := upper_exit_of_descent (anchorState d j) L hodd U hdesc
  have hle := hU L hLm
  change R e L = R (orbWord (anchorState d j)) L at heq
  linarith

/-- **Reach-1 bound on prescribed matching.** If the anchor orbit hits `1` at step `h ≤ m` and
`2^U < μ_j`, every `U`-confined prescribed block of length `m` has matching at most
`U + h·log₂3`. -/
theorem reach_one_prescribed_matching_le (d e : ℕ → ℕ) (j m h : ℕ) (U : ℝ) (hhm : h ≤ m)
    (he_pos : ∀ i < m, 1 ≤ e i) (hU : ∀ n ≤ m, R e n ≤ U) (hodd : Odd (anchorState d j))
    (hh : orbit (anchorState d j) h = 1) (hbig : (2 : ℝ) ^ U < (anchorState d j : ℝ)) :
    ((padicValInt 2 ((leastRealizer e m : ℤ) - anchorState d j) : ℕ) : ℝ)
      ≤ U + (h : ℝ) * alpha := by
  apply matching_le_of_R_ne d e j m h U hhm he_pos hU
  intro heq
  have hup := (reach_one_upper_exit (anchorState d j) h hodd hh U).2 hbig
  have hle := hU h hhm
  change R e h = R (orbWord (anchorState d j)) h at heq
  linarith

end UpperEscape
end EOC
