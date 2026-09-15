import EOC.PrescribedMatching
import EOC.HarmonicPacking

/-!
# Logarithmically widening corridors: forced exit and prescribed-matching bounds

The logarithmic corridor with parameters `B, C, U` is
`−B·log₂(n+1) − C ≤ R_n ≤ U` (`InLogCorridor`); `B = 0` is a fixed corridor.

Every accelerated orbit is either non-injective (hence eventually periodic, so its drift exceeds
every upper wall: `noninjective_orbit_not_upper_confined`) or injective (hence divergent). For
injective orbits, logarithmic lower-drift floors are excluded:

* for `B < 8/9` **unconditionally**, by the repository's harmonic packing
  (`HarmonicPacking.injective_orbit_not_eventually_log_floor`, manuscript Thm 4.5);
* for `B < 1/β* ≈ 1.0358567` by the manuscript's Thm 4.11, which rests on the García–Tal/Curry
  windowed sparsity theorem (manuscript Thm 4.8), an **external theorem** not formalized here. It
  enters only as the explicit hypothesis `LogFloorExclusion Bstar` (a `Prop`, never an axiom).

Main results:

* `logFloor_window_bound` — **quantitative, unconditional**: if `orbit M` is injective on `[0, N)`
  and `R_k ≥ −B log₂(k+1) − C` for all `k < N` (`B ≥ 0`), then
  `N · N^(−B) · 2^(−C) ≤ 3M · e^(7/9) · N^(1/9)`; `logFloor_window_bound'` restates this as
  `N^(8/9 − B) ≤ 3 e^(7/9) · 2^C · M`. With `B = 0` this is a finite-prefix drift-depth bound with
  coefficient `8/9`, versus `2 − log₂3` from row V.
* `LogFloorExclusion` — the manuscript-form external interface; `logFloorExclusion_eight_ninths`
  proves it at `Bstar = 8/9`.
* `exits_logCorridor_of_exclusion` / `exits_logCorridor` — no odd seed stays in a logarithmic
  corridor forever, for `B < Bstar` under the interface, and for `B < 8/9` unconditionally.
* `logCorridor_prescribed_diverges(_of_exclusion)` — no prescribed future confined to such a
  corridor can follow an odd anchor future forever.
* `matching_le_of_R_ne` / `logCorridor_matching_le_exit` — if the anchor future is outside the
  corridor at step `L` while the prescribed block is inside it, the prescribed matching is at most
  `U + L·log₂3`.
* `logCorridor_shadow_window_bound` — prescribed version of the quantitative window bound.

None of this proves EOC, `CriticalCrossing`, or the Collatz conjecture.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace LogCorridor

open Finset HarmonicPacking PrescribedMatching TransportCollapse PairValuation

/-- The logarithmic corridor `−B·log₂(n+1) − C ≤ R_n ≤ U` at step `n`. -/
def InLogCorridor (B C U : ℝ) (d : ℕ → ℕ) (n : ℕ) : Prop :=
  -B * Real.logb 2 ((n : ℝ) + 1) - C ≤ R d n ∧ R d n ≤ U

private theorem R_eq_of_agree {d e : ℕ → ℕ} {t : ℕ} (h : ∀ i < t, d i = e i) :
    R d t = R e t := by
  unfold R
  rw [s_eq_of_prefix_agree h]

/-! ## 1. Quantitative window bound (unconditional) -/

/-- **Harmonic window bound.** If `orbit M` is injective on `[0, N)` and stays above the floor
`−B log₂(k+1) − C` for every `k < N` (`B ≥ 0`), then
`N · N^(−B) · 2^(−C) ≤ 3M · e^(7/9) · N^(1/9)`. -/
theorem logFloor_window_bound (M N : ℕ) (hM : Odd M) (hN : 1 ≤ N)
    (hinj : ∀ i < N, ∀ j < N, orbit M i = orbit M j → i = j)
    (B C : ℝ) (hB : 0 ≤ B)
    (hfloor : ∀ k < N, -B * Real.logb 2 ((k : ℝ) + 1) - C ≤ R (orbWord M) k) :
    (N : ℝ) * ((N : ℝ) ^ (-B) * (2 : ℝ) ^ (-C))
      ≤ 3 * (M : ℝ) * (Real.exp (7 / 9) * (N : ℝ) ^ ((1 : ℝ) / 9)) := by
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM.pos
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  -- the floor value at the right end of the window, as a power
  have hwall : (2 : ℝ) ^ (-B * Real.logb 2 (N : ℝ) - C) = (N : ℝ) ^ (-B) * (2 : ℝ) ^ (-C) := by
    rw [sub_eq_add_neg, Real.rpow_add (by norm_num), mul_comm (-B),
      Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hNpos]
  -- every carry increment is at least the wall value divided by `3M`
  have hterm : ∀ i ∈ range N,
      (N : ℝ) ^ (-B) * (2 : ℝ) ^ (-C) / (3 * (M : ℝ))
        ≤ (2 : ℝ) ^ (R (orbWord M) (0 + i)) / (3 * (M : ℝ)) := by
    intro i hi
    have hi' : i < N := mem_range.mp hi
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [← hwall, zero_add]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hlog : Real.logb 2 ((i : ℝ) + 1) ≤ Real.logb 2 (N : ℝ) :=
      Real.logb_le_logb_of_le (by norm_num) (by positivity)
        (by exact_mod_cast (show i + 1 ≤ N by omega))
    have := hfloor i hi'
    nlinarith
  have hsum := sum_le_sum hterm
  rw [sum_const, card_range, nsmul_eq_mul] at hsum
  have htel := carryU_telescope M 0 hM N
  have hU0 : carryU M 0 = 1 := by simp [carryU]
  rw [hU0, zero_add] at htel
  have hUle := carryU_le M N hM hN hinj
  have hmain : (N : ℝ) * ((N : ℝ) ^ (-B) * (2 : ℝ) ^ (-C) / (3 * (M : ℝ)))
      ≤ Real.exp (7 / 9) * (N : ℝ) ^ ((1 : ℝ) / 9) := by linarith
  rw [mul_div_assoc'] at hmain
  rw [div_le_iff₀ (by positivity)] at hmain
  linarith

/-- The window bound in exponent form: `N^(8/9 − B) ≤ 3 e^(7/9) · 2^C · M`. -/
theorem logFloor_window_bound' (M N : ℕ) (hM : Odd M) (hN : 1 ≤ N)
    (hinj : ∀ i < N, ∀ j < N, orbit M i = orbit M j → i = j)
    (B C : ℝ) (hB : 0 ≤ B)
    (hfloor : ∀ k < N, -B * Real.logb 2 ((k : ℝ) + 1) - C ≤ R (orbWord M) k) :
    (N : ℝ) ^ ((8 : ℝ) / 9 - B) ≤ 3 * Real.exp (7 / 9) * (2 : ℝ) ^ C * (M : ℝ) := by
  have h := logFloor_window_bound M N hM hN hinj B C hB hfloor
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have h2C : (0 : ℝ) < (2 : ℝ) ^ C := by positivity
  have hsplit : (N : ℝ) * (N : ℝ) ^ (-B)
      = (N : ℝ) ^ ((8 : ℝ) / 9 - B) * (N : ℝ) ^ ((1 : ℝ) / 9) := by
    rw [← Real.rpow_add hNpos, show (8 : ℝ) / 9 - B + 1 / 9 = 1 + -B by ring,
      Real.rpow_add hNpos, Real.rpow_one]
  have hN9 : (0 : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 9) := by positivity
  have h2 : (2 : ℝ) ^ (-C) * (2 : ℝ) ^ C = 1 := by
    rw [← Real.rpow_add (by norm_num)]; simp
  have key : (N : ℝ) ^ ((8 : ℝ) / 9 - B) * (N : ℝ) ^ ((1 : ℝ) / 9)
      ≤ (3 * Real.exp (7 / 9) * (2 : ℝ) ^ C * (M : ℝ)) * (N : ℝ) ^ ((1 : ℝ) / 9) := by
    have h' : (N : ℝ) * (N : ℝ) ^ (-B) * (2 : ℝ) ^ (-C) * (2 : ℝ) ^ C
        ≤ 3 * (M : ℝ) * (Real.exp (7 / 9) * (N : ℝ) ^ ((1 : ℝ) / 9)) * (2 : ℝ) ^ C := by
      have := mul_le_mul_of_nonneg_right h h2C.le
      linarith [this]
    rw [mul_assoc ((N : ℝ) * _), h2, mul_one, hsplit] at h'
    linarith
  exact le_of_mul_le_mul_right key hN9

/-! ## 2. The external interface and its unconditional `8/9` instance -/

/-- **External logarithmic-floor exclusion at threshold `Bstar`**, in the form of the manuscript's
Thm 4.11: no injective (equivalently divergent) accelerated orbit satisfies
`R_n ≥ −B log₂ n − K` for all large `n`, for any `B < Bstar` and any constant `K`. For
`Bstar = 1/β*` this is the García–Tal/Curry consequence; it is an explicit hypothesis here. -/
def LogFloorExclusion (Bstar : ℝ) : Prop :=
  ∀ M : ℕ, Odd M → (∀ i j, orbit M i = orbit M j → i = j) →
    ∀ B : ℝ, B < Bstar → ∀ K : ℝ,
      ¬ ∃ N₀ : ℕ, ∀ n ≥ N₀, -B * Real.logb 2 (n : ℝ) - K ≤ R (orbWord M) n

/-- The interface holds unconditionally at `Bstar = 8/9` (from the repository's harmonic packing):
additive constants are absorbed by slightly increasing `B`. -/
theorem logFloorExclusion_eight_ninths : LogFloorExclusion (8 / 9) := by
  intro M hM hinj B hB K ⟨N₀, hfl⟩
  set B₀ : ℝ := max B 0 with hB₀
  set B₁ : ℝ := (B₀ + 8 / 9) / 2 with hB₁
  have hB₀lt : B₀ < 8 / 9 := max_lt hB (by norm_num)
  have hgap : 0 < B₁ - B₀ := by rw [hB₁]; linarith
  have hB₁lt : B₁ < 8 / 9 := by rw [hB₁]; linarith
  set K₀ : ℝ := max K 0 with hK₀
  set t : ℝ := K₀ / (B₁ - B₀) with ht
  set N₂ : ℕ := Nat.ceil ((2 : ℝ) ^ t) with hN₂
  apply injective_orbit_not_eventually_log_floor M hM hinj B₁ hB₁lt
  refine ⟨max (max N₀ N₂) 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hL0 : 0 ≤ Real.logb 2 (n : ℝ) := Real.logb_nonneg (by norm_num) (by exact_mod_cast hn1)
  have hLt : t ≤ Real.logb 2 (n : ℝ) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hnpos]
    have : (2 : ℝ) ^ t ≤ (N₂ : ℝ) := Nat.le_ceil _
    have hN₂n : (N₂ : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast le_trans (le_trans (le_max_right N₀ N₂) (le_max_left _ 1)) hn
    linarith
  have hK : K₀ ≤ (B₁ - B₀) * Real.logb 2 (n : ℝ) := by
    have := mul_le_mul_of_nonneg_left hLt hgap.le
    rw [ht, mul_div_cancel₀ _ hgap.ne'] at this
    linarith
  have hfln := hfl n (le_trans (le_trans (le_max_left N₀ N₂) (le_max_left _ 1)) hn)
  have hBB : B * Real.logb 2 (n : ℝ) ≤ B₀ * Real.logb 2 (n : ℝ) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hL0
  have hKK : K ≤ K₀ := le_max_left _ _
  nlinarith

/-! ## 3. Forced exit from logarithmic corridors -/

private theorem logb_succ_le (n : ℕ) (hn : 1 ≤ n) :
    Real.logb 2 ((n : ℝ) + 1) ≤ Real.logb 2 (n : ℝ) + 1 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h2n : Real.logb 2 (2 * (n : ℝ)) = 1 + Real.logb 2 (n : ℝ) := by
    rw [Real.logb_mul (by norm_num) hnpos.ne', Real.logb_self_eq_one (by norm_num)]
  have hle : Real.logb 2 ((n : ℝ) + 1) ≤ Real.logb 2 (2 * (n : ℝ)) :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity)
      (by have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          linarith)
  linarith

/-- **Forced exit, conditional form.** Under `LogFloorExclusion Bstar`, no odd seed has its whole
drift inside a logarithmic corridor with `B < Bstar`. -/
theorem exits_logCorridor_of_exclusion {Bstar : ℝ} (hX : LogFloorExclusion Bstar)
    (M : ℕ) (hM : Odd M) (B C U : ℝ) (hB : B < Bstar) :
    ¬ ∀ n, InLogCorridor B C U (orbWord M) n := by
  intro h
  by_cases hinj : ∀ i j, orbit M i = orbit M j → i = j
  · apply hX M hM hinj B hB (max B 0 + C)
    refine ⟨1, fun n hn => ?_⟩
    have hlow := (h n).1
    have hlog := logb_succ_le n hn
    have hmono : Real.logb 2 (n : ℝ) ≤ Real.logb 2 ((n : ℝ) + 1) :=
      Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hn) (by linarith)
    rcases le_total 0 B with hB0 | hB0
    · rw [max_eq_left hB0]
      nlinarith
    · rw [max_eq_right hB0]
      nlinarith
  · push Not at hinj
    obtain ⟨i, j, heq, hne⟩ := hinj
    obtain ⟨N, hN⟩ := noninjective_orbit_not_upper_confined U M hM ⟨i, j, hne, heq⟩
    exact hN (fun k _ => (h k).2)

/-- **Forced exit, unconditional for `B < 8/9`.** -/
theorem exits_logCorridor (M : ℕ) (hM : Odd M) (B C U : ℝ) (hB : B < 8 / 9) :
    ¬ ∀ n, InLogCorridor B C U (orbWord M) n :=
  exits_logCorridor_of_exclusion logFloorExclusion_eight_ninths M hM B C U hB

/-! ## 4. Translation to prescribed matching -/

/-- Under `LogFloorExclusion Bstar`, no prescribed future confined to a logarithmic corridor with
`B < Bstar` agrees with an odd anchor future at every digit. -/
theorem logCorridor_prescribed_diverges_of_exclusion {Bstar : ℝ} (hX : LogFloorExclusion Bstar)
    (d e : ℕ → ℕ) (j : ℕ) (hodd : Odd (anchorState d j)) (B C U : ℝ) (hB : B < Bstar)
    (he : ∀ n, InLogCorridor B C U e n) :
    ∃ i, anchorWord d j i ≠ e i := by
  by_contra hno
  push Not at hno
  apply exits_logCorridor_of_exclusion hX (anchorState d j) hodd B C U hB
  intro n
  have hR : R (orbWord (anchorState d j)) n = R e n := R_eq_of_agree (fun i _ => hno i)
  unfold InLogCorridor
  rw [hR]
  exact he n

/-- Unconditional version for `B < 8/9`. -/
theorem logCorridor_prescribed_diverges (d e : ℕ → ℕ) (j : ℕ) (hodd : Odd (anchorState d j))
    (B C U : ℝ) (hB : B < 8 / 9) (he : ∀ n, InLogCorridor B C U e n) :
    ∃ i, anchorWord d j i ≠ e i :=
  logCorridor_prescribed_diverges_of_exclusion logFloorExclusion_eight_ninths d e j hodd B C U hB
    he

/-- **Matching bound from a drift mismatch.** If a positive block `e` (length `m`) keeps
`R ≤ U` through `m` and its drift at some `L ≤ m` differs from the anchor future's, then the
prescribed matching is at most `U + L·log₂3`. -/
theorem matching_le_of_R_ne (d e : ℕ → ℕ) (j m L : ℕ) (U : ℝ) (hLm : L ≤ m)
    (he_pos : ∀ i < m, 1 ≤ e i) (hU : ∀ n ≤ m, R e n ≤ U)
    (hne : R e L ≠ R (anchorWord d j) L) :
    ((padicValInt 2 ((leastRealizer e m : ℤ) - anchorState d j) : ℕ) : ℝ)
      ≤ U + (L : ℝ) * alpha := by
  classical
  have hex : ∃ i, anchorWord d j i ≠ e i ∧ i < L := by
    by_contra hno
    push Not at hno
    apply hne
    refine (R_eq_of_agree (fun i hi => ?_)).symm
    by_contra h
    exact absurd (hno i h) (by omega)
  set k := Nat.find hex with hkdef
  have hkspec := Nat.find_spec hex
  have hkmin : ∀ i < k, anchorWord d j i = e i := by
    intro i hi
    by_contra h
    exact Nat.find_min hex hi ⟨h, by omega⟩
  rw [prescribed_matching_split d e j m k (by omega) he_pos hkmin hkspec.1]
  have hmin : S e k + min (anchorWord d j k) (e k) ≤ s e (k + 1) := by
    rw [s_succ]
    have := min_le_right (anchorWord d j k) (e k)
    unfold S
    omega
  have hRk := hU (k + 1) (by omega)
  unfold R at hRk
  have hα : 0 < alpha := lt_trans one_pos one_lt_alpha
  have hkL : ((k + 1 : ℕ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast (show k + 1 ≤ L by omega)
  calc ((S e k + min (anchorWord d j k) (e k) : ℕ) : ℝ)
      ≤ (s e (k + 1) : ℝ) := by exact_mod_cast hmin
    _ ≤ U + ((k + 1 : ℕ) : ℝ) * alpha := by linarith
    _ ≤ U + (L : ℝ) * alpha := by nlinarith

/-- **Log-corridor matching bound at the anchor's exit step.** If the anchor future is outside the
corridor at step `L` while a positive prescribed block `e` (length `m ≥ L`) is inside it at every
step `≤ m`, then the prescribed matching is at most `U + L·log₂3`. -/
theorem logCorridor_matching_le_exit (d e : ℕ → ℕ) (j m L : ℕ) (B C U : ℝ) (hLm : L ≤ m)
    (he_pos : ∀ i < m, 1 ≤ e i) (he : ∀ n ≤ m, InLogCorridor B C U e n)
    (hexit : ¬ InLogCorridor B C U (anchorWord d j) L) :
    ((padicValInt 2 ((leastRealizer e m : ℤ) - anchorState d j) : ℕ) : ℝ)
      ≤ U + (L : ℝ) * alpha := by
  apply matching_le_of_R_ne d e j m L U hLm he_pos (fun n hn => (he n hn).2)
  intro hReq
  apply hexit
  unfold InLogCorridor
  rw [← hReq]
  exact he L hLm

/-- **Prescribed window bound.** A prescribed future with log floor `−B log₂(k+1) − C` (`B ≥ 0`)
that follows the anchor future on `[0, N)`, along an anchor orbit injective on `[0, N)`, forces
`N^(8/9 − B) ≤ 3 e^(7/9) · 2^C · μ_j`. -/
theorem logCorridor_shadow_window_bound (d e : ℕ → ℕ) (j N : ℕ) (hN : 1 ≤ N)
    (hodd : Odd (anchorState d j)) (hagree : ∀ i < N, anchorWord d j i = e i)
    (hinj : ∀ i < N, ∀ i' < N, orbit (anchorState d j) i = orbit (anchorState d j) i' → i = i')
    (B C : ℝ) (hB : 0 ≤ B) (hfloor : ∀ k < N, -B * Real.logb 2 ((k : ℝ) + 1) - C ≤ R e k) :
    (N : ℝ) ^ ((8 : ℝ) / 9 - B) ≤ 3 * Real.exp (7 / 9) * (2 : ℝ) ^ C * (anchorState d j : ℝ) := by
  apply logFloor_window_bound' (anchorState d j) N hodd hN hinj B C hB
  intro k hk
  have h := hfloor k hk
  have hR : R (orbWord (anchorState d j)) k = R e k :=
    R_eq_of_agree (fun i hi => hagree i (by omega))
  rw [hR]
  exact h

end LogCorridor
end EOC
