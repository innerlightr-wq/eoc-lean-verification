import EOC.TaoLike.NormalizedHarmonicLaw

/-!
# Harmonic exceptional-set summability (Milestone 13)

Converts the finite all-shifts persistence theorem (`all_shifts_averaged_persistence_finite_
normalized`, Milestones 11–12) into a genuine summability statement over dyadic seed windows
`[2^L, 2^(L+1))`: the normalized-probability of *some* shift `t < Ttotal(L)` producing a
persistent length-`n(L)` future block decays fast enough in the scale `L` to be summable.

**STRATEGIC PURPOSE.** Beyond the technical summability statement, this file audits whether the
result already supports a "soft-EOC" route eliminating a hypothetical divergent orbit. It does
**not** — see Part 6 (the soft-EOC audit) for the precise reason: summability is a statement
about the seed *ensemble* under the harmonic law, not about any single deterministic orbit.

**EPISTEMIC STATUS.** The main theorem (`harmonic_exceptional_summability`) is a GENERIC
structural theorem: it takes the scale-dependent parameterizations `n, Tearly, Ttotal, sMaxNat,
Q, Qpre, Qearly : ℕ → ℕ` and the Tao witnesses `Kfuture, Kearly, Kprefix` (held FIXED across all
scales `L`) as explicit inputs, together with explicit growth-rate hypotheses on the
parameterizations and the same kind of external Tao residue-closeness/information-budget
hypotheses used throughout Milestones 7–12 (now asserted uniformly for every `L ≥ L0`). No
concrete closed-form choice of these parameterizations satisfying every hypothesis
simultaneously (for arbitrary given `c0, cPrefix, c0early`) is exhibited — doing so is a
separate, genuinely delicate numerical-parameter-region exercise (see the final report). This
file proves the STRUCTURAL fact: *given* valid parameterizations, the resulting exceptional
probabilities are summable. `Real.log`/`Nat.log` do not appear; all scale bookkeeping is by the
natural number `L` and the fixed base `2`.

Nothing here proves EOC, FOP, pointwise orbit divergence-elimination, or the Collatz
conjecture. Tao's mixing theorem remains an explicit external hypothesis throughout.
-/

namespace EOC
namespace TaoExternal

open Finset

/-! ## Part 1: the dyadic scale-`L` exceptional event -/

/-- **Dyadic persistence exceptional event.** Seeds in `[2^L, 2^(L+1))` for which some shift
`t < Ttotal` has its restarted length-`n` future block persist below `c` — literally
`allShiftsPersistenceEvent`, reused rather than duplicated. -/
abbrev dyadicPersistenceExceptionalEvent (Ttotal n : ℕ) (c : ℝ) : Set ℕ :=
  allShiftsPersistenceEvent Ttotal n c

/-! ## Part 2: dyadic window mass positivity -/

/-- **Dyadic window mass positivity, for `L ≥ 1`.** `2^L + 1` is an odd witness inside
`[2^L, 2^(L+1))` for every `L ≥ 1` — note `2^L` itself is even for `L ≥ 1`, so
`harmonicWindowMass_pos_of_odd_left` (which needs the *left endpoint* odd) does not apply
directly; the witness used here is the next integer up. (`L = 0` gives the degenerate window
`[1,2)`, whose only point `1` is already an odd left endpoint — not needed downstream, since
the summability theorem only ever concerns sufficiently large `L`.) -/
theorem harmonicWindowMass_dyadic_pos (L : ℕ) (hL : 1 ≤ L) :
    0 < harmonicWindowMass (2 ^ L) (2 ^ L + 2 ^ L) := by
  have h2L : 2 ≤ 2 ^ L := by
    calc (2:ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hL
  have heven : Even (2 ^ L) := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hL
    rw [hk, pow_add, pow_one]
    exact ⟨2 ^ k, by ring⟩
  have hodd : Odd (2 ^ L + 1) := heven.add_one
  have hle : 2 ^ L ≤ 2 ^ L + 1 := Nat.le_succ _
  have hlt : 2 ^ L + 1 < 2 ^ L + 2 ^ L := by omega
  exact harmonicWindowMass_pos_of_mem (2 ^ L) (2 ^ L + 2 ^ L) (2 ^ L + 1) hle hlt hodd

/-! ## Part 3: generic geometric/polynomial-geometric summability (Mathlib reuse) -/

/-- **Linear-times-geometric summability.** `Summable (fun L => (C:ℝ) * ((L:ℝ) + 1) * r ^ L)` for
`0 ≤ r < 1` and any constant `C` — a direct combination of Mathlib's
`summable_pow_mul_geometric_of_norm_lt_one` (for the `L * r^L` piece) and
`summable_geometric_of_lt_one` (for the `r^L` piece), with no geometric series reproved from
scratch. -/
theorem summable_const_mul_succ_mul_geometric (C r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun L : ℕ => C * ((L : ℝ) + 1) * r ^ L) := by
  have hnorm : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have h1 : Summable (fun L : ℕ => (L : ℝ) * r ^ L) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
  have h2 : Summable (fun L : ℕ => r ^ L) := summable_geometric_of_lt_one hr0 hr1
  have h3 : Summable (fun L : ℕ => (L : ℝ) * r ^ L + r ^ L) := h1.add h2
  have heq : (fun L : ℕ => C * ((L : ℝ) + 1) * r ^ L)
      = fun L : ℕ => C * ((L : ℝ) * r ^ L + r ^ L) := by
    funext L; ring
  rw [heq]
  exact h3.mul_left C

/-- **Linear-times-geometric summability, without the `+1`.** `Summable (fun L => C * L * r^L)`
for `0 ≤ r < 1` — the direct `summable_pow_mul_geometric_of_norm_lt_one` instance. -/
theorem summable_const_mul_mul_geometric (C r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun L : ℕ => C * (L : ℝ) * r ^ L) := by
  have hnorm : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have h1 : Summable (fun L : ℕ => (L : ℝ) * r ^ L) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
  simpa [mul_assoc] using h1.mul_left C

/-! ## Part 4: `I0 > 0` -/

/-- The iid persistence bit-rate `I0` is strictly positive — follows directly from
`rateNats_pos` and `rateNats_eq_I0_mul_log_two`. Not previously stated as a standalone
theorem; needed here to get a genuine geometric base `< 1` for the iid decay term. -/
theorem I0_pos : 0 < I0 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have heq := rateNats_eq_I0_mul_log_two
  nlinarith [rateNats_pos, heq, hlog2]

/-! ## Part 5: auditing the BAD-tail mgf term's sign -/

/-- **`geomUpperMgf theta > 1` for every valid tilt.** Audited explicitly (per the task's
warning): since `exp(theta) > 1` for `theta > 0`, the numerator `2·exp(theta) - 2` of
`geomUpperMgf theta - 1` is positive, and the denominator `2 - exp(theta)` is positive by
`theta < log 2`. Consequently `(geomUpperMgf theta)^t` is *increasing*, not decreasing, in `t` —
exactly the reason the BAD-tail term needs `sMaxNat` to dominate `Ttotal`, not merely to be
positive. -/
theorem geomUpperMgf_gt_one (theta : ℝ) (hθ0 : 0 < theta) (hθ1 : theta < Real.log 2) :
    1 < geomUpperMgf theta := by
  unfold geomUpperMgf
  have hexp1 : 1 < Real.exp theta := by
    calc (1:ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ < Real.exp theta := Real.exp_lt_exp.mpr hθ0
  have hexp2 : Real.exp theta < 2 := by
    calc Real.exp theta < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr hθ1
      _ = 2 := Real.exp_log (by norm_num)
  rw [lt_div_iff₀ (by linarith)]
  linarith

/-! ## Part 6: the scale-`L` probability bound (crude worst-shift bound, `× Ttotal L`) -/

/-- **Dyadic persistence probability bound at scale `L`.** Direct application of
`all_shifts_averaged_persistence_finite_normalized` (with `Y := 2^L`, `H := 2^L`, `η := 1`),
followed by bounding each of the two finite `Finset.sum`s by (number of shifts) × (worst-case
per-shift value): the EARLY-sum's Tao error is largest at `t = 0`, the LATE-sum's `Kprefix`
error is largest at `t = Tearly L` (smallest `t` in range), and the LATE-sum's mgf term is
largest at `t = Ttotal L - 1` (largest `t` in range, since `geomUpperMgf theta > 1` makes it
*increasing* in `t` — audited in `geomUpperMgf_gt_one`). No GOOD/BAD mathematics is re-derived;
this is pure Finset/monotonicity bookkeeping on top of the already-proved M11/M12 bound. -/
theorem dyadic_persistence_probability_bound
    (n Tearly Ttotal sMaxNat Q Qpre Qearly : ℕ → ℕ)
    (L : ℕ) (hL : 1 ≤ L)
    (c : ℝ)
    (c0 : ℝ) (Kfuture : TaoMixingConstants c0) (hKfuture : TaoMixingProperty c0 Kfuture)
    (theta : ℝ) (hθ0 : 0 < theta) (hθ1 : theta < Real.log 2)
    (cPrefix : ℝ) (hcPrefix : 0 < cPrefix)
    (Kprefix : TaoMixingConstants cPrefix) (hKprefix : TaoMixingProperty cPrefix Kprefix)
    (c0early : ℝ) (hc0early : 0 < c0early)
    (Kearly : TaoMixingConstants c0early) (hKearly : TaoMixingProperty c0early Kearly)
    (hn : 1 ≤ n L)
    (hTearly_pos : 1 ≤ Tearly L)
    (hTle : Tearly L ≤ Ttotal L)
    (hthick : 4 * (2 : ℝ) ^ (sMaxNat L + 1) ≤ (2 : ℝ) ^ L)
    (hQ1 : 1 ≤ Q L)
    (hQrel : (Q L : ℝ) ≥ (2 + c0) * (n L : ℝ))
    (hbudget_param : 2 * (1 + 1 / (1 : ℝ)) * (2 : ℝ) ^ (sMaxNat L + 2 * Q L)
      ≤ Kfuture.Cres * (2 : ℝ) ^ L)
    (hQpre1 : 1 ≤ Qpre L)
    (hQprerel_uniform : (Qpre L : ℝ) ≥ (2 + cPrefix) * (Ttotal L : ℝ))
    (hresidue_prefix : taoL1TV
        (pushforward (genEventProb (normalizedHarmonicWindowWeight (2 ^ L) (2 ^ L + 2 ^ L)))
          (fun m => (m : ZMod (2 ^ Qpre L))))
        (unifOddResidues (Qpre L))
      ≤ Kprefix.Cres * (2 : ℝ) ^ (-(Qpre L : ℝ)))
    (hQrel_early_uniform : (Qearly L : ℝ) ≥ (2 + c0early) * ((Tearly L + n L : ℕ) : ℝ))
    (hresidue_early : taoL1TV
        (pushforward (genEventProb (normalizedHarmonicWindowWeight (2 ^ L) (2 ^ L + 2 ^ L)))
          (fun m => (m : ZMod (2 ^ Qearly L)))) (unifOddResidues (Qearly L))
      ≤ Kearly.Cres * (2 : ℝ) ^ (-(Qearly L : ℝ))) :
    genEventProb (normalizedHarmonicWindowWeight (2 ^ L) (2 ^ L + 2 ^ L))
        (dyadicPersistenceExceptionalEvent (Ttotal L) (n L) c)
      ≤ (Ttotal L : ℝ) *
        (2 * Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n L : ℝ)))
          + Kearly.A * (2 : ℝ) ^ (-(Kearly.c1 * (n L : ℝ)))
          + Kfuture.A * (2 : ℝ) ^ (-(Kfuture.c1 * (n L : ℝ)))
          + Real.exp (-(theta * (sMaxNat L : ℝ))) * (geomUpperMgf theta) ^ (Ttotal L)
          + Kprefix.A * (2 : ℝ) ^ (-(Kprefix.c1 * (Tearly L : ℝ)))) := by
  have hYpos : 0 < 2 ^ L := by positivity
  have hMpos : 0 < harmonicWindowMass (2 ^ L) (2 ^ L + 2 ^ L) := harmonicWindowMass_dyadic_pos L hL
  have hthick' : 4 * (2 : ℝ) ^ (sMaxNat L + 1) ≤ (1 : ℝ) * ((2 ^ L : ℕ) : ℝ) := by
    push_cast; rw [one_mul]; exact hthick
  have hHη : (1 : ℝ) * ((2 ^ L : ℕ) : ℝ) ≤ ((2 ^ L : ℕ) : ℝ) := by rw [one_mul]
  have hsmall : 2 ^ (sMaxNat L + 1) ≤ 2 ^ L := by
    have hnn : (0:ℝ) ≤ (2 : ℝ) ^ (sMaxNat L + 1) := by positivity
    have hR : (2 : ℝ) ^ (sMaxNat L + 1) ≤ (2 : ℝ) ^ L := by linarith [hthick, hnn]
    exact_mod_cast hR
  have hbudget_param' : 2 * (1 + 1 / (1:ℝ)) * (2 : ℝ) ^ (sMaxNat L + 2 * Q L)
      ≤ Kfuture.Cres * ((2 ^ L : ℕ) : ℝ) := by push_cast; exact hbudget_param
  have hraw := all_shifts_averaged_persistence_finite_normalized (2 ^ L) (2 ^ L) hYpos hMpos
    (Tearly L) (Ttotal L) hTearly_pos hTle (n L) hn c (sMaxNat L) hsmall 1 one_pos hHη
    hthick' c0 (Q L) hQ1 hQrel Kfuture hKfuture hbudget_param' theta hθ0 hθ1 cPrefix hcPrefix
    (Qpre L) hQpre1 hQprerel_uniform Kprefix hKprefix hresidue_prefix c0early hc0early Kearly
    hKearly (Qearly L) hQrel_early_uniform hresidue_early
  -- Bound the EARLY sum by (count) × (worst-case value, at t = 0).
  have hearly_le : ∑ t ∈ range (Tearly L),
        (Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n L : ℝ)))
        + Kearly.A * (2 : ℝ) ^ (-(Kearly.c1 * ((t + n L : ℕ) : ℝ))))
      ≤ (Tearly L : ℝ) * (Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n L : ℝ)))
          + Kearly.A * (2 : ℝ) ^ (-(Kearly.c1 * (n L : ℝ)))) := by
    have hpt : ∀ t ∈ range (Tearly L), Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n L : ℝ)))
          + Kearly.A * (2 : ℝ) ^ (-(Kearly.c1 * ((t + n L : ℕ) : ℝ)))
        ≤ Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n L : ℝ)))
          + Kearly.A * (2 : ℝ) ^ (-(Kearly.c1 * (n L : ℝ))) := by
      intro t _
      have hexp_le : -(Kearly.c1 * ((t + n L : ℕ) : ℝ)) ≤ -(Kearly.c1 * (n L : ℝ)) := by
        push_cast
        nlinarith [Kearly.hc1, Nat.cast_nonneg (α := ℝ) t]
      have hpow_le : (2 : ℝ) ^ (-(Kearly.c1 * ((t + n L : ℕ) : ℝ)))
          ≤ (2 : ℝ) ^ (-(Kearly.c1 * (n L : ℝ))) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_le
      linarith [mul_le_mul_of_nonneg_left hpow_le Kearly.hA.le]
    calc ∑ t ∈ range (Tearly L), (Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n L : ℝ)))
            + Kearly.A * (2 : ℝ) ^ (-(Kearly.c1 * ((t + n L : ℕ) : ℝ))))
        ≤ ∑ _t ∈ range (Tearly L), (Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n L : ℝ)))
            + Kearly.A * (2 : ℝ) ^ (-(Kearly.c1 * (n L : ℝ)))) := Finset.sum_le_sum hpt
      _ = (Tearly L : ℝ) * (Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n L : ℝ)))
          + Kearly.A * (2 : ℝ) ^ (-(Kearly.c1 * (n L : ℝ)))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- Bound the LATE sum by (count) × (worst-case value: `Kprefix` term at `t = Tearly L`, mgf
  -- term at `t = Ttotal L`, since `geomUpperMgf theta > 1` makes it increasing in `t`).
  have hMlate_nonneg : 0 ≤ Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n L : ℝ)))
      + Kfuture.A * (2 : ℝ) ^ (-(Kfuture.c1 * (n L : ℝ)))
      + Real.exp (-(theta * (sMaxNat L : ℝ))) * (geomUpperMgf theta) ^ (Ttotal L)
      + Kprefix.A * (2 : ℝ) ^ (-(Kprefix.c1 * (Tearly L : ℝ))) := by
    have h1 : 0 ≤ Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n L : ℝ))) := by positivity
    have h2 : 0 ≤ Kfuture.A * (2 : ℝ) ^ (-(Kfuture.c1 * (n L : ℝ))) :=
      mul_nonneg Kfuture.hA.le (by positivity)
    have hmgf_nonneg : 0 ≤ geomUpperMgf theta := by
      linarith [geomUpperMgf_gt_one theta hθ0 hθ1]
    have h3 : 0 ≤ Real.exp (-(theta * (sMaxNat L : ℝ))) * (geomUpperMgf theta) ^ (Ttotal L) :=
      mul_nonneg (Real.exp_pos _).le (pow_nonneg hmgf_nonneg _)
    have h4 : 0 ≤ Kprefix.A * (2 : ℝ) ^ (-(Kprefix.c1 * (Tearly L : ℝ))) :=
      mul_nonneg Kprefix.hA.le (by positivity)
    linarith
  have hlate_le : ∑ t ∈ Ico (Tearly L) (Ttotal L),
        ((Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n L : ℝ)))
            + Kfuture.A * (2 : ℝ) ^ (-(Kfuture.c1 * (n L : ℝ))))
          + (Real.exp (-(theta * (sMaxNat L : ℝ))) * (geomUpperMgf theta) ^ t
            + Kprefix.A * (2 : ℝ) ^ (-(Kprefix.c1 * (t : ℝ)))))
      ≤ (Ttotal L : ℝ) * (Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n L : ℝ)))
          + Kfuture.A * (2 : ℝ) ^ (-(Kfuture.c1 * (n L : ℝ)))
          + Real.exp (-(theta * (sMaxNat L : ℝ))) * (geomUpperMgf theta) ^ (Ttotal L)
          + Kprefix.A * (2 : ℝ) ^ (-(Kprefix.c1 * (Tearly L : ℝ)))) := by
    have hmgf1 : 1 ≤ geomUpperMgf theta := (geomUpperMgf_gt_one theta hθ0 hθ1).le
    have hpt : ∀ t ∈ Ico (Tearly L) (Ttotal L),
        (Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n L : ℝ)))
            + Kfuture.A * (2 : ℝ) ^ (-(Kfuture.c1 * (n L : ℝ))))
          + (Real.exp (-(theta * (sMaxNat L : ℝ))) * (geomUpperMgf theta) ^ t
            + Kprefix.A * (2 : ℝ) ^ (-(Kprefix.c1 * (t : ℝ))))
        ≤ Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n L : ℝ)))
          + Kfuture.A * (2 : ℝ) ^ (-(Kfuture.c1 * (n L : ℝ)))
          + Real.exp (-(theta * (sMaxNat L : ℝ))) * (geomUpperMgf theta) ^ (Ttotal L)
          + Kprefix.A * (2 : ℝ) ^ (-(Kprefix.c1 * (Tearly L : ℝ))) := by
      intro t htI
      obtain ⟨ht1, ht2⟩ := Finset.mem_Ico.mp htI
      have hmgf_le : (geomUpperMgf theta) ^ t ≤ (geomUpperMgf theta) ^ (Ttotal L) :=
        pow_le_pow_right₀ hmgf1 ht2.le
      have hprefix_exp_le : -(Kprefix.c1 * (t : ℝ)) ≤ -(Kprefix.c1 * (Tearly L : ℝ)) := by
        have : (Tearly L : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht1
        nlinarith [Kprefix.hc1, this]
      have hprefix_pow_le : (2 : ℝ) ^ (-(Kprefix.c1 * (t : ℝ)))
          ≤ (2 : ℝ) ^ (-(Kprefix.c1 * (Tearly L : ℝ))) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hprefix_exp_le
      have hmgf_term_le : Real.exp (-(theta * (sMaxNat L : ℝ))) * (geomUpperMgf theta) ^ t
          ≤ Real.exp (-(theta * (sMaxNat L : ℝ))) * (geomUpperMgf theta) ^ (Ttotal L) :=
        mul_le_mul_of_nonneg_left hmgf_le (Real.exp_pos _).le
      have hprefix_term_le : Kprefix.A * (2 : ℝ) ^ (-(Kprefix.c1 * (t : ℝ)))
          ≤ Kprefix.A * (2 : ℝ) ^ (-(Kprefix.c1 * (Tearly L : ℝ))) :=
        mul_le_mul_of_nonneg_left hprefix_pow_le Kprefix.hA.le
      linarith [hmgf_term_le, hprefix_term_le]
    calc ∑ t ∈ Ico (Tearly L) (Ttotal L),
          ((Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n L : ℝ)))
              + Kfuture.A * (2 : ℝ) ^ (-(Kfuture.c1 * (n L : ℝ))))
            + (Real.exp (-(theta * (sMaxNat L : ℝ))) * (geomUpperMgf theta) ^ t
              + Kprefix.A * (2 : ℝ) ^ (-(Kprefix.c1 * (t : ℝ)))))
        ≤ ∑ _t ∈ Ico (Tearly L) (Ttotal L),
            (Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n L : ℝ)))
              + Kfuture.A * (2 : ℝ) ^ (-(Kfuture.c1 * (n L : ℝ)))
              + Real.exp (-(theta * (sMaxNat L : ℝ))) * (geomUpperMgf theta) ^ (Ttotal L)
              + Kprefix.A * (2 : ℝ) ^ (-(Kprefix.c1 * (Tearly L : ℝ)))) := Finset.sum_le_sum hpt
      _ = ((Ttotal L - Tearly L : ℕ) : ℝ) *
            (Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n L : ℝ)))
              + Kfuture.A * (2 : ℝ) ^ (-(Kfuture.c1 * (n L : ℝ)))
              + Real.exp (-(theta * (sMaxNat L : ℝ))) * (geomUpperMgf theta) ^ (Ttotal L)
              + Kprefix.A * (2 : ℝ) ^ (-(Kprefix.c1 * (Tearly L : ℝ)))) := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ ≤ (Ttotal L : ℝ) *
            (Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n L : ℝ)))
              + Kfuture.A * (2 : ℝ) ^ (-(Kfuture.c1 * (n L : ℝ)))
              + Real.exp (-(theta * (sMaxNat L : ℝ))) * (geomUpperMgf theta) ^ (Ttotal L)
              + Kprefix.A * (2 : ℝ) ^ (-(Kprefix.c1 * (Tearly L : ℝ)))) := by
        apply mul_le_mul_of_nonneg_right _ hMlate_nonneg
        have : (Ttotal L - Tearly L : ℕ) ≤ Ttotal L := Nat.sub_le _ _
        exact_mod_cast this
  have hTearly_le_Ttotal_R : (Tearly L : ℝ) ≤ (Ttotal L : ℝ) := by exact_mod_cast hTle
  have hMearly_nonneg : 0 ≤ Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n L : ℝ)))
      + Kearly.A * (2 : ℝ) ^ (-(Kearly.c1 * (n L : ℝ))) := by
    have h1 : 0 ≤ Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n L : ℝ))) := by positivity
    have h2 : 0 ≤ Kearly.A * (2 : ℝ) ^ (-(Kearly.c1 * (n L : ℝ))) :=
      mul_nonneg Kearly.hA.le (by positivity)
    linarith
  have hearly_le' : (Tearly L : ℝ) * (Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n L : ℝ)))
        + Kearly.A * (2 : ℝ) ^ (-(Kearly.c1 * (n L : ℝ))))
      ≤ (Ttotal L : ℝ) * (Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n L : ℝ)))
        + Kearly.A * (2 : ℝ) ^ (-(Kearly.c1 * (n L : ℝ)))) :=
    mul_le_mul_of_nonneg_right hTearly_le_Ttotal_R hMearly_nonneg
  linarith [hraw, hearly_le, hlate_le, hearly_le']

/-! ## Part 7: the main dyadic exceptional-set summability theorem -/

/-- Converts a real-linear-in-`L` exponent of `2` into an ordinary natural power of a fixed
base — the bridge letting each Tao-error term's `rpow` bound become a genuine geometric term
`ρ^L` amenable to `summable_pow_mul_geometric_of_norm_lt_one`. -/
theorem rpow_two_neg_mul_nat_eq_pow (a : ℝ) (L : ℕ) :
    (2 : ℝ) ^ (-(a * (L : ℝ))) = ((2 : ℝ) ^ (-a)) ^ L := by
  rw [show -(a * (L : ℝ)) = (-a) * (L : ℝ) by ring, Real.rpow_mul (by norm_num), Real.rpow_natCast]

/-- **Main theorem: dyadic harmonic exceptional-set summability.** Under a GENERIC
parameterization `n, Tearly, Ttotal, sMaxNat, Q, Qpre, Qearly : ℕ → ℕ` (holding the Tao
witnesses `Kfuture, Kearly, Kprefix` FIXED across all scales `L`), with:
* the same per-`L` structural/Tao hypotheses `all_shifts_averaged_persistence_finite_normalized`
  needs, asserted uniformly for every `L ≥ L0`;
* explicit positive linear growth rates `an` (for `n`), `at'` (for `Tearly`), and `abad` (the
  net BAD-tail decay rate, audited explicitly via `hbad_rate` per the task's warning about
  `geomUpperMgf theta > 1`);
* the crude bound `Ttotal L ≤ L` (giving an `O(L)` shift-count prefactor),

the resulting dyadic exceptional probabilities are summable in the scale `L`. No GOOD/BAD
mathematics, no Tao mixing theorem, and no new residue-closeness fact is (re-)proved here —
only `dyadic_persistence_probability_bound`'s crude per-`L` bound is combined with the growth
hypotheses into five explicit geometric-times-linear terms, each summable via
`summable_const_mul_mul_geometric`. -/
theorem harmonic_exceptional_summability
    (n Tearly Ttotal sMaxNat Q Qpre Qearly : ℕ → ℕ)
    (L0 : ℕ) (hL0 : 1 ≤ L0)
    (an at' abad : ℝ) (han : 0 < an) (hat' : 0 < at') (habad : 0 < abad)
    (c : ℝ)
    (c0 : ℝ) (Kfuture : TaoMixingConstants c0) (hKfuture : TaoMixingProperty c0 Kfuture)
    (theta : ℝ) (hθ0 : 0 < theta) (hθ1 : theta < Real.log 2)
    (cPrefix : ℝ) (hcPrefix : 0 < cPrefix)
    (Kprefix : TaoMixingConstants cPrefix) (hKprefix : TaoMixingProperty cPrefix Kprefix)
    (c0early : ℝ) (hc0early : 0 < c0early)
    (Kearly : TaoMixingConstants c0early) (hKearly : TaoMixingProperty c0early Kearly)
    (hn_growth : ∀ L, L0 ≤ L → an * (L : ℝ) ≤ (n L : ℝ))
    (hTearly_growth : ∀ L, L0 ≤ L → at' * (L : ℝ) ≤ (Tearly L : ℝ))
    (hn1 : ∀ L, L0 ≤ L → 1 ≤ n L)
    (hTearly_pos : ∀ L, L0 ≤ L → 1 ≤ Tearly L)
    (hTle : ∀ L, L0 ≤ L → Tearly L ≤ Ttotal L)
    (hTtotal_le : ∀ L, L0 ≤ L → Ttotal L ≤ L)
    (hthick : ∀ L, L0 ≤ L → 4 * (2 : ℝ) ^ (sMaxNat L + 1) ≤ (2 : ℝ) ^ L)
    (hQ1 : ∀ L, L0 ≤ L → 1 ≤ Q L)
    (hQrel : ∀ L, L0 ≤ L → (Q L : ℝ) ≥ (2 + c0) * (n L : ℝ))
    (hbudget_param : ∀ L, L0 ≤ L →
      2 * (1 + 1 / (1 : ℝ)) * (2 : ℝ) ^ (sMaxNat L + 2 * Q L) ≤ Kfuture.Cres * (2 : ℝ) ^ L)
    (hQpre1 : ∀ L, L0 ≤ L → 1 ≤ Qpre L)
    (hQprerel_uniform : ∀ L, L0 ≤ L → (Qpre L : ℝ) ≥ (2 + cPrefix) * (Ttotal L : ℝ))
    (hresidue_prefix : ∀ L, L0 ≤ L → taoL1TV
        (pushforward (genEventProb (normalizedHarmonicWindowWeight (2 ^ L) (2 ^ L + 2 ^ L)))
          (fun m => (m : ZMod (2 ^ Qpre L))))
        (unifOddResidues (Qpre L))
      ≤ Kprefix.Cres * (2 : ℝ) ^ (-(Qpre L : ℝ)))
    (hQrel_early_uniform : ∀ L, L0 ≤ L →
      (Qearly L : ℝ) ≥ (2 + c0early) * ((Tearly L + n L : ℕ) : ℝ))
    (hresidue_early : ∀ L, L0 ≤ L → taoL1TV
        (pushforward (genEventProb (normalizedHarmonicWindowWeight (2 ^ L) (2 ^ L + 2 ^ L)))
          (fun m => (m : ZMod (2 ^ Qearly L)))) (unifOddResidues (Qearly L))
      ≤ Kearly.Cres * (2 : ℝ) ^ (-(Qearly L : ℝ)))
    (hbad_rate : ∀ L, L0 ≤ L →
      theta * (sMaxNat L : ℝ) - (Ttotal L : ℝ) * Real.log (geomUpperMgf theta) ≥ abad * (L : ℝ)) :
    Summable (fun L : ℕ => if L < L0 then (0 : ℝ) else
      genEventProb (normalizedHarmonicWindowWeight (2 ^ L) (2 ^ L + 2 ^ L))
        (dyadicPersistenceExceptionalEvent (Ttotal L) (n L) c)) := by
  set ρ1 : ℝ := (2 : ℝ) ^ (-(I0 * an)) with hρ1_def
  set ρ2 : ℝ := (2 : ℝ) ^ (-(Kearly.c1 * an)) with hρ2_def
  set ρ3 : ℝ := (2 : ℝ) ^ (-(Kfuture.c1 * an)) with hρ3_def
  set ρ4 : ℝ := Real.exp (-abad) with hρ4_def
  set ρ5 : ℝ := (2 : ℝ) ^ (-(Kprefix.c1 * at')) with hρ5_def
  have hρ1_mem : 0 ≤ ρ1 ∧ ρ1 < 1 := ⟨by positivity, by
    rw [hρ1_def]; rw [show (1:ℝ) = (2:ℝ)^(0:ℝ) by simp]
    exact Real.rpow_lt_rpow_left_iff (by norm_num) |>.mpr (by nlinarith [I0_pos, han])⟩
  have hρ2_mem : 0 ≤ ρ2 ∧ ρ2 < 1 := ⟨by positivity, by
    rw [hρ2_def]; rw [show (1:ℝ) = (2:ℝ)^(0:ℝ) by simp]
    exact Real.rpow_lt_rpow_left_iff (by norm_num) |>.mpr (by nlinarith [Kearly.hc1, han])⟩
  have hρ3_mem : 0 ≤ ρ3 ∧ ρ3 < 1 := ⟨by positivity, by
    rw [hρ3_def]; rw [show (1:ℝ) = (2:ℝ)^(0:ℝ) by simp]
    exact Real.rpow_lt_rpow_left_iff (by norm_num) |>.mpr (by nlinarith [Kfuture.hc1, han])⟩
  have hρ4_mem : 0 ≤ ρ4 ∧ ρ4 < 1 := ⟨by positivity, by
    rw [hρ4_def]; rw [show (1:ℝ) = Real.exp 0 by simp]
    exact Real.exp_lt_exp.mpr (by linarith [habad])⟩
  have hρ5_mem : 0 ≤ ρ5 ∧ ρ5 < 1 := ⟨by positivity, by
    rw [hρ5_def]; rw [show (1:ℝ) = (2:ℝ)^(0:ℝ) by simp]
    exact Real.rpow_lt_rpow_left_iff (by norm_num) |>.mpr (by nlinarith [Kprefix.hc1, hat'])⟩
  set BOUND : ℕ → ℝ := fun L =>
    2 * Real.exp (lambdaStar * c) * (L : ℝ) * ρ1 ^ L + Kearly.A * (L : ℝ) * ρ2 ^ L
      + Kfuture.A * (L : ℝ) * ρ3 ^ L + (L : ℝ) * ρ4 ^ L + Kprefix.A * (L : ℝ) * ρ5 ^ L
    with hBOUND_def
  have hBOUND_summable : Summable BOUND := by
    rw [hBOUND_def]
    have hs1 := summable_const_mul_mul_geometric (2 * Real.exp (lambdaStar * c)) ρ1
      hρ1_mem.1 hρ1_mem.2
    have hs2 := summable_const_mul_mul_geometric Kearly.A ρ2 hρ2_mem.1 hρ2_mem.2
    have hs3 := summable_const_mul_mul_geometric Kfuture.A ρ3 hρ3_mem.1 hρ3_mem.2
    have hs4 := summable_const_mul_mul_geometric 1 ρ4 hρ4_mem.1 hρ4_mem.2
    have hs5 := summable_const_mul_mul_geometric Kprefix.A ρ5 hρ5_mem.1 hρ5_mem.2
    have heq4 : (fun L : ℕ => (1:ℝ) * (L : ℝ) * ρ4 ^ L) = fun L : ℕ => (L : ℝ) * ρ4 ^ L := by
      funext L; ring
    rw [heq4] at hs4
    have hcombined := ((hs1.add hs2).add hs3).add (hs4.add hs5)
    have heq : (fun L : ℕ =>
        2 * Real.exp (lambdaStar * c) * (L : ℝ) * ρ1 ^ L + Kearly.A * (L : ℝ) * ρ2 ^ L
          + Kfuture.A * (L : ℝ) * ρ3 ^ L + (L : ℝ) * ρ4 ^ L + Kprefix.A * (L : ℝ) * ρ5 ^ L)
        = (fun L : ℕ =>
            2 * Real.exp (lambdaStar * c) * (L : ℝ) * ρ1 ^ L
              + Kearly.A * (L : ℝ) * ρ2 ^ L + Kfuture.A * (L : ℝ) * ρ3 ^ L
              + ((L : ℝ) * ρ4 ^ L + Kprefix.A * (L : ℝ) * ρ5 ^ L)) := by
      funext L; ring
    rw [heq]
    exact hcombined
  have hBOUND_nonneg : ∀ L, 0 ≤ BOUND L := by
    intro L
    rw [hBOUND_def]
    have h1 : 0 ≤ 2 * Real.exp (lambdaStar * c) * (L : ℝ) * ρ1 ^ L := by
      apply mul_nonneg (mul_nonneg (by positivity) (Nat.cast_nonneg L)) (pow_nonneg hρ1_mem.1 L)
    have h2 : 0 ≤ Kearly.A * (L : ℝ) * ρ2 ^ L :=
      mul_nonneg (mul_nonneg Kearly.hA.le (Nat.cast_nonneg L)) (pow_nonneg hρ2_mem.1 L)
    have h3 : 0 ≤ Kfuture.A * (L : ℝ) * ρ3 ^ L :=
      mul_nonneg (mul_nonneg Kfuture.hA.le (Nat.cast_nonneg L)) (pow_nonneg hρ3_mem.1 L)
    have h4 : 0 ≤ (L : ℝ) * ρ4 ^ L := mul_nonneg (Nat.cast_nonneg L) (pow_nonneg hρ4_mem.1 L)
    have h5 : 0 ≤ Kprefix.A * (L : ℝ) * ρ5 ^ L :=
      mul_nonneg (mul_nonneg Kprefix.hA.le (Nat.cast_nonneg L)) (pow_nonneg hρ5_mem.1 L)
    linarith
  apply Summable.of_nonneg_of_le (fun L => by
    split_ifs with h
    · exact le_refl 0
    · unfold genEventProb
      apply tsum_nonneg
      intro x
      exact Set.indicator_nonneg (fun y _ => normalizedHarmonicWindowWeight_nonneg (2 ^ L)
        (2 ^ L + 2 ^ L) y) x) (fun L => ?_) hBOUND_summable
  split_ifs with hL
  · exact hBOUND_nonneg L
  · push_neg at hL
    have hL1 : 1 ≤ L := le_trans hL0 hL
    have hbound := dyadic_persistence_probability_bound n Tearly Ttotal sMaxNat Q Qpre Qearly L hL1
      c c0 Kfuture hKfuture theta hθ0 hθ1 cPrefix hcPrefix Kprefix hKprefix c0early hc0early Kearly
      hKearly (hn1 L hL) (hTearly_pos L hL) (hTle L hL) (hthick L hL) (hQ1 L hL) (hQrel L hL)
      (hbudget_param L hL) (hQpre1 L hL) (hQprerel_uniform L hL) (hresidue_prefix L hL)
      (hQrel_early_uniform L hL) (hresidue_early L hL)
    have hTtotal_R : (Ttotal L : ℝ) ≤ (L : ℝ) := by exact_mod_cast hTtotal_le L hL
    -- Bound each of the five terms by `ρi ^ L`.
    have hterm1 : (2 : ℝ) ^ (-(I0 * (n L : ℝ))) ≤ ρ1 ^ L := by
      rw [hρ1_def, ← rpow_two_neg_mul_nat_eq_pow]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [I0_pos, hn_growth L hL])
    have hterm2 : (2 : ℝ) ^ (-(Kearly.c1 * (n L : ℝ))) ≤ ρ2 ^ L := by
      rw [hρ2_def, ← rpow_two_neg_mul_nat_eq_pow]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by nlinarith [Kearly.hc1, hn_growth L hL])
    have hterm3 : (2 : ℝ) ^ (-(Kfuture.c1 * (n L : ℝ))) ≤ ρ3 ^ L := by
      rw [hρ3_def, ← rpow_two_neg_mul_nat_eq_pow]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by nlinarith [Kfuture.hc1, hn_growth L hL])
    have hterm5 : (2 : ℝ) ^ (-(Kprefix.c1 * (Tearly L : ℝ))) ≤ ρ5 ^ L := by
      rw [hρ5_def, ← rpow_two_neg_mul_nat_eq_pow]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by nlinarith [Kprefix.hc1, hTearly_growth L hL])
    have hterm4 : Real.exp (-(theta * (sMaxNat L : ℝ))) * (geomUpperMgf theta) ^ (Ttotal L)
        ≤ ρ4 ^ L := by
      have hmgf_pos : 0 < geomUpperMgf theta := lt_trans one_pos (geomUpperMgf_gt_one theta hθ0 hθ1)
      have heq : (geomUpperMgf theta) ^ (Ttotal L)
          = Real.exp ((Ttotal L : ℝ) * Real.log (geomUpperMgf theta)) := by
        rw [Real.exp_nat_mul, Real.exp_log hmgf_pos]
      rw [heq, ← Real.exp_add]
      rw [hρ4_def, ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have := hbad_rate L hL
      nlinarith [this]
    have h5terms : (2 : ℝ) ^ (-(I0 * (n L : ℝ)))
          + Kearly.A * (2 : ℝ) ^ (-(Kearly.c1 * (n L : ℝ)))
        ≤ ρ1 ^ L + Kearly.A * ρ2 ^ L :=
      add_le_add hterm1 (mul_le_mul_of_nonneg_left hterm2 Kearly.hA.le)
    have hfull :
        2 * Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n L : ℝ)))
          + Kearly.A * (2 : ℝ) ^ (-(Kearly.c1 * (n L : ℝ)))
          + Kfuture.A * (2 : ℝ) ^ (-(Kfuture.c1 * (n L : ℝ)))
          + Real.exp (-(theta * (sMaxNat L : ℝ))) * (geomUpperMgf theta) ^ (Ttotal L)
          + Kprefix.A * (2 : ℝ) ^ (-(Kprefix.c1 * (Tearly L : ℝ)))
        ≤ 2 * Real.exp (lambdaStar * c) * ρ1 ^ L + Kearly.A * ρ2 ^ L
          + Kfuture.A * ρ3 ^ L + ρ4 ^ L + Kprefix.A * ρ5 ^ L := by
      have hc1 : 2 * Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n L : ℝ)))
          ≤ 2 * Real.exp (lambdaStar * c) * ρ1 ^ L :=
        mul_le_mul_of_nonneg_left hterm1 (by positivity)
      have hc2 : Kearly.A * (2 : ℝ) ^ (-(Kearly.c1 * (n L : ℝ))) ≤ Kearly.A * ρ2 ^ L :=
        mul_le_mul_of_nonneg_left hterm2 Kearly.hA.le
      have hc3 : Kfuture.A * (2 : ℝ) ^ (-(Kfuture.c1 * (n L : ℝ))) ≤ Kfuture.A * ρ3 ^ L :=
        mul_le_mul_of_nonneg_left hterm3 Kfuture.hA.le
      have hc5 : Kprefix.A * (2 : ℝ) ^ (-(Kprefix.c1 * (Tearly L : ℝ))) ≤ Kprefix.A * ρ5 ^ L :=
        mul_le_mul_of_nonneg_left hterm5 Kprefix.hA.le
      linarith [hc1, hc2, hc3, hterm4, hc5]
    have hMlate_nonneg' : 0 ≤ 2 * Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n L : ℝ)))
          + Kearly.A * (2 : ℝ) ^ (-(Kearly.c1 * (n L : ℝ)))
          + Kfuture.A * (2 : ℝ) ^ (-(Kfuture.c1 * (n L : ℝ)))
          + Real.exp (-(theta * (sMaxNat L : ℝ))) * (geomUpperMgf theta) ^ (Ttotal L)
          + Kprefix.A * (2 : ℝ) ^ (-(Kprefix.c1 * (Tearly L : ℝ))) := by
      have hmgf_nonneg : 0 ≤ geomUpperMgf theta := by
        linarith [geomUpperMgf_gt_one theta hθ0 hθ1]
      have h1 : 0 ≤ 2 * Real.exp (lambdaStar * c) * (2:ℝ)^(-(I0*(n L:ℝ))) := by positivity
      have h2 : 0 ≤ Kearly.A * (2:ℝ)^(-(Kearly.c1*(n L:ℝ))) :=
        mul_nonneg Kearly.hA.le (by positivity)
      have h3 : 0 ≤ Kfuture.A * (2:ℝ)^(-(Kfuture.c1*(n L:ℝ))) :=
        mul_nonneg Kfuture.hA.le (by positivity)
      have h4 : 0 ≤ Real.exp (-(theta*(sMaxNat L:ℝ))) * (geomUpperMgf theta)^(Ttotal L) :=
        mul_nonneg (Real.exp_pos _).le (pow_nonneg hmgf_nonneg _)
      have h5 : 0 ≤ Kprefix.A * (2:ℝ)^(-(Kprefix.c1*(Tearly L:ℝ))) :=
        mul_nonneg Kprefix.hA.le (by positivity)
      linarith
    have hL_nonneg : (0:ℝ) ≤ (L:ℝ) := Nat.cast_nonneg L
    calc genEventProb (normalizedHarmonicWindowWeight (2 ^ L) (2 ^ L + 2 ^ L))
          (dyadicPersistenceExceptionalEvent (Ttotal L) (n L) c)
        ≤ (Ttotal L : ℝ) *
          (2 * Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n L : ℝ)))
            + Kearly.A * (2 : ℝ) ^ (-(Kearly.c1 * (n L : ℝ)))
            + Kfuture.A * (2 : ℝ) ^ (-(Kfuture.c1 * (n L : ℝ)))
            + Real.exp (-(theta * (sMaxNat L : ℝ))) * (geomUpperMgf theta) ^ (Ttotal L)
            + Kprefix.A * (2 : ℝ) ^ (-(Kprefix.c1 * (Tearly L : ℝ)))) := by
          have := hbound
          linarith [this]
      _ ≤ (L : ℝ) *
          (2 * Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n L : ℝ)))
            + Kearly.A * (2 : ℝ) ^ (-(Kearly.c1 * (n L : ℝ)))
            + Kfuture.A * (2 : ℝ) ^ (-(Kfuture.c1 * (n L : ℝ)))
            + Real.exp (-(theta * (sMaxNat L : ℝ))) * (geomUpperMgf theta) ^ (Ttotal L)
            + Kprefix.A * (2 : ℝ) ^ (-(Kprefix.c1 * (Tearly L : ℝ)))) :=
          mul_le_mul_of_nonneg_right hTtotal_R hMlate_nonneg'
      _ ≤ (L : ℝ) * (2 * Real.exp (lambdaStar * c) * ρ1 ^ L + Kearly.A * ρ2 ^ L
            + Kfuture.A * ρ3 ^ L + ρ4 ^ L + Kprefix.A * ρ5 ^ L) :=
          mul_le_mul_of_nonneg_left hfull hL_nonneg
      _ = BOUND L := by rw [hBOUND_def]; ring

end TaoExternal
end EOC
