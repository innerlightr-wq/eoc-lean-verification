import EOC.ExceptionalPowerBound

/-!
# The zero-corridor heavy-regime lemma

Companion to `docs/CURRY_REALIZER_WINDOW_INTERFACE.md`.

Curry's windowed sparsity bound (external Theorem 2.3, not formalized here) splits a window
count into a **heavy** branch — an entropy count over parity prefixes with at least `γ·J` odd
steps — and a **light** branch, which is the only place collision-freeness is used and the only
source of the spatial power saving `X^{γα}`. The split is optimized at the crossing
`H₂(γ_*) = α γ_*`, giving `β_* = α γ_* ≈ 0.9653844`.

This file records the elementary arithmetic that decides which branch a **zero-corridor**
valuation word lands in, and it is the reason the light branch never engages.

Write `ρ = 1/α = log_3 2 ≈ 0.6309298`. Under the correspondence of §C of the audit, `k`
accelerated steps are exactly `S_k` raw steps of `n ↦ n/2, (3n+1)/2`, of which exactly `k` are
odd steps; so the raw odd-step density at an accelerated boundary is `k / S_k`.

* `oddDensity_ge_inv_alpha` — zero confinement `S_k ≤ α k` forces density `k/S_k ≥ ρ`.
* `oddDensity_succ_ge_inv_alpha` — the same at the `+1` realizer-modulus depth `S_k + 1`, where
  the count of odd steps is `k+1` (the terminal state is odd). **Strict**, and with no finite
  exceptional range.
* `binEntropy_inv_alpha_lt_one` — the certificate `H₂(ρ) < 1 = α·ρ`, which places `ρ` strictly
  on the heavy side of the crossing. Proved from the repository's own `I₀ > 0`, so no analytic
  machinery is introduced and `γ_*` never has to be defined.

**What this does and does not mean.** It says the transplant of Curry's *proof* to the
zero-corridor realizer family lands entirely in the entropy branch, whose exponent
`H₂(ρ) = 1 − I₀/α` is already what `ExceptionalPowerBound.survivor_count_le_rpow` proves
unconditionally and with explicit constants. It says nothing against Curry's Theorem 2.3 itself,
which continues to apply to actual divergent orbits.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace CurryHeavyRegime

open Real

/-! ## 1. Zero confinement forces the heavy odd-step density -/

/-- **Aligned boundaries.** If a zero-corridor prefix of accelerated length `k ≥ 1` has total
valuation `S ≤ α k`, then the raw odd-step density `k / S` is at least `ρ = 1/α`.

`S` is the raw length and `k` the number of odd steps among those `S` raw steps, so `k/S` is
exactly the quantity Curry's heavy/light threshold `γ` is compared against. -/
theorem oddDensity_ge_inv_alpha {k S : ℝ} (hS : 0 < S) (hconf : S ≤ alpha * k) :
    alpha⁻¹ ≤ k / S := by
  have hα : (0 : ℝ) < alpha := by linarith [one_lt_alpha]
  have key : alpha⁻¹ * S ≤ k := by
    have h := mul_le_mul_of_nonneg_left hconf (inv_pos.mpr hα).le
    rwa [← mul_assoc, inv_mul_cancel₀ hα.ne', one_mul] at h
  exact (le_div_iff₀ hS).mpr key

/-- **The `+1` realizer-modulus depth.** The least realizer of a word of total valuation `S`
lives below `2^(S+1)`, so Curry's window proof may take raw depth `S + 1` rather than `S`.

At that depth the raw orbit has taken `k + 1` odd steps, not `k`: the terminal accelerated state
`m_k` sits at raw position `S` and is itself odd. The density is therefore `(k+1)/(S+1)`, and it
is **strictly** above `ρ` for every `k ≥ 0` with no exceptional range, because `α > 1`.

(Counting only `k` odd steps here undercounts by one and produces a spurious finite exceptional
range; §H of the audit records that error and its correction.) -/
theorem oddDensity_succ_ge_inv_alpha {k S : ℝ} (hS : 0 < S)
    (hconf : S ≤ alpha * k) : alpha⁻¹ < (k + 1) / (S + 1) := by
  have hα1 : (1 : ℝ) < alpha := one_lt_alpha
  have hα : (0 : ℝ) < alpha := by linarith
  have hS1 : (0 : ℝ) < S + 1 := by linarith
  have key : alpha⁻¹ * (S + 1) < k + 1 := by
    have h1 : S + 1 < alpha * (k + 1) := by nlinarith
    have h2 := mul_lt_mul_of_pos_left h1 (inv_pos.mpr hα)
    rwa [← mul_assoc, inv_mul_cancel₀ hα.ne', one_mul] at h2
  exact (lt_div_iff₀ hS1).mpr key

/-! ## 2. `ρ` lies strictly on the heavy side of Curry's crossing -/

/-- **The heavy-side certificate.** `H₂(ρ) < 1`, while `α · ρ = 1` exactly.

Since Curry's threshold function `γ ↦ H₂(γ) − α γ` is strictly decreasing on `(1/2, 1/α)` and
vanishes at the crossing `γ_*`, its strict negativity at `γ = ρ` places `γ_* < ρ`: a zero-corridor
word, whose density is `≥ ρ` by §1, is strictly inside the heavy branch.

Proved from the repository's existing calibration — `1 − I₀/α = H₂(1/α)` together with `I₀ > 0` —
so `γ_*` is never defined and no intermediate-value or monotonicity machinery is needed. -/
theorem binEntropy_inv_alpha_lt_one :
    Real.binEntropy alpha⁻¹ / Real.log 2 < 1 := by
  have h := ExceptionalPowerBound.one_sub_I0_div_alpha_eq
  have hI := ExceptionalPowerBound.I0_pos'
  have hα : (0 : ℝ) < alpha := by linarith [one_lt_alpha]
  have hpos : 0 < TaoExternal.I0 / alpha := div_pos hI hα
  linarith

/-- `α · ρ = 1`: the light-branch exponent evaluated at `ρ` is exactly the trivial exponent. -/
theorem alpha_mul_inv_alpha : alpha * alpha⁻¹ = 1 :=
  mul_inv_cancel₀ (by
    have : (1 : ℝ) < alpha := one_lt_alpha
    linarith : alpha ≠ 0)

/-- **Heavy-side comparison, assembled.** At `γ = ρ` the light exponent `α γ` equals `1` while
the heavy exponent `H₂(γ)` is strictly below `1`. So at the density a zero-corridor word actually
has, the entropy branch is the binding one and the collision branch is slack. -/
theorem heavy_binds_at_inv_alpha :
    Real.binEntropy alpha⁻¹ / Real.log 2 < alpha * alpha⁻¹ := by
  rw [alpha_mul_inv_alpha]; exact binEntropy_inv_alpha_lt_one

end CurryHeavyRegime
end EOC
