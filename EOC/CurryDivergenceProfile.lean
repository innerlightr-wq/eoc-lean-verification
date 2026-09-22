import EOC.CurryFoundation

/-!
# The divergent-orbit profile: elementary consequences of the Curry drift collapse

Companion to `docs/CURRY_DIVERGENCE_PART2_AUDIT.md`. Every theorem here is a **Level 2**
item in that audit: an elementary consequence of `EOC.CurryFoundation.R_tendsto_atBot`
that the three source manuscripts either state in a different coordinate or do not state
at all, and that `EOC/CurryFoundation.lean` stopped short of recording.

Nothing here is new mathematics. The audit's point is that these are the statements a
reader of the three papers would expect to find already formalized, and they were not:

* `deficit_tendsto_atTop` — `Δ_k → ∞` for the *actual* restarted orbit. `CurryFoundation`
  proves the bridging equivalence `deficit_tendsto_atTop_iff` but never instantiates it,
  so the repository contained `Δ_k ≥ 0` (`deficit_nonneg`) and the equivalence, but no
  theorem concluding `Δ_k → ∞`.
* `valuationMean_lt_alpha_eventually` — `D_N < α` for all large `N`. This is the
  cross-paper corollary of Curry against the valuation-mean manuscript, whose own
  Theorem 4.3 gives only `limsup D_N ≤ α` and in fact permits `D_N > α` at every finite
  `N`. Under the Curry interface the inequality becomes strict and eventual.
* `occupation_above_finite` — `#{n : R_n ≥ -G} < ∞` for every level `G`, the qualitative
  shadow of Curry's Theorem 4.2. The quantitative bound `≤ c₁2^{βG}(G+c₂)` is **not**
  formalized and is not implied by anything here; see §T of the audit.

All of these are conditional on `ReciprocalSummable`, the external Curry interface, exactly
as in `CurryFoundation`. None of them is a step toward excluding divergence: §Q and §R of the
audit explain why they describe a hypothetical divergent orbit rather than constrain one.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace CurryFoundation

open Filter Topology HarmonicPacking

section Profile

variable {M : ℕ}

/-! ## 1. The restarted deficit diverges (audit §K) -/

/-- The restarted prefix-sum sequence past a chosen index `n0`, as an integer sequence. -/
private noncomputable def restartS (M : ℕ) (n0 : ℕ) : ℕ → ℤ :=
  fun k => (s (orbWord M) (n0 + k) : ℤ) - (s (orbWord M) n0 : ℤ)

/-- The shifted-drift identity for the restarted word: `S'_k - kα = R_{n0+k} - R_{n0}`.
This is the hypothesis `deficit_tendsto_atTop_iff` asks for, discharged for the real orbit. -/
private theorem restart_drift_eq (M : ℕ) (n0 : ℕ) (k : ℕ) :
    ((restartS M n0 k : ℝ)) - (k : ℝ) * alpha
      = R (orbWord M) (n0 + k) - R (orbWord M) n0 := by
  unfold restartS R
  push_cast
  ring

/-- **`Δ_k → ∞`.** Past the last global drift maximum, the deficit below the Beatty line
diverges to `+∞`.

`CurryFoundation` proved `zero_corridor_tail` (`Δ_k ≥ 0`) and the equivalence
`deficit_tendsto_atTop_iff`, but never combined them for the actual orbit. This is that
combination, and it is the statement the audit's consolidated profile (§Q) quotes. -/
theorem deficit_tendsto_atTop (hM : Odd M) (hrs : ReciprocalSummable M) :
    ∃ n0 : ℕ, Tendsto (fun k => deficit (restartS M n0) k) atTop atTop := by
  refine ⟨0, ?_⟩
  have hR := R_tendsto_atBot hM hrs
  -- `R_{0+k} - R_0 → -∞` because `R_{n} → -∞` and `R_0` is a constant
  have hshift : Tendsto (fun k => R (orbWord M) (0 + k) - R (orbWord M) 0) atTop atBot := by
    have h1 : Tendsto (fun k : ℕ => R (orbWord M) (0 + k)) atTop atBot := by
      simpa [zero_add] using hR
    have h2 := tendsto_atBot_add_const_right atTop (-(R (orbWord M) 0)) h1
    simpa [sub_eq_add_neg] using h2
  exact (deficit_tendsto_atTop_iff (M := M) (restart_drift_eq M 0)).mp hshift

/-! ## 2. The valuation mean is eventually strictly below `α` (audit §I) -/

/-- **`D_N < α` eventually.** For a reciprocally-summable orbit the valuation mean
`D_N = S_N / N` is *strictly* below the critical value `α = log₂ 3` for all large `N`.

This is the cross-paper corollary of §I of the audit. The valuation-mean manuscript's own
Theorem 4.3 bounds `D_N ≤ α + (log₂ m₀ + (1/6)log₂ N + 1/(3 ln 2))/N`, whose correction term
is *positive*, so it does not exclude `D_N > α` at any finite `N`; and its conclusion is a
`limsup`, which permits `D_N = α` along a subsequence. Under the Curry interface both are
ruled out. The proof is one line from `R_tendsto_atBot`, since `R_N = N(D_N - α)`. -/
theorem valuationMean_lt_alpha_eventually (hM : Odd M) (hrs : ReciprocalSummable M) :
    ∀ᶠ N in atTop, (s (orbWord M) N : ℝ) / (N : ℝ) < alpha := by
  have hR := R_tendsto_atBot hM hrs
  have hneg : ∀ᶠ N in atTop, R (orbWord M) N < 0 :=
    hR.eventually (eventually_lt_atBot 0)
  have hpos : ∀ᶠ N : ℕ in atTop, 0 < (N : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    exact_mod_cast hN
  filter_upwards [hneg, hpos] with N hN hNpos
  have hR' : (s (orbWord M) N : ℝ) - (N : ℝ) * alpha < 0 := by
    simpa [R] using hN
  rw [div_lt_iff₀ hNpos]
  linarith

/-! ## 3. Shallow negative drift is occupied only finitely often (audit §M) -/

/-- **Qualitative occupation.** For every level `G`, only finitely many times `n` have drift
`R_n ≥ -G`; equivalently, in Curry's coordinate, `#{n : g_n ≤ G} < ∞`.

This is the *qualitative shadow* of Curry's Theorem 4.2. The theorem's quantitative content —
`#{n : g_n ≤ G} ≤ c₁2^{βG}(G + c₂)` with `β > β_* = 0.9653…`, a power saving of `2^{-(1-β)G}`
over what mere distinctness of the states gives — is **not** captured here and is not a
consequence of `R_tendsto_atBot`. Audit §T records it as the principal piece of Curry's
paper that the current reduction discards. -/
theorem occupation_above_finite (hM : Odd M) (hrs : ReciprocalSummable M) (G : ℝ) :
    {n : ℕ | -G ≤ R (orbWord M) n}.Finite := by
  have hR := R_tendsto_atBot hM hrs
  obtain ⟨N, hN⟩ := (tendsto_atBot.mp hR (-G - 1)).exists_forall_of_atTop
  refine Set.Finite.subset (Set.finite_Iio N) ?_
  intro n hn
  have hn' : -G ≤ R (orbWord M) n := hn
  by_contra hcon
  exact absurd (hN n (not_lt.mp hcon)) (by linarith)

/-- **Every fixed level is escaped.** Restatement of `occupation_above_finite` in the form
used by Route A of the audit's §H: finiteness at every level is *equivalent* to `g_n → ∞`. -/
theorem eventually_R_lt (hM : Odd M) (hrs : ReciprocalSummable M) (G : ℝ) :
    ∀ᶠ n in atTop, R (orbWord M) n < -G :=
  (R_tendsto_atBot hM hrs).eventually (eventually_lt_atBot (-G))

end Profile

end CurryFoundation
end EOC
