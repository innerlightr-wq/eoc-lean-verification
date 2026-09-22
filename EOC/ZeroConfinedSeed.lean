import EOC.CurryFoundation
import EOC.Periodic
import EOC.SeparatedReturns
import EOC.CurryDivergenceProfile

/-!
# The restarted seed: link (5) of the divergence chain, at the seed level

`docs/DIVERGENCE_EXCLUSION_SURVEY.md` identifies this as the one *assemblable* gap in the chain

```
divergent orbit → Σ1/m_j < ∞ → E_∞ < ∞ → R_n → −∞ → last global max n₀
                → the restart at m* = m_{n₀} is zero-confined forever
                → so excluding positive realization of infinite zero-confined words excludes divergence.
```

`EOC.CurryFoundation.zero_corridor_tail` proves the corridor inequality **in shifted-index form on
the original seed's word**:

```
(s (orbWord M) (n₀+k) : ℝ) − (s (orbWord M) n₀ : ℝ) ≤ ⌊k·α⌋ .
```

What link (6) actually consumes is the statement about an **actual positive odd integer** `m*`,
namely `∃ m*, Odd m* ∧ ∀ k ≥ 1, R (orbWord m*) k < 0`. That restatement existed only in
`paper/eoc_rev6.tex` (Proposition `prop:lastmax`), whose status label reads
`\status{companion work; already formalized in the repository}` — an over-claim: the shifted-index
inequality was formalized, the seed-level statement was not.

This file assembles it, from ingredients that were all already present but never combined:
`Periodic.orbit_add`, `SeparatedReturns.sum_concat`, `Confinement.odd_orbit`, and
`CurryFoundation.exists_last_atBot_max` / `R_tendsto_atBot`.

**This is infrastructure, not progress toward excluding divergence.** It closes a bookkeeping gap
between two parts of the repository; the mathematical content of the chain is unchanged, and it
remains conditional on Curry's external, unformalized reciprocal-summability theorem.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace ZeroConfinedSeed

open CurryFoundation HarmonicPacking Filter Topology

/-! ## 1. The restart identity for prefix sums -/

/-- **Prefix sums restart.** `s_{n₀+k}(M) = s_{n₀}(M) + s_k(m_{n₀})`.

The orbit shift `orbit M (n₀+i) = orbit (orbit M n₀) i` (`Periodic.orbit_add`) turns the tail of
`M`'s valuation word into the *whole* valuation word of the restarted seed. -/
theorem s_orbWord_restart (M n0 k : ℕ) :
    s (orbWord M) (n0 + k) = s (orbWord M) n0 + s (orbWord (orbit M n0)) k := by
  have h1 := SeparatedReturns.sum_concat (orbWord M) (s (orbWord M)) (s_zero _) (s_succ _) n0 k
  rw [h1]
  congr 1
  unfold s
  refine Finset.sum_congr rfl fun j _ => ?_
  show a (orbit M (n0 + j)) = a (orbit (orbit M n0) j)
  rw [orbit_add]

/-- **Drift restarts by subtraction.** `R_k(m_{n₀}) = R_{n₀+k}(M) − R_{n₀}(M)`.

This is the real-valued form of `s_orbWord_restart`: the `n₀·α` terms cancel. -/
theorem R_restart (M n0 k : ℕ) :
    R (orbWord (orbit M n0)) k = R (orbWord M) (n0 + k) - R (orbWord M) n0 := by
  have h := s_orbWord_restart M n0 k
  unfold R
  have hcast : ((s (orbWord M) (n0 + k) : ℕ) : ℝ)
      = ((s (orbWord M) n0 : ℕ) : ℝ) + ((s (orbWord (orbit M n0)) k : ℕ) : ℝ) := by
    exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) h
  push_cast at hcast ⊢
  linarith

/-! ## 2. The seed-level statement -/

/-- **An actual positive odd seed whose drift is negative forever.**

Given Curry's reciprocal summability for `M`, the drift `R_n(M)` tends to `−∞`
(`R_tendsto_atBot`), so it has a *last* global maximum at some `n₀` (`exists_last_atBot_max`).
The restarted seed `m* = orbit M n₀` is an actual positive odd integer, and by `R_restart` its own
drift satisfies `R_k(m*) < 0` for every `k ≥ 1`.

This is the form Proposition `prop:lastmax` states and that the divergence equivalence consumes. -/
theorem exists_neg_drift_seed {M : ℕ} (hM : Odd M) (hrs : ReciprocalSummable M) :
    ∃ m0, Odd m0 ∧ ∀ k, 1 ≤ k → R (orbWord m0) k < 0 := by
  obtain ⟨n0, -, hlast⟩ := exists_last_atBot_max (R_tendsto_atBot hM hrs)
  refine ⟨orbit M n0, odd_orbit hM n0, fun k hk => ?_⟩
  rw [R_restart]
  have := hlast k hk
  linarith

/-- **The same seed is zero-confined at every horizon**, in the repository's `Confined` predicate.

`R_0 = 0` because `s_0 = 0`, and `R_k < 0` for `k ≥ 1`. This is exactly the hypothesis shape that
`Periodic.leastRealizer_unbounded_of_confined_evPeriodic` and
`BoundedDrift`-style escape theorems consume, and the shape in which the open problem
"no positive integer realizes an infinite zero-confined word" is posed. -/
theorem exists_zero_confined_seed {M : ℕ} (hM : Odd M) (hrs : ReciprocalSummable M) :
    ∃ m0, Odd m0 ∧ ∀ N, Confined 0 (orbWord m0) N := by
  obtain ⟨m0, hodd, hneg⟩ := exists_neg_drift_seed hM hrs
  refine ⟨m0, hodd, fun N j _ => ?_⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [R, s_zero]
  · exact le_of_lt (hneg j hj)

/-- **Integer corridor form.** `s_k(m*) ≤ ⌊k·α⌋` for every `k ≥ 1`: the restarted seed's word lies
in the exact integral zero corridor. -/
theorem exists_zero_corridor_seed {M : ℕ} (hM : Odd M) (hrs : ReciprocalSummable M) :
    ∃ m0, Odd m0 ∧ ∀ k, 1 ≤ k → (s (orbWord m0) k : ℤ) ≤ ⌊(k : ℝ) * alpha⌋ := by
  obtain ⟨m0, hodd, hneg⟩ := exists_neg_drift_seed hM hrs
  refine ⟨m0, hodd, fun k hk => ?_⟩
  have h := hneg k hk
  unfold R at h
  exact Int.le_floor.mpr (by push_cast; linarith)

/-! ## 3. The full profile at a single seed

`CurryDivergenceProfile.deficit_tendsto_atTop` states `∃ n0, Δ_k → ∞` but is proved with
`refine ⟨0, ?_⟩` — at `n0 = 0`, not at the last global drift maximum its docstring names. The
statement is true (the `∃` is bare), but it is *not* the combination it claims to be: at `n0 = 0`
the companion bound `deficit_nonneg` need not hold, so `Δ_k ≥ 0` and `Δ_k → ∞` are never available
at the same `n0` anywhere in the repository.

With the restart bridge above they are available at the same seed, which is the form the chain
needs. -/

/-- **The restarted seed's own drift tends to `−∞`.** -/
theorem R_restart_tendsto {M : ℕ} (hM : Odd M) (hrs : ReciprocalSummable M) (n0 : ℕ) :
    Tendsto (fun k => R (orbWord (orbit M n0)) k) atTop atBot := by
  have hR := R_tendsto_atBot hM hrs
  have h1 : Tendsto (fun k : ℕ => R (orbWord M) (n0 + k)) atTop atBot :=
    (hR.comp (Filter.tendsto_add_atTop_nat n0)).congr (fun k => by
      show R (orbWord M) (k + n0) = R (orbWord M) (n0 + k)
      rw [Nat.add_comm])
  have h2 := tendsto_atBot_add_const_right atTop (-(R (orbWord M) n0)) h1
  simpa [R_restart, sub_eq_add_neg] using h2

/-- **The complete divergence-candidate profile, at one actual positive odd seed.**

If `M` has a reciprocally summable orbit then there is an actual positive odd integer `m*` whose
*own* valuation word is zero-confined at every horizon **and** whose own drift tends to `−∞`.

This is the object the divergence equivalence consumes, and the two properties now hold at the
*same* seed — which was not the case before (see the note above). -/
theorem exists_zero_confined_seed_tendsto {M : ℕ} (hM : Odd M) (hrs : ReciprocalSummable M) :
    ∃ m0, Odd m0 ∧ (∀ N, Confined 0 (orbWord m0) N) ∧
      Tendsto (fun k => R (orbWord m0) k) atTop atBot := by
  obtain ⟨n0, -, hlast⟩ := exists_last_atBot_max (R_tendsto_atBot hM hrs)
  refine ⟨orbit M n0, odd_orbit hM n0, fun N j _ => ?_, R_restart_tendsto hM hrs n0⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [R, s_zero]
  · rw [R_restart]
    have := hlast j hj
    linarith

end ZeroConfinedSeed
end EOC
