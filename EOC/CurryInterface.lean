import EOC.ZeroConfinedSeed
import EOC.UpperEscape

/-!
# An honest interface for Curry's external input

Companion to `docs/CURRY_INDEPENDENT_AUDIT.md`, which audits
*M. J. Curry, "An Explicit Windowed Sparsity Bound for Divergent 3x+1 Orbits, with
Logarithmic-Floor Exclusion beyond the Harmonic Barrier", 24 August 2026*
(archived at `docs/sources/Curry_WindowedSparsity.pdf`, sha256 `67daa37d…`) from the source text.

The audit found the proof correct. **It is still not formalized**, so it must appear here as an
explicit hypothesis and never as an axiom. This file separates the three layers:

1. **External, audited on paper, not formalized** — `WindowedSparsity` (Curry Thm 2.3) and
   `CurryReciprocalSummability` (Curry Prop 3.1).
2. **Formalized implications** — everything below with a proof.
3. **Remaining formalization obligation** — `PowerSavingImpliesSummable`, the dyadic summation
   that takes Thm 2.3 to Prop 3.1. Stated, not proved.

Nothing here introduces a parallel notion of orbit or of divergence: `orbit`, `orbWord`,
`Confined`, `R` and `ReciprocalSummable` are the repository's existing definitions, and the
injectivity/divergence equivalence is built on the existing `UpperEscape.injective_orbit_tendsto`.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace CurryInterface

open CurryFoundation HarmonicPacking UpperEscape Filter Topology

/-! ## 1. Divergence, and its equivalence with injectivity

Curry's hypothesis class is *aperiodic* (equivalently collision-free) orbits; the repository's is
*injective* orbits; the chain's conclusion is about *divergent* orbits. For the deterministic
positive accelerated map these coincide, and the equivalence is elementary. -/

/-- The accelerated orbit of `M` diverges: every value bound is eventually exceeded. -/
def DivergentOrbit (M : ℕ) : Prop := ∀ K : ℕ, ∃ N₀, ∀ n ≥ N₀, K < orbit M n

/-- A repeated value makes the orbit periodic from the first occurrence onwards. -/
theorem orbit_period_of_eq {M i j : ℕ} (h : orbit M i = orbit M j) (k : ℕ) :
    orbit M (i + k) = orbit M (j + k) := by
  rw [orbit_add, orbit_add, h]

/-- A non-injective orbit returns to `orbit M i` at arbitrarily late times, hence does not
diverge. -/
theorem not_divergent_of_eq {M i j : ℕ} (hij : i < j) (h : orbit M i = orbit M j) :
    ¬ DivergentOrbit M := by
  intro hdiv
  obtain ⟨p, hp⟩ : ∃ p, j = i + p ∧ 1 ≤ p := ⟨j - i, by omega, by omega⟩
  obtain ⟨hjp, hp1⟩ := hp
  have hret : ∀ t, orbit M (i + t * p) = orbit M i := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
        have hstep : orbit M (i + p + t * p) = orbit M (i + t * p) := by
          have hh := orbit_period_of_eq h (t * p)
          rw [hjp] at hh
          exact hh.symm
        calc orbit M (i + (t + 1) * p) = orbit M (i + p + t * p) := by ring_nf
          _ = orbit M (i + t * p) := hstep
          _ = orbit M i := ih
  obtain ⟨N₀, hN₀⟩ := hdiv (orbit M i)
  have := hN₀ (i + N₀ * p) (by nlinarith)
  rw [hret N₀] at this
  omega

/-- **Injective ⟺ divergent**, for the deterministic positive accelerated map.

Forward: `UpperEscape.injective_orbit_tendsto` (already in the repository). Backward: a repeated
value makes the orbit eventually periodic, hence bounded. -/
theorem injective_iff_divergent (M : ℕ) :
    (∀ i j, orbit M i = orbit M j → i = j) ↔ DivergentOrbit M := by
  constructor
  · intro hinj K; exact injective_orbit_tendsto M hinj K
  · intro hdiv i j hij
    by_contra hne
    rcases Nat.lt_or_ge i j with h | h
    · exact not_divergent_of_eq h hij hdiv
    · exact not_divergent_of_eq (by omega : j < i) hij.symm hdiv

/-! ## 2. The external input, stated as hypotheses

Neither of these is proved here. `CurryReciprocalSummability` is exactly what the downstream chain
consumes; `WindowedSparsity` is the stronger statement Curry actually proves, recorded so that the
remaining formalization obligation can be named precisely. -/

/-- **Curry Theorem 2.3, conclusion form.** A set `A` admits a *power saving* count: for some
`β < 1` there is `C` with `#(A ∩ [a, a+X)) ≤ C·X^β·log(2X)`, uniformly in the window position `a`.

The audit verifies Curry's proof of this for collision-free `A`, with the explicit exponent
`β > β* = γ*·log₂3 = H(γ*) = 0.9653844…`. The fact that `β*` can be taken `< 1` is what makes the
dyadic sum in §3 converge, and is the whole content of "beyond the harmonic barrier". -/
def PowerSavingCount (A : Set ℕ) : Prop :=
  ∃ β : ℝ, β < 1 ∧ ∃ C : ℝ, 0 < C ∧
    ∀ a X : ℕ, 1 ≤ a → 2 ≤ X →
      ((A ∩ Set.Ico a (a + X)).ncard : ℝ) ≤ C * (X : ℝ) ^ β * Real.log (2 * X)

/-- **Curry Theorem 2.3, as an external hypothesis.** Every divergent positive accelerated orbit
has a power-saving value count. Audited on paper, not formalized. -/
def WindowedSparsity : Prop :=
  ∀ M : ℕ, Odd M → DivergentOrbit M → PowerSavingCount (Set.range (orbit M))

/-- **Curry Proposition 3.1, as an external hypothesis.** This is the *only* external input the
divergence-to-zero-confined-seed reduction actually consumes. -/
def CurryReciprocalSummability : Prop :=
  ∀ M : ℕ, Odd M → DivergentOrbit M → ReciprocalSummable M

/-- **The remaining formalization obligation**, named precisely: the dyadic summation of
Curry §3, which turns the windowed count into reciprocal summability. Curry's proof is three lines
and the audit confirms it; formalizing it needs summation over a set along dyadic blocks.

This is a `def`, i.e. a *statement*, deliberately left unproved — not an axiom. -/
def PowerSavingImpliesSummable : Prop :=
  ∀ M : ℕ, Odd M → PowerSavingCount (Set.range (orbit M)) → ReciprocalSummable M

/-- With that obligation discharged, the weaker hypothesis follows from the stronger one. -/
theorem curry_summability_of_windowed
    (hbridge : PowerSavingImpliesSummable) (hws : WindowedSparsity) :
    CurryReciprocalSummability :=
  fun M hM hdiv => hbridge M hM (hws M hM hdiv)

/-! ## 3. The reduction, composed -/

/-- **Divergence ⟹ a zero-confined positive seed.** Composes the external input with the
formalized bridge `ZeroConfinedSeed.exists_zero_confined_seed_tendsto`.

Given Curry's Proposition 3.1, a divergent positive accelerated orbit yields an *actual positive
odd integer* whose own valuation word is zero-confined at every horizon and whose own drift tends
to `−∞`. -/
theorem zero_confined_seed_of_divergent (hCurry : CurryReciprocalSummability)
    {M : ℕ} (hM : Odd M) (hdiv : DivergentOrbit M) :
    ∃ m0, Odd m0 ∧ (∀ N, Confined 0 (orbWord m0) N) ∧
      Tendsto (fun k => R (orbWord m0) k) atTop atBot :=
  ZeroConfinedSeed.exists_zero_confined_seed_tendsto hM (hCurry M hM hdiv)

/-- **The reduction in its contrapositive, usable form.**

If no positive odd seed is zero-confined at every horizon, then — given Curry's input — no positive
accelerated orbit is injective, i.e. none diverges.

This is the Lean statement of the forward half of `thm:DEequiv`, with the external input visible as
an explicit hypothesis rather than hidden. -/
theorem no_divergent_orbit_of_universal_drift_exit
    (hCurry : CurryReciprocalSummability)
    (hDE : ∀ m0 : ℕ, Odd m0 → ∃ N, ¬ Confined 0 (orbWord m0) N)
    {M : ℕ} (hM : Odd M) : ¬ DivergentOrbit M := by
  intro hdiv
  obtain ⟨m0, hodd, hconf, -⟩ := zero_confined_seed_of_divergent hCurry hM hdiv
  obtain ⟨N, hN⟩ := hDE m0 hodd
  exact hN (hconf N)

/-- **And with injectivity in place of divergence**, via `injective_iff_divergent`. -/
theorem no_injective_orbit_of_universal_drift_exit
    (hCurry : CurryReciprocalSummability)
    (hDE : ∀ m0 : ℕ, Odd m0 → ∃ N, ¬ Confined 0 (orbWord m0) N)
    {M : ℕ} (hM : Odd M) : ¬ (∀ i j, orbit M i = orbit M j → i = j) := by
  intro hinj
  exact no_divergent_orbit_of_universal_drift_exit hCurry hDE hM
    ((injective_iff_divergent M).mp hinj)

/-! ## 4. The restricted target is *equivalent*, not weaker

A zero-confined positive orbit is automatically injective — a repeat makes it eventually periodic,
and a periodic segment has strictly positive drift — hence divergent, hence (given Curry) it carries
every necessary divergent-orbit property. So restricting the word class by properties that all
divergent orbits have does not weaken the target; it only makes more hypotheses available inside a
proof. See `docs/DIVERGENCE_SURVEY_SCOPE_NOTE.md` §D. -/

/-- A seed that is zero-confined at every horizon has an injective orbit. -/
theorem injective_of_zero_confined {m0 : ℕ} (hm0 : Odd m0)
    (hconf : ∀ N, Confined 0 (orbWord m0) N) :
    ∀ i j, orbit m0 i = orbit m0 j → i = j := by
  by_contra h
  push_neg at h
  obtain ⟨i, j, heq, hne⟩ := h
  obtain ⟨N, hN⟩ := noninjective_orbit_not_upper_confined 0 m0 hm0 ⟨i, j, hne, heq⟩
  exact hN (hconf N)

/-- Hence a zero-confined seed is a genuine divergence candidate: its orbit diverges. -/
theorem divergent_of_zero_confined {m0 : ℕ} (hm0 : Odd m0)
    (hconf : ∀ N, Confined 0 (orbWord m0) N) : DivergentOrbit m0 :=
  (injective_iff_divergent m0).mp (injective_of_zero_confined hm0 hconf)

end CurryInterface
end EOC
