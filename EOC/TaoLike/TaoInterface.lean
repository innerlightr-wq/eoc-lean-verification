import EOC.TaoLike.ResidueTV
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Tao finite-valuation mixing interface (Milestone 4)

## Source

Terence Tao, *Almost all orbits of the Collatz map attain almost bounded values*,
arXiv:1909.03562, **version 7 (16 Jul 2026)**. The result formalized as an interface below is
**Proposition 1.9** of that paper (Section 1.2, "Syracuse formulation"), quoted verbatim from
the source (its own variable names `𝐍`, `n'`, `c₀`, `c₁` preserved in this quotation):

> Let `n ∈ ℕ`, and let `𝐍` be a random variable taking values in `2ℕ+1`. Suppose there exist
> an absolute constant `c₀ > 0` and some natural number `n' ≥ (2+c₀)n` such that `𝐍 mod 2^n'`
> is approximately uniformly distributed in the odd residue classes `(2ℤ+1)/2^n'ℤ` of
> `ℤ/2^n'ℤ`, in the sense that
> `d_TV(𝐍 mod 2^n', Unif((2ℤ+1)/2^n'ℤ)) ≪ 2^{-n'}`.
> Then
> `d_TV(a⃗^(n)(𝐍), Geom(2)^n) ≪ 2^{-c₁n}`
> for some absolute constant `c₁ > 0` (depending on `c₀`).

with the paper's supporting definitions (its equations (1.1), (1.8), (1.9), and Definition
1.7), audited against this repo's own conventions:

* **Accelerated map.** `Syr(N) := Col^{ν₂(3N+1)+1}(N)`, i.e. `Syr(N) = (3N+1) / 2^{ν₂(3N+1)}`
  — **EXACT MATCH** with this repo's `T` (`EOC.Basic`), with Tao's `ν₂(3N+1)` an EXACT MATCH
  for this repo's `a` (`a m = padicValNat 2 (3*m+1)`, `EOC.Basic`).
* **Valuation vector.** `a⃗^(n)(N) := (ν₂(3N+1), ν₂(3·Syr(N)+1), …, ν₂(3·Syr^{n-1}(N)+1))` —
  **EXACT MATCH** with `fun i : Fin n => a (orbit N i)` (`orbit`/`orbit_succ` from
  `EOC.ValuationWord`, since `orbit N (i+1) = T (orbit N i)` unfolds exactly to iterated
  `Syr`).
* **Geometric law.** `Geom(μ)` on support `{1,2,3,…}` with `P(Geom(μ)=a) = (1/μ)·((μ-1)/μ)^{a-1}`
  (Definition 1.7); for `μ = 2` this is `P(Geom(2)=a) = 2^{-a}`, `a ≥ 1` — **EXACT MATCH** with
  the target law formalized below as `geom2` (no `+1`/`-1` shift needed: Tao's own `Geom(2)`
  is already supported on `{1,2,…}`, unlike e.g. Mathlib's `geometricPMF`/`geometricMeasure`,
  which are supported on `{0,1,2,…}`; we therefore avoid the Mathlib geometric API entirely
  here rather than risk a silent off-by-one).
* **TV convention.** `d_TV(X,Y) := Σ_{r∈R} |P(X=r) - P(Y=r)|` (paper's eq. (1.9)) — the
  **full L1** sum, with **no** `1/2` prefactor. This repo's Milestone-3 `EOC.dTV`-shaped
  quantity (see `conditional_residue_tv_eta_bound`, `EOC.TaoLike.ResidueTV`) is instead
  `(1/2) * Σ_v |P(v) - U(v)|`, the standard *half*-L1 convention. **CONVENTION FACTOR**: for
  discrete laws, `sup_E |P(E) - Q(E)| = (1/2) · Σ_x |P(x) - Q(x)|` (a standard fact — the
  event-sup characterization of total variation, sometimes called Scheffé's identity), so
  Tao's `d_TV` is *exactly twice* the event-sup quantity `EventTVBound` defined below, and
  *exactly twice* Milestone 3's own `dTV`. This identity is **not proved** in this file (it is
  out of scope for an interface milestone, requiring general summability/coupling
  machinery for the infinite-support valuation-vector case); it is reported here explicitly,
  as required, rather than silently assumed. The interface below is therefore stated using
  the `EventTVBound`/event-sup convention throughout (matching Milestone 3's own convention),
  with constants `Cres`, `A` understood as *already absorbing* whatever factor is needed
  relative to Tao's literal `≪` constants (which are themselves unspecified).
* **Residue support.** `Unif((2ℤ+1)/2^n'ℤ)` is uniform on the **odd** residue classes modulo
  `2^n'` — **EXACT MATCH** with `oddResidues`/`oddResidues_card` from `EOC.TaoLike.ResidueTV`
  (cardinality `2^(n'-1)`, *not* `2^n'`), reused directly below as `unifOddResidues`.
* **`Q` vs `n`.** Tao's `n'` is our `Q`; the hypothesis is `n' ≥ (2+c₀)n`, i.e. `Q` must grow
  *linearly* in `n` (with slope `≥ 2+c₀`), not merely `Q ≥ n`. This exact relation is encoded
  in `finite_valuation_mixing` below; it is **not** combined with our own
  `2^(Q+S)/Y`-scale bound in this file (Part 11 of the Milestone 4 brief: the arithmetic
  budget connecting the two belongs to the *next* milestone).

## What is formally defined here

* `EventProb`, `EventTVBound`, `pushforward` — a lightweight event-probability/TV
  abstraction (no general measure theory), plus one generic sanity lemma
  `event_prob_le_of_tv`.
* `geom2` — the one-digit `Geom(2)` weight function, **with a Lean-checked proof** that it
  normalizes to `1` (`geom2_normalizes`).
* `valuationVector` — the real Syracuse valuation vector, reusing `a`/`orbit` (no
  duplication).
* `unifOddResidues` — uniform-on-odd-residues, reusing `oddResidues`/`oddResidues_card`.
* `TaoMixingConstants`, `TaoMixingHypothesis` — the external interface itself.

## EXTERNAL THEOREM INTERFACE — what is external / NOT proved in this repo

`TaoMixingHypothesis.finite_valuation_mixing` is an **EXTERNAL THEOREM INTERFACE**: an
explicit structure *field* (not a Lean `axiom`, not a `sorry`) that any downstream theorem
consumes as an *explicit hypothesis* `(tao : TaoMixingHypothesis)`. It is Tao's Proposition
1.9 as quoted and audited above; **nothing about its mathematical content is proved by the
Lean kernel** here or anywhere else in this repository. Whether a term of type
`TaoMixingHypothesis` actually exists is guaranteed only by Tao's own (published,
peer-reviewed) mathematical proof, not by this file. `#print axioms` on every genuinely
*proved* declaration in this file will show only the standard core axioms; no custom `axiom`
is introduced anywhere.

## What is NOT done here

* Tao's Proposition 1.9 is **not proved**.
* Persistence / shifted persistence / Chernoff bounds / long excursions are **not** touched.
* The arithmetic budget connecting our `2^(Q+S)/Y` bound to Tao's `n' ≥ (2+c₀)n` /
  `≪ 2^{-n'}` hypotheses (roughly `S + 2Q + margin ≤ log₂ Y`) is **not** encoded here; that
  belongs to the next milestone (`conditional_future_valuation_mixing`).
* The interface does **not** connect our verified residue-TV bound to `N`'s residue
  pushforward; Milestone 4 is an interface audit only (Part 6 of the brief).
-/

namespace EOC
namespace TaoExternal

open Finset

/-! ### Event-probability / total-variation abstraction -/

/-- A (not necessarily normalized, not necessarily nonnegative) event-probability functional
on `α`: assigns a real number to every subset ("event") of `α`. No measure-theoretic axioms
are imposed — this interface only needs TV-style comparison, not full probability theory. -/
def EventProb (α : Type*) := Set α → ℝ

/-- Pushforward of an event-probability functional along a map, via preimage. -/
def pushforward {α β : Type*} (P : EventProb α) (f : α → β) : EventProb β :=
  fun E => P (f ⁻¹' E)

/-- **Event-level total variation bound.** `EventTVBound P Q ε` means every event's
probability under `P` and `Q` differs by at most `ε`. For discrete laws this is the standard
`sup_E |P(E) - Q(E)|` total-variation distance — see the module doc for the exact
factor-of-2 relationship to Tao's literal `d_TV` (full-`Σ` convention, his eq. (1.9)). -/
def EventTVBound {α : Type*} (P Q : EventProb α) (ε : ℝ) : Prop :=
  ∀ E : Set α, |P E - Q E| ≤ ε

/-- **Minimal downstream sanity check.** If two event-probability functionals are within `ε`
in the `EventTVBound` sense, then any event's probability under `P` is bounded by its
probability under `Q` plus `ε`. This is the generic consequence downstream persistence
arguments actually need; it is deliberately *not* specialized to Collatz. -/
theorem event_prob_le_of_tv {α : Type*} {P Q : EventProb α} {ε : ℝ}
    (h : EventTVBound P Q ε) (E : Set α) : P E ≤ Q E + ε := by
  have h2 := (abs_le.mp (h E)).2
  linarith

/-! ### The one-digit `Geom(2)` law -/

/-- Tao's `Geom(2)`: `P(k) = 2^{-k}` for `k ≥ 1`, `0` off its support. Support is exactly
`{1,2,3,…}`, matching Tao's Definition 1.7 for `μ = 2` with no shift. -/
noncomputable def geom2 (k : ℕ) : ℝ := if 1 ≤ k then (1 / 2 : ℝ) ^ k else 0

theorem geom2_eq_of_pos {k : ℕ} (hk : 1 ≤ k) : geom2 k = (1 / 2 : ℝ) ^ k := if_pos hk

theorem geom2_eq_zero : geom2 0 = 0 := by unfold geom2; simp

/-- **Normalization check** (Part 4 of the Milestone 4 brief): `Σ_{k≥1} 2^{-k} = 1`,
Lean-checked, not merely asserted. -/
theorem geom2_normalizes : ∑' k : ℕ, geom2 k = 1 := by
  have hsum0 : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hval : ∑' n : ℕ, (1 / 2 : ℝ) ^ n = 2 := by
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
  have hle : ∀ k, 0 ≤ geom2 k ∧ geom2 k ≤ (1 / 2 : ℝ) ^ k := by
    intro k
    unfold geom2
    split_ifs with h
    · exact ⟨by positivity, le_refl _⟩
    · exact ⟨le_refl _, by positivity⟩
  have hsumg : Summable geom2 :=
    Summable.of_nonneg_of_le (fun k => (hle k).1) (fun k => (hle k).2) hsum0
  rw [hsumg.tsum_eq_zero_add, geom2_eq_zero, zero_add]
  have hgn1 : ∀ n : ℕ, geom2 (n + 1) = (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ n := by
    intro n
    rw [geom2_eq_of_pos (by omega)]
    ring
  rw [tsum_congr hgn1, tsum_mul_left, hval]
  norm_num

/-! ### The real-side valuation vector -/

/-- The length-`n` Syracuse valuation vector of `m`: `(a m, a (T m), …, a (T^(n-1) m))`,
reusing `a`/`orbit` (`EOC.Basic`, `EOC.ValuationWord`) exactly — this is Tao's `a⃗^(n)(N)`
(his eq. (1.8)), no duplication. -/
noncomputable def valuationVector (m n : ℕ) : Fin n → ℕ := fun i => a (orbit m i)

@[simp] theorem valuationVector_apply (m n : ℕ) (i : Fin n) :
    valuationVector m n i = a (orbit m i) := rfl

/-! ### Uniform distribution on odd residues -/

/-- Uniform distribution on the odd residue classes modulo `2^Q`, as an event-probability
functional on `ZMod (2^Q)`. Reuses `oddResidues`/`oddResidues_card`
(`EOC.TaoLike.ResidueTV`) directly: support cardinality `2^(Q-1)`, **not** `2^Q` (Part 9 of
the Milestone 4 brief — this is the same odd-residue convention as Tao's own
`Unif((2ℤ+1)/2^n'ℤ)`). -/
noncomputable def unifOddResidues (Q : ℕ) : EventProb (ZMod (2 ^ Q)) :=
  fun E => (∑ v ∈ oddResidues Q, Set.indicator E (fun _ => (1 : ℝ)) (v : ZMod (2 ^ Q))) /
    (2 : ℝ) ^ (Q - 1)

/-! ### Tao's external constants and hypothesis -/

/-- The constants Tao's Proposition 1.9 supplies for a given `c₀ > 0`: `c₁ > 0` (the mixing
rate, depending on `c₀`), together with the (also `c₀`-dependent, and otherwise
unspecified — Tao states his theorem with `≪` throughout) implicit constants `Cres`, `A`
hidden in the hypothesis's and conclusion's `≪` respectively. -/
structure TaoMixingConstants (c0 : ℝ) where
  c1 : ℝ
  hc1 : 0 < c1
  Cres : ℝ
  hCres : 0 < Cres
  A : ℝ
  hA : 0 < A

/-- **EXTERNAL THEOREM INTERFACE.** Tao's Proposition 1.9 (quoted and audited in the module
doc above), as an explicit hypothesis structure rather than a Lean `axiom`: any downstream
theorem that needs this result takes `(tao : TaoMixingHypothesis)` as an explicit parameter.
`iidGeom2Vector n` names the (not further constructed here — see the module doc) event-
probability functional of the iid `Geom(2)^n` law on `Fin n → ℕ`; `finite_valuation_mixing`
is the proposition itself. Neither field is proved by this repository. -/
structure TaoMixingHypothesis where
  /-- The law of `n` iid `Geom(2)` digits, as an event-probability functional. Its single-
  coordinate marginals are `geom2` (not asserted here as a structure axiom — see module doc:
  Milestone 4 is an interface audit, not a construction of the product law). -/
  iidGeom2Vector : (n : ℕ) → EventProb (Fin n → ℕ)
  /-- Tao's Proposition 1.9 itself. For every `c₀ > 0` there are constants
  `K : TaoMixingConstants c₀` such that: for every `n ≥ 1`, every residue modulus exponent
  `Qres` with `(Qres : ℝ) ≥ (2 + c₀) * n`, and every event-probability functional `N`
  on `ℕ` supported on the odd naturals, if `N`'s pushforward mod `2^Qres` is within
  `K.Cres * 2^(-Qres)` (`EventTVBound` convention) of uniform on odd residues, then `N`'s
  pushforward under `valuationVector · n` is within `K.A * 2^(-K.c1*n)` of `iidGeom2Vector n`. -/
  finite_valuation_mixing :
    ∀ c0 : ℝ, 0 < c0 → ∃ K : TaoMixingConstants c0,
      ∀ (n Qres : ℕ) (N : EventProb ℕ),
        1 ≤ n → (Qres : ℝ) ≥ (2 + c0) * (n : ℝ) →
        N {m : ℕ | ¬ Odd m} = 0 →
        EventTVBound (pushforward N (fun m => (m : ZMod (2 ^ Qres)))) (unifOddResidues Qres)
          (K.Cres * (2 : ℝ) ^ (-(Qres : ℝ))) →
        EventTVBound (pushforward N (fun m => valuationVector m n)) (iidGeom2Vector n)
          (K.A * (2 : ℝ) ^ (-(K.c1 * (n : ℝ))))

end TaoExternal
end EOC
