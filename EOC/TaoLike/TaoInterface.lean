import EOC.TaoLike.ResidueTV
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Tao finite-valuation mixing interface (Milestones 4 and 4B)

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
  **full L1** sum, with **no** `1/2` prefactor. This is formalized directly below as
  `taoL1TV` (Milestone 4B; superseding Milestone 4's `EventTVBound`, which conflated the
  literal Tao metric with the strictly weaker *event-sup* notion — see `EventDiscrepancyBound`
  and the metric bridge `event_discrepancy_le_taoL1TV`). This repo's Milestone-3 `dTV`-shaped
  quantity (`conditional_residue_tv_eta_bound`, `EOC.TaoLike.ResidueTV`) remains the *half*-L1
  / event-sup convention, i.e. exactly `EventDiscrepancyBound`'s sense, and is **exactly half**
  of `taoL1TV` for genuine discrete laws (a standard fact, *not* proved in this file — it is
  not needed: `finite_valuation_mixing` below is stated directly in `taoL1TV`, matching Tao
  literally, with no convention-factor caveat required).
* **Residue support.** `Unif((2ℤ+1)/2^n'ℤ)` is uniform on the **odd** residue classes modulo
  `2^n'` — **EXACT MATCH** with `oddResidues`/`oddResidues_card` from `EOC.TaoLike.ResidueTV`
  (cardinality `2^(n'-1)`, *not* `2^n'`), reused directly below as `unifOddResidues`.
* **`Q` vs `n`.** Tao's `n'` is our `Q`; the hypothesis is `n' ≥ (2+c₀)n`, i.e. `Q` must grow
  *linearly* in `n` (with slope `≥ 2+c₀`), not merely `Q ≥ n`. This exact relation is encoded
  in `finite_valuation_mixing` below; it is **not** combined with our own
  `2^(Q+S)/Y`-scale bound in this file (Part 11 of the Milestone 4 brief: the arithmetic
  budget connecting the two belongs to a later milestone).
* **`n = 0`.** Tao's literal domain is `n ∈ ℕ` (which includes `0`); our interface requires
  `1 ≤ n`. This is an honest **interface specialization** (documented, not a literal-match
  claim) — harmless since all downstream uses have a positive horizon, but `n = 0` is not
  literally covered.
* **`c₀` quantifier.** The literal wording is "there exist an absolute constant `c₀ > 0`"
  (existential), but the surrounding discussion in the source (and the proof, which is
  uniform in `c₀`) supports instantiating the proposition at *any* chosen `c₀ > 0` — the
  "existence" is of a single global witness, not a restriction to a distinguished one.
  We encode the **proof-level generalization** `∀ c0 > 0, …` rather than the bare literal
  existential, and flag this explicitly here per Part 10 of the Milestone 4B brief, rather
  than silently strengthening the external theorem without comment.

## Milestone 4B: making the geometric target semantically concrete

Milestone 4 left `iidGeom2Vector : (n : ℕ) → EventProb (Fin n → ℕ)` as an **unconstrained**
structure field: nothing forced it to have `Geom(2)` marginals, be nonnegative, additive, or
independent across coordinates. A downstream proof could have discharged
`TaoMixingHypothesis` against a functional bearing no relation to Tao's actual target law,
while the name `iidGeom2Vector` suggested otherwise. Milestone 4B repairs this:

* `atomWeight n a := ∏ i, geom2 (a i)` is the joint atom weight of the length-`n` iid
  `Geom(2)` vector at `a`, and `atomWeight_tsum_eq_one` is a **Lean-checked proof** (not an
  assumption) that `Σ' a : Fin n → ℕ, atomWeight n a = 1`, established by induction on `n`
  using the finite-product tsum factorization `Σ' p : ℕ × (Fin n → ℕ), f p.1 * g p.2 =
  (Σ' k, f k)(Σ' b, g b)` (`Summable.tsum_mul_tsum`) transported along `Fin.consEquiv`. This
  is the semantic certificate that the target is genuinely the iid product law, not merely
  suggestively named.
* `genEventProb w` builds an `EventProb` from any weight function by countable summation over
  the event (`Σ' x, indicator E w x`); with a summable weight, an `EventProb` built this way
  is additive by construction, which is exactly what makes the metric bridge provable.
* `iidGeom2VectorProb n := genEventProb (atomWeight n)` is the **fixed, concrete** target;
  `TaoMixingHypothesis` no longer carries a free `iidGeom2Vector` field and refers to
  `iidGeom2VectorProb` directly.
* `taoL1TV P Q := Σ' x, |P {x} - Q {x}|` is Tao's own metric, literally (his eq. (1.9)),
  defined for *any* `EventProb`; the later Tao interface separately requires its starting
  functional to satisfy `IsProbabilityLaw`.
* `EventDiscrepancyBound` is the strictly weaker event-sup notion (Milestone 4's
  `EventTVBound`, renamed for honesty); `event_discrepancy_le_taoL1TV` proves the one
  direction we actually need (`taoL1TV ≤ ε → event-sup ≤ ε`) for laws of `genEventProb`
  shape, i.e. exactly the concrete geometric/uniform-residue targets built here.

## M38: repairing the starting-law boundary

`EventProb α` deliberately remains a lightweight function type because existing concrete
laws and pushforwards use it extensionally.  It is not treated as a probability law by type
alone.  `IsProbabilityLaw P` now requires a representation `P = genEventProb w` with
nonnegative, summable atom weights of total mass one, and `finite_valuation_mixing` quantifies
only over event functionals carrying this certificate.  Thus singleton masses determine all
event values, closing the malformed interface that previously admitted arbitrary values on
nonsingleton events.

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
  belongs to a later milestone (`conditional_future_valuation_mixing`).
* The interface does **not** connect our verified residue-TV bound to `N`'s residue
  pushforward.
-/

namespace EOC
namespace TaoExternal

open Finset

/-! ### Event-function abstraction -/

/-- An extensional real-valued event functional on `α`.  This lightweight carrier remains
useful for concrete generated laws and their pushforwards.  It is not by itself a probability
law; `IsProbabilityLaw` below supplies that boundary condition. -/
def EventProb (α : Type*) := Set α → ℝ

/-- Pushforward of an event-probability functional along a map, via preimage. -/
def pushforward {α β : Type*} (P : EventProb α) (f : α → β) : EventProb β :=
  fun E => P (f ⁻¹' E)

/-- **Event discrepancy** (Milestone 4's `EventTVBound`, renamed): `EventDiscrepancyBound P Q
ε` means every event's probability under `P` and `Q` differs by at most `ε`. This is the
`sup_E |P(E) - Q(E)|` notion — strictly weaker than (in general half of) Tao's literal
`taoL1TV` below; see the module doc. -/
def EventDiscrepancyBound {α : Type*} (P Q : EventProb α) (ε : ℝ) : Prop :=
  ∀ E : Set α, |P E - Q E| ≤ ε

theorem event_prob_le_of_discrepancy {α : Type*} {P Q : EventProb α} {ε : ℝ}
    (h : EventDiscrepancyBound P Q ε) (E : Set α) : P E ≤ Q E + ε := by
  have h2 := (abs_le.mp (h E)).2
  linarith

/-! ### Discrete laws generated by a weight function -/

/-- Build an `EventProb` from a weight function by countable summation over the event. With a
summable weight, an `EventProb` of this shape is additive by construction: this is what makes
the metric bridge `event_discrepancy_le_taoL1TV` below provable, in contrast to a wholly
arbitrary `EventProb` (which need not be additive at all). -/
noncomputable def genEventProb {α : Type*} (w : α → ℝ) : EventProb α :=
  fun E => ∑' x, Set.indicator E w x

theorem genEventProb_singleton {α : Type*} (w : α → ℝ) (a : α) :
    genEventProb w {a} = w a := by
  unfold genEventProb
  rw [tsum_eq_single a (fun b hb => by simp [Set.indicator, hb])]
  simp

theorem genEventProb_empty {α : Type*} (w : α → ℝ) : genEventProb w ∅ = 0 := by
  unfold genEventProb; simp

theorem genEventProb_univ {α : Type*} (w : α → ℝ) (h : ∑' x, w x = 1) :
    genEventProb w Set.univ = 1 := by
  unfold genEventProb
  simpa using h

/-- A genuine discrete probability law: an event functional generated by nonnegative,
summable atom weights of total mass one.  Requiring this representation at the external Tao
boundary rules out arbitrary values on nonsingleton events while avoiding unnecessary
measure-theory machinery for the countable laws used in this repository. -/
def IsProbabilityLaw {α : Type*} (P : EventProb α) : Prop :=
  ∃ w : α → ℝ,
    (∀ x, 0 ≤ w x) ∧ Summable w ∧ (∑' x, w x = 1) ∧ P = genEventProb w

theorem isProbabilityLaw_genEventProb {α : Type*} (w : α → ℝ)
    (hw_nonneg : ∀ x, 0 ≤ w x) (hw_summable : Summable w)
    (hw_sum : ∑' x, w x = 1) :
    IsProbabilityLaw (genEventProb w) :=
  ⟨w, hw_nonneg, hw_summable, hw_sum, rfl⟩

theorem IsProbabilityLaw.nonneg {α : Type*} {P : EventProb α}
    (hP : IsProbabilityLaw P) (E : Set α) : 0 ≤ P E := by
  obtain ⟨w, hw_nonneg, hw_summable, _, rfl⟩ := hP
  unfold genEventProb
  exact tsum_nonneg (fun x => Set.indicator_nonneg (fun y _ => hw_nonneg y) x)

theorem IsProbabilityLaw.univ {α : Type*} {P : EventProb α}
    (hP : IsProbabilityLaw P) : P Set.univ = 1 := by
  obtain ⟨w, _, _, hw_sum, rfl⟩ := hP
  exact genEventProb_univ w hw_sum

/-- A genuine discrete law is determined on every event by its singleton masses.  This is
the exact structural fact absent from the old Tao interface. -/
theorem IsProbabilityLaw.event_eq_tsum_singletons {α : Type*} {P : EventProb α}
    (hP : IsProbabilityLaw P) (E : Set α) :
    P E = ∑' x, Set.indicator E (fun y => P {y}) x := by
  obtain ⟨w, _, _, _, rfl⟩ := hP
  simp_rw [genEventProb_singleton]
  rfl

/-- Two genuine discrete laws with the same singleton masses agree on every event. -/
theorem IsProbabilityLaw.ext_singleton {α : Type*} {P Q : EventProb α}
    (hP : IsProbabilityLaw P) (hQ : IsProbabilityLaw Q)
    (h_singleton : ∀ x, P {x} = Q {x}) : P = Q := by
  funext E
  rw [hP.event_eq_tsum_singletons E, hQ.event_eq_tsum_singletons E]
  apply tsum_congr
  intro x
  by_cases hx : x ∈ E
  · simp only [Set.indicator_of_mem hx]
    exact h_singleton x
  · simp only [Set.indicator_of_notMem hx]

/-! ### Tao's literal metric and its bridge to event discrepancy -/

/-- **Tao's total-variation metric, literally** (his eq. (1.9)): the full-`Σ` sum of
atom-probability differences. Defined for any `EventProb` (in particular the abstract
external starting law `N`), via singleton evaluation. -/
noncomputable def taoL1TV {α : Type*} (P Q : EventProb α) : ℝ :=
  ∑' x : α, |P {x} - Q {x}|

theorem taoL1TV_genEventProb {α : Type*} (w1 w2 : α → ℝ) :
    taoL1TV (genEventProb w1) (genEventProb w2) = ∑' x, |w1 x - w2 x| := by
  unfold taoL1TV
  exact tsum_congr (fun x => by rw [genEventProb_singleton, genEventProb_singleton])

/-- **Metric bridge** (Part 6/7 of the Milestone 4B brief): Tao's full-`Σ` bound implies the
weaker event-discrepancy bound, for laws generated by a nonnegative summable weight function
(exactly the shape of `iidGeom2VectorProb`/`unifOddResidues` below). We prove only the
direction Tao's theorem actually gives us (`taoL1TV ≤ ε → event discrepancy ≤ ε`); the
converse (`event discrepancy ≤ ε → taoL1TV ≤ 2ε`) is not needed downstream and is not proved
here. -/
theorem event_discrepancy_le_taoL1TV {α : Type*} {w1 w2 : α → ℝ}
    (h1nn : ∀ x, 0 ≤ w1 x) (h2nn : ∀ x, 0 ≤ w2 x)
    (h1 : Summable w1) (h2 : Summable w2) :
    EventDiscrepancyBound (genEventProb w1) (genEventProb w2)
      (taoL1TV (genEventProb w1) (genEventProb w2)) := by
  rw [taoL1TV_genEventProb]
  intro E
  have hind1nn : ∀ x, 0 ≤ Set.indicator E w1 x := fun x => Set.indicator_nonneg (fun y _ => h1nn y) x
  have hind2nn : ∀ x, 0 ≤ Set.indicator E w2 x := fun x => Set.indicator_nonneg (fun y _ => h2nn y) x
  have hind1le : ∀ x, Set.indicator E w1 x ≤ w1 x :=
    fun x => Set.indicator_le_self' (fun y _ => h1nn y) x
  have hind2le : ∀ x, Set.indicator E w2 x ≤ w2 x :=
    fun x => Set.indicator_le_self' (fun y _ => h2nn y) x
  have hind1 : Summable (Set.indicator E w1) :=
    Summable.of_nonneg_of_le hind1nn hind1le h1
  have hind2 : Summable (Set.indicator E w2) :=
    Summable.of_nonneg_of_le hind2nn hind2le h2
  have hdiff_dom : ∀ x, |Set.indicator E w1 x - Set.indicator E w2 x| ≤ w1 x + w2 x := by
    intro x
    rw [abs_sub_le_iff]
    refine ⟨?_, ?_⟩
    · linarith [hind1le x, hind2nn x, h1nn x, h2nn x]
    · linarith [hind2le x, hind1nn x, h1nn x, h2nn x]
  have habs_summable :
      Summable (fun x => |Set.indicator E w1 x - Set.indicator E w2 x|) :=
    Summable.of_nonneg_of_le (fun x => abs_nonneg _) hdiff_dom (h1.add h2)
  have hw12_dom : ∀ x, |w1 x - w2 x| ≤ w1 x + w2 x := by
    intro x; rw [abs_sub_le_iff]; constructor <;> linarith [h1nn x, h2nn x]
  have hw12_summable : Summable (fun x => |w1 x - w2 x|) :=
    Summable.of_nonneg_of_le (fun x => abs_nonneg _) hw12_dom (h1.add h2)
  have hstep1 : genEventProb w1 E - genEventProb w2 E
      = ∑' x, (Set.indicator E w1 x - Set.indicator E w2 x) := by
    unfold genEventProb; exact (Summable.tsum_sub hind1 hind2).symm
  have hstep2 : |∑' x, (Set.indicator E w1 x - Set.indicator E w2 x)|
      ≤ ∑' x, |Set.indicator E w1 x - Set.indicator E w2 x| := by
    have hnorm := norm_tsum_le_tsum_norm (f := fun x =>
      Set.indicator E w1 x - Set.indicator E w2 x) habs_summable
    rwa [Real.norm_eq_abs, show (fun x => ‖Set.indicator E w1 x - Set.indicator E w2 x‖)
      = (fun x => |Set.indicator E w1 x - Set.indicator E w2 x|) from
      funext (fun x => Real.norm_eq_abs _)] at hnorm
  calc |genEventProb w1 E - genEventProb w2 E|
      = |∑' x, (Set.indicator E w1 x - Set.indicator E w2 x)| := by rw [hstep1]
    _ ≤ ∑' x, |Set.indicator E w1 x - Set.indicator E w2 x| := hstep2
    _ ≤ ∑' x, |w1 x - w2 x| := by
        apply Summable.tsum_mono habs_summable hw12_summable
        intro x
        by_cases hx : x ∈ E
        · simp [Set.indicator, hx]
        · simp [Set.indicator, hx, abs_nonneg]

/-! ### The one-digit `Geom(2)` law -/

/-- Tao's `Geom(2)`: `P(k) = 2^{-k}` for `k ≥ 1`, `0` off its support. Support is exactly
`{1,2,3,…}`, matching Tao's Definition 1.7 for `μ = 2` with no shift. -/
noncomputable def geom2 (k : ℕ) : ℝ := if 1 ≤ k then (1 / 2 : ℝ) ^ k else 0

theorem geom2_eq_of_pos {k : ℕ} (hk : 1 ≤ k) : geom2 k = (1 / 2 : ℝ) ^ k := if_pos hk

theorem geom2_eq_zero : geom2 0 = 0 := by unfold geom2; simp

theorem geom2_nonneg (k : ℕ) : 0 ≤ geom2 k := by unfold geom2; split_ifs <;> positivity

theorem geom2_le_half_pow (k : ℕ) : geom2 k ≤ (1 / 2 : ℝ) ^ k := by
  unfold geom2; split_ifs with h
  · exact le_refl _
  · positivity

theorem geom2_summable : Summable geom2 := by
  have hsum0 : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  exact Summable.of_nonneg_of_le geom2_nonneg geom2_le_half_pow hsum0

/-- **Normalization check** (Part 4 of the Milestone 4 brief, preserved from Milestone 4):
`Σ_{k≥1} 2^{-k} = 1`, Lean-checked, not merely asserted. -/
theorem geom2_normalizes : ∑' k : ℕ, geom2 k = 1 := by
  have hsum0 : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hval : ∑' n : ℕ, (1 / 2 : ℝ) ^ n = 2 := by
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
  rw [geom2_summable.tsum_eq_zero_add, geom2_eq_zero, zero_add]
  have hgn1 : ∀ n : ℕ, geom2 (n + 1) = (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ n := by
    intro n
    rw [geom2_eq_of_pos (by omega)]
    ring
  rw [tsum_congr hgn1, tsum_mul_left, hval]
  norm_num

/-! ### The iid `Geom(2)^n` vector law, made concrete (Milestone 4B) -/

/-- The joint atom weight of the length-`n` iid `Geom(2)` vector at `a`: `∏ i, geom2 (a i)`.
This is the semantic core of the target law (Part 3 of the Milestone 4B brief). -/
noncomputable def atomWeight (n : ℕ) (a : Fin n → ℕ) : ℝ := ∏ i, geom2 (a i)

theorem atomWeight_nonneg (n : ℕ) (a : Fin n → ℕ) : 0 ≤ atomWeight n a :=
  Finset.prod_nonneg (fun i _ => geom2_nonneg _)

theorem atomWeight_cons (n : ℕ) (k : ℕ) (a : Fin n → ℕ) :
    atomWeight (n + 1) (Fin.cons k a) = geom2 k * atomWeight n a := by
  unfold atomWeight
  rw [Fin.prod_univ_succ]
  simp

theorem atomWeight_summable (n : ℕ) : Summable (atomWeight n) := by
  induction n with
  | zero => exact Summable.of_finite
  | succ n ih =>
    have hmul : Summable (fun p : ℕ × (Fin n → ℕ) => geom2 p.1 * atomWeight n p.2) :=
      Summable.mul_of_nonneg geom2_summable ih geom2_nonneg (atomWeight_nonneg n)
    have heq : (fun p : ℕ × (Fin n → ℕ) => geom2 p.1 * atomWeight n p.2)
        = (atomWeight (n + 1)) ∘ (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)) := by
      funext p
      simp only [Function.comp_apply]
      rw [← atomWeight_cons n p.1 p.2]
      congr 1
    rw [heq] at hmul
    exact (Equiv.summable_iff (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ))).mp hmul

theorem atomWeight_tsum_succ (n : ℕ) :
    ∑' a : Fin (n + 1) → ℕ, atomWeight (n + 1) a
      = (∑' k : ℕ, geom2 k) * ∑' a : Fin n → ℕ, atomWeight n a := by
  rw [← Equiv.tsum_eq (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ))]
  have heq : ∀ p : ℕ × (Fin n → ℕ),
      atomWeight (n + 1) (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ) p)
        = geom2 p.1 * atomWeight n p.2 := by
    intro p
    rw [← atomWeight_cons n p.1 p.2]
    congr 1
  simp_rw [heq]
  exact (Summable.tsum_mul_tsum geom2_summable (atomWeight_summable n)
    (Summable.mul_of_nonneg geom2_summable (atomWeight_summable n) geom2_nonneg
      (atomWeight_nonneg n))).symm

/-- **Product normalization** (Part 3/13 of the Milestone 4B brief) — established by
induction, not merely postulated: `Σ' a : Fin n → ℕ, ∏ i, geom2 (a i) = 1`. -/
theorem atomWeight_tsum_eq_one (n : ℕ) : ∑' a : Fin n → ℕ, atomWeight n a = 1 := by
  induction n with
  | zero => simp [atomWeight]
  | succ n ih => rw [atomWeight_tsum_succ, ih, geom2_normalizes, mul_one]

/-- **The fixed, concrete iid `Geom(2)^n` target law** (Part 4/8 of the Milestone 4B brief):
`TaoMixingHypothesis` refers to this directly, replacing Milestone 4's unconstrained
`iidGeom2Vector` field. -/
noncomputable def iidGeom2VectorProb (n : ℕ) : EventProb (Fin n → ℕ) := genEventProb (atomWeight n)

/-- **The atom/singleton certificate** (Part 13 of the Milestone 4B brief): the semantic
statement that `iidGeom2VectorProb` truly assigns each vector its iid product probability. -/
theorem iidGeom2VectorProb_singleton (n : ℕ) (a : Fin n → ℕ) :
    iidGeom2VectorProb n {a} = ∏ i, geom2 (a i) :=
  genEventProb_singleton (atomWeight n) a

theorem iidGeom2VectorProb_univ (n : ℕ) : iidGeom2VectorProb n Set.univ = 1 :=
  genEventProb_univ (atomWeight n) (atomWeight_tsum_eq_one n)

theorem iidGeom2VectorProb_empty (n : ℕ) : iidGeom2VectorProb n ∅ = 0 :=
  genEventProb_empty (atomWeight n)

theorem iidGeom2VectorProb_isProbabilityLaw (n : ℕ) :
    IsProbabilityLaw (iidGeom2VectorProb n) := by
  unfold iidGeom2VectorProb
  exact isProbabilityLaw_genEventProb (atomWeight n) (atomWeight_nonneg n)
    (atomWeight_summable n) (atomWeight_tsum_eq_one n)

/-! ### The real-side valuation vector -/

/-- The length-`n` Syracuse valuation vector of `m`: `(a m, a (T m), …, a (T^(n-1) m))`,
reusing `a`/`orbit` (`EOC.Basic`, `EOC.ValuationWord`) exactly — this is Tao's `a⃗^(n)(N)`
(his eq. (1.8)), no duplication. -/
noncomputable def valuationVector (m n : ℕ) : Fin n → ℕ := fun i => a (orbit m i)

@[simp] theorem valuationVector_apply (m n : ℕ) (i : Fin n) :
    valuationVector m n i = a (orbit m i) := rfl

/-! ### Uniform distribution on odd residues -/

/-- Weight function for uniform-on-odd-residues modulo `2^Q`: `1/2^(Q-1)` on the (image of
the) odd residues, `0` elsewhere. -/
noncomputable def unifOddResiduesWeight (Q : ℕ) (v : ZMod (2 ^ Q)) : ℝ :=
  (if v ∈ (oddResidues Q).image (fun n : ℕ => (n : ZMod (2 ^ Q))) then 1 else 0) /
    (2 : ℝ) ^ (Q - 1)

/-- Uniform distribution on the odd residue classes modulo `2^Q`, as an event-probability
functional on `ZMod (2^Q)`, built via `genEventProb` (hence additive by construction).
Reuses `oddResidues`/`oddResidues_card` (`EOC.TaoLike.ResidueTV`) directly: support
cardinality `2^(Q-1)`, **not** `2^Q` (Part 9 of the Milestone 4 brief — this is the same
odd-residue convention as Tao's own `Unif((2ℤ+1)/2^n'ℤ)`). -/
noncomputable def unifOddResidues (Q : ℕ) : EventProb (ZMod (2 ^ Q)) :=
  genEventProb (unifOddResiduesWeight Q)

theorem unifOddResiduesWeight_nonneg (Q : ℕ) (v : ZMod (2 ^ Q)) :
    0 ≤ unifOddResiduesWeight Q v := by
  unfold unifOddResiduesWeight; positivity

/-- **Normalization of the uniform-odd-residue target** (Part 11 of the Milestone 4B
brief), for `Q ≥ 1`: `unifOddResidues Q Set.univ = 1`. -/
theorem unifOddResidues_univ (Q : ℕ) (hQ : 1 ≤ Q) : unifOddResidues Q Set.univ = 1 := by
  apply genEventProb_univ
  have : NeZero (2 ^ Q) := ⟨by positivity⟩
  rw [tsum_fintype]
  have hinj : Set.InjOn (fun n : ℕ => (n : ZMod (2 ^ Q))) (oddResidues Q) := by
    intro x hx y hy hxy
    have hxlt : x < 2 ^ Q := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
    have hylt : y < 2 ^ Q := Finset.mem_range.mp (Finset.mem_filter.mp hy).1
    have := congrArg ZMod.val hxy
    rwa [ZMod.val_cast_of_lt hxlt, ZMod.val_cast_of_lt hylt] at this
  have hcard : ((oddResidues Q).image (fun n : ℕ => (n : ZMod (2 ^ Q)))).card
      = (oddResidues Q).card := Finset.card_image_of_injOn hinj
  rw [oddResidues_card Q hQ] at hcard
  unfold unifOddResiduesWeight
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  have hbool : (∑ v : ZMod (2 ^ Q),
      (if v ∈ (oddResidues Q).image (fun n : ℕ => (n : ZMod (2 ^ Q))) then (1 : ℝ) else 0))
      = ((oddResidues Q).image (fun n : ℕ => (n : ZMod (2 ^ Q)))).card := by
    rw [Finset.sum_boole]
    congr 1
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [hbool, hcard]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (Q - 1) := by positivity
  push_cast
  field_simp

theorem unifOddResidues_isProbabilityLaw (Q : ℕ) (hQ : 1 ≤ Q) :
    IsProbabilityLaw (unifOddResidues Q) := by
  unfold unifOddResidues
  apply isProbabilityLaw_genEventProb (unifOddResiduesWeight Q)
      (unifOddResiduesWeight_nonneg Q) Summable.of_finite
  have h := unifOddResidues_univ Q hQ
  simpa [unifOddResidues, genEventProb] using h

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
Unlike Milestone 4, the conclusion refers directly to the **concrete** `iidGeom2VectorProb n`
(Milestone 4B) — there is no arbitrary `iidGeom2Vector` field left to instantiate against a
functional unrelated to Tao's actual target law. Both sides of `finite_valuation_mixing` are
stated in Tao's own literal metric `taoL1TV` (his eq. (1.9), full-`Σ` convention).  The
starting event functional `N` is required to satisfy `IsProbabilityLaw N`, so it is generated
by nonnegative, summable atom weights of total mass one rather than being an arbitrary set
function. Converting *our own* half-L1 `ResidueTV` bound into this full-L1 hypothesis is a
genuinely separate step, deferred to the next milestone (the factor of 2 between the two
conventions matters there, not here — see the module doc). -/
structure TaoMixingHypothesis where
  /-- Tao's Proposition 1.9 itself. For every `c₀ > 0` there are constants
  `K : TaoMixingConstants c₀` such that: for every `n ≥ 1`, every residue modulus exponent
  `Qres` with `(Qres : ℝ) ≥ (2 + c₀) * n`, and every discrete probability law `N` on `ℕ`
  supported on the odd naturals, if `N`'s pushforward mod `2^Qres` is within
  `K.Cres * 2^(-Qres)` of uniform on odd residues **in Tao's own `taoL1TV` metric**, then
  `N`'s pushforward under `valuationVector · n` is within `K.A * 2^(-K.c1*n)` of the concrete
  `iidGeom2VectorProb n`, again in `taoL1TV`. -/
  finite_valuation_mixing :
    ∀ c0 : ℝ, 0 < c0 → ∃ K : TaoMixingConstants c0,
      ∀ (n Qres : ℕ) (N : EventProb ℕ),
        IsProbabilityLaw N →
        1 ≤ n → (Qres : ℝ) ≥ (2 + c0) * (n : ℝ) →
        N {m : ℕ | ¬ Odd m} = 0 →
        taoL1TV (pushforward N (fun m => (m : ZMod (2 ^ Qres)))) (unifOddResidues Qres)
          ≤ K.Cres * (2 : ℝ) ^ (-(Qres : ℝ)) →
        taoL1TV (pushforward N (fun m => valuationVector m n)) (iidGeom2VectorProb n)
          ≤ K.A * (2 : ℝ) ^ (-(K.c1 * (n : ℝ)))

/-- **Fixed-witness Tao mixing property** (interface refactor, Milestone "uniform Tao witness"):
exactly the property `tao.finite_valuation_mixing c0 hc0` asserts of its existentially-chosen
`K`, but stated as a standalone `Prop` about a *given* `K`. This is what lets a single `K`
(chosen once, e.g. via `(tao.finite_valuation_mixing c0 hc0).choose` /
`(tao.finite_valuation_mixing c0 hc0).choose_spec`) be threaded uniformly through many
downstream applications (e.g. one per realized prefix in Milestone 11's GOOD-prefix
aggregation), instead of each downstream theorem re-deriving its own — mathematically
unconstrained, but *Lean-opaque* — witness from `tao`. Purely a witness-management
definition: no new mathematical content, no strengthening of `TaoMixingHypothesis`. -/
def TaoMixingProperty (c0 : ℝ) (K : TaoMixingConstants c0) : Prop :=
  ∀ (n Qres : ℕ) (N : EventProb ℕ),
    IsProbabilityLaw N →
    1 ≤ n → (Qres : ℝ) ≥ (2 + c0) * (n : ℝ) →
    N {m : ℕ | ¬ Odd m} = 0 →
    taoL1TV (pushforward N (fun m => (m : ZMod (2 ^ Qres)))) (unifOddResidues Qres)
      ≤ K.Cres * (2 : ℝ) ^ (-(Qres : ℝ)) →
    taoL1TV (pushforward N (fun m => valuationVector m n)) (iidGeom2VectorProb n)
      ≤ K.A * (2 : ℝ) ^ (-(K.c1 * (n : ℝ)))

/-- Any `K` obtained from `tao.finite_valuation_mixing c0 hc0` satisfies `TaoMixingProperty`
by construction — the bridge from the existential interface to the fixed-witness one. -/
theorem taoMixingProperty_choose (tao : TaoMixingHypothesis) (c0 : ℝ) (hc0 : 0 < c0) :
    TaoMixingProperty c0 (tao.finite_valuation_mixing c0 hc0).choose :=
  (tao.finite_valuation_mixing c0 hc0).choose_spec

end TaoExternal
end EOC
