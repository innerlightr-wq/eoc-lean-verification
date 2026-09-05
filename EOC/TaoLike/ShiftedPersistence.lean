import EOC.TaoLike.ConditionalMixing
import EOC.TaoLike.PersistenceModel

/-!
# Shifted persistence transfer (Milestone 7)

Combines Milestone 5's `conditional_future_event_bound` (real Collatz future valuation vector
vs. `iidGeom2VectorProb`, within an explicit `TaoMixingHypothesis` error) with Milestone 6's
`geometric_persistence_upper_bound`/`geometric_persistence_upper_bound_bits` (iid persistence
Chernoff rate) to bound the probability that a real Collatz future block persists below a
drift ceiling `c`, for `geomPersistenceEvent collatzAlpha c n` taken as the event `E`.

**EPISTEMIC STATUS.** FORMALLY VERIFIED *conditional on* `TaoMixingHypothesis` — same external
dependency as Milestone 5, inherited unchanged through the hypothesis, not a global `axiom`.
This is a single-restart, single-future-block averaged/conditional statement: ONE admissible
restart + ONE future block + the persistence event transfer. It is **not** the early/late
global theorem (no `ε log Y` split, no union over shifts, no Borel–Cantelli conclusion — those
are later milestones), and it is **not** a pointwise claim about individual Collatz orbits, nor
a formalization of Tao's Proposition 1.9 itself, nor of the Collatz conjecture.
-/

namespace EOC
namespace TaoExternal

open Finset

/-- **Fixed-witness natural-log shifted persistence transfer.** Specializes
`conditional_future_event_bound_of_constants` at `E := geomPersistenceEvent collatzAlpha c n`
and bounds its iid term with `geometric_persistence_upper_bound`. Reuses Milestones 5 and 6 as
black boxes: no unfolding of `iidGeom2VectorProb`, `conditionalRestartLaw`, `tsum`, the
Chernoff proof, or the residue-TV mixing proof. `K` is supplied by the caller (with its
defining `TaoMixingProperty hK`) rather than derived internally, so the same `K` reappears
verbatim in the conclusion — enabling uniform reuse across many realized prefixes. -/
theorem conditional_shifted_persistence_upper_bound_of_constants
    (c0 : ℝ) (K : TaoMixingConstants c0) (hK : TaoMixingProperty c0 K)
    (d : ℕ → ℕ) (t r : ℕ) (h : Realizes d t r) (ht : 1 ≤ t)
    (c : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (Y H : ℕ) (hYr : r ≤ Y) (hYpos : 0 < Y) (η : ℝ) (hη : 0 < η)
    (hH : η * (Y : ℝ) ≤ (H : ℝ))
    (Q : ℕ) (hQrel : (Q : ℝ) ≥ (2 + c0) * (n : ℝ)) (hQ1 : 1 ≤ Q)
    (hthick : 4 * (2 ^ (S d t + 1) : ℝ) ≤ η * (Y : ℝ)) :
    ∃ (kmin N : ℕ) (W : ℝ), 0 < W ∧
      W = ∑ j ∈ range N, (1 : ℝ) / ((r : ℝ) + (2 ^ (S d t + 1) : ℝ) * ((kmin : ℝ) + j)) ∧
      (2 * (1 + 1 / η) * (2 : ℝ) ^ (S d t + 2 * Q) ≤ K.Cres * (Y : ℝ) →
        pushforward (conditionalRestartLaw r (2 ^ (S d t + 1)) kmin N W (orbit r t) t)
            (fun m : ℕ => valuationVector m n) (geomPersistenceEvent collatzAlpha c n)
          ≤ Real.exp (lambdaStar * c) * Real.exp (-(rateNats * (n : ℝ)))
            + K.A * (2 : ℝ) ^ (-(K.c1 * (n : ℝ)))) := by
  obtain ⟨kmin, N, W, hWpos, hWdef, hmix⟩ :=
    conditional_future_event_bound_of_constants c0 K hK d t r h ht n hn Y H hYr hYpos η hη hH Q
      hQrel hQ1 hthick (geomPersistenceEvent collatzAlpha c n)
  refine ⟨kmin, N, W, hWpos, hWdef, ?_⟩
  intro hbudget
  have hreal := hmix hbudget
  have hiid := geometric_persistence_upper_bound c n hn
  linarith [hreal, hiid]

/-- **Convenience wrapper** (unchanged public API): chooses `K` once from `tao`, then invokes
the fixed-witness version. -/
theorem conditional_shifted_persistence_upper_bound
    (tao : TaoMixingHypothesis)
    (d : ℕ → ℕ) (t r : ℕ) (h : Realizes d t r) (ht : 1 ≤ t)
    (c : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (Y H : ℕ) (hYr : r ≤ Y) (hYpos : 0 < Y) (η : ℝ) (hη : 0 < η)
    (hH : η * (Y : ℝ) ≤ (H : ℝ))
    (c0 : ℝ) (hc0 : 0 < c0) (Q : ℕ) (hQrel : (Q : ℝ) ≥ (2 + c0) * (n : ℝ)) (hQ1 : 1 ≤ Q)
    (hthick : 4 * (2 ^ (S d t + 1) : ℝ) ≤ η * (Y : ℝ)) :
    ∃ (K : TaoMixingConstants c0) (kmin N : ℕ) (W : ℝ), 0 < W ∧
      W = ∑ j ∈ range N, (1 : ℝ) / ((r : ℝ) + (2 ^ (S d t + 1) : ℝ) * ((kmin : ℝ) + j)) ∧
      (2 * (1 + 1 / η) * (2 : ℝ) ^ (S d t + 2 * Q) ≤ K.Cres * (Y : ℝ) →
        pushforward (conditionalRestartLaw r (2 ^ (S d t + 1)) kmin N W (orbit r t) t)
            (fun m : ℕ => valuationVector m n) (geomPersistenceEvent collatzAlpha c n)
          ≤ Real.exp (lambdaStar * c) * Real.exp (-(rateNats * (n : ℝ)))
            + K.A * (2 : ℝ) ^ (-(K.c1 * (n : ℝ)))) := by
  obtain ⟨K, hK⟩ := tao.finite_valuation_mixing c0 hc0
  obtain ⟨kmin, N, W, hWpos, hWdef, hbound⟩ :=
    conditional_shifted_persistence_upper_bound_of_constants c0 K hK d t r h ht c n hn Y H hYr
      hYpos η hη hH Q hQrel hQ1 hthick
  exact ⟨K, kmin, N, W, hWpos, hWdef, hbound⟩

/-- **Fixed-witness bit-rate corollary.** Same statement, iid term expressed via `I0` and
`Real.rpow`; `K` supplied explicitly as above. -/
theorem conditional_shifted_persistence_upper_bound_bits_of_constants
    (c0 : ℝ) (K : TaoMixingConstants c0) (hK : TaoMixingProperty c0 K)
    (d : ℕ → ℕ) (t r : ℕ) (h : Realizes d t r) (ht : 1 ≤ t)
    (c : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (Y H : ℕ) (hYr : r ≤ Y) (hYpos : 0 < Y) (η : ℝ) (hη : 0 < η)
    (hH : η * (Y : ℝ) ≤ (H : ℝ))
    (Q : ℕ) (hQrel : (Q : ℝ) ≥ (2 + c0) * (n : ℝ)) (hQ1 : 1 ≤ Q)
    (hthick : 4 * (2 ^ (S d t + 1) : ℝ) ≤ η * (Y : ℝ)) :
    ∃ (kmin N : ℕ) (W : ℝ), 0 < W ∧
      W = ∑ j ∈ range N, (1 : ℝ) / ((r : ℝ) + (2 ^ (S d t + 1) : ℝ) * ((kmin : ℝ) + j)) ∧
      (2 * (1 + 1 / η) * (2 : ℝ) ^ (S d t + 2 * Q) ≤ K.Cres * (Y : ℝ) →
        pushforward (conditionalRestartLaw r (2 ^ (S d t + 1)) kmin N W (orbit r t) t)
            (fun m : ℕ => valuationVector m n) (geomPersistenceEvent collatzAlpha c n)
          ≤ Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n : ℝ)))
            + K.A * (2 : ℝ) ^ (-(K.c1 * (n : ℝ)))) := by
  obtain ⟨kmin, N, W, hWpos, hWdef, hmix⟩ :=
    conditional_future_event_bound_of_constants c0 K hK d t r h ht n hn Y H hYr hYpos η hη hH Q
      hQrel hQ1 hthick (geomPersistenceEvent collatzAlpha c n)
  refine ⟨kmin, N, W, hWpos, hWdef, ?_⟩
  intro hbudget
  have hreal := hmix hbudget
  have hiid := geometric_persistence_upper_bound_bits c n hn
  linarith [hreal, hiid]

/-- **Convenience wrapper** (unchanged public API): chooses `K` once from `tao`, then invokes
the fixed-witness version. -/
theorem conditional_shifted_persistence_upper_bound_bits
    (tao : TaoMixingHypothesis)
    (d : ℕ → ℕ) (t r : ℕ) (h : Realizes d t r) (ht : 1 ≤ t)
    (c : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (Y H : ℕ) (hYr : r ≤ Y) (hYpos : 0 < Y) (η : ℝ) (hη : 0 < η)
    (hH : η * (Y : ℝ) ≤ (H : ℝ))
    (c0 : ℝ) (hc0 : 0 < c0) (Q : ℕ) (hQrel : (Q : ℝ) ≥ (2 + c0) * (n : ℝ)) (hQ1 : 1 ≤ Q)
    (hthick : 4 * (2 ^ (S d t + 1) : ℝ) ≤ η * (Y : ℝ)) :
    ∃ (K : TaoMixingConstants c0) (kmin N : ℕ) (W : ℝ), 0 < W ∧
      W = ∑ j ∈ range N, (1 : ℝ) / ((r : ℝ) + (2 ^ (S d t + 1) : ℝ) * ((kmin : ℝ) + j)) ∧
      (2 * (1 + 1 / η) * (2 : ℝ) ^ (S d t + 2 * Q) ≤ K.Cres * (Y : ℝ) →
        pushforward (conditionalRestartLaw r (2 ^ (S d t + 1)) kmin N W (orbit r t) t)
            (fun m : ℕ => valuationVector m n) (geomPersistenceEvent collatzAlpha c n)
          ≤ Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (n : ℝ)))
            + K.A * (2 : ℝ) ^ (-(K.c1 * (n : ℝ)))) := by
  obtain ⟨K, hK⟩ := tao.finite_valuation_mixing c0 hc0
  obtain ⟨kmin, N, W, hWpos, hWdef, hbound⟩ :=
    conditional_shifted_persistence_upper_bound_bits_of_constants c0 K hK d t r h ht c n hn Y H
      hYr hYpos η hη hH Q hQrel hQ1 hthick
  exact ⟨K, kmin, N, W, hWpos, hWdef, hbound⟩

end TaoExternal
end EOC
