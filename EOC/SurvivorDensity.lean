import EOC.CapacityBounds
import EOC.SurvivorCounting
import EOC.TaoLike.PersistenceModel

/-!
# A finite survivor-density bound

Combines three existing ingredients:

* `SurvivorCounting.card_seeds_le_sum` — seeds whose length-`N` prefix word lies in a finite set
  `W` are at most `∑_{w ∈ W} (X / 2^{S_N(w)+1} + 1)`;
* `TaoExternal.geometric_persistence_upper_bound_bits` — the iid `Geom(2)` persistence
  probability is at most `e^{λ* c} · 2^{-I₀ n}`;
* `CapacityBounds.card_confinedWords_le_choose` — `W_c(N) ≤ C(s_N, N)`.

The bridge is `sum_half_pow_confined_eq`: the `Geom(2)` persistence probability of the
repository's iid model equals the finite sum `∑_{w ∈ W_c(N)} 2^{-S_N(w)}` over the confined words
(`W_c(N) = confinedWords N (collatzBarrier c)`), because a non-positive word has zero `Geom(2)`
weight.

Main result:

* `survivor_count_le` — for `c : ℕ`, `N ≥ 1`, and every `X`,
  `#{μ < X : μ odd, c-confined for N steps} ≤ (X/2) · e^{λ* c} · 2^{-I₀ N} + C(⌊Nα + c⌋₊, N)`.

Both terms are explicit; `EntropyBounds` bounds the binomial term by `e^{s_N · H(N/s_N)}`.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace SurvivorDensity

open Finset FiniteValuationWord CapacityBounds TaoExternal

variable {N : ℕ}

/-- The repository's real-valued digit sum is the finite word's prefix sum. -/
theorem digitSum_eq_prefixSum (w : FiniteValuationWord N) {j : ℕ} (hj : j ≤ N) :
    digitSum N w j = (w.prefixSum j : ℝ) := by
  rw [w.prefixSum_eq_s hj, s, Nat.cast_sum, digitSum, Finset.sum_filter]
  have h2 : ∑ i : Fin N, (if (i : ℕ) < j then (w.toInfinite i : ℝ) else 0)
      = ∑ i ∈ range N, (if i < j then (w.toInfinite i : ℝ) else 0) :=
    Fin.sum_univ_eq_sum_range (fun i => if i < j then (w.toInfinite i : ℝ) else 0) N
  have h3 : ∑ i ∈ range N, (if i < j then (w.toInfinite i : ℝ) else 0)
      = ∑ i ∈ range j, (w.toInfinite i : ℝ) := by
    rw [← Finset.sum_filter]
    congr 1
    ext i
    simp only [mem_filter, mem_range]
    omega
  rw [← h3, ← h2]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

/-- The iid persistence event, restricted to finite words, is paper-faithful confinement. -/
theorem mem_persistenceEvent_iff (c : ℝ) (w : FiniteValuationWord N) :
    w ∈ geomPersistenceEvent collatzAlpha c N ↔ PaperConfined alpha c w := by
  unfold geomPersistenceEvent PaperConfined centeredSum
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h j hj1 hjN
    have := h j hj1 hjN
    rwa [digitSum_eq_prefixSum w hjN] at this
  · intro h j hj1 hjN
    rw [digitSum_eq_prefixSum w hjN]
    exact h j hj1 hjN

theorem atomWeight_eq_of_positive (w : FiniteValuationWord N) (hw : w.Positive) :
    atomWeight N w = (1 / 2 : ℝ) ^ w.total := by
  rw [atomWeight, total_eq_sum_univ, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_congr rfl fun i _ => geom2_eq_of_pos (hw i)

theorem atomWeight_eq_zero_of_not_positive (w : FiniteValuationWord N) (hw : ¬ w.Positive) :
    atomWeight N w = 0 := by
  simp only [Positive, not_forall, not_le] at hw
  obtain ⟨i, hi⟩ := hw
  have h0 : w i = 0 := by omega
  rw [atomWeight]
  exact Finset.prod_eq_zero (mem_univ i) (by rw [h0, geom2_eq_zero])

/-- **Mass identity.** The iid `Geom(2)` persistence probability is the finite dyadic sum over
the confined words: `p_N(c) = ∑_{w ∈ W_c(N)} 2^{-S_N(w)}`. -/
theorem sum_half_pow_confined_eq (c : ℕ) (hN : 1 ≤ N) :
    ∑ w ∈ confinedWords N (collatzBarrier c), (1 / 2 : ℝ) ^ w.total =
      iidGeom2VectorProb N (geomPersistenceEvent collatzAlpha c N) := by
  classical
  unfold iidGeom2VectorProb genEventProb
  rw [tsum_eq_sum (s := confinedWords N (collatzBarrier c))]
  · refine Finset.sum_congr rfl fun w hw => ?_
    obtain ⟨hp, hc⟩ := (mem_collatzConfinedWords c hN).mp hw
    rw [Set.indicator_of_mem ((mem_persistenceEvent_iff _ w).mpr hc),
      atomWeight_eq_of_positive w hp]
  · intro w hw
    by_cases hE : w ∈ geomPersistenceEvent collatzAlpha c N
    · have hnp : ¬ w.Positive := fun hp =>
        hw ((mem_collatzConfinedWords c hN).mpr ⟨hp, (mem_persistenceEvent_iff _ w).mp hE⟩)
      rw [Set.indicator_of_mem hE, atomWeight_eq_zero_of_not_positive w hnp]
    · exact Set.indicator_of_notMem hE _

/-- The prefix word of a confined odd seed is a confined positive word. -/
theorem prefixWord_mem (c : ℕ) (hN : 1 ≤ N) {μ : ℕ} (hμ : Odd μ)
    (hconf : Confined (c : ℝ) (fun i => a (orbit μ i)) N) :
    SurvivorCounting.prefixWord N μ ∈ confinedWords N (collatzBarrier c) := by
  rw [mem_collatzConfinedWords c hN]
  refine ⟨fun i => hd_pos_of_orbit hμ i, ?_⟩
  rw [paperConfined_alpha_iff_confined (Nat.cast_nonneg c)]
  refine confined_congr (fun i hi => ?_) hconf
  rw [toInfinite_apply_of_lt _ hi]
  rfl

open Classical in
/-- **Finite survivor-density bound.** For every `X`, the odd seeds below `X` that stay
`c`-confined for `N` steps number at most `(X/2) · e^{λ* c} · 2^{-I₀ N} + C(⌊Nα + c⌋₊, N)`. -/
theorem survivor_count_le (c : ℕ) (hN : 1 ≤ N) (X : ℕ) :
    (((range X).filter fun μ => Odd μ ∧ Confined (c : ℝ) (fun i => a (orbit μ i)) N).card : ℝ) ≤
      (X : ℝ) / 2 * (Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (N : ℝ)))) +
        (Nat.choose (collatzBarrier c N) N : ℝ) := by
  set W := confinedWords N (collatzBarrier c)
  have hcount := SurvivorCounting.card_seeds_le_sum N X
    (fun μ => Confined (c : ℝ) (fun i => a (orbit μ i)) N) W
    (fun μ _ hodd hP => prefixWord_mem c hN hodd hP)
  have h1 : (((range X).filter fun μ => Odd μ ∧ Confined (c : ℝ) (fun i => a (orbit μ i)) N).card
      : ℝ) ≤ ∑ w ∈ W, (((X / 2 ^ (S w.toInfinite N + 1) : ℕ) : ℝ) + 1) := by
    have := (Nat.cast_le (α := ℝ)).mpr hcount
    push_cast at this
    convert this using 3
  have h2 : ∀ w ∈ W, ((X / 2 ^ (S w.toInfinite N + 1) : ℕ) : ℝ) ≤
      (X : ℝ) / 2 * (1 / 2 : ℝ) ^ w.total := by
    intro w _
    have hS : S w.toInfinite N = w.total := by
      rw [S, ← w.prefixSum_eq_s le_rfl]
      rfl
    rw [hS]
    calc ((X / 2 ^ (w.total + 1) : ℕ) : ℝ) ≤ (X : ℝ) / ((2 ^ (w.total + 1) : ℕ) : ℝ) :=
          Nat.cast_div_le
      _ = (X : ℝ) / 2 * (1 / 2 : ℝ) ^ w.total := by
          push_cast
          rw [pow_succ, div_pow, one_pow]
          field_simp
  calc _ ≤ ∑ w ∈ W, (((X / 2 ^ (S w.toInfinite N + 1) : ℕ) : ℝ) + 1) := h1
    _ ≤ ∑ w ∈ W, ((X : ℝ) / 2 * (1 / 2 : ℝ) ^ w.total + 1) :=
        sum_le_sum fun w hw => by linarith [h2 w hw]
    _ = (X : ℝ) / 2 * ∑ w ∈ W, (1 / 2 : ℝ) ^ w.total + (W.card : ℝ) := by
        rw [sum_add_distrib, ← mul_sum]
        simp
    _ ≤ (X : ℝ) / 2 * (Real.exp (lambdaStar * c) * (2 : ℝ) ^ (-(I0 * (N : ℝ)))) +
        (Nat.choose (collatzBarrier c N) N : ℝ) := by
        gcongr
        · rw [sum_half_pow_confined_eq c hN]
          exact geometric_persistence_upper_bound_bits c N hN
        · exact_mod_cast card_confinedWords_le_choose hN _

end SurvivorDensity
end EOC
