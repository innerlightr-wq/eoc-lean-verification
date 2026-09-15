import EOC.LiftDigits
import EOC.SurvivorDensity
import EOC.ExceptionalPowerBound
import EOC.TaoLike.Cylinder

/-!
# The exact residue-discrepancy decomposition of confined-seed counts

Let `W = W_c(N) = CapacityBounds.confinedWords N (collatzBarrier c)` and, for `w ∈ W`,
`r_w = leastRealizer w N`, `S_w = S_N(w)`.

* `seed_count_eq_sum` — the confined odd seeds below `X` are partitioned by their length-`N`
  valuation word: `S_X(N) = ∑_{w ∈ W} #{μ < X : μ realizes w}`.
* `seed_count_eq_residue_sum` — with `LiftDigits.card_realizers_exact`:
  `S_X(N) = ∑_{w ∈ W} (⌊X / 2^(S_w+1)⌋ + [r_w < X mod 2^(S_w+1)])`.
* `seed_count_dyadic` — for `X = 2^K`:
  `S_X(N) = ∑_{w ∈ W} (if S_w + 1 ≤ K then 2^(K − S_w − 1) else [r_w < 2^K])`:
  fresh-bit words contribute their exact cylinder share, every post-fresh-bit word contributes
  `1` iff its least realizer lies below `X`.
* `liftDigit_valuation` — the lift digit is characterized by the next valuation of the restarted
  least realizer: `a(T^j(r_j) + 2·3^j·τ_j) = d_j`; the orbit value of `r_{j+1}` at step `j` is
  `T^j(r_j) + 2·3^j·τ_j` (`orbit_leastRealizer_succ`).

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace ResidueDiscrepancy

open Finset FiniteValuationWord CapacityBounds SurvivorDensity LiftDigits SuffixTransport

variable {N : ℕ}

theorem word_eq_of_realizes {w w' : FiniteValuationWord N} {μ : ℕ}
    (h : Realizes w.toInfinite N μ) (h' : Realizes w'.toInfinite N μ) : w = w' := by
  funext i
  have e1 := h.2 i i.isLt
  have e2 := h'.2 i i.isLt
  rw [toInfinite_apply_of_lt _ i.isLt] at e1 e2
  exact e1.symm.trans e2

theorem total_eq_S (w : FiniteValuationWord N) : S w.toInfinite N = w.total := by
  rw [S, ← w.prefixSum_eq_s le_rfl]
  rfl

open Classical in
/-- Confined seeds below `X` are partitioned by their length-`N` word. -/
theorem seed_count_eq_sum (c : ℕ) (hN : 1 ≤ N) (X : ℕ) :
    ((range X).filter fun μ => Odd μ ∧ Confined (c : ℝ) (fun i => a (orbit μ i)) N).card =
      ∑ w ∈ confinedWords N (collatzBarrier c),
        ((range X).filter fun μ => Realizes w.toInfinite N μ).card := by
  set W := confinedWords N (collatzBarrier c)
  have hset : ((range X).filter fun μ => Odd μ ∧ Confined (c : ℝ) (fun i => a (orbit μ i)) N) =
      W.biUnion fun w => (range X).filter fun μ => Realizes w.toInfinite N μ := by
    ext μ
    simp only [mem_filter, mem_range, mem_biUnion]
    constructor
    · rintro ⟨hμX, hodd, hconf⟩
      exact ⟨SurvivorCounting.prefixWord N μ, prefixWord_mem c hN hodd hconf, hμX,
        SurvivorCounting.realizes_prefixWord N μ hodd⟩
    · rintro ⟨w, hw, hμX, hreal⟩
      refine ⟨hμX, hreal.1, ?_⟩
      obtain ⟨-, hpc⟩ := (mem_collatzConfinedWords c hN).mp hw
      have hconf := (paperConfined_alpha_iff_confined (Nat.cast_nonneg c) w).mp hpc
      exact confined_congr (fun i hi => (hreal.2 i hi).symm) hconf
  rw [hset, card_biUnion]
  intro w _ w' _ hne
  refine disjoint_left.mpr fun μ hμ hμ' => hne ?_
  exact word_eq_of_realizes (mem_filter.mp hμ).2 (mem_filter.mp hμ').2

theorem positive_toInfinite {c : ℕ} (hN : 1 ≤ N) {w : FiniteValuationWord N}
    (hw : w ∈ confinedWords N (collatzBarrier c)) : ∀ i < N, 1 ≤ w.toInfinite i :=
  (positive_iff_toInfinite w).mp ((mem_collatzConfinedWords c hN).mp hw).1

open Classical in
/-- **Exact residue-discrepancy decomposition.** -/
theorem seed_count_eq_residue_sum (c : ℕ) (hN : 1 ≤ N) (X : ℕ) :
    ((range X).filter fun μ => Odd μ ∧ Confined (c : ℝ) (fun i => a (orbit μ i)) N).card =
      ∑ w ∈ confinedWords N (collatzBarrier c),
        (X / 2 ^ (w.total + 1) +
          if leastRealizer w.toInfinite N < X % 2 ^ (w.total + 1) then 1 else 0) := by
  rw [seed_count_eq_sum c hN X]
  refine sum_congr rfl fun w hw => ?_
  rw [card_realizers_exact N X (positive_toInfinite hN hw), total_eq_S]

open Classical in
/-- **Dyadic form.** For `X = 2^K`: fresh-bit words (`S_w + 1 ≤ K`) contribute `2^(K−S_w−1)`
exactly; every other word contributes `1` iff its least realizer is below `2^K`. -/
theorem seed_count_dyadic (c : ℕ) (hN : 1 ≤ N) (K : ℕ) :
    ((range (2 ^ K)).filter fun μ => Odd μ ∧ Confined (c : ℝ) (fun i => a (orbit μ i)) N).card =
      ∑ w ∈ confinedWords N (collatzBarrier c),
        (if w.total + 1 ≤ K then 2 ^ (K - (w.total + 1))
          else if leastRealizer w.toInfinite N < 2 ^ K then 1 else 0) := by
  rw [seed_count_eq_residue_sum c hN]
  refine sum_congr rfl fun w _ => ?_
  by_cases h : w.total + 1 ≤ K
  · have hdvd : 2 ^ (w.total + 1) ∣ 2 ^ K := pow_dvd_pow 2 h
    rw [Nat.mod_eq_zero_of_dvd hdvd, Nat.pow_div h (by norm_num)]
    simp [h]
  · have hlt : 2 ^ K < 2 ^ (w.total + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    rw [Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt, zero_add]
    simp [h]

/-- The orbit value of `r_{j+1}` at step `j` is the restarted state `T^j(r_j) + 2·3^j·τ_j`. -/
theorem orbit_leastRealizer_succ {d : ℕ → ℕ} {j : ℕ} (hj : 1 ≤ j) (hd : ∀ i < j + 1, 1 ≤ d i) :
    orbit (leastRealizer d (j + 1)) j =
      orbit (leastRealizer d j) j + 2 * 3 ^ j * liftDigit d j := by
  rw [leastRealizer_succ hd]
  exact (EOC.cylinder_restart_leastRealizer d j (liftDigit d j) hj
    fun i hi => hd i (by omega)).2

/-- **Lift-digit characterization.** The restarted state `T^j(r_j) + 2·3^j·τ_j` has next valuation
exactly `d_j`. -/
theorem liftDigit_valuation {d : ℕ → ℕ} {j : ℕ} (hj : 1 ≤ j) (hd : ∀ i < j + 1, 1 ≤ d i) :
    a (orbit (leastRealizer d j) j + 2 * 3 ^ j * liftDigit d j) = d j := by
  rw [← orbit_leastRealizer_succ hj hd]
  exact (leastRealizer_realizes_all d (j + 1) hd).2 j (Nat.lt_succ_self j)

open Classical in
/-- **From a least-realizer counting bound to the improved exponent.** Let `X = 2^K`. If the
post-fresh-bit words (`S_w ≥ K`) whose least realizer lies below `X` are at most `C` times their
Haar share `∑_{S_w ≥ K} 2^K · 2^{-(S_w+1)}` (with `C ≥ 1`), and `N ≥ A·K`, then
`#(E_U ∩ [0, 2^K)) ≤ (C e^{λ* U}/2) · (2^K)^{1 − I₀ A}`.  (Exact dyadic decomposition
`seed_count_dyadic` + `ExceptionalPowerBound.exceptional_count_le_of_firstMoment`.) -/
theorem exceptional_count_le_of_leastRealizerBound (U K : ℕ) {N : ℕ} (hN : 1 ≤ N) (A C : ℝ)
    (hC : 1 ≤ C) (hNA : A * K ≤ N)
    (hyp : ((((confinedWords N (collatzBarrier U)).filter fun w =>
        K ≤ w.total ∧ leastRealizer w.toInfinite N < 2 ^ K).card : ℕ) : ℝ) ≤
      C * ∑ w ∈ (confinedWords N (collatzBarrier U)).filter (fun w => K ≤ w.total),
        (2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (w.total + 1)) :
    (((range (2 ^ K)).filter fun μ =>
        Odd μ ∧ ∀ M, Confined (U : ℝ) (fun i => a (orbit μ i)) M).card : ℝ) ≤
      C * Real.exp (TaoExternal.lambdaStar * U) / 2 *
        ((2 ^ K : ℕ) : ℝ) ^ (1 - TaoExternal.I0 * A) := by
  set W := confinedWords N (collatzBarrier U)
  have hX1 : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  have hlog : Real.logb 2 ((2 ^ K : ℕ) : ℝ) = K := by
    push_cast
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
  refine ExceptionalPowerBound.exceptional_count_le_of_firstMoment U hN hX1 A C (by linarith)
    (by rw [hlog]; exact hNA) ?_
  -- first-moment bound from the dyadic decomposition
  have hdy := seed_count_dyadic U hN K
  set mass : FiniteValuationWord N → ℝ := fun w => (2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (w.total + 1)
  have hterm : ∀ w ∈ W, (((if w.total + 1 ≤ K then 2 ^ (K - (w.total + 1))
      else if leastRealizer w.toInfinite N < 2 ^ K then 1 else 0 : ℕ)) : ℝ) =
      (if w.total + 1 ≤ K then mass w else 0) +
        (if K ≤ w.total ∧ leastRealizer w.toInfinite N < 2 ^ K then 1 else 0) := by
    intro w _
    by_cases h : w.total + 1 ≤ K
    · have hn : ¬ (K ≤ w.total ∧ leastRealizer w.toInfinite N < 2 ^ K) := fun h' => by omega
      simp only [h, hn, ite_true, ite_false, add_zero, mass]
      push_cast
      rw [pow_sub₀ (2 : ℝ) two_ne_zero h, div_pow, one_pow]
      ring
    · have hK : K ≤ w.total := by omega
      simp only [h, hK, true_and, ite_false, zero_add]
      split_ifs <;> simp
  have hcount : ((((range (2 ^ K)).filter fun μ =>
      Odd μ ∧ Confined (U : ℝ) (fun i => a (orbit μ i)) N).card : ℕ) : ℝ) =
      ∑ w ∈ W.filter (fun w => w.total + 1 ≤ K), mass w +
        ((W.filter fun w => K ≤ w.total ∧ leastRealizer w.toInfinite N < 2 ^ K).card : ℝ) := by
    rw [hdy, Nat.cast_sum, sum_congr rfl hterm, sum_add_distrib, sum_filter, sum_boole]
  have hmass : ∑ w ∈ W, mass w =
      ((2 ^ K : ℕ) : ℝ) / 2 * TaoExternal.iidGeom2VectorProb N
        (TaoExternal.geomPersistenceEvent TaoExternal.collatzAlpha U N) := by
    rw [← sum_half_pow_confined_eq U hN, mul_sum]
    push_cast
    refine sum_congr rfl fun w _ => ?_
    simp only [mass]
    rw [pow_succ]
    ring
  have hdeep : W.filter (fun w => ¬ (w.total + 1 ≤ K)) = W.filter fun w => K ≤ w.total := by
    congr 1; ext w; simp only [not_le]; omega
  have hsplitM := sum_filter_add_sum_filter_not W (fun w => w.total + 1 ≤ K) mass
  rw [hdeep] at hsplitM
  have hF : 0 ≤ ∑ w ∈ W.filter (fun w => w.total + 1 ≤ K), mass w :=
    sum_nonneg fun w _ => by simp only [mass]; positivity
  rw [hcount, ← hmass, ← hsplitM]
  nlinarith

end ResidueDiscrepancy
end EOC
