import EOC.SurvivorClusters
import EOC.SurvivorCounting
import Mathlib.Data.Int.CardIntervalMod

/-!
# Lift digits, suffix memory, and the exact residue-count identity

For a positive word `d`, write `r_j = leastRealizer d j` (the least realizer of the length-`j`
prefix, `r_j < 2^(S_j+1)`).

* `leastRealizer_mod` — `r_N ≡ r_j (mod 2^(S_j+1))` for `j ≤ N`.
* `liftDigit`, `leastRealizer_succ`, `liftDigit_lt` — **append recursion**:
  `r_{j+1} = r_j + 2^(S_j+1)·τ_j` with the lift digit `τ_j < 2^(d_j)`.
* `leastRealizer_zero`, `leastRealizer_eq_sum` — **block expansion**:
  `r_N = 1 + ∑_{j<N} 2^(S_j+1)·τ_j`; the binary digits of `r_N` in positions `[S_j+1, S_{j+1}]` are
  exactly the lift digit `τ_j`.
* `suffix_memory` — **dyadic-interval criterion (finite memory)**: for `j ≤ N`,
  `r_N < 2^(S_j+1) ↔ r_j realizes the whole word through N`, i.e. the normalized least realizer
  `u_N = r_N / 2^(S_N+1)` lies in `[0, 2^{-(S_N−S_j)})` iff the least realizer of the depth-`j`
  prefix continues naturally along the last `N − j` digits.
* `suffix_memory_transport`, `suffix_memory_modEq` — the SuffixTransport form: iff the restart state
  `T^j(r_j)` realizes the suffix word `σ^j d` for `N − j` steps, iff
  `T^j(r_j) ≡ leastRealizer (σ^j d) (N−j) (mod 2^(S_N − S_j + 1))`.
* `realizes_iff_modEq`, `card_realizers_exact` — **exact residue-count identity**:
  `#{μ < X : μ realizes d through N} = ⌊X / 2^(S_N+1)⌋ + [r_N < X mod 2^(S_N+1)]`.
* `card_realizers_dyadic` — for `X = 2^K ≤ 2^(S_N)`: the count is `[r_N < 2^K]` (post-fresh-bit
  regime: a word contributes a seed below `X` iff its least realizer does).

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace LiftDigits

open Finset SuffixTransport SurvivorClusters

variable {d : ℕ → ℕ}

theorem realizes_restrict {N t x : ℕ} (h : Realizes d N x) (ht : t ≤ N) : Realizes d t x :=
  ⟨h.1, fun j hj => h.2 j (by omega)⟩

theorem S_mono (d : ℕ → ℕ) {j N : ℕ} (h : j ≤ N) : S d j ≤ S d N := by
  simp only [S, s]
  exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr h)

theorem S_succ' (d : ℕ → ℕ) (j : ℕ) : S d (j + 1) = S d j + d j := by
  simp only [S]
  exact s_succ d j

/-- Prefix least realizers are residues of longer ones. -/
theorem leastRealizer_mod {N j : ℕ} (hd : ∀ i < N, 1 ≤ d i) (hj : j ≤ N) :
    leastRealizer d N % 2 ^ (S d j + 1) = leastRealizer d j :=
  mod_eq_leastRealizer_of_realizes (realizes_restrict (leastRealizer_realizes_all d N hd) hj)

/-- The lift digit `τ_j`: the block of `r_{j+1}` above position `S_j`. -/
def liftDigit (d : ℕ → ℕ) (j : ℕ) : ℕ := leastRealizer d (j + 1) / 2 ^ (S d j + 1)

/-- **Append recursion.** `r_{j+1} = r_j + 2^(S_j+1)·τ_j`. -/
theorem leastRealizer_succ {j : ℕ} (hd : ∀ i < j + 1, 1 ≤ d i) :
    leastRealizer d (j + 1) = leastRealizer d j + 2 ^ (S d j + 1) * liftDigit d j := by
  have h := leastRealizer_mod hd (Nat.le_succ j)
  rw [liftDigit, ← h, Nat.mod_add_div]

theorem liftDigit_lt (j : ℕ) : liftDigit d j < 2 ^ d j := by
  unfold liftDigit
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
  have h := leastRealizer_lt d (j + 1)
  rw [S_succ'] at h
  calc leastRealizer d (j + 1) < 2 ^ (S d j + d j + 1) := h
    _ = 2 ^ (d j + (S d j + 1)) := by ring_nf

theorem leastRealizer_zero (d : ℕ → ℕ) : leastRealizer d 0 = 1 := by
  have hodd := (leastRealizer_realizes_all d 0 (fun i hi => absurd hi (Nat.not_lt_zero i))).1
  have hlt := leastRealizer_lt d 0
  simp only [S, s, Finset.range_zero, Finset.sum_empty, zero_add, pow_one] at hlt
  obtain ⟨k, hk⟩ := hodd
  omega

/-- **Block expansion** `r_N = 1 + ∑_{j<N} 2^(S_j+1)·τ_j`. -/
theorem leastRealizer_eq_sum {N : ℕ} (hd : ∀ i < N, 1 ≤ d i) :
    leastRealizer d N = 1 + ∑ j ∈ range N, 2 ^ (S d j + 1) * liftDigit d j := by
  induction N with
  | zero => simp [leastRealizer_zero]
  | succ n ih =>
      rw [leastRealizer_succ hd, ih (fun i hi => hd i (by omega)), Finset.sum_range_succ]
      ring

/-- `r_N = r_j` iff `r_j` realizes the whole word through `N`. -/
theorem eq_iff_realizes {N j : ℕ} (hd : ∀ i < N, 1 ≤ d i) (hj : j ≤ N) :
    leastRealizer d N = leastRealizer d j ↔ Realizes d N (leastRealizer d j) := by
  constructor
  · intro h
    rw [← h]
    exact leastRealizer_realizes_all d N hd
  · intro h
    have hm := mod_eq_leastRealizer_of_realizes h
    have hlt : leastRealizer d j < 2 ^ (S d N + 1) :=
      lt_of_lt_of_le (leastRealizer_lt d j)
        (Nat.pow_le_pow_right (by norm_num) (by have := S_mono d hj; omega))
    rw [Nat.mod_eq_of_lt hlt] at hm
    exact hm.symm

/-- **Suffix memory (dyadic-interval criterion).** For `j ≤ N`:
`r_N < 2^(S_j+1)` iff the prefix least realizer `r_j` realizes the whole word through `N`. -/
theorem suffix_memory {N j : ℕ} (hd : ∀ i < N, 1 ≤ d i) (hj : j ≤ N) :
    leastRealizer d N < 2 ^ (S d j + 1) ↔ Realizes d N (leastRealizer d j) := by
  rw [← eq_iff_realizes hd hj]
  constructor
  · intro h
    rw [← leastRealizer_mod hd hj, Nat.mod_eq_of_lt h]
  · intro h
    rw [h]
    exact leastRealizer_lt d j

/-- Splicing: a realizer of the first `j` digits whose `j`-th orbit value realizes the suffix
realizes the whole word. -/
theorem realizes_of_prefix_suffix {N j x : ℕ} (hj : j ≤ N) (hx : Realizes d j x)
    (hs : Realizes (shiftWord d j) (N - j) (orbit x j)) : Realizes d N x := by
  refine ⟨hx.1, fun i hi => ?_⟩
  rcases lt_or_ge i j with hij | hij
  · exact hx.2 i hij
  · have h := hs.2 (i - j) (by omega)
    rw [← orbit_add, show j + (i - j) = i by omega] at h
    simpa [shiftWord, show j + (i - j) = i by omega] using h

/-- **Suffix memory, SuffixTransport form.** `r_N < 2^(S_j+1)` iff the restart state `T^j(r_j)`
realizes the suffix word `σ^j d` for `N − j` steps. -/
theorem suffix_memory_transport {N j : ℕ} (hd : ∀ i < N, 1 ≤ d i) (hj : j ≤ N) :
    leastRealizer d N < 2 ^ (S d j + 1) ↔
      Realizes (shiftWord d j) (N - j) (orbit (leastRealizer d j) j) := by
  rw [suffix_memory hd hj]
  have hrj : Realizes d j (leastRealizer d j) :=
    leastRealizer_realizes_all d j fun i hi => hd i (by omega)
  exact ⟨fun h => realizes_shiftWord h hj, fun h => realizes_of_prefix_suffix hj hrj h⟩

/-- **Suffix memory, congruence form.** `r_N < 2^(S_j+1)` iff the restart state `T^j(r_j)` is
congruent to the least realizer of the suffix word modulo `2^(S_N − S_j + 1)`. -/
theorem suffix_memory_modEq {N j : ℕ} (hd : ∀ i < N, 1 ≤ d i) (hj : j ≤ N) :
    leastRealizer d N < 2 ^ (S d j + 1) ↔
      orbit (leastRealizer d j) j ≡ leastRealizer (shiftWord d j) (N - j)
        [MOD 2 ^ (S (shiftWord d j) (N - j) + 1)] := by
  rw [suffix_memory_transport hd hj]
  have hsd : ∀ i < N - j, 1 ≤ shiftWord d j i := fun i hi => hd (j + i) (by omega)
  have hodd : Odd (orbit (leastRealizer d j) j) :=
    odd_orbit (leastRealizer_realizes_all d j fun i hi => hd i (by omega)).1 j
  constructor
  · exact modEq_leastRealizer_of_realizes
  · intro h
    exact realizes_of_modEq (leastRealizer_realizes_all _ _ hsd) hsd hodd h.symm

/-- Realizers of a positive word are exactly its least-realizer residue class. -/
theorem realizes_iff_modEq {N μ : ℕ} (hd : ∀ i < N, 1 ≤ d i) :
    Realizes d N μ ↔ μ ≡ leastRealizer d N [MOD 2 ^ (S d N + 1)] := by
  have hr := leastRealizer_realizes_all d N hd
  constructor
  · exact modEq_leastRealizer_of_realizes
  · intro h
    have hμodd : Odd μ := by
      have h2 : μ ≡ leastRealizer d N [MOD 2] :=
        Nat.ModEq.of_dvd (dvd_pow_self 2 (by omega)) h
      rw [Nat.odd_iff, ← Nat.odd_iff.mp hr.1]
      exact h2
    exact realizes_of_modEq hr hd hμodd h.symm

/-- **Exact residue-count identity.**
`#{μ < X : μ realizes d through N} = ⌊X / 2^(S_N+1)⌋ + [r_N < X mod 2^(S_N+1)]`. -/
theorem card_realizers_exact (N X : ℕ) (hd : ∀ i < N, 1 ≤ d i)
    [DecidablePred fun μ => Realizes d N μ] :
    ((range X).filter fun μ => Realizes d N μ).card =
      X / 2 ^ (S d N + 1) + if leastRealizer d N < X % 2 ^ (S d N + 1) then 1 else 0 := by
  have hset : ((range X).filter fun μ => Realizes d N μ) =
      (range X).filter fun μ => μ ≡ leastRealizer d N [MOD 2 ^ (S d N + 1)] := by
    ext μ
    simp only [mem_filter, mem_range]
    rw [realizes_iff_modEq hd]
  rw [hset, ← Nat.count_eq_card_filter_range,
    Nat.count_modEq_card _ (by positivity : 0 < 2 ^ (S d N + 1)),
    Nat.mod_eq_of_lt (leastRealizer_lt d N)]

/-- **Post-fresh-bit (dyadic) regime.** For `X = 2^K` with `K ≤ S_N`, a word contributes a seed
below `X` iff its least realizer is below `X`. -/
theorem card_realizers_dyadic (N K : ℕ) (hd : ∀ i < N, 1 ≤ d i) (hK : K ≤ S d N)
    [DecidablePred fun μ => Realizes d N μ] :
    ((range (2 ^ K)).filter fun μ => Realizes d N μ).card =
      if leastRealizer d N < 2 ^ K then 1 else 0 := by
  rw [card_realizers_exact N (2 ^ K) hd]
  have hlt : 2 ^ K < 2 ^ (S d N + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  rw [Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt, zero_add]

end LiftDigits
end EOC
