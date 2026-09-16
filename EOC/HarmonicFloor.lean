import EOC.HarmonicPacking
import EOC.Confinement
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The harmonic drift ceiling under non-descent

`EOC.DirectDescent.R_le_of_nondescent` bounds the drift of a non-descending prefix by
`R_N ≤ N / (3 M ln 2)`, using only `m_k ≥ M`.  That bound is **linear in `N`** and becomes
vacuous exactly at `N ≈ 3 M ln 2 = 2.079 M`, which is why the direct-Collatz endgame currently
needs `L₁(M) < C M` for some `C < 3 ln 2`.

This file proves a strictly better, **logarithmic** ceiling by using the non-descent floor
*together with* the distinctness of the orbit states: the states are distinct integers coprime to
`6` and all `≥ M`, so the `j`-th of them is at least `M + 3j - 2`, and

  `∑_{k<N} 1/m_k ≤ 2/(M-2) + (1/3) log (1 + 3N/(M-2))`   (`sum_inv_orbit_le_of_nondescent`)

instead of the trivial `N/M`.  Feeding this into the Eliahou–Rozier identity gives

  `R_N ≤ (1/9) log₂ (1 + 3N/(M-2)) + 2/(3 ln 2 (M-2))`   (`R_le_of_nondescent_harmonic`),

so a non-descending prefix of length `N = C·M` forces `R ≤ (1/9) log₂(1+3C) + o(1)`; e.g.
`C = 13/9` gives `0.268` and `C = 2` gives `0.312`, against the old bound's `0.694` and `0.962`.
For `N ≪ M` the two agree to first order (`log(1+3N/M) ≈ 3N/M`), so the gain is confined to the
regime `N ≍ M` — which is precisely the regime of the open target `L₁(M) < (13/9) M`.

Distinctness is **not** automatic: it fails exactly when the orbit is eventually periodic.  That
case is isolated here by `R_lt_of_orbit_eq`: a repeated state forces the drift to increase
strictly, i.e. a repeat is a genuine nontrivial cycle lying above `M`.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace HarmonicFloor

open Finset HarmonicPacking

/-! ## 1. A lower bound for the coprime-to-`6` rank -/

/-- Companion to `three_mul_coprimeSixRank_le_add_two`: for `x` coprime to `6`,
`x ≤ 3 · rank x` (the enumeration `1, 5, 7, 11, …` has density `1/3`). -/
theorem le_three_mul_coprimeSixRank {x : ℕ} (hodd : Odd x) (hthree : ¬ 3 ∣ x) :
    x ≤ 3 * coprimeSixRank x := by
  rcases mod_six_eq_one_or_five hodd hthree with hmod | hmod
  · unfold coprimeSixRank
    rw [ite_eq_left hmod]
    have hdecomp := Nat.mod_add_div x 6
    omega
  · unfold coprimeSixRank
    rw [ite_eq_right (by omega)]
    have hdecomp := Nat.mod_add_div x 6
    omega

/-! ## 2. Shifted rearrangement for antitone functions -/

/-- For an antitone `f` and a finite set `T` of naturals all of whose elements are `≥ r₀`, the sum
of `f` over `T` is at most the sum of `f` over the shifted initial segment
`{r₀, r₀+1, …, r₀ + |T| - 1}`.  (The `r₀ = 0` case is
`HarmonicPacking.sum_le_sum_range_card_of_antitone`.) -/
theorem sum_le_sum_range_shift_of_antitone (f : ℕ → ℝ) (hf : Antitone f) (r₀ : ℕ) :
    ∀ T : Finset ℕ, (∀ x ∈ T, r₀ ≤ x) → ∑ x ∈ T, f x ≤ ∑ j ∈ range T.card, f (r₀ + j) := by
  intro T
  induction T using Finset.induction_on_max with
  | empty => intro _; simp
  | insert a s hlt ih =>
    intro hT
    have ha : a ∉ s := fun has => lt_irrefl a (hlt a has)
    have hs : ∀ x ∈ s, r₀ ≤ x := fun x hx => hT x (mem_insert_of_mem hx)
    have hr₀a : r₀ ≤ a := hT a (mem_insert_self a s)
    have hcard : r₀ + s.card ≤ a := by
      have hsub : s ⊆ Finset.Ico r₀ a := fun x hx => mem_Ico.mpr ⟨hs x hx, hlt x hx⟩
      have hle := card_le_card hsub
      rw [Nat.card_Ico] at hle
      omega
    rw [sum_insert ha, card_insert_of_notMem ha, sum_range_succ, add_comm]
    exact add_le_add (ih hs) (hf hcard)

/-! ## 3. Harmonic packing with a floor -/

/-- **Packing distinct coprime-to-`6` values above a floor.**  If `m 0, …, m (n-1)` are pairwise
distinct, odd, not divisible by `3` and all at least `M ≥ 3`, then
`∑_{k<n} 1/m_k ≤ ∑_{j<n} 1/((M-2) + 3j)`: the extremal configuration is the initial segment of the
integers coprime to `6` starting at `M`. -/
theorem sum_inv_le_sum_inv_shift (m : ℕ → ℕ) (n M : ℕ) (hM3 : 3 ≤ M)
    (hinj : ∀ i < n, ∀ j < n, m i = m j → i = j)
    (hodd : ∀ i < n, Odd (m i)) (hthree : ∀ i < n, ¬ 3 ∣ m i)
    (hge : ∀ i < n, M ≤ m i) :
    ∑ k ∈ range n, (1 : ℝ) / (m k : ℝ)
      ≤ ∑ j ∈ range n, (1 : ℝ) / (((M : ℝ) - 2) + 3 * (j : ℝ)) := by
  set f : ℕ → ℝ := fun j => (1 : ℝ) / (3 * (j : ℝ) + 1) with hf
  set r : ℕ → ℕ := fun k => coprimeSixRank (m k) - 1 with hr
  set r₀ : ℕ := (M + 2) / 3 - 1 with hr₀
  have hr₀pos : 1 ≤ (M + 2) / 3 := by omega
  -- every rank is at least `⌈M/3⌉`
  have hrank : ∀ k < n, r₀ ≤ r k := by
    intro k hk
    have h1 := le_three_mul_coprimeSixRank (hodd k hk) (hthree k hk)
    have h2 := hge k hk
    have h3 := coprimeSixRank_pos (m k)
    simp only [hr, hr₀]
    omega
  have hrinj : Set.InjOn r (range n : Set ℕ) := by
    intro i hi j hj hij
    have hi' : i < n := mem_range.mp hi
    have hj' : j < n := mem_range.mp hj
    have hpi := coprimeSixRank_pos (m i)
    have hpj := coprimeSixRank_pos (m j)
    have hrk : coprimeSixRank (m i) = coprimeSixRank (m j) := by
      simp only [hr] at hij
      omega
    exact hinj i hi' j hj'
      (coprimeSixRank_injective_on (hodd i hi') (hthree i hi') (hodd j hj') (hthree j hj') hrk)
  have hterm : ∀ k ∈ range n, (1 : ℝ) / (m k : ℝ) ≤ f (r k) := by
    intro k hk
    have hk' : k < n := mem_range.mp hk
    have hle := HarmonicPacking.three_mul_rank_pred_add_one_le (hodd k hk') (hthree k hk')
    have hle' : 3 * ((r k : ℕ) : ℝ) + 1 ≤ (m k : ℝ) := by exact_mod_cast hle
    exact one_div_le_one_div_of_le (by positivity) hle'
  have himg : ∀ x ∈ (range n).image r, r₀ ≤ x := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hx
    exact hrank k (mem_range.mp hk)
  -- the shifted initial segment dominates `1/((M-2) + 3j)`
  have hcast : (3 : ℝ) * (r₀ : ℝ) ≥ (M : ℝ) - 3 := by
    have h1 : (M : ℕ) ≤ 3 * ((M + 2) / 3) := by omega
    have h2 : (r₀ : ℝ) = (((M + 2) / 3 : ℕ) : ℝ) - 1 := by
      rw [hr₀, Nat.cast_sub hr₀pos, Nat.cast_one]
    have h3 : (M : ℝ) ≤ 3 * (((M + 2) / 3 : ℕ) : ℝ) := by exact_mod_cast h1
    rw [h2]; linarith
  have hfinal : ∀ j ∈ range n,
      f (r₀ + j) ≤ (1 : ℝ) / (((M : ℝ) - 2) + 3 * (j : ℝ)) := by
    intro j _
    have hMpos : (0 : ℝ) < (M : ℝ) - 2 := by
      have : (3 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM3
      linarith
    have hjnn : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hge' : ((M : ℝ) - 2) + 3 * (j : ℝ) ≤ 3 * ((r₀ : ℝ) + (j : ℝ)) + 1 := by linarith
    have hcastj : ((r₀ + j : ℕ) : ℝ) = (r₀ : ℝ) + (j : ℝ) := by push_cast; ring
    simp only [hf, hcastj]
    exact one_div_le_one_div_of_le (by linarith) hge'
  calc ∑ k ∈ range n, (1 : ℝ) / (m k : ℝ)
      ≤ ∑ k ∈ range n, f (r k) := sum_le_sum hterm
    _ = ∑ x ∈ (range n).image r, f x := (sum_image hrinj).symm
    _ ≤ ∑ j ∈ range ((range n).image r).card, f (r₀ + j) :=
        sum_le_sum_range_shift_of_antitone f HarmonicPacking.inv_three_mul_add_one_antitone r₀ _
          himg
    _ = ∑ j ∈ range n, f (r₀ + j) := by rw [card_image_of_injOn hrinj, card_range]
    _ ≤ ∑ j ∈ range n, (1 : ℝ) / (((M : ℝ) - 2) + 3 * (j : ℝ)) := sum_le_sum hfinal

/-! ## 4. The shifted harmonic sum is logarithmic -/

/-- Telescoping bound: `∑_{j<n} 1/(b + 3(j+1)) ≤ (1/3)(log (b+3n) - log b)` for `b > 0`. -/
theorem sum_range_inv_shift_succ_le (b : ℝ) (hb : 0 < b) (n : ℕ) :
    ∑ j ∈ range n, (1 : ℝ) / (b + 3 * ((j : ℝ) + 1))
      ≤ (1 / 3) * (Real.log (b + 3 * (n : ℝ)) - Real.log b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hbn : (0 : ℝ) < b + 3 * (n : ℝ) := by positivity
    have hbn3 : (0 : ℝ) < b + 3 * (n : ℝ) + 3 := by linarith
    have hstep : (1 : ℝ) / (b + 3 * ((n : ℝ) + 1))
        ≤ (1 / 3) * (Real.log (b + 3 * ((n : ℝ) + 1)) - Real.log (b + 3 * (n : ℝ))) := by
      have h := Real.one_sub_inv_le_log_of_pos (div_pos hbn3 hbn)
      rw [Real.log_div hbn3.ne' hbn.ne', inv_div] at h
      have hid : 1 - (b + 3 * (n : ℝ)) / (b + 3 * (n : ℝ) + 3) = 3 / (b + 3 * (n : ℝ) + 3) := by
        field_simp
        ring
      rw [hid] at h
      have hrw : b + 3 * ((n : ℝ) + 1) = b + 3 * (n : ℝ) + 3 := by ring
      have hthird : (1 : ℝ) / (b + 3 * (n : ℝ) + 3)
          = (1 / 3) * (3 / (b + 3 * (n : ℝ) + 3)) := by ring
      rw [hrw, hthird]
      linarith
    rw [sum_range_succ]
    have hcast : ((n : ℕ) + 1 : ℝ) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
    push_cast at ih hstep ⊢
    linarith

/-- **The shifted harmonic sum.** `∑_{j<n} 1/(b + 3j) ≤ 1/b + (1/3) log (1 + 3n/b)` for `b > 0`. -/
theorem sum_range_inv_shift_le (b : ℝ) (hb : 0 < b) (n : ℕ) :
    ∑ j ∈ range n, (1 : ℝ) / (b + 3 * (j : ℝ))
      ≤ 1 / b + (1 / 3) * Real.log (1 + 3 * (n : ℝ) / b) := by
  have hlognn : ∀ t : ℕ, Real.log (1 + 3 * (t : ℝ) / b)
      = Real.log (b + 3 * (t : ℝ)) - Real.log b := by
    intro t
    have hbt : (0 : ℝ) < b + 3 * (t : ℝ) := by positivity
    rw [← Real.log_div hbt.ne' hb.ne']
    congr 1
    field_simp
  rcases n with _ | t
  · simp only [Nat.cast_zero, mul_zero, zero_div, add_zero, Real.log_one, mul_zero,
      sum_range_zero, add_zero]
    positivity
  · rw [sum_range_succ']
    have h0 : (1 : ℝ) / (b + 3 * ((0 : ℕ) : ℝ)) = 1 / b := by norm_num
    have haux := sum_range_inv_shift_succ_le b hb t
    have hmono : Real.log (b + 3 * (t : ℝ)) ≤ Real.log (b + 3 * ((t + 1 : ℕ) : ℝ)) := by
      apply Real.log_le_log (by positivity)
      push_cast
      linarith
    rw [hlognn (t + 1)]
    have hcast : ∀ j : ℕ, ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by intro j; push_cast; ring
    simp only [hcast] at haux hmono ⊢
    rw [h0]
    linarith

/-! ## 5. The harmonic ceiling along a non-descending orbit -/

/-- **Harmonic packing under non-descent.**  If the first `N` states of the odd orbit of `M ≥ 3`
are pairwise distinct and all at least `M`, then
`∑_{k<N} 1/m_k ≤ 2/(M-2) + (1/3) log (1 + 3N/(M-2))`.

Compare `HarmonicPacking.sum_inv_orbit_le`, which uses only distinctness and gives
`7/3 + (1/3) log N`; and the trivial floor bound `N/M`. -/
theorem sum_inv_orbit_le_of_nondescent (M N : ℕ) (hM : Odd M) (hM3 : 3 ≤ M)
    (hinj : ∀ i < N, ∀ j < N, orbit M i = orbit M j → i = j)
    (hge : ∀ i < N, M ≤ orbit M i) :
    ∑ k ∈ range N, (1 : ℝ) / (orbit M k : ℝ)
      ≤ 2 / ((M : ℝ) - 2) + (1 / 3) * Real.log (1 + 3 * (N : ℝ) / ((M : ℝ) - 2)) := by
  have hMR : (3 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM3
  have hb : (0 : ℝ) < (M : ℝ) - 2 := by linarith
  have hlognn : ∀ t : ℕ, 0 ≤ Real.log (1 + 3 * (t : ℝ) / ((M : ℝ) - 2)) := by
    intro t
    apply Real.log_nonneg
    have : (0 : ℝ) ≤ 3 * (t : ℝ) / ((M : ℝ) - 2) := by positivity
    linarith
  rcases N with _ | n
  · simp only [sum_range_zero]
    have := hlognn 0
    have h2 : (0 : ℝ) < 2 / ((M : ℝ) - 2) := by positivity
    linarith
  rw [sum_range_succ']
  -- the initial state
  have h0 : (1 : ℝ) / (orbit M 0 : ℝ) ≤ 1 / ((M : ℝ) - 2) := by
    rw [orbit_zero]
    exact one_div_le_one_div_of_le hb (by linarith)
  -- the post-initial states are distinct, coprime to `6`, and `≥ M`
  have hpack := sum_inv_le_sum_inv_shift (fun k => orbit M (k + 1)) n M hM3
    (fun i hi j hj heq => by
      have := hinj (i + 1) (by omega) (j + 1) (by omega) heq
      omega)
    (fun i _ => odd_orbit hM (i + 1))
    (fun i _ => three_not_dvd_orbit_succ M i)
    (fun i hi => hge (i + 1) (by omega))
  have hsum := sum_range_inv_shift_le ((M : ℝ) - 2) hb n
  have hnn : (0 : ℝ) ≤ 3 * (n : ℝ) / ((M : ℝ) - 2) :=
    div_nonneg (by positivity) hb.le
  have hmono : Real.log (1 + 3 * (n : ℝ) / ((M : ℝ) - 2))
      ≤ Real.log (1 + 3 * ((n + 1 : ℕ) : ℝ) / ((M : ℝ) - 2)) := by
    apply Real.log_le_log (by linarith)
    push_cast
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h3 : 3 * (n : ℝ) / ((M : ℝ) - 2) ≤ 3 * ((n : ℝ) + 1) / ((M : ℝ) - 2) := by
      have hinv : (0 : ℝ) < ((M : ℝ) - 2)⁻¹ := by positivity
      rw [div_eq_mul_inv, div_eq_mul_inv]
      nlinarith
    linarith
  calc ∑ k ∈ range n, (1 : ℝ) / (orbit M (k + 1) : ℝ) + (1 : ℝ) / (orbit M 0 : ℝ)
      ≤ (1 / ((M : ℝ) - 2) + (1 / 3) * Real.log (1 + 3 * (n : ℝ) / ((M : ℝ) - 2)))
          + 1 / ((M : ℝ) - 2) := add_le_add (le_trans hpack hsum) h0
    _ = 2 / ((M : ℝ) - 2) + (1 / 3) * Real.log (1 + 3 * (n : ℝ) / ((M : ℝ) - 2)) := by ring
    _ ≤ 2 / ((M : ℝ) - 2)
          + (1 / 3) * Real.log (1 + 3 * ((n + 1 : ℕ) : ℝ) / ((M : ℝ) - 2)) := by linarith

/-- **The harmonic carry bound.** Under non-descent with distinct states,
`E_N = log₂ U_N ≤ (1/9) log₂ (1 + 3N/(M-2)) + 2/(3 ln 2 (M-2))`. -/
theorem carryE_le_of_nondescent (M N : ℕ) (hM : Odd M) (hM3 : 3 ≤ M)
    (hinj : ∀ i < N, ∀ j < N, orbit M i = orbit M j → i = j)
    (hge : ∀ i < N, M ≤ orbit M i) :
    carryE M N ≤ (1 / (9 * Real.log 2)) * Real.log (1 + 3 * (N : ℝ) / ((M : ℝ) - 2))
      + 2 / (3 * Real.log 2 * ((M : ℝ) - 2)) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hterm : ∀ k ∈ range N, Real.logb 2 (1 + 1 / (3 * (orbit M k : ℝ)))
      ≤ (1 / (3 * Real.log 2)) * (1 / (orbit M k : ℝ)) := by
    intro k _
    calc Real.logb 2 (1 + 1 / (3 * (orbit M k : ℝ)))
        ≤ 1 / (3 * (orbit M k : ℝ)) / Real.log 2 :=
          HarmonicPacking.logb_two_one_add_le _ (by positivity)
      _ = (1 / (3 * Real.log 2)) * (1 / (orbit M k : ℝ)) := by ring
  have hpack := sum_inv_orbit_le_of_nondescent M N hM hM3 hinj hge
  have hMR : (3 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM3
  have hb : (0 : ℝ) < (M : ℝ) - 2 := by linarith
  calc carryE M N
      ≤ ∑ k ∈ range N, (1 / (3 * Real.log 2)) * (1 / (orbit M k : ℝ)) := sum_le_sum hterm
    _ = (1 / (3 * Real.log 2)) * ∑ k ∈ range N, (1 / (orbit M k : ℝ)) := by rw [mul_sum]
    _ ≤ (1 / (3 * Real.log 2))
          * (2 / ((M : ℝ) - 2) + (1 / 3) * Real.log (1 + 3 * (N : ℝ) / ((M : ℝ) - 2))) :=
        mul_le_mul_of_nonneg_left hpack (by positivity)
    _ = (1 / (9 * Real.log 2)) * Real.log (1 + 3 * (N : ℝ) / ((M : ℝ) - 2))
          + 2 / (3 * Real.log 2 * ((M : ℝ) - 2)) := by field_simp; ring

/-- **The harmonic drift ceiling.**  If the odd seed `M ≥ 3` has pairwise distinct states through
step `N`, none of which is below `M`, then

  `R_N ≤ (1/(9 ln 2)) log (1 + 3N/(M-2)) + 2/(3 ln 2 (M-2))`.

This replaces the linear ceiling `R_N ≤ N/(3M ln 2)` of `DirectDescent.R_le_of_nondescent`; the two
agree to first order for `N ≪ M`, and for `N = C·M` the new one is `(1/9) log₂(1+3C) + O(1/M)`
instead of `C/(3 ln 2)`. -/
theorem R_le_of_nondescent_harmonic (M N : ℕ) (hM : Odd M) (hM3 : 3 ≤ M)
    (hinj : ∀ i ≤ N, ∀ j ≤ N, orbit M i = orbit M j → i = j)
    (hge : ∀ i ≤ N, M ≤ orbit M i) :
    R (orbWord M) N ≤ (1 / (9 * Real.log 2)) * Real.log (1 + 3 * (N : ℝ) / ((M : ℝ) - 2))
      + 2 / (3 * Real.log 2 * ((M : ℝ) - 2)) := by
  have hMR : (3 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM3
  have hM0 : (0 : ℝ) < (M : ℝ) := by linarith
  have hid := orbit_mul_two_rpow_R M N hM
  have hMN : (M : ℝ) ≤ (orbit M N : ℝ) := by exact_mod_cast hge N le_rfl
  -- `2^{R_N} = M U_N / m_N ≤ U_N = 2^{E_N}`
  have hpow : (2 : ℝ) ^ (R (orbWord M) N) ≤ carryU M N := by
    have h1 : (M : ℝ) * (2 : ℝ) ^ (R (orbWord M) N) ≤ (orbit M N : ℝ) * (2 : ℝ) ^ (R (orbWord M) N) :=
      mul_le_mul_of_nonneg_right hMN (Real.rpow_nonneg (by norm_num) _)
    rw [hid] at h1
    exact le_of_mul_le_mul_left (by linarith) hM0
  have hEcarry : R (orbWord M) N ≤ carryE M N := by
    rw [carryU_eq_two_rpow_carryE] at hpow
    exact (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp hpow
  have hE := carryE_le_of_nondescent M N hM hM3
    (fun i hi j hj h => hinj i hi.le j hj.le h) (fun i hi => hge i hi.le)
  linarith

/-! ## 6. Band occupancy: the drift cannot stay high -/

/-- The carry product is nondecreasing along an odd orbit (proved again below as strict
monotonicity; this weak form is what the occupancy bound needs). -/
theorem carryU_le_of_le (M : ℕ) (hM : Odd M) {i j : ℕ} (hij : i ≤ j) :
    carryU M i ≤ carryU M j := by
  induction j with
  | zero => simp_all
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h | h
    · have hpos := carryU_pos M j
      have hmj : (0 : ℝ) < (orbit M j : ℝ) := by exact_mod_cast (odd_orbit hM j).pos
      have hstep : carryU M j ≤ carryU M (j + 1) := by
        rw [carryU_succ]
        nlinarith [one_div_pos.mpr (by positivity : (0 : ℝ) < 3 * (orbit M j : ℝ))]
      exact le_trans (ih (by omega)) hstep
    · have : i = j + 1 := by omega
      subst this; exact le_rfl

/-- **The weighted observable.** `∑_{j<N} 2^{R_j} ≤ M · U_N · ∑_{j<N} 1/m_j`, from the
Eliahou–Rozier identity `2^{R_j} = M U_j / m_j` and `U_j ≤ U_N`. -/
theorem sum_two_rpow_R_le (M N : ℕ) (hM : Odd M) :
    ∑ j ∈ range N, (2 : ℝ) ^ (R (orbWord M) j)
      ≤ (M : ℝ) * carryU M N * ∑ j ∈ range N, (1 : ℝ) / (orbit M j : ℝ) := by
  rw [mul_sum]
  refine sum_le_sum fun j hj => ?_
  have hjN : j ≤ N := (mem_range.mp hj).le
  have hmj : (0 : ℝ) < (orbit M j : ℝ) := by exact_mod_cast (odd_orbit hM j).pos
  have hid := orbit_mul_two_rpow_R M j hM
  have hU : carryU M j ≤ carryU M N := carryU_le_of_le M hM hjN
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  -- `m_j 2^{R_j} = M U_j ≤ M U_N = m_j · (M U_N / m_j)`
  have key : (orbit M j : ℝ) * (2 : ℝ) ^ (R (orbWord M) j)
      ≤ (orbit M j : ℝ) * ((M : ℝ) * carryU M N * (1 / (orbit M j : ℝ))) := by
    have hrhs : (orbit M j : ℝ) * ((M : ℝ) * carryU M N * (1 / (orbit M j : ℝ)))
        = (M : ℝ) * carryU M N := by field_simp
    rw [hrhs, hid]
    nlinarith
  exact le_of_mul_le_mul_left key hmj

/-- **Band occupancy.**  Under non-descent with distinct states, the number of steps `j < N` whose
drift stays above `-A` is at most `2^A · M · U_N · (2/(M-2) + (1/3) log (1 + 3N/(M-2)))`.

With `N = C·M` and `U_N ≤ e^{C/3}` this is a bound of the form `(const) · M`: the drift must spend
a definite fraction of a long non-descending prefix strictly below any fixed level. -/
theorem band_occupancy (M N : ℕ) (hM : Odd M) (hM3 : 3 ≤ M) (A : ℝ)
    (hinj : ∀ i < N, ∀ j < N, orbit M i = orbit M j → i = j)
    (hge : ∀ i < N, M ≤ orbit M i) :
    (((range N).filter (fun j => -A ≤ R (orbWord M) j)).card : ℝ) * (2 : ℝ) ^ (-A)
      ≤ (M : ℝ) * carryU M N
        * (2 / ((M : ℝ) - 2) + (1 / 3) * Real.log (1 + 3 * (N : ℝ) / ((M : ℝ) - 2))) := by
  set T := (range N).filter (fun j => -A ≤ R (orbWord M) j) with hT
  have hlow : (T.card : ℝ) * (2 : ℝ) ^ (-A) ≤ ∑ j ∈ T, (2 : ℝ) ^ (R (orbWord M) j) := by
    have hterm : ∀ j ∈ T, (2 : ℝ) ^ (-A) ≤ (2 : ℝ) ^ (R (orbWord M) j) := by
      intro j hj
      have := (mem_filter.mp hj).2
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) this
    calc (T.card : ℝ) * (2 : ℝ) ^ (-A) = ∑ _j ∈ T, (2 : ℝ) ^ (-A) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ j ∈ T, (2 : ℝ) ^ (R (orbWord M) j) := sum_le_sum hterm
  have hsub : ∑ j ∈ T, (2 : ℝ) ^ (R (orbWord M) j)
      ≤ ∑ j ∈ range N, (2 : ℝ) ^ (R (orbWord M) j) := by
    apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    intro j _ _
    exact Real.rpow_nonneg (by norm_num) _
  have hW := sum_two_rpow_R_le M N hM
  have hpack := sum_inv_orbit_le_of_nondescent M N hM hM3 hinj hge
  have hUM : (0 : ℝ) ≤ (M : ℝ) * carryU M N := by
    have := carryU_pos M N
    have : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    positivity
  calc (T.card : ℝ) * (2 : ℝ) ^ (-A)
      ≤ ∑ j ∈ range N, (2 : ℝ) ^ (R (orbWord M) j) := le_trans hlow hsub
    _ ≤ (M : ℝ) * carryU M N * ∑ j ∈ range N, (1 : ℝ) / (orbit M j : ℝ) := hW
    _ ≤ (M : ℝ) * carryU M N
          * (2 / ((M : ℝ) - 2) + (1 / 3) * Real.log (1 + 3 * (N : ℝ) / ((M : ℝ) - 2))) :=
        mul_le_mul_of_nonneg_left hpack hUM

/-! ## 7. The distinctness hypothesis: a repeat is a cycle with strictly increasing drift -/

/-- The carry product is strictly increasing along an odd orbit. -/
theorem carryU_lt_succ (M k : ℕ) (hM : Odd M) : carryU M k < carryU M (k + 1) := by
  have hpos := carryU_pos M k
  have hmk : (0 : ℝ) < (orbit M k : ℝ) := by exact_mod_cast (odd_orbit hM k).pos
  rw [carryU_succ]
  nlinarith [one_div_pos.mpr (by positivity : (0 : ℝ) < 3 * (orbit M k : ℝ))]

theorem carryU_strictMono (M : ℕ) (hM : Odd M) : StrictMono (carryU M) := by
  apply strictMono_nat_of_lt_succ
  exact fun k => carryU_lt_succ M k hM

/-- **A repeated state forces strictly increasing drift.**  If `m_i = m_j` with `i < j`, then
`R_i < R_j`.  (Consequently an orbit that revisits a state is periodic with a strictly positive
drift per period, so it cannot stay confined: distinctness fails only for genuine nontrivial
cycles.) -/
theorem R_lt_of_orbit_eq (M i j : ℕ) (hM : Odd M) (hij : i < j) (heq : orbit M i = orbit M j) :
    R (orbWord M) i < R (orbWord M) j := by
  have hidi := orbit_mul_two_rpow_R M i hM
  have hidj := orbit_mul_two_rpow_R M j hM
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM.pos
  have hmi : (0 : ℝ) < (orbit M i : ℝ) := by exact_mod_cast (odd_orbit hM i).pos
  have hU : carryU M i < carryU M j := carryU_strictMono M hM hij
  -- `m_i 2^{R_i} = M U_i < M U_j = m_j 2^{R_j} = m_i 2^{R_j}`
  have hlt : (orbit M i : ℝ) * (2 : ℝ) ^ (R (orbWord M) i)
      < (orbit M i : ℝ) * (2 : ℝ) ^ (R (orbWord M) j) := by
    rw [hidi, heq, hidj]
    · exact mul_lt_mul_of_pos_left hU hM0
  have hpow : (2 : ℝ) ^ (R (orbWord M) i) < (2 : ℝ) ^ (R (orbWord M) j) :=
    lt_of_mul_lt_mul_left (by linarith) hmi.le
  exact (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp hpow

end HarmonicFloor
end EOC
