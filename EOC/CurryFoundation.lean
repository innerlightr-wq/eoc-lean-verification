import EOC.HarmonicPacking
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# The Curry foundation: reciprocal summability to the zero-corridor tail

This file formalizes the **elementary downstream chain** behind the audited external theorem
of Michael John Curry, *"An Explicit Windowed Sparsity Bound for Divergent 3x + 1 Orbits, with
Logarithmic-Floor Exclusion beyond the Harmonic Barrier"* (24 Aug 2026) — see
`docs/CURRY_FOUNDATION.md` for the full audit and provenance.

**What is *not* done here.** Curry's Theorem 2.3 (the windowed sparsity bound itself) is
*not* formalized: it is an analytic, self-contained, five-page argument over the raw map
`n ↦ n/2, (3n+1)/2`, independently audited (not merely cited) but external to this repository,
exactly like `LogFloorExclusion` in `EOC.LogCorridor`. It enters here only through the single
external interface `ReciprocalSummable`, at the weakest point that makes it usable: the
reciprocal-summability conclusion of Curry's Proposition 3.1 (manuscript Proposition 4.9),
translated to the accelerated map's own `orbit`/`orbWord`/`R`/`carryE`/`carryU` (all reused
unchanged from `EOC.ValuationWord`, `EOC.Confinement`, `EOC.HarmonicPacking` — no parallel
definitions are introduced).

**Why `Summable (fun n => 1/(orbit M n))` alone suffices.** Indexing the reciprocal sum by
*time* `n` rather than by *value* is not a weakening: for an orbit whose value set is
collision-free (Curry's own hypothesis), `n ↦ orbit M n` is injective, so the two sums agree.
Conversely, summability of the time-indexed series already *forces* the terms to tend to `0`,
which is impossible for an eventually periodic orbit (the terms would recur among finitely many
fixed positive values); so this single hypothesis quietly carries the injectivity/divergence
content as well, and no separate `injective_orbit` hypothesis needs to be threaded through the
chain below (`orbit_tendsto_atTop` derives `m_n → ∞` from `ReciprocalSummable` alone).

**Chain formalized** (Level B / Level C in `docs/CURRY_FOUNDATION.md`):

* `ReciprocalSummable` — the external interface.
* `orbit_tendsto_atTop` — `m_n → ∞` (Lean target 2).
* `carryE_tendsto`, `carryU_tendsto` — `E_n → E_∞ < ∞`, `Q_n → Q_∞ < ∞` (Lean target 1).
* `R_tendsto_atBot` — `R_n → -∞` (Lean target 3).
* `summable_two_rpow_R` — `∑ 2^{R_n} < ∞`.
* `exists_last_atBot_max` — a generic, Collatz-independent real-sequence fact: a sequence
  tending to `-∞` has a last global maximum (Lean target 4).
* `alpha_smul_not_int` — `k·α ∉ ℤ` for `k ≥ 1` (Lean target 5's number-theoretic ingredient,
  proved directly rather than assumed).
* `zero_corridor_tail` — the Zero-Corridor Tail Theorem: past the last global drift maximum,
  every restarted prefix sum stays on or below the Beatty line `⌊kα⌋` (Lean target 5).
* `deficit_nonneg`, `deficit_tendsto_atTop_iff`, `beatty_gap_mem`, `deficit_succ` — the deficit
  dynamics (Lean target 6).

**A correction to the informal audit.** The audit's write-up (`docs/CURRY_FOUNDATION.md` §8.5)
states the zero-corridor step "uses irrationality of α". Formalizing it here shows this is not
quite precise: `S'_k ≤ ⌊kα⌋` follows from `S'_k < kα` for *integer* `S'_k` by the plain
definition of the floor (`Int.le_floor`), with no rationality hypothesis on `α` at all.
Irrationality of `α` is genuinely needed elsewhere in the package — for the Beatty-gap fact
`b_k ∈ {1,2}` used in the deficit recurrence — so `alpha_smul_not_int` is kept and used there,
but is not load-bearing for `zero_corridor_tail` itself. This is exactly the kind of
attribution-precision the audit asked to be checked "as a theorem, not a heuristic."

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace CurryFoundation

open Filter Topology Finset HarmonicPacking

/-! ## 1. The external interface -/

/-- **External interface.** Reciprocal summability of the accelerated orbit of `M`, in the
strongest form Curry's audited Theorem 2.3 delivers (manuscript Proposition 4.9): the
time-indexed series `∑ 1/m_n` converges. This is *not* proved in this repository — Curry's
window theorem is not formalized here — and is not an axiom of Lean; it is an ordinary
hypothesis threaded through every theorem below, exactly as `LogFloorExclusion` is in
`EOC.LogCorridor`. -/
def ReciprocalSummable (M : ℕ) : Prop :=
  Summable (fun n : ℕ => 1 / (orbit M n : ℝ))

section Chain

variable {M : ℕ}

theorem orbit_pos (hM : Odd M) (n : ℕ) : 0 < (orbit M n : ℝ) := by
  exact_mod_cast (odd_orbit hM n).pos

/-! ## 2. Injective positive orbit tends to infinity (Lean target 2) -/

/-- **`m_n → ∞`.** A reciprocally-summable accelerated orbit's values tend to infinity — not
merely unboundedly, but genuinely as a limit, since the summands are eventually forced to `0`
and a positive sequence with reciprocal tending to `0` tends to `+∞`. -/
theorem orbit_tendsto_atTop (hM : Odd M) (hrs : ReciprocalSummable M) :
    Tendsto (fun n => (orbit M n : ℝ)) atTop atTop := by
  have h0 : Tendsto (fun n : ℕ => 1 / (orbit M n : ℝ)) atTop (𝓝 0) := hrs.tendsto_atTop_zero
  have hpos : Tendsto (fun n : ℕ => 1 / (orbit M n : ℝ)) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h0
      (Filter.Eventually.of_forall fun n =>
        Set.mem_Ioi.mpr (by have := orbit_pos hM n; positivity))
  have hinv := tendsto_inv_nhdsGT_zero.comp hpos
  simp only [Function.comp_def, one_div, inv_inv] at hinv
  exact hinv

/-! ## 3. Bounded carry sum / bounded carry product (Lean target 1) -/

theorem carryE_monotone (hM : Odd M) : Monotone (carryE M) := by
  apply monotone_nat_of_le_succ
  intro n
  have hstep : (0 : ℝ) ≤ Real.logb 2 (1 + 1 / (3 * (orbit M n : ℝ))) := by
    apply Real.logb_nonneg (by norm_num)
    have := orbit_pos hM n
    have h2 : (0 : ℝ) ≤ 1 / (3 * (orbit M n : ℝ)) := by positivity
    linarith
  have hE : carryE M (n + 1) = carryE M n + Real.logb 2 (1 + 1 / (3 * (orbit M n : ℝ))) := by
    unfold carryE
    rw [Finset.sum_range_succ]
  linarith [hE, hstep]

theorem carryE_bddAbove (hM : Odd M) (hrs : ReciprocalSummable M) :
    BddAbove (Set.range (carryE M)) := by
  have hcomp : Summable (fun n : ℕ => 1 / (3 * (orbit M n : ℝ))) := by
    have heq : (fun n : ℕ => 1 / (3 * (orbit M n : ℝ)))
        = (fun n : ℕ => (1 / 3) * (1 / (orbit M n : ℝ))) := by
      funext n; ring
    rw [heq]
    exact hrs.mul_left (1 / 3)
  refine ⟨(1 / Real.log 2) * ∑' n, 1 / (3 * (orbit M n : ℝ)), ?_⟩
  rintro y ⟨N, rfl⟩
  have hterm : ∀ n ∈ range N,
      Real.logb 2 (1 + 1 / (3 * (orbit M n : ℝ))) ≤ (1 / (3 * (orbit M n : ℝ))) / Real.log 2 := by
    intro n _
    exact logb_two_one_add_le _ (by positivity)
  have hsum_le : carryE M N ≤ ∑ n ∈ range N, (1 / (3 * (orbit M n : ℝ))) / Real.log 2 := by
    unfold carryE
    exact Finset.sum_le_sum hterm
  have hpull : ∑ n ∈ range N, (1 / (3 * (orbit M n : ℝ))) / Real.log 2
      = (1 / Real.log 2) * ∑ n ∈ range N, 1 / (3 * (orbit M n : ℝ)) := by
    rw [Finset.mul_sum]; congr 1; funext n; ring
  have htsum_le : ∑ n ∈ range N, 1 / (3 * (orbit M n : ℝ)) ≤ ∑' n, 1 / (3 * (orbit M n : ℝ)) :=
    hcomp.sum_le_tsum (range N) (fun n _ => by positivity)
  have hlogpos : (0 : ℝ) ≤ 1 / Real.log 2 := by positivity
  calc carryE M N ≤ ∑ n ∈ range N, (1 / (3 * (orbit M n : ℝ))) / Real.log 2 := hsum_le
    _ = (1 / Real.log 2) * ∑ n ∈ range N, 1 / (3 * (orbit M n : ℝ)) := hpull
    _ ≤ (1 / Real.log 2) * ∑' n, 1 / (3 * (orbit M n : ℝ)) :=
        mul_le_mul_of_nonneg_left htsum_le hlogpos

/-- **`E_n → E_∞ < ∞`.** The manuscript's carry-budget sum converges (it does not merely grow
like `O(log N)`, the unconditional harmonic-packing bound of `EOC.HarmonicPacking`). -/
theorem carryE_tendsto (hM : Odd M) (hrs : ReciprocalSummable M) :
    ∃ Einfty : ℝ, Tendsto (carryE M) atTop (𝓝 Einfty) :=
  ⟨_, tendsto_atTop_ciSup (carryE_monotone hM) (carryE_bddAbove hM hrs)⟩

/-- **`Q_n → Q_∞ < ∞`.** The manuscript's carry product converges. -/
theorem carryU_tendsto (hM : Odd M) (hrs : ReciprocalSummable M) :
    ∃ Qinfty : ℝ, 0 < Qinfty ∧ Tendsto (carryU M) atTop (𝓝 Qinfty) := by
  obtain ⟨Einfty, hE⟩ := carryE_tendsto hM hrs
  refine ⟨(2 : ℝ) ^ Einfty, by positivity, ?_⟩
  have hrpow : Tendsto (fun n => (2 : ℝ) ^ carryE M n) atTop (𝓝 ((2 : ℝ) ^ Einfty)) :=
    Filter.Tendsto.rpow tendsto_const_nhds hE (Or.inl (by norm_num))
  have heq : (fun n => (2 : ℝ) ^ carryE M n) = carryU M := by
    funext n; exact (carryU_eq_two_rpow_carryE M n).symm
  rwa [heq] at hrpow

/-! ## 4. `R_n → -∞` (Lean target 3) -/

theorem two_rpow_R_eq (hM : Odd M) (n : ℕ) :
    (2 : ℝ) ^ (R (orbWord M) n) = (M : ℝ) * carryU M n / (orbit M n : ℝ) := by
  have hid := orbit_mul_two_rpow_R M n hM
  have hpos := orbit_pos hM n
  rw [eq_div_iff hpos.ne']
  linarith [hid]

/-- **`R_n → -∞`.** The drift of every reciprocally-summable accelerated orbit tends to `-∞`.
Labeled `CURRY + ELEMENTARY CONSEQUENCE` in `docs/CURRY_FOUNDATION.md`: not stated by Curry, a
short rigorous consequence of `orbit_tendsto_atTop` (target 2) and `carryU_tendsto` (target 1)
via the Eliahou–Rozier identity `orbit_mul_two_rpow_R`. -/
theorem R_tendsto_atBot (hM : Odd M) (hrs : ReciprocalSummable M) :
    Tendsto (fun n => R (orbWord M) n) atTop atBot := by
  obtain ⟨Qinfty, _hQinftypos, hQ⟩ := carryU_tendsto hM hrs
  have hnum : Tendsto (fun n => (M : ℝ) * carryU M n) atTop (𝓝 ((M : ℝ) * Qinfty)) := hQ.const_mul _
  have hden : Tendsto (fun n => (orbit M n : ℝ)) atTop atTop := orbit_tendsto_atTop hM hrs
  have hratio : Tendsto (fun n => (M : ℝ) * carryU M n / (orbit M n : ℝ)) atTop (𝓝 0) :=
    hnum.div_atTop hden
  have h0 : Tendsto (fun n => (2 : ℝ) ^ (R (orbWord M) n)) atTop (𝓝 0) := by
    simpa [two_rpow_R_eq hM] using hratio
  rw [tendsto_atBot]
  intro b
  have hb2pos : (0 : ℝ) < (2 : ℝ) ^ b := by positivity
  have hev : ∀ᶠ n in atTop, (2 : ℝ) ^ (R (orbWord M) n) < (2 : ℝ) ^ b :=
    (tendsto_order.mp h0).2 _ hb2pos
  filter_upwards [hev] with n hn
  exact le_of_lt ((Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp hn)

/-! ## 5. `∑ 2^{R_n} < ∞` -/

theorem carryU_monotone (hM : Odd M) : Monotone (carryU M) := by
  apply monotone_nat_of_le_succ
  intro n
  have hfac : (1 : ℝ) ≤ 1 + 1 / (3 * (orbit M n : ℝ)) := by
    have h1 := orbit_pos hM n
    have h2 : (0 : ℝ) ≤ 1 / (3 * (orbit M n : ℝ)) := by positivity
    linarith
  rw [carryU_succ]
  exact le_mul_of_one_le_right (carryU_pos M n).le hfac

/-- **`∑ 2^{R_n} < ∞`.** Not stated by Curry or in the manuscript; a short derivation from the
exact identity `m_n 2^{R_n} = m_0 Q_n` together with reciprocal summability and boundedness of
`Q_n`. -/
theorem summable_two_rpow_R (hM : Odd M) (hrs : ReciprocalSummable M) :
    Summable (fun n => (2 : ℝ) ^ (R (orbWord M) n)) := by
  obtain ⟨Qinfty, _hQinftypos, hQ⟩ := carryU_tendsto hM hrs
  have hQle : ∀ n, carryU M n ≤ Qinfty :=
    fun n => ge_of_tendsto hQ (eventually_atTop.mpr ⟨n, fun c hc => carryU_monotone hM hc⟩)
  have hbound : ∀ n, (2 : ℝ) ^ (R (orbWord M) n) ≤ (M : ℝ) * Qinfty * (1 / (orbit M n : ℝ)) := by
    intro n
    rw [two_rpow_R_eq hM, div_eq_mul_inv, one_div]
    have hMnn : (0 : ℝ) ≤ (M : ℝ) := by positivity
    have hinvnn : (0 : ℝ) ≤ (orbit M n : ℝ)⁻¹ := by positivity
    calc (M : ℝ) * carryU M n * (orbit M n : ℝ)⁻¹
        ≤ (M : ℝ) * Qinfty * (orbit M n : ℝ)⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ hinvnn
          exact mul_le_mul_of_nonneg_left (hQle n) hMnn
      _ = (M : ℝ) * Qinfty * (orbit M n : ℝ)⁻¹ := rfl
  have hnonneg : ∀ n, (0 : ℝ) ≤ (2 : ℝ) ^ (R (orbWord M) n) := fun _ => by positivity
  have hmaj : Summable (fun n => (M : ℝ) * Qinfty * (1 / (orbit M n : ℝ))) := hrs.mul_left _
  exact Summable.of_nonneg_of_le hnonneg hbound hmaj

end Chain

/-! ## 6. A last global maximum (Lean target 4, Collatz-independent) -/

/-- **Last global maximum.** A generic real-sequence fact, proved independently of Collatz: if
`f n → -∞`, then `f` attains a global maximum and there is a *last* index attaining it,
strictly exceeding `f` at every later index. -/
theorem exists_last_atBot_max {f : ℕ → ℝ} (hf : Tendsto f atTop atBot) :
    ∃ n0, (∀ n, f n ≤ f n0) ∧ ∀ k, 1 ≤ k → f (n0 + k) < f n0 := by
  -- Stage 1: a finite window whose max over it is already the global max `Mstar`.
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp ((tendsto_atBot.mp hf) (f 0))
  obtain ⟨m1, hm1mem, hm1max⟩ :=
    Finset.exists_max_image (range (N1 + 1)) f ⟨0, mem_range.mpr (by omega)⟩
  have hm1lt : m1 < N1 + 1 := mem_range.mp hm1mem
  set Mstar : ℝ := f m1 with hMstar
  have hglobal : ∀ n, f n ≤ Mstar := by
    intro n
    by_cases h : n ≤ N1
    · exact hm1max n (mem_range.mpr (by omega))
    · push Not at h
      calc f n ≤ f 0 := hN1 n (by omega)
        _ ≤ Mstar := hm1max 0 (mem_range.mpr (by omega))
  -- Stage 2: strictly below `Mstar` past some `N2`.
  obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp ((tendsto_atBot.mp hf) (Mstar - 1))
  set N : ℕ := max N1 N2 with hNdef
  have hN1leN : N1 ≤ N := le_max_left N1 N2
  have hN2leN : N2 ≤ N := le_max_right N1 N2
  -- Stage 3: the last maximizer within `range (N+1)` is the last global maximizer.
  set S : Finset ℕ := (range (N + 1)).filter (fun n => f n = Mstar) with hSdef
  have hSne : S.Nonempty := by
    refine ⟨m1, ?_⟩
    rw [hSdef, mem_filter]
    exact ⟨mem_range.mpr (by omega), rfl⟩
  set n0 : ℕ := S.max' hSne with hn0def
  have hn0S : n0 ∈ S := S.max'_mem hSne
  have hn0eq : f n0 = Mstar := (mem_filter.mp hn0S).2
  refine ⟨n0, by rw [hn0eq]; exact hglobal, ?_⟩
  intro k hk
  rw [hn0eq]
  by_cases h : n0 + k ≤ N
  · have hne : f (n0 + k) ≠ Mstar := by
      intro heq
      have hmem : n0 + k ∈ S := by
        rw [hSdef, mem_filter]; exact ⟨mem_range.mpr (by omega), heq⟩
      have := Finset.le_max' S (n0 + k) hmem
      omega
    exact lt_of_le_of_ne (hglobal (n0 + k)) hne
  · push Not at h
    have hle : f (n0 + k) ≤ Mstar - 1 := hN2 (n0 + k) (by omega)
    linarith

/-! ## 7. Irrationality of `k·α` and the zero-corridor tail (Lean target 5) -/

/-- The one number-theoretic fact used in the deficit dynamics below: `k·α` is never an integer
for `k ≥ 1`. Proved directly (`3^k = 2^j` is impossible by parity / size), not assumed. -/
theorem alpha_smul_not_int (k : ℕ) (hk : 1 ≤ k) (j : ℤ) : (k : ℝ) * alpha ≠ (j : ℝ) := by
  intro heq
  have hexp : (k : ℝ) * Real.log 3 = (j : ℝ) * Real.log 2 := by
    have halpha : alpha = Real.log 3 / Real.log 2 := by unfold alpha; rw [Real.logb]
    rw [halpha] at heq
    have hlog2ne : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    field_simp at heq
    linarith [heq]
  have h3k : (3 : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log 3) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
  have h2j : (2 : ℝ) ^ (j : ℝ) = Real.exp ((j : ℝ) * Real.log 2) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm]
  have hexp' : (3 : ℝ) ^ k = (2 : ℝ) ^ (j : ℝ) := by rw [h3k, hexp, ← h2j]
  by_cases hj0 : 0 ≤ j
  · lift j to ℕ using hj0 with j'
    have hexp'' : (3 : ℝ) ^ k = (2 : ℝ) ^ j' := by
      rwa [show ((j' : ℤ) : ℝ) = ((j' : ℕ) : ℝ) from by push_cast; ring,
        Real.rpow_natCast] at hexp'
    have hnat : (3 : ℕ) ^ k = 2 ^ j' := by exact_mod_cast hexp''
    rcases Nat.eq_zero_or_pos j' with hj'0 | hj'pos
    · subst hj'0
      simp only [pow_zero] at hnat
      have h3ge : 3 ≤ (3 : ℕ) ^ k := by
        calc (3 : ℕ) = 3 ^ 1 := (pow_one 3).symm
          _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      omega
    · have hodd3 : Odd (3 : ℕ) := ⟨1, by norm_num⟩
      have hodd : Odd ((3 : ℕ) ^ k) := hodd3.pow
      have heven : Even ((2 : ℕ) ^ j') := (Nat.even_pow' (by omega)).mpr (by norm_num)
      have hodd2 : (3 : ℕ) ^ k % 2 = 1 := Nat.odd_iff.mp hodd
      have heven2 : (2 : ℕ) ^ j' % 2 = 0 := Nat.even_iff.mp heven
      rw [hnat] at hodd2
      omega
  · push Not at hj0
    have hjR : (j : ℝ) < 0 := by exact_mod_cast hj0
    have h1 : (2 : ℝ) ^ (j : ℝ) < 1 := by
      have := (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr hjR
      rwa [Real.rpow_zero] at this
    have h2 : (1 : ℝ) ≤ (3 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    linarith [hexp']

theorem alpha_lt_two : alpha < 2 := by
  unfold alpha
  rw [Real.logb_lt_iff_lt_rpow (by norm_num : (1 : ℝ) < 2) (by norm_num : (0 : ℝ) < 3)]
  have h4 : (2 : ℝ) ^ (2 : ℝ) = 4 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
    norm_num
  rw [h4]; norm_num

/-- **Zero-Corridor Tail Theorem.** After the last global maximum of the drift, every
restarted prefix of a reciprocally-summable accelerated orbit's valuation word stays on or
below the Beatty line `⌊kα⌋`, strictly and for every `k ≥ 1`. This is the audited chain's
final target (Level C in `docs/CURRY_FOUNDATION.md`): the shifted drift is `R'_k := R(n0+k) -
R(n0) = S'_k - kα` where `S'_k := s(orbWord M)(n0+k) - s(orbWord M) n0`, and `R'_k < 0`
translates directly, via `Int.le_floor`, into `S'_k ≤ ⌊kα⌋`. -/
theorem zero_corridor_tail (hM : Odd M) (hrs : ReciprocalSummable M) :
    ∃ n0 : ℕ, ∀ k : ℕ, 1 ≤ k →
      (s (orbWord M) (n0 + k) : ℝ) - (s (orbWord M) n0 : ℝ) ≤ ⌊(k : ℝ) * alpha⌋ := by
  obtain ⟨n0, _hmax, hlast⟩ := exists_last_atBot_max (R_tendsto_atBot hM hrs)
  refine ⟨n0, fun k hk => ?_⟩
  have hRstep : R (orbWord M) (n0 + k) - R (orbWord M) n0
      = ((s (orbWord M) (n0 + k) : ℝ) - (s (orbWord M) n0 : ℝ)) - (k : ℝ) * alpha := by
    unfold R; push_cast; ring
  have hneg : R (orbWord M) (n0 + k) - R (orbWord M) n0 < 0 := by
    have := hlast k hk; linarith
  set Sk : ℝ := (s (orbWord M) (n0 + k) : ℝ) - (s (orbWord M) n0 : ℝ) with hSk
  have hlt : Sk < (k : ℝ) * alpha := by linarith [hRstep, hneg]
  have hSkInt : ∃ z : ℤ, Sk = (z : ℝ) :=
    ⟨(s (orbWord M) (n0 + k) : ℤ) - (s (orbWord M) n0 : ℤ), by push_cast [hSk]; ring⟩
  obtain ⟨z, hz⟩ := hSkInt
  have hzlt : (z : ℝ) < (k : ℝ) * alpha := hz ▸ hlt
  have hzfloor : z ≤ ⌊(k : ℝ) * alpha⌋ := Int.le_floor.mpr hzlt.le
  rw [hz]; exact_mod_cast hzfloor

/-! ## 8. Deficit dynamics (Lean target 6) -/

/-- The deficit below the Beatty line, for a prefix-sum sequence `S`. -/
noncomputable def deficit (S : ℕ → ℤ) (k : ℕ) : ℝ := (⌊(k : ℝ) * alpha⌋ : ℝ) - (S k : ℝ)

theorem deficit_nonneg (hM : Odd M) (hrs : ReciprocalSummable M) :
    ∃ n0 : ℕ, ∀ k, 1 ≤ k →
      0 ≤ deficit (fun k => (s (orbWord M) (n0 + k) : ℤ) - (s (orbWord M) n0 : ℤ)) k := by
  obtain ⟨n0, hcor⟩ := zero_corridor_tail hM hrs
  refine ⟨n0, fun k hk => ?_⟩
  have := hcor k hk
  unfold deficit
  push_cast
  linarith

/-- `R'_k = -Δ_k - {kα}`, with the fractional-part correction bounded in `(-1,0)`: `R'_k → -∞`
is exactly equivalent to `Δ_k → ∞`. -/
theorem deficit_tendsto_atTop_iff {S : ℕ → ℤ} {n0 : ℕ}
    (hR : ∀ k, ((S k : ℝ)) - (k : ℝ) * alpha
      = R (orbWord M) (n0 + k) - R (orbWord M) n0) :
    Tendsto (fun k => R (orbWord M) (n0 + k) - R (orbWord M) n0) atTop atBot
      ↔ Tendsto (fun k => deficit S k) atTop atTop := by
  have hrew : ∀ k, R (orbWord M) (n0 + k) - R (orbWord M) n0 = -(deficit S k)
      + ((⌊(k : ℝ) * alpha⌋ : ℝ) - (k : ℝ) * alpha) := by
    intro k; unfold deficit; rw [← hR k]; ring
  have hbound : ∀ k : ℕ, -1 < (⌊(k : ℝ) * alpha⌋ : ℝ) - (k : ℝ) * alpha
      ∧ (⌊(k : ℝ) * alpha⌋ : ℝ) - (k : ℝ) * alpha ≤ 0 :=
    fun k => ⟨by linarith [Int.sub_one_lt_floor ((k : ℝ) * alpha)],
      by linarith [Int.floor_le ((k : ℝ) * alpha)]⟩
  constructor
  · intro h
    rw [tendsto_atTop]
    intro b
    have hev : ∀ᶠ k in atTop, R (orbWord M) (n0 + k) - R (orbWord M) n0 ≤ -(b + 1) := by
      have := (tendsto_atBot.mp h) (-(b + 1)); exact this
    filter_upwards [hev] with k hk
    have hb1 := (hbound k).1
    rw [hrew k] at hk
    linarith
  · intro h
    rw [tendsto_atBot]
    intro b
    have hev : ∀ᶠ k in atTop, -b ≤ deficit S k := (tendsto_atTop.mp h) (-b)
    filter_upwards [hev] with k hk
    have hb2 := (hbound k).2
    rw [hrew k]
    linarith

/-- **Beatty gap.** `⌊(k+1)α⌋ - ⌊kα⌋ ∈ {1, 2}` for `1 < α < 2`. -/
theorem beatty_gap_mem (k : ℕ) :
    ⌊((k : ℝ) + 1) * alpha⌋ - ⌊(k : ℝ) * alpha⌋ = 1
      ∨ ⌊((k : ℝ) + 1) * alpha⌋ - ⌊(k : ℝ) * alpha⌋ = 2 := by
  have hlo : (⌊(k : ℝ) * alpha⌋ : ℝ) + alpha ≤ ((k : ℝ) + 1) * alpha := by
    have := Int.floor_le ((k : ℝ) * alpha); nlinarith
  have hhi : ((k : ℝ) + 1) * alpha < (⌊(k : ℝ) * alpha⌋ : ℝ) + 1 + alpha := by
    have := Int.lt_floor_add_one ((k : ℝ) * alpha); nlinarith
  have h1lt : (1 : ℝ) < alpha := one_lt_alpha
  have h2gt : alpha < 2 := alpha_lt_two
  have hlo' : (⌊(k : ℝ) * alpha⌋ : ℝ) + 1 < ((k : ℝ) + 1) * alpha := by linarith
  have hhi' : ((k : ℝ) + 1) * alpha < (⌊(k : ℝ) * alpha⌋ : ℝ) + 3 := by linarith
  have hfloor_lo' : ⌊(k : ℝ) * alpha⌋ + 1 ≤ ⌊((k : ℝ) + 1) * alpha⌋ := by
    apply Int.le_floor.mpr
    push_cast
    linarith [hlo']
  have hfloor_hi' : ⌊((k : ℝ) + 1) * alpha⌋ < ⌊(k : ℝ) * alpha⌋ + 3 := by
    have hh : (⌊((k : ℝ) + 1) * alpha⌋ : ℝ) < ((⌊(k : ℝ) * alpha⌋ + 3 : ℤ) : ℝ) := by
      push_cast
      exact lt_of_le_of_lt (Int.floor_le _) hhi'
    exact_mod_cast hh
  omega

/-- **Deficit recurrence.** `Δ_{k+1} = Δ_k + b_{k+1} - d_k` where `b_{k+1}` is the Beatty gap
and `d_k = S(k+1) - S(k)` is the valuation digit. Pure algebra from the definitions. -/
theorem deficit_succ (S : ℕ → ℤ) (k : ℕ) :
    deficit S (k + 1) = deficit S k
      + ((⌊((k : ℝ) + 1) * alpha⌋ - ⌊(k : ℝ) * alpha⌋ : ℤ) : ℝ)
      - ((S (k + 1) - S k : ℤ) : ℝ) := by
  unfold deficit
  push_cast
  ring

end CurryFoundation
end EOC
