import EOC.HarmonicPacking
import EOC.Confinement
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# A linear realizer floor already forces descent

The Fourier/counting side of this project bounds *how many* seeds have long confined prefixes.  For
the
Collatz conjecture itself what is needed is a **pointwise** statement, and this file records how weak that
statement may be: a **linear** lower bound on the least seed realizing a `c`-confined word already
forces
every sufficiently large odd seed to have a strictly smaller iterate, with an explicit threshold.

* `carryU_le_of_nondescent` — under non-descent, `U_N = ∏(1 + 1/(3 m_k)) ≤ (1 + 1/(3M))^N`.
* `R_le_of_nondescent` — hence `R_N ≤ N / (3 M ln 2)` (using `orbit_mul_two_rpow_R`).
* `confined_of_nondescent` — **non-descent for `N ≤ 3cM ln 2` steps ⇒ the own word is `c`-confined
to `N`**.
* `LinearRealizerFloor c A B N₀` — every odd `M` whose own word is `c`-confined to depth `N ≥ N₀`
satisfies
  `A·N − B ≤ M`.
* `descent_of_linearFloor` — if `3 A c ln 2 > 1` then every odd `M` above the explicit threshold
  `mstar = max ((A+B)/(3Ac ln 2 − 1), (N₀+1)/(3c ln 2))` has a strictly smaller iterate.
* `reachesOne_of_linearFloor` — with a finite base check below the threshold, every odd seed reaches
`1`.

At `c = 1` the critical coefficient is `1/(3 ln 2) = 0.4808983…`, so a floor `r_min(N,1) ≥ 0.49 N −
B`
would suffice.  Empirically `r_min(N,1)` grows like `2^{0.15N}` and the tightest ratio in the
verified range
is `27/39 = 0.692` (scratch/rmin_2026-09-16).  The floor itself is **OPEN**.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace DirectDescent

open Finset HarmonicPacking

/-- Under non-descent the carry product is at most `(1 + 1/(3M))^N`. -/
theorem carryU_le_of_nondescent {M N : ℕ} (hM : 0 < M) (h : ∀ i < N, M ≤ orbit M i) :
    carryU M N ≤ (1 + 1 / (3 * (M : ℝ))) ^ N := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  unfold carryU
  calc ∏ k ∈ range N, (1 + 1 / (3 * (orbit M k : ℝ)))
      ≤ ∏ _k ∈ range N, (1 + 1 / (3 * (M : ℝ))) := by
        refine prod_le_prod (fun k _ => ?_) (fun k hk => ?_)
        · have : (0 : ℝ) ≤ 1 / (3 * (orbit M k : ℝ)) := by positivity
          linarith
        · have hk'' : (M : ℝ) ≤ (orbit M k : ℝ) := by exact_mod_cast h k (mem_range.mp hk)
          have : 1 / (3 * (orbit M k : ℝ)) ≤ 1 / (3 * (M : ℝ)) :=
            one_div_le_one_div_of_le (by linarith) (by linarith)
          linarith
    _ = (1 + 1 / (3 * (M : ℝ))) ^ N := by rw [prod_const, card_range]

/-- Under non-descent through step `N`, the drift satisfies `R_N ≤ N / (3 M ln 2)`. -/
theorem R_le_of_nondescent {M N : ℕ} (hM : 0 < M) (hodd : Odd M) (h : ∀ i ≤ N, M ≤ orbit M i) :
    R (orbWord M) N ≤ (N : ℝ) / (3 * (M : ℝ) * Real.log 2) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hid := orbit_mul_two_rpow_R M N hodd
  have hON : (0 : ℝ) < (orbit M N : ℝ) := by
    have := h N le_rfl; have : 0 < orbit M N := lt_of_lt_of_le hM this
    exact_mod_cast this
  have hMN : (M : ℝ) ≤ (orbit M N : ℝ) := by exact_mod_cast h N le_rfl
  have hU := carryU_le_of_nondescent hM (fun i hi => h i hi.le)
  -- `2^{R_N} = M U_N / m_N ≤ U_N ≤ (1 + 1/(3M))^N`
  have hpow : (2 : ℝ) ^ (R (orbWord M) N) ≤ (1 + 1 / (3 * (M : ℝ))) ^ N := by
    have h1 : (orbit M N : ℝ) * (2 : ℝ) ^ (R (orbWord M) N) ≤ (M : ℝ) * (1 + 1 / (3 * (M : ℝ))) ^ N := by
      rw [hid]
      exact mul_le_mul_of_nonneg_left hU (le_of_lt hM')
    have h2 : (M : ℝ) * (2 : ℝ) ^ (R (orbWord M) N) ≤ (orbit M N : ℝ) * (2 : ℝ) ^ (R (orbWord M) N) :=
      mul_le_mul_of_nonneg_right hMN (Real.rpow_nonneg (by norm_num) _)
    have h3 : (M : ℝ) * (2 : ℝ) ^ (R (orbWord M) N) ≤ (M : ℝ) * (1 + 1 / (3 * (M : ℝ))) ^ N :=
      le_trans h2 h1
    exact le_of_mul_le_mul_left h3 hM'
  -- take logs
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hx : (0 : ℝ) < 1 + 1 / (3 * (M : ℝ)) := by positivity
  have hlog : R (orbWord M) N * Real.log 2 ≤ (N : ℝ) * Real.log (1 + 1 / (3 * (M : ℝ))) := by
    have := Real.log_le_log (Real.rpow_pos_of_pos (by norm_num) _) hpow
    rwa [Real.log_rpow (by norm_num), Real.log_pow] at this
  have hsmall : Real.log (1 + 1 / (3 * (M : ℝ))) ≤ 1 / (3 * (M : ℝ)) := by
    have := Real.add_one_le_exp (1 / (3 * (M : ℝ)))
    have h' : 1 + 1 / (3 * (M : ℝ)) ≤ Real.exp (1 / (3 * (M : ℝ))) := by linarith
    calc Real.log (1 + 1 / (3 * (M : ℝ))) ≤ Real.log (Real.exp (1 / (3 * (M : ℝ)))) :=
          Real.log_le_log hx h'
      _ = 1 / (3 * (M : ℝ)) := Real.log_exp _
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have : R (orbWord M) N * Real.log 2 ≤ (N : ℝ) * (1 / (3 * (M : ℝ))) :=
    le_trans hlog (mul_le_mul_of_nonneg_left hsmall hN0)
  have hstep : R (orbWord M) N * Real.log 2 * (3 * (M : ℝ)) ≤ (N : ℝ) := by
    have h' := mul_le_mul_of_nonneg_right this (by positivity : (0 : ℝ) ≤ 3 * (M : ℝ))
    calc R (orbWord M) N * Real.log 2 * (3 * (M : ℝ))
        ≤ (N : ℝ) * (1 / (3 * (M : ℝ))) * (3 * (M : ℝ)) := h'
      _ = (N : ℝ) := by field_simp
  rw [le_div_iff₀ (by positivity)]
  calc R (orbWord M) N * (3 * (M : ℝ) * Real.log 2)
      = R (orbWord M) N * Real.log 2 * (3 * (M : ℝ)) := by ring
    _ ≤ (N : ℝ) := hstep

/-- **Non-descent gives a confined word.**  If `M` is never strictly exceeded downwards through step
`N`
and `N ≤ 3 c M ln 2`, then the own word of `M` is `c`-confined to depth `N`. -/
theorem confined_of_nondescent {M N : ℕ} {c : ℝ} (hM : 0 < M) (hodd : Odd M)
    (h : ∀ i ≤ N, M ≤ orbit M i) (hN : (N : ℝ) ≤ 3 * c * (M : ℝ) * Real.log 2) :
    Confined c (orbWord M) N := by
  intro j hj
  have hjle : (j : ℝ) ≤ (N : ℝ) := by exact_mod_cast hj
  have hR := R_le_of_nondescent hM hodd (fun i hi => h i (le_trans hi hj))
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hden : (0 : ℝ) < 3 * (M : ℝ) * Real.log 2 := by positivity
  have : (j : ℝ) / (3 * (M : ℝ) * Real.log 2) ≤ c := by
    rw [div_le_iff₀ hden]
    nlinarith [hjle, hN]
  linarith [hR]

/-- **The linear realizer floor**: every odd seed whose own word is `c`-confined to depth `N ≥ N₀`
is at
least `A·N − B`.  (`r_min(N,c) ≥ A N − B` in the notation of `EOC.rmin`.) -/
def LinearRealizerFloor (c A B : ℝ) (N0 : ℕ) : Prop :=
  ∀ M N : ℕ, Odd M → N0 ≤ N → Confined c (orbWord M) N → A * (N : ℝ) - B ≤ (M : ℝ)

/-- The explicit descent threshold. -/
noncomputable def mstar (c A B : ℝ) (N0 : ℕ) : ℝ :=
  max ((A + B) / (3 * A * c * Real.log 2 - 1)) (((N0 : ℝ) + 1) / (3 * c * Real.log 2))

/-- **Linear realizer floor ⇒ strict descent above an explicit threshold.**  If `3 A c ln 2 > 1`,
every
odd `M > mstar c A B N₀` has an iterate strictly below `M`. -/
theorem descent_of_linearFloor {c A B : ℝ} {N0 : ℕ} (hc : 0 < c) (hA : 0 < A)
    (hcrit : 1 < 3 * A * c * Real.log 2) (hfloor : LinearRealizerFloor c A B N0)
    {M : ℕ} (hM : 0 < M) (hodd : Odd M) (hMs : mstar c A B N0 < (M : ℝ)) :
    ∃ n, 1 ≤ n ∧ orbit M n < M := by
  by_contra hcon
  push Not at hcon
  have hnd : ∀ i, M ≤ orbit M i := by
    intro i
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp
    · exact hcon i hi
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  set N : ℕ := ⌊3 * c * (M : ℝ) * Real.log 2⌋₊ with hNdef
  have hpos : (0 : ℝ) ≤ 3 * c * (M : ℝ) * Real.log 2 := by positivity
  have hNle : (N : ℝ) ≤ 3 * c * (M : ℝ) * Real.log 2 := Nat.floor_le hpos
  have hNge : 3 * c * (M : ℝ) * Real.log 2 - 1 < (N : ℝ) := by
    have := Nat.lt_floor_add_one (3 * c * (M : ℝ) * Real.log 2)
    linarith
  -- `N ≥ N₀`
  have hN0 : N0 ≤ N := by
    have h1 : ((N0 : ℝ) + 1) / (3 * c * Real.log 2) < (M : ℝ) :=
      lt_of_le_of_lt (le_max_right _ _) hMs
    have h2 : (N0 : ℝ) + 1 < 3 * c * (M : ℝ) * Real.log 2 := by
      rw [div_lt_iff₀ (by positivity)] at h1; nlinarith
    have : (N0 : ℝ) < (N : ℝ) := by linarith
    exact_mod_cast this.le
  -- the word is confined, so the floor applies
  have hconf := confined_of_nondescent hM hodd (fun i _ => hnd i) hNle
  have hge := hfloor M N hodd hN0 hconf
  -- contradiction with the threshold
  have h1 : (A + B) / (3 * A * c * Real.log 2 - 1) < (M : ℝ) :=
    lt_of_le_of_lt (le_max_left _ _) hMs
  rw [div_lt_iff₀ (by linarith)] at h1
  nlinarith [hge, hNge, hA, hM']


/-- `M` reaches `1`. -/
def ReachesOne (M : ℕ) : Prop := ∃ n, orbit M n = 1

theorem orbit_add (M n k : ℕ) : orbit M (n + k) = orbit (orbit M n) k := by
  induction k with
  | zero => simp
  | succ k ih => rw [show n + (k + 1) = (n + k) + 1 by omega, orbit_succ, ih, orbit_succ]

/-- **Floor + finite base check ⇒ every odd seed reaches 1.**  Minimal-counterexample induction on
the
strictly smaller iterate supplied by `descent_of_linearFloor`. -/
theorem reachesOne_of_linearFloor {c A B : ℝ} {N0 : ℕ} (hc : 0 < c) (hA : 0 < A)
    (hcrit : 1 < 3 * A * c * Real.log 2) (hfloor : LinearRealizerFloor c A B N0)
    (hbase : ∀ M : ℕ, 0 < M → Odd M → (M : ℝ) ≤ mstar c A B N0 → ReachesOne M) :
    ∀ M : ℕ, 0 < M → Odd M → ReachesOne M := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    intro hM hodd
    by_cases hsmall : (M : ℝ) ≤ mstar c A B N0
    · exact hbase M hM hodd hsmall
    · obtain ⟨n, hn1, hlt⟩ := descent_of_linearFloor hc hA hcrit hfloor hM hodd (not_le.mp hsmall)
      have hpos : 0 < orbit M n := by
        rcases Nat.eq_zero_or_pos (orbit M n) with h0 | h
        · exact absurd (h0 ▸ odd_orbit hodd n) (by simp)
        · exact h
      obtain ⟨k, hk⟩ := ih (orbit M n) hlt hpos (odd_orbit hodd n)
      exact ⟨n + k, by rw [orbit_add, hk]⟩


/-! ## Dyadic scales suffice -/

/-- Confinement to depth `N` implies confinement to any smaller depth. -/
theorem confined_mono {c : ℝ} {d : ℕ → ℕ} {N N' : ℕ} (h : Confined c d N) (hle : N' ≤ N) :
    Confined c d N' := fun j hj => h j (le_trans hj hle)

/-- **Dyadic realizer floor**: every odd seed whose own word is `c`-confined to depth `2^k`
(`k ≥ k₀`) is at least `2^k`. -/
def DyadicRealizerFloor (c : ℝ) (k0 : ℕ) : Prop :=
  ∀ M k : ℕ, Odd M → k0 ≤ k → Confined c (orbWord M) (2 ^ k) → ((2 : ℝ) ^ k) ≤ (M : ℝ)

/-- **Dyadic floor ⇒ linear floor with `A = 1/2`.**  For `2^k ≤ N < 2^{k+1}` confinement to depth `N`
gives confinement to depth `2^k`, hence `M ≥ 2^k > N/2`. -/
theorem linearFloor_of_dyadic {c : ℝ} {k0 : ℕ} (h : DyadicRealizerFloor c k0) :
    LinearRealizerFloor c (1 / 2) 0 (2 ^ k0) := by
  intro M N hodd hN hconf
  have hNpos : 0 < N := lt_of_lt_of_le (pow_pos (by norm_num : 0 < 2) k0) hN
  set k := Nat.log 2 N with hk
  have hk0 : k0 ≤ k := by
    have : Nat.log 2 (2 ^ k0) ≤ Nat.log 2 N := Nat.log_mono_right hN
    rwa [Nat.log_pow (by norm_num)] at this
  have hpow_le : 2 ^ k ≤ N := Nat.pow_log_le_self 2 hNpos.ne'
  have hlt : N < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  have hM := h M k hodd hk0 (confined_mono hconf hpow_le)
  have h1 : (N : ℝ) < 2 * (2 : ℝ) ^ k := by
    have h' : (N : ℝ) < ((2 ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast hlt
    push_cast at h'
    rw [pow_succ] at h'
    linarith
  linarith

/-- **Dyadic floor ⇒ every odd seed reaches 1** (at `c = 1`: `3·(1/2)·ln 2 = 1.0397… > 1`), given a
finite base check. -/
theorem reachesOne_of_dyadicFloor {k0 : ℕ} (h : DyadicRealizerFloor 1 k0)
    (hbase : ∀ M : ℕ, 0 < M → Odd M → (M : ℝ) ≤ mstar 1 (1 / 2) 0 (2 ^ k0) → ReachesOne M) :
    ∀ M : ℕ, 0 < M → Odd M → ReachesOne M := by
  refine reachesOne_of_linearFloor (by norm_num) (by norm_num) ?_ (linearFloor_of_dyadic h) hbase
  -- `3 * (1/2) * 1 * log 2 > 1` since `log 2 > 0.693`
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  nlinarith [h2]



/-! ## The `L₁(m) < C m` formulation -/

/-- **A minimal counterexample is automatically `1`-confined for `2m` steps.**  If the orbit of `M` never
goes below `M` through step `2M`, then its own word is `1`-confined to depth `2M`, because
`2/(3 ln 2) = 0.962… < 1`. -/
theorem confined_two_mul_of_nondescent {M : ℕ} (hM : 0 < M) (hodd : Odd M)
    (h : ∀ i ≤ 2 * M, M ≤ orbit M i) : Confined 1 (orbWord M) (2 * M) := by
  refine confined_of_nondescent hM hodd h ?_
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have : ((2 * M : ℕ) : ℝ) = 2 * (M : ℝ) := by push_cast; ring
  rw [this]
  nlinarith [h2, hM']

/-- **`L₁(m) < 2m` (eventually) ⇒ eventual strict descent.**  Contrapositive of
`confined_two_mul_of_nondescent`: a seed with no smaller iterate through step `2M` would be `1`-confined to
depth `2M`.  Combined with `reachesOne_of_linearFloor`-style induction this is the direct-Collatz target. -/
theorem descent_of_L1_lt_two_mul {M0 : ℕ}
    (h : ∀ M : ℕ, M0 ≤ M → 0 < M → Odd M → ¬ Confined 1 (orbWord M) (2 * M)) :
    ∀ M : ℕ, M0 ≤ M → 0 < M → Odd M → ∃ n, 1 ≤ n ∧ orbit M n < M := by
  intro M hM0 hM hodd
  by_contra hcon
  push Not at hcon
  refine h M hM0 hM hodd (confined_two_mul_of_nondescent hM hodd ?_)
  intro i _
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · exact hcon i hi



/-! ## Only record seeds matter -/

/-- `M` is **minimally `c`-confined to depth `N`** (an `L_c`-record witness): its own word is `c`-confined to
depth `N`, and no smaller odd seed is.  Equivalently `M = r_min(N,c)` in the notation of `EOC.rmin`. -/
def MinimalConfined (c : ℝ) (M N : ℕ) : Prop :=
  Odd M ∧ Confined c (orbWord M) N ∧ ∀ M' : ℕ, M' < M → Odd M' → ¬ Confined c (orbWord M') N

/-- **Record-only reduction.**  The linear realizer floor need only be checked on record seeds: if every
minimally confined `M` at depth `N ≥ N₀` satisfies `A·N − B ≤ M`, the floor holds for *all* odd seeds. -/
theorem linearFloor_of_minimal {c A B : ℝ} {N0 : ℕ}
    (h : ∀ M N : ℕ, N0 ≤ N → MinimalConfined c M N → A * (N : ℝ) - B ≤ (M : ℝ)) :
    LinearRealizerFloor c A B N0 := by
  intro M N hodd hN hconf
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    by_cases hmin : ∀ M' : ℕ, M' < M → Odd M' → ¬ Confined c (orbWord M') N
    · exact h M N hN ⟨hodd, hconf, hmin⟩
    · push Not at hmin
      obtain ⟨M', hlt, hodd', hconf'⟩ := hmin
      have hle : (M' : ℝ) ≤ (M : ℝ) := by exact_mod_cast hlt.le
      exact le_trans (ih M' hlt hodd' hconf') hle



/-! ## Track B: the `13/9` form (seed 27 is the observed extremizer) -/

/-- A seed that never drops below itself through step `⌊13M/9⌋` is `1`-confined to that depth, since
`13/9 = 1.444… < 3 ln 2 = 2.079…`.  (Seed 27 attains `L₁(27)/27 = 13/9` exactly.) -/
theorem confined_thirteen_ninths_of_nondescent {M : ℕ} (hM : 0 < M) (hodd : Odd M)
    (h : ∀ i ≤ 13 * M / 9, M ≤ orbit M i) : Confined 1 (orbWord M) (13 * M / 9) := by
  refine confined_of_nondescent hM hodd h ?_
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hdiv : ((13 * M / 9 : ℕ) : ℝ) ≤ (13 * M : ℕ) / (9 : ℕ) := Nat.cast_div_le
  have hcast : ((13 * M : ℕ) : ℝ) = 13 * (M : ℝ) := by push_cast; ring
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have : ((13 * M / 9 : ℕ) : ℝ) ≤ 13 * (M : ℝ) / 9 := by
    rw [hcast] at hdiv; simpa using hdiv
  nlinarith [this, h2, hM']

/-- **Track B target ⇒ descent.**  If `L₁(M) < ⌊13M/9⌋` for every large odd `M` — i.e. seed 27 is the ratio
extremizer — then every such `M` has a strictly smaller iterate, hence Collatz via the part-8 induction. -/
theorem descent_of_L1_lt_thirteen_ninths {M0 : ℕ}
    (h : ∀ M : ℕ, M0 ≤ M → 0 < M → Odd M → ¬ Confined 1 (orbWord M) (13 * M / 9)) :
    ∀ M : ℕ, M0 ≤ M → 0 < M → Odd M → ∃ n, 1 ≤ n ∧ orbit M n < M := by
  intro M hM0 hM hodd
  by_contra hcon
  push Not at hcon
  refine h M hM0 hM hodd (confined_thirteen_ninths_of_nondescent hM hodd ?_)
  intro i _
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · exact hcon i hi


end DirectDescent
end EOC
