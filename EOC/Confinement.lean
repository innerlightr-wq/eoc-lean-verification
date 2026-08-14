import EOC.Realizer
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace EOC

/-! ### Definition 5.5: confinement, `L_c(m)`, `r_min(N,c)` -/

/-- $\alpha = \log_2 3$. -/
noncomputable def alpha : ℝ := Real.logb 2 3

/-- The drift $R_j(D) = S_j - j\alpha$. -/
noncomputable def R (d : ℕ → ℕ) (j : ℕ) : ℝ := (s d j : ℝ) - (j : ℝ) * alpha

/-- `D` (length `N`) is `c`-confined: `R_j(D) ≤ c` for all `0 ≤ j ≤ N`. -/
def Confined (c : ℝ) (d : ℕ → ℕ) (N : ℕ) : Prop := ∀ j ≤ N, R d j ≤ c

/-- **Notation only — not certified.** `L_c(m)` from Definition 5.5, via
`sSup`. This matches the paper's intended finite max only when
`{N : Confined c (own word of m) N}` is bounded above. The paper asserts
this always holds ("finite since `R_j → +∞` on any orbit reaching 1 or a
cycle", citing Lemma 4.2), but neither Lemma 4.2 nor "every orbit reaches 1
or a cycle" is formalized in this project — the latter, unconditionally, is
exactly as hard as Collatz. `L` is *not* used anywhere below; included purely
so the notation exists, with any future use needing its own boundedness
hypothesis. -/
noncomputable def L (c : ℝ) (m : ℕ) : ℕ :=
  sSup {N : ℕ | Confined c (fun i => a (orbit m i)) N}

/-- `r_min(N,c)`, via `sInf` over the image of `leastRealizer` on the
`c`-confined, word-valid length-`N` words. Unlike `L`, `sInf` on `ℕ` needs no
boundedness or finiteness assumption — ℕ is well-ordered, and `sInf ∅ = 0`
by convention — so `rmin` is unconditionally well-defined. -/
noncomputable def rmin (c : ℝ) (N : ℕ) : ℕ :=
  sInf ((fun d => leastRealizer d N) ''
    {d : ℕ → ℕ | (∀ i < N, 1 ≤ d i) ∧ Confined c d N})

/-! ### Infrastructure: confinement depends only on the word up to `N` -/

private theorem s_eq_of_agree {d1 d2 : ℕ → ℕ} {N : ℕ} (hagree : ∀ i < N, d1 i = d2 i)
    {j : ℕ} (hj : j ≤ N) : s d1 j = s d2 j := by
  unfold s
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  exact hagree i (by omega)

private theorem R_eq_of_agree {d1 d2 : ℕ → ℕ} {N : ℕ} (hagree : ∀ i < N, d1 i = d2 i)
    {j : ℕ} (hj : j ≤ N) : R d1 j = R d2 j := by
  unfold R
  rw [s_eq_of_agree hagree hj]

/-- Confinement transfers along agreement of the underlying words on `[0,N)`. -/
theorem confined_congr {d1 d2 : ℕ → ℕ} {N : ℕ} {c : ℝ}
    (hagree : ∀ i < N, d1 i = d2 i) (h1 : Confined c d1 N) : Confined c d2 N := by
  intro j hj
  rw [← R_eq_of_agree hagree hj]
  exact h1 j hj

/-! ### Infrastructure: every odd orbit is a valid word -/

theorem a_pos_of_odd {m : ℕ} (hm : Odd m) : 1 ≤ a m := by
  unfold a
  have h2dvd : (2 : ℕ) ∣ (3 * m + 1) := by
    obtain ⟨w, hw⟩ := hm
    exact ⟨3 * w + 2, by rw [hw]; ring⟩
  have hne0 : padicValNat 2 (3 * m + 1) ≠ 0 := by
    intro hcon
    rcases padicValNat.eq_zero_iff.mp hcon with h1 | h1 | h1
    · norm_num at h1
    · omega
    · exact h1 h2dvd
  omega

theorem odd_T {m : ℕ} (hm : Odd m) : Odd (T m) := by
  obtain ⟨k, hk0⟩ := (pow_padicValNat_dvd : 2 ^ a m ∣ (3 * m + 1))
  have hk : 3 * m + 1 = 2 ^ a m * k := hk0
  have hTm : T m = k := by
    unfold T
    rw [hk, Nat.mul_div_cancel_left k (by positivity)]
  rw [hTm]
  have hkne : k ≠ 0 := by
    intro hk0'
    rw [hk0', mul_zero] at hk
    omega
  have haeq : a m = padicValNat 2 (3 * m + 1) := rfl
  have hval : padicValNat 2 (3 * m + 1) = a m + padicValNat 2 k := by
    conv_lhs => rw [hk]
    rw [padicValNat.mul (by positivity) hkne, padicValNat_base_pow (by norm_num) (a m)]
  have hz : padicValNat 2 k = 0 := by
    have h2 := hval
    rw [← haeq] at h2
    omega
  rw [Nat.odd_iff]
  rcases padicValNat.eq_zero_iff.mp hz with h1 | h1 | h1
  · exact absurd h1 (by norm_num)
  · exact absurd h1 hkne
  · omega

theorem odd_orbit {m : ℕ} (hm : Odd m) : ∀ i, Odd (orbit m i) := by
  intro i
  induction i with
  | zero => rwa [orbit_zero]
  | succ i ih =>
    rw [orbit_succ]
    exact odd_T ih

theorem hd_pos_of_orbit {m : ℕ} (hm : Odd m) : ∀ i, 1 ≤ a (orbit m i) :=
  fun i => a_pos_of_odd (odd_orbit hm i)

/-! ### `leastRealizer_le_of_modEq`, proved locally from public API only -/

private theorem leastRealizer_le_of_modEq (d : ℕ → ℕ) (N x : ℕ)
    (hxmod : 3 ^ N * x + q d N ≡ 2 ^ S d N [MOD 2 ^ (S d N + 1)]) :
    leastRealizer d N ≤ x := by
  have hmodEq2 : 3 ^ N * x + q d N ≡ 3 ^ N * leastRealizer d N + q d N [MOD 2 ^ (S d N + 1)] :=
    hxmod.trans (leastRealizer_modEq d N).symm
  have hcancel1 : 3 ^ N * x ≡ 3 ^ N * leastRealizer d N [MOD 2 ^ (S d N + 1)] :=
    Nat.ModEq.add_right_cancel (Nat.ModEq.refl (q d N)) hmodEq2
  have hcop : Nat.Coprime (2 ^ (S d N + 1)) (3 ^ N) :=
    Nat.Coprime.pow (S d N + 1) N (by decide)
  have hcancel2 : x ≡ leastRealizer d N [MOD 2 ^ (S d N + 1)] :=
    Nat.ModEq.cancel_left_of_coprime hcop hcancel1
  have hlt := leastRealizer_lt d N
  by_cases hcase : x < 2 ^ (S d N + 1)
  · have hxeq : x % 2 ^ (S d N + 1) = x := Nat.mod_eq_of_lt hcase
    have hlreq : leastRealizer d N % 2 ^ (S d N + 1) = leastRealizer d N := Nat.mod_eq_of_lt hlt
    have hmodraw : x % 2 ^ (S d N + 1) = leastRealizer d N % 2 ^ (S d N + 1) := hcancel2
    rw [hxeq, hlreq] at hmodraw
    omega
  · omega

/-! ### Proposition 5.7 (Record-chronology inversion)

**Audit classification**: Exact formalization of the paper's proof
argument; prefix-confinement reformulation of the literal `L_c(m) ≥ N`
statement, with equivalence to that notation conditional on the missing
boundedness/finiteness fact discussed at `L` above. `hne` and `hN` are
explicit, flagged hypotheses not literally written in the paper's statement
of Prop 5.7. -/
theorem record_chronology (c : ℝ) (N : ℕ) (hN : 1 ≤ N)
    (hne : ∃ d : ℕ → ℕ, (∀ i < N, 1 ≤ d i) ∧ Confined c d N) :
    rmin c N = sInf {m : ℕ | Odd m ∧ Confined c (fun i => a (orbit m i)) N} := by
  unfold rmin
  set LHSset : Set ℕ :=
    (fun d => leastRealizer d N) '' {d : ℕ → ℕ | (∀ i < N, 1 ≤ d i) ∧ Confined c d N}
    with hLHSdef
  set RHSset : Set ℕ := {m : ℕ | Odd m ∧ Confined c (fun i => a (orbit m i)) N} with hRHSdef
  have hLHSne : LHSset.Nonempty := by
    obtain ⟨d0, hd0⟩ := hne
    exact ⟨leastRealizer d0 N, d0, hd0, rfl⟩
  have hRHSne : RHSset.Nonempty := by
    obtain ⟨d0, hd0v, hd0c⟩ := hne
    refine ⟨leastRealizer d0 N, leastRealizer_odd d0 N hN hd0v, ?_⟩
    have hreal : Realizes d0 N (leastRealizer d0 N) :=
      (realizerCongruence d0 N (leastRealizer d0 N)
        (leastRealizer_odd d0 N hN hd0v) hd0v).mpr (leastRealizer_modEq d0 N)
    exact confined_congr (fun i hi => (hreal.2 i hi).symm) hd0c
  apply le_antisymm
  · obtain ⟨hoddInf, hconfInf⟩ := Nat.sInf_mem hRHSne
    set d0 : ℕ → ℕ := fun i => a (orbit (sInf RHSset) i) with hd0def
    have hd0v : ∀ i < N, 1 ≤ d0 i := fun i _ => hd_pos_of_orbit hoddInf i
    have hLHSmem : leastRealizer d0 N ∈ LHSset := ⟨d0, ⟨hd0v, hconfInf⟩, rfl⟩
    have hle1 : sInf LHSset ≤ leastRealizer d0 N := Nat.sInf_le hLHSmem
    have hreal0 : Realizes d0 N (sInf RHSset) := ⟨hoddInf, fun i _ => rfl⟩
    have hcong0 := (realizerCongruence d0 N (sInf RHSset) hoddInf hd0v).mp hreal0
    have hle2 : leastRealizer d0 N ≤ sInf RHSset :=
      leastRealizer_le_of_modEq d0 N (sInf RHSset) hcong0
    exact le_trans hle1 hle2
  · obtain ⟨d1, ⟨hd1v, hd1c⟩, hd1eq⟩ := Nat.sInf_mem hLHSne
    have hoddd1 : Odd (leastRealizer d1 N) := leastRealizer_odd d1 N hN hd1v
    have hreald1 : Realizes d1 N (leastRealizer d1 N) :=
      (realizerCongruence d1 N (leastRealizer d1 N) hoddd1 hd1v).mpr (leastRealizer_modEq d1 N)
    have hconfd1 : Confined c (fun i => a (orbit (leastRealizer d1 N) i)) N :=
      confined_congr (fun i hi => (hreald1.2 i hi).symm) hd1c
    have hRHSmem : leastRealizer d1 N ∈ RHSset := ⟨hoddd1, hconfd1⟩
    have hle3 : sInf RHSset ≤ leastRealizer d1 N := Nat.sInf_le hRHSmem
    have hd1eq' : leastRealizer d1 N = sInf LHSset := by
      simpa using hd1eq
    rw [hd1eq'] at hle3
    exact hle3
/-! ### Proposition 5.8 (Monotonicity) -/

/-- $\alpha = \log_2 3 > 1$. -/
theorem one_lt_alpha : 1 < alpha := by
  unfold alpha
  unfold Real.logb
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlt : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  have hself : Real.log 2 / Real.log 2 = 1 := div_self (ne_of_gt hlog2pos)
  have hdiff : Real.log 3 / Real.log 2 - Real.log 2 / Real.log 2
             = (Real.log 3 - Real.log 2) / Real.log 2 := by ring
  have hpos : 0 < (Real.log 3 - Real.log 2) / Real.log 2 :=
    div_pos (sub_pos.mpr hlt) hlog2pos
  rw [hself] at hdiff
  linarith [hdiff, hpos]

/-- The paper's "append $d_N=1$" construction (proof of Prop 5.8, p. 11). -/
private theorem exists_confined_succ {c : ℝ} {d : ℕ → ℕ} {N : ℕ}
    (hd_pos : ∀ i < N, 1 ≤ d i) (hconf : Confined c d N) :
    ∃ d' : ℕ → ℕ, (∀ i < N + 1, 1 ≤ d' i) ∧ Confined c d' (N + 1) := by
  refine ⟨fun k => if k = N then 1 else d k, ?_, ?_⟩
  · intro i hi
    by_cases h : i = N
    · rw [h]; simp
    · have hiN : i < N := by omega
      have heq : (fun k => if k = N then 1 else d k) i = d i := by simp [h]
      rw [heq]
      exact hd_pos i hiN
  · have hagree : ∀ i < N, (fun k => if k = N then 1 else d k) i = d i := by
      intro i hi
      have hne : i ≠ N := by omega
      simp [hne]
    intro j hj
    by_cases hcase : j ≤ N
    · rw [R_eq_of_agree hagree hcase]
      exact hconf j hcase
    · have hjeq : j = N + 1 := by omega
      have hsN : s (fun k => if k = N then 1 else d k) N = s d N :=
        s_eq_of_agree hagree (le_refl N)
      have hsstep : s (fun k => if k = N then 1 else d k) (N + 1) = s d N + 1 := by
        rw [s_succ, hsN]
        simp
      have hReq : R (fun k => if k = N then 1 else d k) (N + 1) = R d N + (1 - alpha) := by
        unfold R
        rw [hsstep]
        push_cast
        ring
      rw [hjeq, hReq]
      have hcN : R d N ≤ c := hconf N (le_refl N)
      linarith [one_lt_alpha]

/-- `leastRealizer` is monotone in its length argument, for a fixed word `d`. -/
theorem leastRealizer_mono (d : ℕ → ℕ) (N : ℕ)
    (hd_pos : ∀ i < N + 1, 1 ≤ d i) :
    leastRealizer d N ≤ leastRealizer d (N + 1) := by
  have hodd : Odd (leastRealizer d (N + 1)) :=
    leastRealizer_odd d (N + 1) (by omega) hd_pos
  have hreal : Realizes d (N + 1) (leastRealizer d (N + 1)) :=
    (realizerCongruence d (N + 1) (leastRealizer d (N + 1)) hodd hd_pos).mpr
      (leastRealizer_modEq d (N + 1))
  have hd_posN : ∀ i < N, 1 ≤ d i := fun i hi => hd_pos i (by omega)
  have hrealN : Realizes d N (leastRealizer d (N + 1)) :=
    ⟨hodd, fun j hj => hreal.2 j (by omega)⟩
  have hcongN := (realizerCongruence d N (leastRealizer d (N + 1)) hodd hd_posN).mp hrealN
  exact leastRealizer_le_of_modEq d N (leastRealizer d (N + 1)) hcongN

/-- **Proposition 5.8 (Monotonicity).** Exact restatement: `hne` alone, at
the base `N`, propagates to `N+1` via `exists_confined_succ`. -/
theorem rmin_mono (c : ℝ) (N : ℕ)
    (hne : ∃ d : ℕ → ℕ, (∀ i < N, 1 ≤ d i) ∧ Confined c d N) :
    rmin c N ≤ rmin c (N + 1) := by
  unfold rmin
  set LHSset : Set ℕ :=
    (fun d => leastRealizer d N) '' {d : ℕ → ℕ | (∀ i < N, 1 ≤ d i) ∧ Confined c d N}
    with hLHSdef
  set RHSset : Set ℕ :=
    (fun d => leastRealizer d (N + 1)) ''
      {d : ℕ → ℕ | (∀ i < N + 1, 1 ≤ d i) ∧ Confined c d (N + 1)}
    with hRHSdef
  have hRHSne : RHSset.Nonempty := by
    obtain ⟨d0, hd0v, hd0c⟩ := hne
    obtain ⟨d0', hd0'v, hd0'c⟩ := exists_confined_succ hd0v hd0c
    exact ⟨leastRealizer d0' (N + 1), d0', ⟨hd0'v, hd0'c⟩, rfl⟩
  obtain ⟨d1, ⟨hd1v, hd1c⟩, hd1eq⟩ := Nat.sInf_mem hRHSne
  have hd1eq' : leastRealizer d1 (N + 1) = sInf RHSset := by simpa using hd1eq
  have hd1vN : ∀ i < N, 1 ≤ d1 i := fun i hi => hd1v i (by omega)
  have hd1cN : Confined c d1 N := by
    intro j hj
    exact hd1c j (by omega)
  have hLHSmem : leastRealizer d1 N ∈ LHSset := ⟨d1, ⟨hd1vN, hd1cN⟩, rfl⟩
  have hle1 : sInf LHSset ≤ leastRealizer d1 N := Nat.sInf_le hLHSmem
  have hle2 : leastRealizer d1 N ≤ leastRealizer d1 (N + 1) := leastRealizer_mono d1 N hd1v
  calc sInf LHSset ≤ leastRealizer d1 N := hle1
    _ ≤ leastRealizer d1 (N + 1) := hle2
    _ = sInf RHSset := hd1eq'

/-! ### Proposition 5.9 (Single-window equivalence) — logarithmic core -/

private theorem a_one : a 1 = 2 := by
  unfold a
  have h4 : (3 * 1 + 1 : ℕ) = 2 ^ 2 := by norm_num
  rw [h4]
  exact padicValNat_base_pow (by norm_num) 2

private theorem T_one : T 1 = 1 := by
  unfold T
  rw [a_one]
  norm_num

private theorem orbit_one : ∀ j, orbit 1 j = 1 := by
  intro j
  induction j with
  | zero => rw [orbit_zero]
  | succ j ih => rw [orbit_succ, ih, T_one]

/-- Elementary route to "least realizer 1 ↔ constant word (2,2,...,2)",
avoiding Pillar 4 entirely. -/
theorem leastRealizer_eq_one_iff (d : ℕ → ℕ) (N : ℕ) (hN : 1 ≤ N)
    (hd_pos : ∀ i < N, 1 ≤ d i) :
    leastRealizer d N = 1 ↔ ∀ i < N, d i = 2 := by
  constructor
  · intro h1
    have hodd : Odd (leastRealizer d N) := leastRealizer_odd d N hN hd_pos
    have hreal : Realizes d N (leastRealizer d N) :=
      (realizerCongruence d N (leastRealizer d N) hodd hd_pos).mpr (leastRealizer_modEq d N)
    rw [h1] at hreal
    intro i hi
    have h := hreal.2 i hi
    rw [orbit_one, a_one] at h
    exact h.symm
  · intro hall
    have hd_pos' : ∀ i < N, 1 ≤ d i := fun i hi => by rw [hall i hi]; norm_num
    have hreal1 : Realizes d N 1 := by
      refine ⟨by norm_num, ?_⟩
      intro j hj
      rw [orbit_one, a_one]
      exact (hall j hj).symm
    have hcong1 := (realizerCongruence d N 1 (by norm_num) hd_pos').mp hreal1
    have h1lt : 1 < 2 ^ (S d N + 1) := by
      have hpow : (2:ℕ) ^ (S d N + 1) = 2 * 2 ^ (S d N) := by rw [pow_succ]; ring
      have hpos : 0 < 2 ^ (S d N) := by positivity
      omega
    exact (leastRealizer_unique d N 1 h1lt hcong1).symm

/-- Two realizers of the same word are congruent mod `2^(S+1)`; if unequal,
they differ by at least the modulus. Division-free: derived directly from
the mod-value forced by `hmodraw`, not from an explicit quotient. -/
private theorem realizer_gap (d : ℕ → ℕ) (N m0 : ℕ) (hm0ne : m0 ≠ 1)
    (hcong1 : 3 ^ N * 1 + q d N ≡ 2 ^ S d N [MOD 2 ^ (S d N + 1)])
    (hcong0 : 3 ^ N * m0 + q d N ≡ 2 ^ S d N [MOD 2 ^ (S d N + 1)]) :
    1 + 2 ^ (S d N + 1) ≤ m0 := by
  have hmodEq2 : 3 ^ N * 1 + q d N ≡ 3 ^ N * m0 + q d N [MOD 2 ^ (S d N + 1)] :=
    hcong1.trans hcong0.symm
  have hcancel1 : 3 ^ N * 1 ≡ 3 ^ N * m0 [MOD 2 ^ (S d N + 1)] :=
    Nat.ModEq.add_right_cancel (Nat.ModEq.refl (q d N)) hmodEq2
  have hcop : Nat.Coprime (2 ^ (S d N + 1)) (3 ^ N) :=
    Nat.Coprime.pow (S d N + 1) N (by decide)
  have hcancel2 : (1:ℕ) ≡ m0 [MOD 2 ^ (S d N + 1)] :=
    Nat.ModEq.cancel_left_of_coprime hcop hcancel1
  have h1lt : (1:ℕ) < 2 ^ (S d N + 1) := by
    have hpow : (2:ℕ) ^ (S d N + 1) = 2 * 2 ^ (S d N) := by rw [pow_succ]; ring
    have hpos : 0 < 2 ^ (S d N) := by positivity
    omega
  have hmod1 : (1:ℕ) % 2 ^ (S d N + 1) = 1 := Nat.mod_eq_of_lt h1lt
  have hmodraw : (1:ℕ) % 2 ^ (S d N + 1) = m0 % 2 ^ (S d N + 1) := hcancel2
  rw [hmod1] at hmodraw
  have hm0_not_lt : ¬ m0 < 2 ^ (S d N + 1) := by
    intro hlt
    have hm0mod : m0 % 2 ^ (S d N + 1) = m0 := Nat.mod_eq_of_lt hlt
    rw [hm0mod] at hmodraw
    exact hm0ne hmodraw.symm
  have hMle : 2 ^ (S d N + 1) ≤ m0 := by omega
  have hm0neM : m0 ≠ 2 ^ (S d N + 1) := by
    intro heq
    rw [heq, Nat.mod_self] at hmodraw
    omega
  omega

private theorem sum_range_const_two (M : ℕ) : ∑ i ∈ Finset.range M, (2:ℕ) = 2 * M := by
  induction M with
  | zero => simp
  | succ M ih => rw [Finset.sum_range_succ, ih]; ring

/-- Base-2 `logb` is monotone on positives, built from `Real.log_le_log`
directly rather than a packaged `logb`/`rpow` iff-lemma. -/
private theorem logb2_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    Real.logb 2 x ≤ Real.logb 2 y := by
  unfold Real.logb
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogle : Real.log x ≤ Real.log y := Real.log_le_log hx hxy
  have hdiff : Real.log y / Real.log 2 - Real.log x / Real.log 2
             = (Real.log y - Real.log x) / Real.log 2 := by ring
  have hnn : 0 ≤ (Real.log y - Real.log x) / Real.log 2 :=
    div_nonneg (by linarith) (le_of_lt hlog2pos)
  linarith [hdiff, hnn]

/-- `logb 2 (2^k) = k` for natural `k`, via `Real.log_pow` — a
`Monoid.npow`-level fact, not `Real.rpow`. -/
private theorem logb2_two_pow (k : ℕ) : Real.logb 2 ((2:ℝ)^k) = (k:ℝ) := by
  unfold Real.logb
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [Real.log_pow, mul_div_assoc, div_self (ne_of_gt hlog2pos), mul_one]

/-- **Proposition 5.9, logarithmic core.** `hc`, `hε_pos` retained per the
paper's stated hypotheses even though this proof may not need either — to be
recorded as an audit finding if confirmed unused. The `L_c(m)` side is
expressed via bounded confined prefixes; `L` is unused. -/
theorem single_window_equiv_log
    (c ε : ℝ) (hc : 0 < c) (hε_pos : 0 < ε) (hε_le : ε ≤ 2) :
    (∀ N : ℕ, 1 ≤ N →
       ∀ d : ℕ → ℕ,
         (∀ i < N, 1 ≤ d i) →
         Confined c d N →
         3 ≤ leastRealizer d N →
         ε * (N : ℝ) ≤ Real.logb 2 (leastRealizer d N))
    ↔
    (∀ m0 : ℕ, Odd m0 → 3 ≤ m0 →
       ∀ N : ℕ, 1 ≤ N →
         Confined c (fun i => a (orbit m0 i)) N →
         ε * (N : ℝ) ≤ Real.logb 2 m0) := by
  constructor
  · intro hLHS m0 hm0odd hm0ge3 N hN1 hconf
    set d0 : ℕ → ℕ := fun i => a (orbit m0 i) with hd0def
    have hd0_pos : ∀ i < N, 1 ≤ d0 i := fun i _ => hd_pos_of_orbit hm0odd i
    have hreal0 : Realizes d0 N m0 := ⟨hm0odd, fun i _ => rfl⟩
    have hcong0' := (realizerCongruence d0 N m0 hm0odd hd0_pos).mp hreal0
    have hle : leastRealizer d0 N ≤ m0 := leastRealizer_le_of_modEq d0 N m0 hcong0'
    by_cases hcase : 3 ≤ leastRealizer d0 N
    · have hbound := hLHS N hN1 d0 hd0_pos hconf hcase
      have hlr_pos : (0:ℝ) < (leastRealizer d0 N : ℝ) := by
        have h : 0 < leastRealizer d0 N := by omega
        exact_mod_cast h
      have hleR : (leastRealizer d0 N : ℝ) ≤ (m0:ℝ) := by exact_mod_cast hle
      have hmono : Real.logb 2 (leastRealizer d0 N : ℝ) ≤ Real.logb 2 (m0:ℝ) :=
        logb2_mono hlr_pos hleR
      linarith [hbound, hmono]
    · push_neg at hcase
      have hlr_odd : Odd (leastRealizer d0 N) := leastRealizer_odd d0 N hN1 hd0_pos
      rw [Nat.odd_iff] at hlr_odd
      have hlr1 : leastRealizer d0 N = 1 := by omega
      have hall2 : ∀ i < N, d0 i = 2 := (leastRealizer_eq_one_iff d0 N hN1 hd0_pos).mp hlr1
      have hcong1' : 3 ^ N * 1 + q d0 N ≡ 2 ^ S d0 N [MOD 2 ^ (S d0 N + 1)] := by
        have h := leastRealizer_modEq d0 N
        rw [hlr1] at h
        exact h
      have hgap := realizer_gap d0 N m0 (by omega) hcong1' hcong0'
      have hSeq : s d0 N = 2 * N := by
        unfold s
        rw [show (∑ i ∈ Finset.range N, d0 i) = ∑ i ∈ Finset.range N, (2:ℕ) from
          Finset.sum_congr rfl (fun i hi => hall2 i (Finset.mem_range.mp hi))]
        exact sum_range_const_two N
      unfold S at hgap
      rw [hSeq] at hgap
      have hgapR : (1:ℝ) + (2:ℝ) ^ (2 * N + 1) ≤ (m0:ℝ) := by
        have hcst : ((1 + 2 ^ (2 * N + 1) : ℕ) : ℝ) ≤ (m0:ℝ) := by exact_mod_cast hgap
        push_cast at hcst
        linarith
      have hpowle : (2:ℝ) ^ (2 * N + 1) ≤ (m0:ℝ) := by linarith
      have hlogle : Real.logb 2 ((2:ℝ) ^ (2 * N + 1)) ≤ Real.logb 2 (m0:ℝ) :=
        logb2_mono (by positivity) hpowle
      rw [logb2_two_pow] at hlogle
      have hcast2 : ((2 * N + 1 : ℕ):ℝ) = 2 * (N:ℝ) + 1 := by push_cast; ring
      rw [hcast2] at hlogle
      have hN_nonneg : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
      have hmul : ε * (N:ℝ) ≤ 2 * (N:ℝ) := mul_le_mul_of_nonneg_right hε_le hN_nonneg
      linarith
  · intro hRHS N hN1 d hd_pos hconf hge3
    set m0 := leastRealizer d N with hm0def
    have hodd : Odd m0 := leastRealizer_odd d N hN1 hd_pos
    have hreal : Realizes d N m0 :=
      (realizerCongruence d N m0 hodd hd_pos).mpr (leastRealizer_modEq d N)
    have hconf' : Confined c (fun i => a (orbit m0 i)) N :=
      confined_congr (fun i hi => (hreal.2 i hi).symm) hconf
    exact hRHS m0 hodd hge3 N hN1 hconf'
/-! ### Proposition 5.9 — exponential corollary of the logarithmic core

The one place `Real.rpow` enters this project. Built from `Real.exp_le_exp`,
`Real.exp_log`, `Real.log_exp` (high confidence, essentially definitional)
via `Real.rpow_def_of_pos` (the one name below not independently confirmed
against source this round — flagged as the residual risk). -/

private theorem rpow_two_mono {y z : ℝ} (hyz : y ≤ z) : (2:ℝ) ^ y ≤ (2:ℝ) ^ z := by
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2),
      Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
  apply Real.exp_le_exp.mpr
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith [hyz, hlog2pos]

private theorem rpow_two_logb2 {x : ℝ} (hx : 0 < x) :
    (2:ℝ) ^ Real.logb 2 x = x := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2ne : Real.log 2 ≠ 0 := ne_of_gt hlog2pos
  have hexp : Real.log 2 * (Real.log x / Real.log 2) = Real.log x := by
    field_simp
  unfold Real.logb
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2), hexp, Real.exp_log hx]
private theorem logb2_rpow_two (A : ℝ) : Real.logb 2 ((2:ℝ) ^ A) = A := by
  unfold Real.logb
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2), Real.log_exp]
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2ne : Real.log 2 ≠ 0 := ne_of_gt hlog2pos
  field_simp

private theorem exp_log_bridge {A : ℝ} {x : ℕ} (hx : 0 < x) :
    (2:ℝ) ^ A ≤ (x:ℝ) ↔ A ≤ Real.logb 2 (x:ℝ) := by
  constructor
  · intro h
    have hmono := logb2_mono (by positivity : (0:ℝ) < (2:ℝ) ^ A) h
    rwa [logb2_rpow_two] at hmono
  · intro h
    have hxR : (0:ℝ) < (x:ℝ) := by exact_mod_cast hx
    have hmono := rpow_two_mono h
    rwa [rpow_two_logb2 hxR] at hmono

/-- **Proposition 5.9, exponential form.** Statement (i) — `r(D) ≥ 2^{εN}`
for `r(D) ≥ 3` — is now an exact restatement of the paper (previously
sidestepped as the postponed corollary). Statement (ii) is still expressed
via bounded confined prefixes rather than literal `L_c(m)`, for the same
reason as `record_chronology`/`rmin_mono`: `L`'s sSup finiteness is
uncertified. So overall this is exact for (i), faithful reformulation for
(ii) — same status as everything since Proposition 5.7. -/
theorem single_window_equiv
    (c ε : ℝ) (hc : 0 < c) (hε_pos : 0 < ε) (hε_le : ε ≤ 2) :
    (∀ N : ℕ, 1 ≤ N →
       ∀ d : ℕ → ℕ,
         (∀ i < N, 1 ≤ d i) →
         Confined c d N →
         3 ≤ leastRealizer d N →
         (2:ℝ) ^ (ε * (N:ℝ)) ≤ (leastRealizer d N : ℝ))
    ↔
    (∀ m0 : ℕ, Odd m0 → 3 ≤ m0 →
       ∀ N : ℕ, 1 ≤ N →
         Confined c (fun i => a (orbit m0 i)) N →
         (2:ℝ) ^ (ε * (N:ℝ)) ≤ (m0 : ℝ)) := by
  have hcore := single_window_equiv_log c ε hc hε_pos hε_le
  constructor
  · intro hLHS m0 hm0odd hm0ge3 N hN1 hconf
    have hLHSlog : ∀ N' : ℕ, 1 ≤ N' →
       ∀ d : ℕ → ℕ,
         (∀ i < N', 1 ≤ d i) →
         Confined c d N' →
         3 ≤ leastRealizer d N' →
         ε * (N':ℝ) ≤ Real.logb 2 (leastRealizer d N') := by
      intro N' hN1' d hd_pos hconf' hge3'
      have hpos : 0 < leastRealizer d N' := by omega
      exact (exp_log_bridge hpos).mp (hLHS N' hN1' d hd_pos hconf' hge3')
    have hRHSlog := hcore.mp hLHSlog m0 hm0odd hm0ge3 N hN1 hconf
    have hpos : 0 < m0 := by omega
    exact (exp_log_bridge hpos).mpr hRHSlog
  · intro hRHS N hN1 d hd_pos hconf hge3
    have hRHSlog : ∀ m0' : ℕ, Odd m0' → 3 ≤ m0' →
       ∀ N' : ℕ, 1 ≤ N' →
         Confined c (fun i => a (orbit m0' i)) N' →
         ε * (N':ℝ) ≤ Real.logb 2 m0' := by
      intro m0' hm0'odd hm0'ge3 N' hN1' hconf'
      have hpos : 0 < m0' := by omega
      exact (exp_log_bridge hpos).mp (hRHS m0' hm0'odd hm0'ge3 N' hN1' hconf')
    have hLHSlog := hcore.mpr hRHSlog N hN1 d hd_pos hconf hge3
    have hpos : 0 < leastRealizer d N := by omega
    exact (exp_log_bridge hpos).mpr hLHSlog
end EOC
