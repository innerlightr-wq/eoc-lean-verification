import EOC.TaoLike.Cylinder

/-!
# Compatible realizer lift (Milestone 37B)

Exact relationship between the canonical least realizers of a length-`N` prefix and its
length-`(N+1)` extension by one more prescribed digit.

Main results:

* `leastRealizer_succ_mod_eq` — `leastRealizer d (N+1) % 2^(S d N+1) = leastRealizer d N`.
* `liftDigit` — the resulting compatible lift digit `k_N := leastRealizer d (N+1) / 2^(S d N+1)`.
* `leastRealizer_succ_eq` — the exact extension relation
  `leastRealizer d (N+1) = leastRealizer d N + liftDigit d N * 2^(S d N+1)`.
* `liftDigit_lt` — `liftDigit d N < 2 ^ d N`.
* `liftDigit_unique` — uniqueness of the lift digit in that range.
* `liftDigit_eq_zero_iff` — the zero-lift criterion: `liftDigit d N = 0` iff the length-`N`
  canonical realizer's own actual next valuation already equals the prescribed digit `d N`.
  **FORMALLY VERIFIED COMPATIBILITY**, not a pointwise breakthrough: it is definitionally the
  same statement as "does `leastRealizer d N` already realize the next digit", just restated.
* `leastRealizer_eq_of_agree` — words agreeing through `N` have the same length-`N` realizer.
* `leastRealizer_succ_ne_of_digit_ne` / `leastRealizer_succ_modEq_of_agree` — two words agreeing
  through `N` but differing at digit `N` have distinct length-`(N+1)` realizers, congruent mod
  `2^(S d N+1)`: a 2-adic separation **lower bound**, not in general an exact value (see the
  research report for why exactness fails in general).
* `q_modEq_of_leastRealizer_eq` / `swap_two_digits_leastRealizer_ne` — an
  **information-blindness** witness: two length-2 words with the *same* total valuation `S`
  (hence the same drift `R`) can have distinct carries `q` and hence distinct `leastRealizer`s.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC

/-! ## Prefix-agreement infrastructure -/

private theorem s_eq_of_agree_le (d d' : ℕ → ℕ) (N : ℕ) (hagree : ∀ i < N, d i = d' i) :
    ∀ j ≤ N, s d j = s d' j := by
  intro j hj
  unfold s
  exact Finset.sum_congr rfl (fun i hi => hagree i (by
    have := Finset.mem_range.mp hi; omega))

private theorem q_eq_of_agree (d d' : ℕ → ℕ) :
    ∀ N, (∀ i < N, d i = d' i) → q d N = q d' N := by
  intro N
  induction N with
  | zero => intro _; rfl
  | succ n ih =>
    intro hagree
    have hagree' : ∀ i < n, d i = d' i := fun i hi => hagree i (by omega)
    have hsn : s d n = s d' n := s_eq_of_agree_le d d' (n + 1) hagree n (by omega)
    rw [q_succ, q_succ, ih hagree', hsn]

/-- Two words agreeing on `[0,N)` have the same canonical length-`N` realizer: `leastRealizer`
depends only on the prefix, not on any tail data. No positivity hypothesis is needed. -/
theorem leastRealizer_eq_of_agree (d d' : ℕ → ℕ) (N : ℕ) (hagree : ∀ i < N, d i = d' i) :
    leastRealizer d N = leastRealizer d' N := by
  have hSeq : S d N = S d' N := s_eq_of_agree_le d d' N hagree N le_rfl
  have hqeq : q d N = q d' N := q_eq_of_agree d d' N hagree
  have hcong : 3 ^ N * leastRealizer d N + q d' N ≡ 2 ^ S d' N [MOD 2 ^ (S d' N + 1)] := by
    have h := leastRealizer_modEq d N
    rwa [hqeq, hSeq] at h
  exact leastRealizer_unique d' N (leastRealizer d N)
    (by rw [← hSeq]; exact leastRealizer_lt d N) hcong

/-! ## Phase 2: the exact extension relation -/

/-- The two canonical realizers of a common prefix (length `N` vs. `N+1`) are congruent
modulo `2^(S d N + 1)`: extending the word by one more (positive) digit only ever adjusts the
representative by a multiple of the modulus attached to the shorter prefix. -/
theorem leastRealizer_succ_modEq (d : ℕ → ℕ) (N : ℕ) (hd_pos : ∀ i < N + 1, 1 ≤ d i) :
    leastRealizer d (N + 1) ≡ leastRealizer d N [MOD 2 ^ (S d N + 1)] := by
  have hodd : Odd (leastRealizer d (N + 1)) :=
    leastRealizer_odd d (N + 1) (by omega) hd_pos
  have hreal : Realizes d (N + 1) (leastRealizer d (N + 1)) :=
    (realizerCongruence d (N + 1) (leastRealizer d (N + 1)) hodd hd_pos).mpr
      (leastRealizer_modEq d (N + 1))
  have hd_posN : ∀ i < N, 1 ≤ d i := fun i hi => hd_pos i (by omega)
  have hrealN : Realizes d N (leastRealizer d (N + 1)) :=
    ⟨hodd, fun j hj => hreal.2 j (by omega)⟩
  have hcongN := (realizerCongruence d N (leastRealizer d (N + 1)) hodd hd_posN).mp hrealN
  have hmodEq2 : 3 ^ N * leastRealizer d (N + 1) + q d N
      ≡ 3 ^ N * leastRealizer d N + q d N [MOD 2 ^ (S d N + 1)] :=
    hcongN.trans (leastRealizer_modEq d N).symm
  have hcancel1 : 3 ^ N * leastRealizer d (N + 1) ≡ 3 ^ N * leastRealizer d N
      [MOD 2 ^ (S d N + 1)] :=
    Nat.ModEq.add_right_cancel (Nat.ModEq.refl (q d N)) hmodEq2
  have hcop : Nat.Coprime (2 ^ (S d N + 1)) (3 ^ N) :=
    Nat.Coprime.pow (S d N + 1) N (by decide)
  exact Nat.ModEq.cancel_left_of_coprime hcop hcancel1

/-- Same fact, in `%`-form: since `leastRealizer d N` is already below the modulus, it is
literally the residue of `leastRealizer d (N+1)`. -/
theorem leastRealizer_succ_mod_eq (d : ℕ → ℕ) (N : ℕ) (hd_pos : ∀ i < N + 1, 1 ≤ d i) :
    leastRealizer d (N + 1) % 2 ^ (S d N + 1) = leastRealizer d N := by
  have hmod := leastRealizer_succ_modEq d N hd_pos
  have hlt := leastRealizer_lt d N
  have hself : leastRealizer d N % 2 ^ (S d N + 1) = leastRealizer d N := Nat.mod_eq_of_lt hlt
  rw [Nat.ModEq] at hmod
  rwa [hself] at hmod

/-- **The compatible lift digit** `k_N`. -/
def liftDigit (d : ℕ → ℕ) (N : ℕ) : ℕ := leastRealizer d (N + 1) / 2 ^ (S d N + 1)

/-- **The exact extension relation** (Phase 2 target):
`r_{N+1} = r_N + k_N · 2^{S_N+1}`. -/
theorem leastRealizer_succ_eq (d : ℕ → ℕ) (N : ℕ) (hd_pos : ∀ i < N + 1, 1 ≤ d i) :
    leastRealizer d (N + 1) = leastRealizer d N + liftDigit d N * 2 ^ (S d N + 1) := by
  unfold liftDigit
  have hdm := Nat.div_add_mod (leastRealizer d (N + 1)) (2 ^ (S d N + 1))
  rw [leastRealizer_succ_mod_eq d N hd_pos] at hdm
  have hcomm : 2 ^ (S d N + 1) * (leastRealizer d (N + 1) / 2 ^ (S d N + 1))
      = (leastRealizer d (N + 1) / 2 ^ (S d N + 1)) * 2 ^ (S d N + 1) := mul_comm _ _
  omega

/-- **The exact range** `0 ≤ k_N < 2^{d_N}` (unconditionally — no positivity hypothesis
needed for this direction). -/
theorem liftDigit_lt (d : ℕ → ℕ) (N : ℕ) :
    liftDigit d N < 2 ^ d N := by
  have hlt := leastRealizer_lt d (N + 1)
  have hSsucc : S d (N + 1) = S d N + d N := s_succ d N
  have hpow : (2 : ℕ) ^ (S d (N + 1) + 1) = 2 ^ d N * 2 ^ (S d N + 1) := by
    rw [hSsucc, ← pow_add]
    congr 1
    omega
  rw [hpow] at hlt
  have hpos : 0 < 2 ^ (S d N + 1) := by positivity
  unfold liftDigit
  exact (Nat.div_lt_iff_lt_mul hpos).mpr hlt

/-- **Uniqueness** of the lift digit in its exact range. -/
theorem liftDigit_unique (d : ℕ → ℕ) (N k : ℕ) (hd_pos : ∀ i < N + 1, 1 ≤ d i)
    (heq : leastRealizer d (N + 1) = leastRealizer d N + k * 2 ^ (S d N + 1)) :
    k = liftDigit d N := by
  have hext := leastRealizer_succ_eq d N hd_pos
  have hmuleq : k * 2 ^ (S d N + 1) = liftDigit d N * 2 ^ (S d N + 1) := by omega
  have hpos : 0 < 2 ^ (S d N + 1) := by positivity
  exact Nat.eq_of_mul_eq_mul_right hpos hmuleq

/-! ## Phase 3: the zero-lift criterion -/

/-- **Zero-lift criterion** (Phase 3 target). `liftDigit d N = 0` — equivalently
`leastRealizer d (N+1) = leastRealizer d N` — holds exactly when the canonical length-`N`
realizer's own *actual* dynamics already produces the prescribed next digit `d N`.
**FORMALLY VERIFIED COMPATIBILITY**: this is a restatement, not new information — see the
module's research report. -/
theorem liftDigit_eq_zero_iff (d : ℕ → ℕ) (N : ℕ) (hN : 1 ≤ N)
    (hd_pos : ∀ i < N + 1, 1 ≤ d i) :
    liftDigit d N = 0 ↔ a (orbit (leastRealizer d N) N) = d N := by
  have hd_posN : ∀ i < N, 1 ≤ d i := fun i hi => hd_pos i (by omega)
  have hrealN : Realizes d N (leastRealizer d N) :=
    leastRealizer_realizes d N hN hd_posN
  have hSsucc : S d (N + 1) = S d N + d N := s_succ d N
  have hboundle : (2 : ℕ) ^ (S d N + 1) ≤ 2 ^ (S d (N + 1) + 1) := by
    apply Nat.pow_le_pow_right (by norm_num)
    omega
  constructor
  · intro hk0
    have heq : leastRealizer d (N + 1) = leastRealizer d N := by
      have hext := leastRealizer_succ_eq d N hd_pos
      rw [hk0, zero_mul, add_zero] at hext
      exact hext
    have hreal' : Realizes d (N + 1) (leastRealizer d N) := by
      rw [← heq]
      exact leastRealizer_realizes d (N + 1) (by omega) hd_pos
    exact hreal'.2 N (by omega)
  · intro hval
    have hreal' : Realizes d (N + 1) (leastRealizer d N) :=
      ⟨hrealN.1, fun j hj => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hj'
        · exact hrealN.2 j hj'
        · rwa [hj']⟩
    have hcong' := (realizerCongruence d (N + 1) (leastRealizer d N) hrealN.1 hd_pos).mp hreal'
    have heq : leastRealizer d N = leastRealizer d (N + 1) :=
      leastRealizer_unique d (N + 1) (leastRealizer d N)
        (lt_of_lt_of_le (leastRealizer_lt d N) hboundle) hcong'
    have hext := leastRealizer_succ_eq d N hd_pos
    rw [← heq] at hext
    have hpos : 0 < 2 ^ (S d N + 1) := by positivity
    have : liftDigit d N * 2 ^ (S d N + 1) = 0 := by omega
    exact (Nat.mul_eq_zero.mp this).resolve_right (by omega)

/-! ## Phase 4: first-differing-digit geometry -/

/-- Two words sharing a prefix through `N` and differing at digit `N` have **distinct**
length-`(N+1)` realizers. -/
theorem leastRealizer_succ_ne_of_digit_ne (d d' : ℕ → ℕ) (N : ℕ)
    (hd_pos : ∀ i < N + 1, 1 ≤ d i) (hd'_pos : ∀ i < N + 1, 1 ≤ d' i)
    (hne : d N ≠ d' N) :
    leastRealizer d (N + 1) ≠ leastRealizer d' (N + 1) := by
  intro heq
  have hreal : Realizes d (N + 1) (leastRealizer d (N + 1)) :=
    (realizerCongruence d (N + 1) (leastRealizer d (N + 1))
      (leastRealizer_odd d (N + 1) (by omega) hd_pos) hd_pos).mpr (leastRealizer_modEq d (N + 1))
  have hreal' : Realizes d' (N + 1) (leastRealizer d' (N + 1)) :=
    (realizerCongruence d' (N + 1) (leastRealizer d' (N + 1))
      (leastRealizer_odd d' (N + 1) (by omega) hd'_pos) hd'_pos).mpr
      (leastRealizer_modEq d' (N + 1))
  have hvd : a (orbit (leastRealizer d (N + 1)) N) = d N := hreal.2 N (by omega)
  have hvd' : a (orbit (leastRealizer d' (N + 1)) N) = d' N := hreal'.2 N (by omega)
  rw [heq] at hvd
  exact hne (hvd.symm.trans hvd')

/-- Two words agreeing through `N` (regardless of digit `N` itself) have length-`(N+1)`
realizers congruent modulo `2^(S d N+1)`: a **2-adic separation lower bound**. Combined with
`leastRealizer_succ_ne_of_digit_ne`, a differing digit at `N` forces
`v₂(leastRealizer d (N+1) - leastRealizer d' (N+1)) ≥ S d N + 1` — but, in general, *not*
exact equality (see the research report). -/
theorem leastRealizer_succ_modEq_of_agree (d d' : ℕ → ℕ) (N : ℕ)
    (hagree : ∀ i < N, d i = d' i)
    (hd_pos : ∀ i < N + 1, 1 ≤ d i) (hd'_pos : ∀ i < N + 1, 1 ≤ d' i) :
    leastRealizer d (N + 1) ≡ leastRealizer d' (N + 1) [MOD 2 ^ (S d N + 1)] := by
  have hSeq : S d N = S d' N := s_eq_of_agree_le d d' N hagree N le_rfl
  have hLeq : leastRealizer d N = leastRealizer d' N := leastRealizer_eq_of_agree d d' N hagree
  have h1 := leastRealizer_succ_modEq d N hd_pos
  have h2 := leastRealizer_succ_modEq d' N hd'_pos
  rw [← hLeq, ← hSeq] at h2
  exact h1.trans h2.symm

/-! ## Phase 5: an information-blindness witness -/

/-- If two words with the *same* total valuation through `N` produce the *same* canonical
realizer, their carries must agree mod `2^(S d N+1)` too. Contrapositive form: a carry
mismatch (mod the same modulus) forces distinct realizers, **even though `S`/`R` are equal**
— this is the precise sense in which cumulative drift is a strictly coarser invariant than
the exact realizer. -/
theorem q_modEq_of_leastRealizer_eq (d d' : ℕ → ℕ) (N : ℕ) (hS : S d N = S d' N)
    (hLeq : leastRealizer d N = leastRealizer d' N) :
    q d N ≡ q d' N [MOD 2 ^ (S d N + 1)] := by
  have h1 := leastRealizer_modEq d N
  have h2 := leastRealizer_modEq d' N
  rw [← hLeq] at h2
  rw [hS] at h1
  -- h1 : 3^N * leastRealizer d N + q d N   ≡ 2 ^ S d' N [MOD 2 ^ (S d' N + 1)]
  -- h2 : 3^N * leastRealizer d N + q d' N  ≡ 2 ^ S d' N [MOD 2 ^ (S d' N + 1)]
  have hmodEq2 : 3 ^ N * leastRealizer d N + q d N
      ≡ 3 ^ N * leastRealizer d N + q d' N [MOD 2 ^ (S d' N + 1)] :=
    h1.trans h2.symm
  have hcancel : q d N ≡ q d' N [MOD 2 ^ (S d' N + 1)] :=
    Nat.ModEq.add_left_cancel (Nat.ModEq.refl (3 ^ N * leastRealizer d N)) hmodEq2
  rwa [hS]

/-- `2^u ≠ 2^v` (for `u ≠ v`) are never congruent mod `2^(u+v+1)`, since both already lie
strictly below that modulus. -/
private theorem two_pow_ne_modEq (u v : ℕ) (huv : u ≠ v) :
    ¬ (2 ^ u ≡ 2 ^ v [MOD 2 ^ (u + v + 1)]) := by
  intro hmod
  have hune : (2 : ℕ) ^ u ≠ 2 ^ v := fun h => huv (Nat.pow_right_injective (le_refl 2) h)
  have hult : (2 : ℕ) ^ u < 2 ^ (u + v + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hvlt : (2 : ℕ) ^ v < 2 ^ (u + v + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  rw [Nat.ModEq, Nat.mod_eq_of_lt hult, Nat.mod_eq_of_lt hvlt] at hmod
  exact hune hmod

/-- **Information-blindness witness** (Phase 5 target). For distinct positive digits `u ≠ v`,
the length-`2` words `(u,v,…)` and `(v,u,…)` have the **same** total valuation `S _ 2 = u+v`
(hence the same drift `R _ 2`), yet **distinct** canonical realizers `leastRealizer _ 2`. So
`S`/`R` alone do not determine the realizer — cumulative drift is a strictly coarser
projection than the exact 2-adic/carry data. -/
theorem swap_two_digits_leastRealizer_ne (u v : ℕ) (huv : u ≠ v) :
    S (fun i => if i = 0 then u else v) 2 = S (fun i => if i = 0 then v else u) 2 ∧
    leastRealizer (fun i => if i = 0 then u else v) 2
      ≠ leastRealizer (fun i => if i = 0 then v else u) 2 := by
  set d : ℕ → ℕ := fun i => if i = 0 then u else v with hd
  set d' : ℕ → ℕ := fun i => if i = 0 then v else u with hd'
  have hd0 : d 0 = u := if_pos rfl
  have hd1 : d 1 = v := if_neg (by norm_num)
  have hd'0 : d' 0 = v := if_pos rfl
  have hd'1 : d' 1 = u := if_neg (by norm_num)
  have hs1_d : s d 1 = u := by
    have h := s_succ d 0
    rw [s_zero, hd0] at h
    simpa using h
  have hs1_d' : s d' 1 = v := by
    have h := s_succ d' 0
    rw [s_zero, hd'0] at h
    simpa using h
  have hSd : S d 2 = u + v := by
    have h2 : s d 2 = s d 1 + d 1 := s_succ d 1
    show s d 2 = u + v
    rw [h2, hs1_d, hd1]
  have hSd' : S d' 2 = v + u := by
    have h2 : s d' 2 = s d' 1 + d' 1 := s_succ d' 1
    show s d' 2 = v + u
    rw [h2, hs1_d', hd'1]
  have hSeq : S d 2 = S d' 2 := by rw [hSd, hSd', add_comm]
  refine ⟨hSeq, ?_⟩
  intro hLeq
  have hq := q_modEq_of_leastRealizer_eq d d' 2 hSeq hLeq
  have hq1_d : q d 1 = 1 := by
    have h := q_succ d 0
    rw [q_zero, s_zero] at h
    simpa using h
  have hq1_d' : q d' 1 = 1 := by
    have h := q_succ d' 0
    rw [q_zero, s_zero] at h
    simpa using h
  have hqd : q d 2 = 3 + 2 ^ u := by
    have h2 : q d 2 = 3 * q d 1 + 2 ^ s d 1 := q_succ d 1
    rw [h2, hq1_d, hs1_d]
  have hqd' : q d' 2 = 3 + 2 ^ v := by
    have h2 : q d' 2 = 3 * q d' 1 + 2 ^ s d' 1 := q_succ d' 1
    rw [h2, hq1_d', hs1_d']
  rw [hqd, hqd', hSd] at hq
  have hq' : 2 ^ u ≡ 2 ^ v [MOD 2 ^ (u + v + 1)] :=
    Nat.ModEq.add_left_cancel (Nat.ModEq.refl 3) hq
  exact two_pow_ne_modEq u v huv hq'

end EOC
