import EOC.Carry

namespace EOC

/-! ### Proposition 5.2, part (a): descending integrality -/

/-- `2 ∣ 3y → 2 ∣ y`. The base case of "3 is invertible mod powers of 2",
proved directly via `omega`'s native support for divisibility by a literal
modulus, to avoid depending on `Nat.Coprime` API names that turned out not to
match this Mathlib pin. -/
private theorem two_dvd_of_two_dvd_three_mul {y : ℕ} (h : 2 ∣ 3 * y) : 2 ∣ y := by
  omega

/-- Plain positive-common-factor cancellation for `Nat` divisibility, proved
directly from `Nat.eq_of_mul_eq_mul_left`. -/
private theorem cancel_dvd_left {a b c : ℕ} (ha : 0 < a) (h : a * b ∣ a * c) :
    b ∣ c := by
  obtain ⟨e, he⟩ := h
  exact ⟨e, Nat.eq_of_mul_eq_mul_left ha (by rw [← mul_assoc]; exact he)⟩

/-- `2^k ∣ 3x → 2^k ∣ x`, by induction on `k`, using only
`two_dvd_of_two_dvd_three_mul` and `cancel_dvd_left`. Replaces the previous
`Nat.Coprime`-based argument, which depended on `Nat.Coprime.mul`. -/
private theorem cancel_three_dvd_pow_two : ∀ (k x : ℕ), 2 ^ k ∣ 3 * x → 2 ^ k ∣ x := by
  intro k
  induction k with
  | zero => intro x _; exact one_dvd x
  | succ k ih =>
    intro x h
    have hle : (2 : ℕ) ^ k ∣ 2 ^ (k + 1) := pow_dvd_pow 2 (Nat.le_succ k)
    obtain ⟨y, hy⟩ := ih x (dvd_trans hle h)
    have hx3 : 2 ^ (k + 1) ∣ 2 ^ k * (3 * y) := by
      have heq : 3 * x = 2 ^ k * (3 * y) := by rw [hy]; ring
      rwa [heq] at h
    have hy3 : 2 ^ k * 2 ∣ 2 ^ k * (3 * y) := by
      rw [← pow_succ]; exact hx3
    have h2 : (2 : ℕ) ∣ 3 * y := cancel_dvd_left (by positivity) hy3
    obtain ⟨w, hw⟩ := two_dvd_of_two_dvd_three_mul h2
    exact ⟨w, by rw [hy, hw, pow_succ]; ring⟩

/-- `k ∣ (a + k) → k ∣ a`, for `0 < k`. Replaces `Nat.dvd_sub'`, which is not
available under this name in this Mathlib pin. -/
private theorem dvd_of_dvd_add_self_right {k a : ℕ} (hk : 0 < k) (h : k ∣ (a + k)) :
    k ∣ a := by
  obtain ⟨c, hc⟩ := h
  have hc1 : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with hc0 | hc0
    · subst hc0; simp at hc; omega
    · exact hc0
  obtain ⟨c', rfl⟩ := Nat.exists_eq_add_of_le hc1
  refine ⟨c', ?_⟩
  have hexp : k * (1 + c') = k + k * c' := by ring
  omega

/-- One descending step: the aggregate congruence at depth `j+1` implies the
aggregate congruence at depth `j`. Only needs `s_j ≤ s_{j+1}`, true for any
`d j : ℕ`; `d_j ≥ 1` is not used here. -/
private theorem aggregate_dvd_step (d : ℕ → ℕ) (m0 j : ℕ)
    (h : 2 ^ s d (j + 1) ∣ (3 ^ (j + 1) * m0 + q d (j + 1))) :
    2 ^ s d j ∣ (3 ^ j * m0 + q d j) := by
  have hid : 3 ^ (j + 1) * m0 + q d (j + 1) = 3 * (3 ^ j * m0 + q d j) + 2 ^ s d j := by
    rw [q_succ, pow_succ]; ring
  rw [hid] at h
  have hpow : 2 ^ s d j ∣ 2 ^ s d (j + 1) := by
    apply pow_dvd_pow
    rw [s_succ]; omega
  have h' : 2 ^ s d j ∣ (3 * (3 ^ j * m0 + q d j) + 2 ^ s d j) := dvd_trans hpow h
  have h3A : 2 ^ s d j ∣ 3 * (3 ^ j * m0 + q d j) :=
    dvd_of_dvd_add_self_right (by positivity) h'
  exact cancel_three_dvd_pow_two (s d j) (3 ^ j * m0 + q d j) h3A

/-- **Descending integrality** (Prop 5.2 part (a), literal conclusion). -/
theorem aggregate_dvd_of_aggregate (d : ℕ → ℕ) (m0 N : ℕ)
    (hagg : 2 ^ S d N ∣ (3 ^ N * m0 + q d N)) :
    ∀ j, j ≤ N → 2 ^ s d j ∣ (3 ^ j * m0 + q d j) := by
  unfold S at hagg
  suffices H : ∀ i, i ≤ N → 2 ^ s d (N - i) ∣ (3 ^ (N - i) * m0 + q d (N - i)) by
    intro j hj
    have hH := H (N - j) (by omega)
    rwa [show N - (N - j) = j from by omega] at hH
  intro i
  induction i with
  | zero =>
    intro _
    simp only [Nat.sub_zero]
    exact hagg
  | succ i ih =>
    intro hi
    have hiN : i ≤ N := by omega
    have hstep := ih hiN
    have hNi : N - i = (N - (i + 1)) + 1 := by omega
    rw [hNi] at hstep
    exact aggregate_dvd_step d m0 (N - (i + 1)) hstep

/-- **Integrality transferred to `iter`.** -/
theorem iter_matches_closed_form (d : ℕ → ℕ) (m0 N : ℕ)
    (hagg : 2 ^ S d N ∣ (3 ^ N * m0 + q d N)) :
    ∀ j, j ≤ N → 2 ^ s d j * iter d m0 j = 3 ^ j * m0 + q d j := by
  have hclosed := aggregate_dvd_of_aggregate d m0 N hagg
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have hjN : j ≤ N := by omega
    have hIH : 2 ^ s d j * iter d m0 j = 3 ^ j * m0 + q d j := ih hjN
    have hclosed_succ : 2 ^ s d (j + 1) ∣ (3 ^ (j + 1) * m0 + q d (j + 1)) :=
      hclosed (j + 1) hj
    have hfactor : 3 ^ (j + 1) * m0 + q d (j + 1)
        = 3 * (3 ^ j * m0 + q d j) + 2 ^ s d j := by
      rw [q_succ, pow_succ]; ring
    have hid : 3 ^ (j + 1) * m0 + q d (j + 1) = 2 ^ s d j * (3 * iter d m0 j + 1) := by
      rw [hfactor, ← hIH]; ring
    rw [hid, s_succ, pow_add] at hclosed_succ
    have hpos : 0 < 2 ^ s d j := by positivity
    obtain ⟨k, hk⟩ := cancel_dvd_left hpos hclosed_succ
    have hiter_succ : iter d m0 (j + 1) = k := by
      rw [iter_succ, hk, Nat.mul_div_cancel_left k (by positivity)]
    rw [s_succ, pow_add, hiter_succ, hid, hk]
    ring

/-- **The deliverable: `hdvd`, derived rather than assumed.** -/
theorem hdvd_of_aggregate (d : ℕ → ℕ) (m0 N : ℕ)
    (hagg : 2 ^ S d N ∣ (3 ^ N * m0 + q d N)) :
    ∀ i, i < N → 2 ^ d i ∣ (3 * iter d m0 i + 1) := by
  intro i hi
  have hclosed := aggregate_dvd_of_aggregate d m0 N hagg
  have hIH : 2 ^ s d i * iter d m0 i = 3 ^ i * m0 + q d i :=
    iter_matches_closed_form d m0 N hagg i (le_of_lt hi)
  have hclosed_succ : 2 ^ s d (i + 1) ∣ (3 ^ (i + 1) * m0 + q d (i + 1)) :=
    hclosed (i + 1) hi
  have hfactor : 3 ^ (i + 1) * m0 + q d (i + 1)
      = 3 * (3 ^ i * m0 + q d i) + 2 ^ s d i := by
    rw [q_succ, pow_succ]; ring
  have hid : 3 ^ (i + 1) * m0 + q d (i + 1) = 2 ^ s d i * (3 * iter d m0 i + 1) := by
    rw [hfactor, ← hIH]; ring
  rw [hid, s_succ, pow_add] at hclosed_succ
  have hpos : 0 < 2 ^ s d i := by positivity
  exact cancel_dvd_left hpos hclosed_succ

/-! ### Proposition 5.2, part (b): interior oddness -/

/-- **Interior oddness** (Prop 5.2 part (b)). -/
theorem interior_odd (d : ℕ → ℕ) (m0 N : ℕ)
    (hagg : 2 ^ S d N ∣ (3 ^ N * m0 + q d N))
    (hd_pos : ∀ i < N, 1 ≤ d i) :
    ∀ j, j < N → Odd (iter d m0 j) := by
  have hdvd := hdvd_of_aggregate d m0 N hagg
  intro j hj
  obtain ⟨k, hk⟩ := hdvd j hj
  have hiter_succ : iter d m0 (j + 1) = k := by
    rw [iter_succ, hk, Nat.mul_div_cancel_left k (by positivity)]
  have heq : 2 ^ d j * iter d m0 (j + 1) = 3 * iter d m0 j + 1 := by
    rw [hiter_succ]; exact hk.symm
  have h2dvd : (2 : ℕ) ∣ 2 ^ d j := by
    have hp := pow_dvd_pow 2 (hd_pos j hj)
    simpa using hp
  have h2 : (2 : ℕ) ∣ (3 * iter d m0 j + 1) := by
    obtain ⟨c0, hc0⟩ := h2dvd
    refine ⟨c0 * iter d m0 (j + 1), ?_⟩
    rw [← heq, hc0]
    ring
  obtain ⟨c, hc⟩ := h2
  rw [Nat.odd_iff]
  omega

/-- Corollary: for `N ≥ 1`, the seed `m0` itself is forced odd. -/
theorem m0_odd_of_aggregate (d : ℕ → ℕ) (m0 N : ℕ) (hN : 1 ≤ N)
    (hagg : 2 ^ S d N ∣ (3 ^ N * m0 + q d N))
    (hd_pos : ∀ i < N, 1 ≤ d i) :
    Odd m0 := by
  have h := interior_odd d m0 N hagg hd_pos 0 (by omega)
  rwa [iter_zero] at h

/-! ### Proposition 5.2, part (c): exact valuations -/

/-- **Interior exact valuation** (Prop 5.2 part (c), first half). -/
theorem exact_val_interior (d : ℕ → ℕ) (m0 N : ℕ)
    (hagg : 2 ^ S d N ∣ (3 ^ N * m0 + q d N))
    (hd_pos : ∀ i < N, 1 ≤ d i) :
    ∀ j, j + 1 < N → a (iter d m0 j) = d j := by
  intro j hj
  have hjN : j < N := by omega
  obtain ⟨k, hk⟩ := hdvd_of_aggregate d m0 N hagg j hjN
  have hiter_succ : iter d m0 (j + 1) = k := by
    rw [iter_succ, hk, Nat.mul_div_cancel_left k (by positivity)]
  have hoddk : Odd k := by
    rw [← hiter_succ]; exact interior_odd d m0 N hagg hd_pos (j + 1) hj
  obtain ⟨w, hw⟩ := hoddk
  have hkne : k ≠ 0 := by omega
  have hndvd : ¬ (2 ∣ k) := by omega
  unfold a
  rw [hk, padicValNat.mul (by positivity) hkne, padicValNat_base_pow (by norm_num) (d j),
      padicValNat.eq_zero_of_not_dvd hndvd]
  omega

/-- **Terminal exactness ⟺ terminal parity** (Prop 5.2 part (c), second half,
`N ≥ 1`). -/
theorem exact_val_iff_terminal_odd (d : ℕ → ℕ) (m0 N : ℕ) (hN : 1 ≤ N)
    (hagg : 2 ^ S d N ∣ (3 ^ N * m0 + q d N))
    (hd_pos : ∀ i < N, 1 ≤ d i) :
    a (iter d m0 (N - 1)) = d (N - 1) ↔ Odd (iter d m0 N) := by
  have hNsub : N - 1 + 1 = N := by omega
  have hlt : N - 1 < N := by omega
  obtain ⟨k, hk⟩ := hdvd_of_aggregate d m0 N hagg (N - 1) hlt
  have hiter_succ : iter d m0 N = k := by
    rw [← hNsub, iter_succ, hk, Nat.mul_div_cancel_left k (by positivity)]
  have hkne : k ≠ 0 := by
    intro hk0
    rw [hk0, mul_zero] at hk
    omega
  have hval : a (iter d m0 (N - 1)) = d (N - 1) + padicValNat 2 k := by
    unfold a
    rw [hk, padicValNat.mul (by positivity) hkne,
        padicValNat_base_pow (by norm_num) (d (N - 1))]
  rw [hiter_succ, hval, Nat.odd_iff]
  constructor
  · intro heq
    have hz : padicValNat 2 k = 0 := by omega
    rcases padicValNat.eq_zero_iff.mp hz with h1 | h1 | h1
    · exact absurd h1 (by norm_num)
    · exact absurd h1 hkne
    · omega
  · intro hmod
    have hndvd : ¬ (2 ∣ k) := by omega
    rw [padicValNat.eq_zero_of_not_dvd hndvd]
    omega

/-! ### Proposition 5.2, part (d): terminal-parity congruence, full criterion -/

/-- "Adding a multiple of the modulus doesn't change the remainder". -/
private theorem mod_add_mul_self (r n : ℕ) : ∀ c, (r + n * c) % n = r % n := by
  intro c
  induction c with
  | zero => simp
  | succ c ih =>
    have hstep : r + n * (c + 1) = (r + n * c) + n := by ring
    rw [hstep, Nat.add_mod_right, ih]

/-- If `q = 2^S * k` with `k` odd, then `q ≡ 2^S [MOD 2^(S+1)]`. -/
private theorem modEq_two_pow_succ_of_odd_quotient (S : ℕ) {q k : ℕ}
    (hq : q = 2 ^ S * k) (hk : Odd k) :
    q ≡ 2 ^ S [MOD 2 ^ (S + 1)] := by
  obtain ⟨ℓ, hℓ⟩ := hk
  have hq' : q = 2 ^ S + 2 ^ (S + 1) * ℓ := by rw [hq, hℓ, pow_succ]; ring
  show q % 2 ^ (S + 1) = 2 ^ S % 2 ^ (S + 1)
  rw [hq']
  exact mod_add_mul_self (2 ^ S) (2 ^ (S + 1)) ℓ

/-- Converse of `modEq_two_pow_succ_of_odd_quotient`. -/
private theorem odd_quotient_of_modEq_two_pow_succ (S : ℕ) {q k : ℕ}
    (hq : q = 2 ^ S * k) (hmod : q ≡ 2 ^ S [MOD 2 ^ (S + 1)]) : Odd k := by
  rcases Nat.even_or_odd k with heven | hodd
  · exfalso
    obtain ⟨w, hw⟩ := heven
    have hw2 : k = 2 * w := by rw [hw]; ring
    have hq' : q = 2 ^ (S + 1) * w := by rw [hq, hw2, pow_succ]; ring
    have h1 : q % 2 ^ (S + 1) = 0 := by rw [hq']; exact Nat.mul_mod_right _ _
    have hlt : (2:ℕ) ^ S < 2 ^ (S + 1) := by
      have hpos : 0 < (2:ℕ) ^ S := by positivity
      rw [pow_succ]; omega
    have h2 : (2:ℕ) ^ S % 2 ^ (S + 1) = 2 ^ S := Nat.mod_eq_of_lt hlt
    have hmod' : q % 2 ^ (S + 1) = 2 ^ S % 2 ^ (S + 1) := hmod
    rw [h1, h2] at hmod'
    have hpos2 : 0 < (2:ℕ) ^ S := by positivity
    omega
  · exact hodd

/-- `2^S ∣ q ↔ q ≡ 2^S [MOD 2^(S+1)]` reverse direction. -/
private theorem dvd_of_modEq_two_pow_succ (S : ℕ) {q : ℕ}
    (hmod : q ≡ 2 ^ S [MOD 2 ^ (S + 1)]) : 2 ^ S ∣ q := by
  have hlt : (2:ℕ) ^ S < 2 ^ (S + 1) := by
    have hpos : 0 < (2:ℕ) ^ S := by positivity
    rw [pow_succ]; omega
  have h2 : (2:ℕ) ^ S % 2 ^ (S + 1) = 2 ^ S := Nat.mod_eq_of_lt hlt
  have hmod' : q % 2 ^ (S + 1) = 2 ^ S % 2 ^ (S + 1) := hmod
  have hq : q % 2 ^ (S + 1) = 2 ^ S := by rw [hmod', h2]
  obtain ⟨c, hc⟩ : ∃ c, q = 2 ^ (S + 1) * c + 2 ^ S :=
    ⟨q / 2 ^ (S + 1), by
      have hdecomp := Nat.div_add_mod q (2 ^ (S + 1))
      rw [hq] at hdecomp
      exact hdecomp.symm⟩
  exact ⟨2 * c + 1, by rw [hc, pow_succ]; ring⟩

/-- **Proposition 5.2 (Exact realizer congruence) — the full statement.** -/
theorem realizerCongruence (d : ℕ → ℕ) (N m0 : ℕ) (hm0 : Odd m0)
    (hd_pos : ∀ i < N, 1 ≤ d i) :
    Realizes d N m0 ↔ 3 ^ N * m0 + q d N ≡ 2 ^ S d N [MOD 2 ^ (S d N + 1)] := by
  rw [realizes_iff_iter_valuation]
  constructor
  · rintro ⟨-, hval⟩
    have hdvd' : ∀ i < N, 2 ^ d i ∣ (3 * iter d m0 i + 1) := by
      intro i hi
      have hai := hval i hi
      rw [← hai]
      unfold a
      exact pow_padicValNat_dvd
    have hclose := iter_carry_eq d m0 N hdvd'
    have heqN : 2 ^ S d N * iter d m0 N = 3 ^ N * m0 + q d N := hclose N le_rfl
    have hodd : Odd (iter d m0 N) := by
      by_cases hN0 : N = 0
      · subst hN0; rwa [iter_zero]
      · have hNpos : 1 ≤ N := by omega
        have hagg : 2 ^ S d N ∣ (3 ^ N * m0 + q d N) := ⟨iter d m0 N, heqN.symm⟩
        have hlast : a (iter d m0 (N - 1)) = d (N - 1) := hval (N - 1) (by omega)
        exact (exact_val_iff_terminal_odd d m0 N hNpos hagg hd_pos).mp hlast
    exact modEq_two_pow_succ_of_odd_quotient (S d N) heqN.symm hodd
  · intro hmod
    refine ⟨hm0, ?_⟩
    have hagg : 2 ^ S d N ∣ (3 ^ N * m0 + q d N) := dvd_of_modEq_two_pow_succ (S d N) hmod
    intro j hj
    by_cases hcase : j + 1 < N
    · exact exact_val_interior d m0 N hagg hd_pos j hcase
    · have hjeq : j = N - 1 := by omega
      have hNpos : 1 ≤ N := by omega
      have heqN : 2 ^ S d N * iter d m0 N = 3 ^ N * m0 + q d N :=
        iter_matches_closed_form d m0 N hagg N le_rfl
      have hodd : Odd (iter d m0 N) :=
        odd_quotient_of_modEq_two_pow_succ (S d N) heqN.symm hmod
      rw [hjeq]
      exact (exact_val_iff_terminal_odd d m0 N hNpos hagg hd_pos).mpr hodd

/-! ### Remark 5.4 and Lemma 5.6: infrastructure -/

/-- `3^N` is odd, for every `N`. -/
private theorem odd_three_pow (N : ℕ) : Odd (3 ^ N) := by
  induction N with
  | zero => exact ⟨0, by norm_num⟩
  | succ N ih =>
    obtain ⟨w, hw⟩ := ih
    exact ⟨3 * w + 1, by rw [pow_succ, hw]; ring⟩

/-- Existence, by Hensel-style induction on `S`. -/
private theorem exists_lt_dvd (N S Q : ℕ) :
    ∃ x < 2 ^ S, 2 ^ S ∣ (3 ^ N * x + Q) := by
  induction S with
  | zero => exact ⟨0, by norm_num, by simp⟩
  | succ S ih =>
    obtain ⟨x, hxlt, hdvd⟩ := ih
    obtain ⟨c, hc⟩ := hdvd
    have hpow : (2:ℕ) ^ (S + 1) = 2 ^ S + 2 ^ S := by rw [pow_succ]; ring
    rcases Nat.even_or_odd c with ⟨c', hc'⟩ | hcodd
    · have hc2 : c = 2 * c' := by rw [hc']; ring
      refine ⟨x, by omega, c', ?_⟩
      rw [hc, hc2, pow_succ]; ring
    · obtain ⟨w, hw⟩ := hcodd
      obtain ⟨w3, hw3⟩ := odd_three_pow N
      refine ⟨x + 2 ^ S, by omega, w + w3 + 1, ?_⟩
      have step1 : 3 ^ N * (x + 2 ^ S) + Q = (3 ^ N * x + Q) + 3 ^ N * 2 ^ S := by ring
      rw [step1, hc, hw, hw3, pow_succ]; ring

/-- `2^k ∣ 3^N * x → 2^k ∣ x`. -/
private theorem cancel_three_pow_dvd_pow_two : ∀ (N k x : ℕ), 2 ^ k ∣ 3 ^ N * x → 2 ^ k ∣ x := by
  intro N
  induction N with
  | zero => intro k x h; simpa using h
  | succ N ih =>
    intro k x h
    have h' : 2 ^ k ∣ 3 ^ N * (3 * x) := by
      have heq : 3 ^ (N + 1) * x = 3 ^ N * (3 * x) := by rw [pow_succ]; ring
      rwa [heq] at h
    exact cancel_three_dvd_pow_two k x (ih k (3 * x) h')

/-- Uniqueness, `y ≤ x` case. -/
private theorem eq_of_lt_dvd_le (N S Q x y : ℕ) (hx : x < 2 ^ S) (hxd : 2 ^ S ∣ (3 ^ N * x + Q))
    (hyd : 2 ^ S ∣ (3 ^ N * y + Q)) (hxy : y ≤ x) : x = y := by
  obtain ⟨a, ha⟩ := hxd
  obtain ⟨b, hb⟩ := hyd
  have hsplit : 3 ^ N * x + Q = 3 ^ N * (x - y) + b * 2 ^ S := by
    have hxy3 : 3 ^ N * (x - y) + 3 ^ N * y = 3 ^ N * x := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hxy]
    have hb' : 3 ^ N * y + Q = b * 2 ^ S := by rw [hb]; ring
    omega
  have hxmod : (3 ^ N * x + Q) % 2 ^ S = 0 := by rw [ha]; exact Nat.mul_mod_right _ _
  rw [hsplit, Nat.add_mul_mod_self_right] at hxmod
  have hAdvd : 2 ^ S ∣ 3 ^ N * (x - y) := Nat.dvd_of_mod_eq_zero hxmod
  have hxy0 : 2 ^ S ∣ (x - y) := cancel_three_pow_dvd_pow_two N S (x - y) hAdvd
  have hlt : x - y < 2 ^ S := by omega
  obtain ⟨k, hk⟩ := hxy0
  have hk0 : k = 0 := by
    by_contra hk0
    have h1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
    obtain ⟨k', hk'⟩ := Nat.exists_eq_add_of_le h1
    have heq : 2 ^ S * k = 2 ^ S + 2 ^ S * k' := by rw [hk']; ring
    omega
  rw [hk0, mul_zero] at hk
  omega

private theorem eq_of_lt_dvd (N S Q x y : ℕ) (hx : x < 2 ^ S) (hy : y < 2 ^ S)
    (hxd : 2 ^ S ∣ (3 ^ N * x + Q)) (hyd : 2 ^ S ∣ (3 ^ N * y + Q)) :
    x = y := by
  rcases le_total y x with hxy | hxy
  · exact eq_of_lt_dvd_le N S Q x y hx hxd hyd hxy
  · exact (eq_of_lt_dvd_le N S Q y x hy hyd hxd hxy).symm

/-- Generalization of `dvd_of_dvd_add_self_right` to an arbitrary multiple. -/
private theorem dvd_of_dvd_add_mul_right {k a c : ℕ} (hk : 0 < k) (h : k ∣ (a + k * c)) :
    k ∣ a := by
  obtain ⟨m, hm⟩ := h
  have hcm : k * c ≤ k * m := by omega
  have hc_le_m : c ≤ m := Nat.le_of_mul_le_mul_left hcm hk
  obtain ⟨m', hm'⟩ := Nat.exists_eq_add_of_le hc_le_m
  refine ⟨m', ?_⟩
  have hkm : k * m = k * c + k * m' := by rw [hm']; ring
  omega

/-- `2^(S+1) ∣ (A + 2^S) → A ≡ 2^S [MOD 2^(S+1)]`. -/
private theorem modEq_of_dvd_add_pow (S A : ℕ) (h : 2 ^ (S + 1) ∣ (A + 2 ^ S)) :
    A ≡ 2 ^ S [MOD 2 ^ (S + 1)] := by
  obtain ⟨k, hk⟩ := h
  have hkpos : 1 ≤ k := by
    by_cases hk0 : k = 0
    · exfalso; rw [hk0, mul_zero] at hk
      have hSpos : 0 < (2:ℕ) ^ S := by positivity
      omega
    · omega
  obtain ⟨k', hk'⟩ := Nat.exists_eq_add_of_le hkpos
  have hstep : A + 2 ^ S = 2 ^ (S + 1) * k' + 2 ^ S + 2 ^ S := by
    rw [hk, hk', pow_succ]; ring
  have hAeq : A = 2 ^ (S + 1) * k' + 2 ^ S := by omega
  show A % 2 ^ (S + 1) = 2 ^ S % 2 ^ (S + 1)
  rw [hAeq, Nat.mul_add_mod_self_left]

/-- Converse of `modEq_of_dvd_add_pow`. -/
private theorem dvd_add_pow_of_modEq (S A : ℕ) (h : A ≡ 2 ^ S [MOD 2 ^ (S + 1)]) :
    2 ^ (S + 1) ∣ (A + 2 ^ S) := by
  have hmod : A % 2 ^ (S + 1) = 2 ^ S % 2 ^ (S + 1) := h
  have hlt : (2:ℕ) ^ S < 2 ^ (S + 1) := by
    have hpos : 0 < (2:ℕ) ^ S := by positivity
    rw [pow_succ]; omega
  rw [Nat.mod_eq_of_lt hlt] at hmod
  have hdecomp := Nat.div_add_mod A (2 ^ (S + 1))
  rw [hmod] at hdecomp
  refine ⟨A / 2 ^ (S + 1) + 1, ?_⟩
  have hpow : (2:ℕ) ^ (S + 1) = 2 ^ S + 2 ^ S := by rw [pow_succ]; ring
  have hmul : 2 ^ (S + 1) * (A / 2 ^ (S + 1) + 1)
            = 2 ^ (S + 1) * (A / 2 ^ (S + 1)) + 2 ^ (S + 1) := by ring
  omega

/-! ### `coarseAnchor` (Remark 5.4) -/

def coarseAnchor (d : ℕ → ℕ) (N S : ℕ) : ℕ :=
  Nat.find (exists_lt_dvd N S (q d N))

theorem coarseAnchor_lt (d : ℕ → ℕ) (N S : ℕ) : coarseAnchor d N S < 2 ^ S :=
  (Nat.find_spec (exists_lt_dvd N S (q d N))).1

theorem coarseAnchor_dvd (d : ℕ → ℕ) (N S : ℕ) :
    2 ^ S ∣ (3 ^ N * coarseAnchor d N S + q d N) :=
  (Nat.find_spec (exists_lt_dvd N S (q d N))).2

theorem coarseAnchor_unique (d : ℕ → ℕ) (N S x : ℕ) (hxlt : x < 2 ^ S)
    (hxd : 2 ^ S ∣ (3 ^ N * x + q d N)) : x = coarseAnchor d N S :=
  eq_of_lt_dvd N S (q d N) x (coarseAnchor d N S) hxlt (coarseAnchor_lt d N S) hxd
    (coarseAnchor_dvd d N S)

/-! ### `leastRealizer` (r(D)) -/

def leastRealizer (d : ℕ → ℕ) (N : ℕ) : ℕ :=
  Nat.find (exists_lt_dvd N (S d N + 1) (q d N + 2 ^ S d N))

theorem leastRealizer_lt (d : ℕ → ℕ) (N : ℕ) : leastRealizer d N < 2 ^ (S d N + 1) :=
  (Nat.find_spec (exists_lt_dvd N (S d N + 1) (q d N + 2 ^ S d N))).1

theorem leastRealizer_dvd (d : ℕ → ℕ) (N : ℕ) :
    2 ^ (S d N + 1) ∣ (3 ^ N * leastRealizer d N + (q d N + 2 ^ S d N)) :=
  (Nat.find_spec (exists_lt_dvd N (S d N + 1) (q d N + 2 ^ S d N))).2

theorem leastRealizer_modEq (d : ℕ → ℕ) (N : ℕ) :
    3 ^ N * leastRealizer d N + q d N ≡ 2 ^ S d N [MOD 2 ^ (S d N + 1)] := by
  have h := leastRealizer_dvd d N
  have h' : 2 ^ (S d N + 1) ∣ ((3 ^ N * leastRealizer d N + q d N) + 2 ^ S d N) := by
    have heq : 3 ^ N * leastRealizer d N + (q d N + 2 ^ S d N)
             = (3 ^ N * leastRealizer d N + q d N) + 2 ^ S d N := by ring
    rwa [heq] at h
  exact modEq_of_dvd_add_pow (S d N) (3 ^ N * leastRealizer d N + q d N) h'

theorem leastRealizer_unique (d : ℕ → ℕ) (N x : ℕ) (hxlt : x < 2 ^ (S d N + 1))
    (hxmod : 3 ^ N * x + q d N ≡ 2 ^ S d N [MOD 2 ^ (S d N + 1)]) :
    x = leastRealizer d N := by
  have hxdvd := dvd_add_pow_of_modEq (S d N) (3 ^ N * x + q d N) hxmod
  have hxdvd' : 2 ^ (S d N + 1) ∣ (3 ^ N * x + (q d N + 2 ^ S d N)) := by
    have heq : (3 ^ N * x + q d N) + 2 ^ S d N = 3 ^ N * x + (q d N + 2 ^ S d N) := by ring
    rwa [heq] at hxdvd
  exact eq_of_lt_dvd N (S d N + 1) (q d N + 2 ^ S d N) x (leastRealizer d N) hxlt
    (leastRealizer_lt d N) hxdvd' (leastRealizer_dvd d N)

theorem leastRealizer_odd (d : ℕ → ℕ) (N : ℕ) (hN : 1 ≤ N) (hd_pos : ∀ i < N, 1 ≤ d i) :
    Odd (leastRealizer d N) := by
  have hdvd1 := leastRealizer_dvd d N
  have hpow_dvd : 2 ^ S d N ∣ 2 ^ (S d N + 1) := pow_dvd_pow 2 (by omega)
  have hdvd2 : 2 ^ S d N ∣ (3 ^ N * leastRealizer d N + (q d N + 2 ^ S d N)) :=
    dvd_trans hpow_dvd hdvd1
  have heq2 : 3 ^ N * leastRealizer d N + (q d N + 2 ^ S d N)
            = (3 ^ N * leastRealizer d N + q d N) + 2 ^ S d N := by ring
  rw [heq2] at hdvd2
  have hdvd3 : 2 ^ S d N ∣ (3 ^ N * leastRealizer d N + q d N) :=
    dvd_of_dvd_add_self_right (by positivity) hdvd2
  exact m0_odd_of_aggregate d (leastRealizer d N) N hN hdvd3 hd_pos

/-! ### Remark 5.4 -/

theorem leastRealizer_eq_or_eq_add (d : ℕ → ℕ) (N : ℕ) :
    leastRealizer d N = coarseAnchor d N (S d N) ∨
    leastRealizer d N = coarseAnchor d N (S d N) + 2 ^ S d N := by
  have hdvd1 := leastRealizer_dvd d N
  have hpow_dvd : 2 ^ S d N ∣ 2 ^ (S d N + 1) := pow_dvd_pow 2 (by omega)
  have hdvd2 : 2 ^ S d N ∣ (3 ^ N * leastRealizer d N + (q d N + 2 ^ S d N)) :=
    dvd_trans hpow_dvd hdvd1
  have heq2 : 3 ^ N * leastRealizer d N + (q d N + 2 ^ S d N)
            = (3 ^ N * leastRealizer d N + q d N) + 2 ^ S d N := by ring
  rw [heq2] at hdvd2
  have hagg_r : 2 ^ S d N ∣ (3 ^ N * leastRealizer d N + q d N) :=
    dvd_of_dvd_add_self_right (by positivity) hdvd2
  by_cases hcase : leastRealizer d N < 2 ^ S d N
  · left
    exact coarseAnchor_unique d N (S d N) (leastRealizer d N) hcase hagg_r
  · right
    have hcase' : 2 ^ S d N ≤ leastRealizer d N := by omega
    obtain ⟨r', hr'⟩ := Nat.exists_eq_add_of_le hcase'
    have hrlt : leastRealizer d N < 2 ^ (S d N + 1) := leastRealizer_lt d N
    have hpowlt : (2:ℕ) ^ (S d N + 1) = 2 ^ S d N + 2 ^ S d N := by rw [pow_succ]; ring
    have hr'lt : r' < 2 ^ S d N := by omega
    have hexpand : 3 ^ N * leastRealizer d N + q d N
        = (3 ^ N * r' + q d N) + 2 ^ S d N * 3 ^ N := by rw [hr']; ring
    rw [hexpand] at hagg_r
    have hagg_r' : 2 ^ S d N ∣ (3 ^ N * r' + q d N) :=
      dvd_of_dvd_add_mul_right (by positivity) hagg_r
    have heqr' : r' = coarseAnchor d N (S d N) := coarseAnchor_unique d N (S d N) r' hr'lt hagg_r'
    rw [hr', heqr']; ring

theorem coarseAnchor_le_realizer (d : ℕ → ℕ) (N : ℕ) :
    coarseAnchor d N (S d N) ≤ leastRealizer d N := by
  rcases leastRealizer_eq_or_eq_add d N with h | h
  · exact le_of_eq h.symm
  · have hle : coarseAnchor d N (S d N) ≤ coarseAnchor d N (S d N) + 2 ^ S d N :=
      Nat.le_add_right _ _
    rw [← h] at hle
    exact hle

/-! ### Lemma 5.6 (residue pinning) -/

theorem residue_pinning (m0 N : ℕ) (hm0 : Odd m0)
    (hd_pos : ∀ i < N, 1 ≤ a (orbit m0 i))
    (hbound : m0 < 2 ^ (S (fun i => a (orbit m0 i)) N + 1)) :
    leastRealizer (fun i => a (orbit m0 i)) N = m0 := by
  have hreal : Realizes (fun i => a (orbit m0 i)) N m0 := ⟨hm0, fun i _ => rfl⟩
  have hcong := (realizerCongruence (fun i => a (orbit m0 i)) N m0 hm0 hd_pos).mp hreal
  exact (leastRealizer_unique (fun i => a (orbit m0 i)) N m0 hbound hcong).symm

end EOC
