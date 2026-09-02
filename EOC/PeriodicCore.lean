/-!
# PeriodicCore — Mathlib-free, kernel-checked core of the periodic-sector theorem

Only Lean core is used (no Mathlib, no axioms beyond the standard ones, no `sorry`).
`sr`/`qr` satisfy the same recursions as `EOC.s`/`EOC.q` (`s_zero`,`s_succ`,`q_zero`,`q_succ`),
so the bridge file transports them with one induction each.
-/

namespace EOC.PeriodicCore

def sr (d : Nat → Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => sr d j + d j

@[simp] theorem sr_zero (d : Nat → Nat) : sr d 0 = 0 := rfl
theorem sr_succ (d : Nat → Nat) (j : Nat) : sr d (j + 1) = sr d j + d j := rfl

def qr (d : Nat → Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => 3 * qr d j + 2 ^ sr d j

@[simp] theorem qr_zero (d : Nat → Nat) : qr d 0 = 0 := rfl
theorem qr_succ (d : Nat → Nat) (j : Nat) : qr d (j + 1) = 3 * qr d j + 2 ^ sr d j := rfl

/-- The carry of a nonempty block is positive: this is the `+C > 0` sign input. -/
theorem qr_pos (d : Nat → Nat) (L : Nat) (hL : 1 ≤ L) : 0 < qr d L := by
  cases L with
  | zero => omega
  | succ n =>
    rw [qr_succ]
    have : 0 < 2 ^ sr d n := Nat.pow_pos (by decide)
    omega

theorem sr_add_window (d : Nat → Nat) (j : Nat) :
    ∀ L, sr d (j + L) = sr d j + sr (fun i => d (j + i)) L := by
  intro L
  induction L with
  | zero => simp
  | succ n ih =>
    rw [show j + (n + 1) = (j + n) + 1 from by omega, sr_succ, ih, sr_succ]
    show sr d j + sr (fun i => d (j + i)) n + d (j + n)
        = sr d j + (sr (fun i => d (j + i)) n + d (j + n))
    exact Nat.add_assoc _ _ _

theorem sr_congr (d d' : Nat → Nat) (L : Nat) (h : ∀ i, i < L → d i = d' i) :
    sr d L = sr d' L := by
  induction L with
  | zero => rfl
  | succ n ih =>
    rw [sr_succ, sr_succ, ih (fun i hi => h i (by omega)), h n (by omega)]

/-- Lower bound for a positive word: `sr d L ≥ L` when every digit is `≥ 1`. -/
theorem sr_ge_of_pos (d : Nat → Nat) (L : Nat) (hd : ∀ i, i < L → 1 ≤ d i) : L ≤ sr d L := by
  induction L with
  | zero => simp
  | succ n ih =>
    rw [sr_succ]
    have := hd n (by omega)
    have := ih (fun i hi => hd i (by omega))
    omega

/-! ### Eventually periodic words -/

def EvPeriodic (d : Nat → Nat) (j0 L : Nat) : Prop := ∀ i, j0 ≤ i → d (i + L) = d i

theorem evPeriodic_shift (d : Nat → Nat) (j0 L : Nat) (h : EvPeriodic d j0 L) :
    ∀ k i, d (j0 + k * L + i) = d (j0 + i) := by
  intro k
  induction k with
  | zero => intro i; simp
  | succ n ih =>
    intro i
    have : j0 + (n + 1) * L + i = (j0 + n * L + i) + L := by
      rw [Nat.succ_mul]; omega
    rw [this, h _ (by omega), ih]

def blockSum (d : Nat → Nat) (j0 L : Nat) : Nat := sr (fun i => d (j0 + i)) L
def blockCarry (d : Nat → Nat) (j0 L : Nat) : Nat := qr (fun i => d (j0 + i)) L

theorem sr_periodic (d : Nat → Nat) (j0 L : Nat) (h : EvPeriodic d j0 L) :
    ∀ k, sr d (j0 + k * L) = sr d j0 + k * blockSum d j0 L := by
  intro k
  induction k with
  | zero => simp
  | succ n ih =>
    have hsplit : j0 + (n + 1) * L = (j0 + n * L) + L := by rw [Nat.succ_mul]; omega
    rw [hsplit, sr_add_window, ih]
    have hwin : sr (fun i => d (j0 + n * L + i)) L = blockSum d j0 L := by
      unfold blockSum
      apply sr_congr
      intro i _
      exact evPeriodic_shift d j0 L h n i
    rw [hwin, Nat.succ_mul]
    exact Nat.add_assoc _ _ _

/-- The block starting at `j0 + k*L` has the same prefix sums and carry as the block at `j0`. -/
theorem block_shift_invariant (d : Nat → Nat) (j0 L : Nat) (h : EvPeriodic d j0 L) (k : Nat) :
    ∀ M, M ≤ L →
      qr (fun i => d (j0 + k * L + i)) M = qr (fun i => d (j0 + i)) M ∧
      sr (fun i => d (j0 + k * L + i)) M = sr (fun i => d (j0 + i)) M := by
  intro M
  induction M with
  | zero => intro _; exact ⟨rfl, rfl⟩
  | succ n ih =>
    intro hM
    obtain ⟨hq, hs⟩ := ih (by omega)
    refine ⟨?_, ?_⟩
    · rw [qr_succ, qr_succ, hq, hs]
    · rw [sr_succ, sr_succ, hs]
      show sr (fun i => d (j0 + i)) n + d (j0 + k * L + n)
          = sr (fun i => d (j0 + i)) n + d (j0 + n)
      rw [evPeriodic_shift d j0 L h k n]

/-! ### Theorem 1 (sign-sensitive): positive-carry block returns force `3^L < 2^S` -/

private theorem shift_step (A B C yr yr1 : Nat) (hAB : B ≤ A)
    (hrec : B * yr1 = A * yr + C) :
    B * (yr1 * (A - B) + C) = A * (yr * (A - B) + C) := by
  obtain ⟨D, hD⟩ : ∃ D, A = B + D := ⟨A - B, by omega⟩
  have hsub : A - B = D := by omega
  rw [hsub]
  subst hD
  calc B * (yr1 * D + C)
      = (B * yr1) * D + B * C := by rw [Nat.mul_add, Nat.mul_assoc]
    _ = ((B + D) * yr + C) * D + B * C := by rw [hrec]
    _ = (B + D) * yr * D + C * D + B * C := by rw [Nat.add_mul]
    _ = (B + D) * (yr * D) + (B + D) * C := by
        rw [Nat.mul_assoc (B + D) yr D, Nat.add_mul B D C, Nat.mul_comm C D]
        ac_rfl
    _ = (B + D) * (yr * D + C) := by rw [Nat.mul_add]

/-- **Sign-sensitive cycle/expansion theorem.** If `2^S * y(r+1) = 3^L * y r + C` for all
`r`, with `C > 0`, `S ≥ 1`, then `3^L < 2^S`. Uses no positivity of `y` and no exact return
`y (r+·) = y r`. Under the mirror `3m-1` the carry enters as `-C` and the statement is false
(`y ≡ 1`, `L = 1`, `S = 1`: `2·1 = 3·1 - 1`). -/
theorem three_pow_lt_two_pow_of_block_return
    (L S C : Nat) (y : Nat → Nat) (hS : 1 ≤ S) (hC : 0 < C)
    (hrec : ∀ r, 2 ^ S * y (r + 1) = 3 ^ L * y r + C) :
    3 ^ L < 2 ^ S := by
  apply Classical.byContradiction
  intro hnot
  have hAB : 2 ^ S ≤ 3 ^ L := Nat.le_of_not_lt hnot
  let n : Nat → Nat := fun r => y r * (3 ^ L - 2 ^ S) + C
  have hn_step : ∀ r, 2 ^ S * n (r + 1) = 3 ^ L * n r := fun r =>
    shift_step (3 ^ L) (2 ^ S) C (y r) (y (r + 1)) hAB (hrec r)
  have hn_pow : ∀ r, (2 ^ S) ^ r * n r = (3 ^ L) ^ r * n 0 := by
    intro r
    induction r with
    | zero => simp
    | succ k ih =>
      calc (2 ^ S) ^ (k + 1) * n (k + 1)
          = (2 ^ S) ^ k * (2 ^ S * n (k + 1)) := by rw [Nat.pow_succ, Nat.mul_assoc]
        _ = (2 ^ S) ^ k * (3 ^ L * n k) := by rw [hn_step]
        _ = 3 ^ L * ((2 ^ S) ^ k * n k) := by rw [Nat.mul_left_comm]
        _ = 3 ^ L * ((3 ^ L) ^ k * n 0) := by rw [ih]
        _ = (3 ^ L) ^ (k + 1) * n 0 := by
            rw [Nat.pow_succ, Nat.mul_comm ((3 ^ L) ^ k) (3 ^ L), Nat.mul_assoc]
  have hcop : ∀ r, Nat.Coprime ((2 ^ S) ^ r) ((3 ^ L) ^ r) := fun r =>
    Nat.Coprime.pow r r (Nat.Coprime.pow S L (by decide : Nat.Coprime 2 3))
  have hdvd : ∀ r, (2 ^ S) ^ r ∣ n 0 := fun r =>
    Nat.Coprime.dvd_of_dvd_mul_left (hcop r) ⟨n r, (hn_pow r).symm⟩
  have hn0_pos : 0 < n 0 := Nat.lt_of_lt_of_le hC (Nat.le_add_left C _)
  have hle : (2 ^ S) ^ (n 0) ≤ n 0 := Nat.le_of_dvd hn0_pos (hdvd (n 0))
  have h2S : 2 ≤ 2 ^ S := by
    calc 2 = 2 ^ 1 := by simp
      _ ≤ 2 ^ S := Nat.pow_le_pow_right (by decide) hS
  have hge : 2 ^ (n 0) ≤ (2 ^ S) ^ (n 0) := Nat.pow_le_pow_left h2S (n 0)
  have hlt : n 0 < 2 ^ (n 0) := Nat.lt_two_pow_self
  omega

/-! ### Theorem 2 (deterministic drift exit), exact integer form of `R_j ≤ c` -/

theorem bernoulli_nat (A : Nat) : ∀ k, A ^ (k + 1) + (k + 1) * A ^ k ≤ (A + 1) ^ (k + 1) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.pow_succ (A + 1) (k + 1)]
    have h1 : (A ^ (k + 1) + (k + 1) * A ^ k) * (A + 1) ≤ (A + 1) ^ (k + 1) * (A + 1) :=
      Nat.mul_le_mul_right _ ih
    have e : (A ^ (k + 1) + (k + 1) * A ^ k) * (A + 1)
        = (A ^ (k + 1 + 1) + (k + 1 + 1) * A ^ (k + 1)) + (k + 1) * A ^ k := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_one,
          Nat.pow_succ A (k + 1), Nat.succ_mul (k + 1) (A ^ (k + 1)),
          Nat.mul_assoc (k + 1) (A ^ k) A, ← Nat.pow_succ A k]
      ac_rfl
    have h2 : A ^ (k + 1 + 1) + (k + 1 + 1) * A ^ (k + 1)
        ≤ (A ^ (k + 1) + (k + 1) * A ^ k) * (A + 1) := by
      rw [e]; exact Nat.le_add_right _ _
    exact Nat.le_trans h2 h1

theorem pow_dominates (A B M : Nat) (hA : 1 ≤ A) (hAB : A < B) (hM : 1 ≤ M) :
    M * A ^ (M * A) < B ^ (M * A) := by
  have hk : 1 ≤ M * A := Nat.mul_le_mul hM hA
  obtain ⟨k, hk'⟩ : ∃ k, M * A = k + 1 := ⟨M * A - 1, by omega⟩
  rw [hk']
  have hbern := bernoulli_nat A k
  have hmono : (A + 1) ^ (k + 1) ≤ B ^ (k + 1) := Nat.pow_le_pow_left hAB (k + 1)
  have hkey : (k + 1) * A ^ k = M * A ^ (k + 1) := by
    rw [Nat.pow_succ, ← hk']
    ac_rfl
  have hApos : 0 < A ^ (k + 1) := Nat.pow_pos hA
  omega

theorem exists_exit_of_block_growth (d : Nat → Nat) (j0 L : Nat) (h : EvPeriodic d j0 L)
    (hgrow : 3 ^ L < 2 ^ blockSum d j0 L) (c : Nat) :
    ∃ k, 3 ^ (j0 + k * L) * 2 ^ c < 2 ^ sr d (j0 + k * L) := by
  have hA : 1 ≤ 3 ^ L := Nat.pow_pos (by decide)
  have hM : 1 ≤ 3 ^ j0 * 2 ^ c := Nat.mul_le_mul (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide))
  have hdom := pow_dominates (3 ^ L) (2 ^ blockSum d j0 L) (3 ^ j0 * 2 ^ c) hA hgrow hM
  obtain ⟨k, hk⟩ : ∃ k, k = (3 ^ j0 * 2 ^ c) * 3 ^ L := ⟨_, rfl⟩
  rw [← hk] at hdom
  refine ⟨k, ?_⟩
  have hs := sr_periodic d j0 L h k
  rw [hs, Nat.pow_add, Nat.pow_add, Nat.mul_comm k L, Nat.pow_mul 3 L k,
      Nat.mul_comm k (blockSum d j0 L), Nat.pow_mul 2 (blockSum d j0 L) k]
  have h1 : 1 ≤ 2 ^ sr d j0 := Nat.pow_pos (by decide)
  calc 3 ^ j0 * (3 ^ L) ^ k * 2 ^ c
      = (3 ^ j0 * 2 ^ c) * (3 ^ L) ^ k := by ac_rfl
    _ < (2 ^ blockSum d j0 L) ^ k := hdom
    _ = 1 * (2 ^ blockSum d j0 L) ^ k := by simp
    _ ≤ 2 ^ sr d j0 * (2 ^ blockSum d j0 L) ^ k := Nat.mul_le_mul_right _ h1

/-! ### Theorem 3: monotone bounded ℕ-sequences are eventually constant -/

theorem mono_of_step (r : Nat → Nat) (hmono : ∀ N, r N ≤ r (N + 1)) :
    ∀ i j, i ≤ j → r i ≤ r j := by
  intro i j hij
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst this; exact Nat.le_refl _
  | succ n ih =>
    rcases Nat.lt_or_ge i (n + 1) with hlt | hge
    · exact Nat.le_trans (ih (by omega)) (hmono n)
    · have : i = n + 1 := by omega
      subst this; exact Nat.le_refl _

theorem eventually_const_of_mono_bounded (r : Nat → Nat) (hmono : ∀ N, r N ≤ r (N + 1))
    (M : Nat) (hbd : ∀ N, r N ≤ M) :
    ∃ N0, ∀ N, N0 ≤ N → r N = r N0 := by
  suffices H : ∀ B, ∀ (r : Nat → Nat), (∀ N, r N ≤ r (N + 1)) → (∀ N, r N ≤ M) →
      M - r 0 ≤ B → ∃ N0, ∀ N, N0 ≤ N → r N = r N0 from
    H (M - r 0) r hmono hbd (Nat.le_refl _)
  intro B
  induction B with
  | zero =>
    intro r hmono hbd hB
    refine ⟨0, fun N _ => ?_⟩
    have h1 := hbd N
    have h2 := mono_of_step r hmono 0 N (Nat.zero_le _)
    omega
  | succ B ih =>
    intro r hmono hbd hB
    by_cases hconst : ∀ N, r N = r 0
    · exact ⟨0, fun N _ => hconst N⟩
    · have hex : ∃ N1, r 0 < r N1 := by
        apply Classical.byContradiction
        intro hno
        apply hconst
        intro N
        have h1 := mono_of_step r hmono 0 N (Nat.zero_le _)
        have h2 : ¬ r 0 < r N := fun hh => hno ⟨N, hh⟩
        omega
      obtain ⟨N1, hN1⟩ := hex
      have hmono' : ∀ N, r (N1 + N) ≤ r (N1 + (N + 1)) := fun N => by
        rw [show N1 + (N + 1) = (N1 + N) + 1 from by omega]
        exact hmono _
      have hbd' : ∀ N, r (N1 + N) ≤ M := fun N => hbd _
      have hB' : M - r (N1 + 0) ≤ B := by
        simp only [Nat.add_zero]
        omega
      obtain ⟨N0', hN0'⟩ := ih (fun N => r (N1 + N)) hmono' hbd' hB'
      refine ⟨N1 + N0', fun N hN => ?_⟩
      have := hN0' (N - N1) (by omega)
      have hNe : N = N1 + (N - N1) := by omega
      rw [hNe]
      exact this

end EOC.PeriodicCore
