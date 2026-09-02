import EOC.PeriodicCore
import EOC.BoundedDriftCore
/-!
# SignedBlock — sign-sensitive block arithmetic for the affine recurrences (Mathlib-free)

PLUS block:  `2^S * mN = 3^L * mj + C`   (carry enters with `+`)
MINUS block: `2^S * mN + C = 3^L * mj`   (carry enters with `-`, written without Nat subtraction)

* `plus_block_pow_lt_of_endpoint_le`  : endpoint descent `mN ≤ mj`  ⇒ `3^L < 2^S`
* `plus_endpoint_lt_of_pow_le`        : `2^S ≤ 3^L` ⇒ `mj < mN`      (negative-drift block ⇒ ascent)
* `minus_block_pow_lt_of_endpoint_ge` : endpoint ascent `mj ≤ mN`  ⇒ `2^S < 3^L`
* `minus_endpoint_lt_of_pow_le`       : `3^L ≤ 2^S` ⇒ `mN < mj`
* `minus_two_pow_lt_three_pow_of_block_return` : infinite positive `−C` chain ⇒ `2^S < 3^L`
* `minus_block_return_rigid`          : ... and (for `S ≥ 1`) `(3^L − 2^S) * y 0 = C`, `y r = y 0` ∀ r
* `plus_fixed_block_saturation`, `minus_fixed_block_saturation` : saturation equations
* `plus_normalized_step`, `minus_normalized_step` : integer form of the monotonicity of `m_N 2^{R_N}`

Compare `PeriodicCore.three_pow_lt_two_pow_of_block_return` (PLUS chain ⇒ `3^L < 2^S`).
These are statements about the recurrences only; they prove nothing about EOC, DTC, or Collatz.
-/

namespace EOC.SignedBlock
open EOC.PeriodicCore EOC.BoundedDriftCore

/-! ### Single-block endpoint theorems -/

/-- PLUS: a block that does not increase the state is contracting. Only `C > 0` is needed:
no positivity of the states, no `L ≥ 1`, no `S ≥ 1` (the strict product inequality already
forces `mN > 0`). -/
theorem plus_block_pow_lt_of_endpoint_le (L S C mj mN : Nat) (hC : 0 < C)
    (h : 2 ^ S * mN = 3 ^ L * mj + C) (hle : mN ≤ mj) : 3 ^ L < 2 ^ S := by
  have h1 : 3 ^ L * mN < 2 ^ S * mN := by
    calc 3 ^ L * mN ≤ 3 ^ L * mj := Nat.mul_le_mul_left _ hle
      _ < 3 ^ L * mj + C := by omega
      _ = 2 ^ S * mN := h.symm
  exact Nat.lt_of_mul_lt_mul_right h1

/-- PLUS, contrapositive: a non-contracting (in particular a negative-drift) block strictly
increases the state. -/
theorem plus_endpoint_lt_of_pow_le (L S C mj mN : Nat) (hC : 0 < C)
    (h : 2 ^ S * mN = 3 ^ L * mj + C) (hpow : 2 ^ S ≤ 3 ^ L) : mj < mN := by
  apply Classical.byContradiction
  intro hnot
  have := plus_block_pow_lt_of_endpoint_le L S C mj mN hC h (Nat.le_of_not_lt hnot)
  omega

/-- MINUS: a block that does not decrease the state is expanding. -/
theorem minus_block_pow_lt_of_endpoint_ge (L S C mj mN : Nat) (hC : 0 < C)
    (h : 2 ^ S * mN + C = 3 ^ L * mj) (hge : mj ≤ mN) : 2 ^ S < 3 ^ L := by
  have h1 : 2 ^ S * mN < 3 ^ L * mN := by
    calc 2 ^ S * mN < 2 ^ S * mN + C := by omega
      _ = 3 ^ L * mj := h
      _ ≤ 3 ^ L * mN := Nat.mul_le_mul_left _ hge
  exact Nat.lt_of_mul_lt_mul_right h1

/-- MINUS, contrapositive: a non-expanding block strictly decreases the state. -/
theorem minus_endpoint_lt_of_pow_le (L S C mj mN : Nat) (hC : 0 < C)
    (h : 2 ^ S * mN + C = 3 ^ L * mj) (hpow : 3 ^ L ≤ 2 ^ S) : mN < mj := by
  apply Classical.byContradiction
  intro hnot
  have := minus_block_pow_lt_of_endpoint_ge L S C mj mN hC h (Nat.le_of_not_lt hnot)
  omega

/-! ### Saturation (fixed-block) equations -/

theorem plus_fixed_block_saturation (L S C y : Nat) (h : 2 ^ S * y = 3 ^ L * y + C) :
    (2 ^ S - 3 ^ L) * y = C := by
  rw [Nat.sub_mul]; omega

theorem minus_fixed_block_saturation (L S C y : Nat) (h : 2 ^ S * y + C = 3 ^ L * y) :
    (3 ^ L - 2 ^ S) * y = C := by
  rw [Nat.sub_mul]; omega

/-! ### Integer form of normalized-state monotonicity
`Z_N = m_N 2^{S_N} / 3^N` satisfies `Z_{N+1} − Z_N = ± 2^{S_N} / 3^{N+1}`; cleared of denominators: -/

theorem plus_normalized_step (N S d m m' : Nat) (h : 2 ^ d * m' = 3 * m + 1) :
    3 ^ N * (2 ^ (S + d) * m') = 3 ^ (N + 1) * (2 ^ S * m) + 3 ^ N * 2 ^ S := by
  rw [Nat.pow_add, Nat.pow_succ]
  calc 3 ^ N * (2 ^ S * 2 ^ d * m') = 3 ^ N * 2 ^ S * (2 ^ d * m') := by ac_rfl
    _ = 3 ^ N * 2 ^ S * (3 * m + 1) := by rw [h]
    _ = 3 ^ N * 3 * (2 ^ S * m) + 3 ^ N * 2 ^ S := by
        rw [Nat.mul_add, Nat.mul_one]; ac_rfl

theorem minus_normalized_step (N S d m m' : Nat) (h : 2 ^ d * m' + 1 = 3 * m) :
    3 ^ N * (2 ^ (S + d) * m') + 3 ^ N * 2 ^ S = 3 ^ (N + 1) * (2 ^ S * m) := by
  rw [Nat.pow_add, Nat.pow_succ]
  calc 3 ^ N * (2 ^ S * 2 ^ d * m') + 3 ^ N * 2 ^ S
      = 3 ^ N * 2 ^ S * (2 ^ d * m' + 1) := by rw [Nat.mul_add, Nat.mul_one]; ac_rfl
    _ = 3 ^ N * 2 ^ S * (3 * m) := by rw [h]
    _ = 3 ^ N * 3 * (2 ^ S * m) := by ac_rfl

/-! ### MINUS repeated-block chain -/

/-- An infinite positive `−C` chain forces `2^S < 3^L` (otherwise the chain strictly decreases). -/
theorem minus_two_pow_lt_three_pow_of_block_return (L S C : Nat) (y : Nat → Nat)
    (hC : 0 < C) (hy : ∀ r, 0 < y r)
    (hrec : ∀ r, 2 ^ S * y (r + 1) + C = 3 ^ L * y r) : 2 ^ S < 3 ^ L := by
  apply Classical.byContradiction
  intro hnot
  have hpow : 3 ^ L ≤ 2 ^ S := Nat.le_of_not_lt hnot
  have hdec : ∀ r, y (r + 1) < y r := fun r =>
    minus_endpoint_lt_of_pow_le L S C (y r) (y (r + 1)) hC (hrec r) hpow
  have hsum : ∀ r, y r + r ≤ y 0 := by
    intro r; induction r with
    | zero => simp
    | succ r ih => have := hdec r; omega
  have := hsum (y 0)
  have := hy (y 0)
  omega

/-- Key identity for the shifted quantity, in `ℕ` without subtraction:
with `3^L = 2^S + D`, `2^S·(D y_{r+1}) + 3^L·C = 3^L·(D y_r) + 2^S·C`. -/
private theorem minus_shift_identity (L S C D : Nat) (y : Nat → Nat) (hD : 3 ^ L = 2 ^ S + D)
    (hrec : ∀ r, 2 ^ S * y (r + 1) + C = 3 ^ L * y r) (r : Nat) :
    2 ^ S * (D * y (r + 1)) + 3 ^ L * C = 3 ^ L * (D * y r) + 2 ^ S * C := by
  have h := hrec r
  calc 2 ^ S * (D * y (r + 1)) + 3 ^ L * C
      = D * (2 ^ S * y (r + 1)) + (2 ^ S + D) * C := by rw [← hD]; ac_rfl
    _ = D * (2 ^ S * y (r + 1)) + D * C + 2 ^ S * C := by rw [Nat.add_mul]; ac_rfl
    _ = D * (2 ^ S * y (r + 1) + C) + 2 ^ S * C := by rw [Nat.mul_add]
    _ = D * (3 ^ L * y r) + 2 ^ S * C := by rw [h]
    _ = 3 ^ L * (D * y r) + 2 ^ S * C := by ac_rfl

/-- One step of the descent in the case `D y_r ≤ C`. -/
private theorem step_le (L S C : Nat) (X X' : Nat) (h2S : 0 < 2 ^ S)
    (key : 2 ^ S * X' + 3 ^ L * C = 3 ^ L * X + 2 ^ S * C) (hX : X ≤ C) :
    X' ≤ C ∧ 2 ^ S * (C - X') = 3 ^ L * (C - X) := by
  have h3 : 3 ^ L * X ≤ 3 ^ L * C := Nat.mul_le_mul_left _ hX
  have hmul : 2 ^ S * X' ≤ 2 ^ S * C := by omega
  have hX' : X' ≤ C := Nat.le_of_mul_le_mul_left hmul h2S
  refine ⟨hX', ?_⟩
  rw [Nat.mul_sub, Nat.mul_sub]
  omega

/-- One step of the descent in the case `C ≤ D y_r`. -/
private theorem step_ge (L S C : Nat) (X X' : Nat) (h2S : 0 < 2 ^ S)
    (key : 2 ^ S * X' + 3 ^ L * C = 3 ^ L * X + 2 ^ S * C) (hX : C ≤ X) :
    C ≤ X' ∧ 2 ^ S * (X' - C) = 3 ^ L * (X - C) := by
  have h3 : 3 ^ L * C ≤ 3 ^ L * X := Nat.mul_le_mul_left _ hX
  have hmul : 2 ^ S * C ≤ 2 ^ S * X' := by omega
  have hX' : C ≤ X' := Nat.le_of_mul_le_mul_left hmul h2S
  refine ⟨hX', ?_⟩
  rw [Nat.mul_sub, Nat.mul_sub]
  omega

/-- **MINUS rigidity.** An infinite positive `−C` chain with `S ≥ 1` satisfies `2^S < 3^L`,
the saturation equation `(3^L − 2^S)·y 0 = C`, and is constant: `y r = y 0` for all `r`.
(`S ≥ 1` is necessary: with `S = 0`, `y_{r+1} = 3 y_r − 1` gives `1,2,5,14,…`.) -/
theorem minus_block_return_rigid (L S C : Nat) (y : Nat → Nat) (hS : 1 ≤ S)
    (hC : 0 < C) (hy : ∀ r, 0 < y r)
    (hrec : ∀ r, 2 ^ S * y (r + 1) + C = 3 ^ L * y r) :
    2 ^ S < 3 ^ L ∧ (3 ^ L - 2 ^ S) * y 0 = C ∧ ∀ r, y r = y 0 := by
  have hlt := minus_two_pow_lt_three_pow_of_block_return L S C y hC hy hrec
  obtain ⟨D, hD⟩ : ∃ D, 3 ^ L = 2 ^ S + D := ⟨3 ^ L - 2 ^ S, by omega⟩
  have hDpos : 0 < D := by omega
  have hDeq : 3 ^ L - 2 ^ S = D := by omega
  have key := minus_shift_identity L S C D y hD hrec
  have h2S : 0 < 2 ^ S := Nat.pow_pos (by decide)
  have h3L : 0 < 3 ^ L := Nat.pow_pos (by decide)
  -- Step 1: D * y 0 = C, by two cases.
  have hsat : D * y 0 = C := by
    rcases Nat.le_total (D * y 0) C with hle | hge
    · -- case p_r := C − D y_r ≥ 0 : 2^S p_{r+1} = 3^L p_r, p_r ≤ C, so (3^L)^r p_0 ≤ (2^S)^r C
      have hp : ∀ r, D * y r ≤ C ∧ 2 ^ S * (C - D * y (r + 1)) = 3 ^ L * (C - D * y r) := by
        intro r; induction r with
        | zero => exact ⟨hle, (step_le L S C _ _ h2S (key 0) hle).2⟩
        | succ r ih =>
          have h1 := step_le L S C _ _ h2S (key r) ih.1
          exact ⟨h1.1, (step_le L S C _ _ h2S (key (r + 1)) h1.1).2⟩
      have hpow : ∀ r, (3 ^ L) ^ r * (C - D * y 0) = (2 ^ S) ^ r * (C - D * y r) := by
        intro r; induction r with
        | zero => simp
        | succ r ih =>
          calc (3 ^ L) ^ (r + 1) * (C - D * y 0)
              = 3 ^ L * ((3 ^ L) ^ r * (C - D * y 0)) := by rw [Nat.pow_succ]; ac_rfl
            _ = 3 ^ L * ((2 ^ S) ^ r * (C - D * y r)) := by rw [ih]
            _ = (2 ^ S) ^ r * (3 ^ L * (C - D * y r)) := by ac_rfl
            _ = (2 ^ S) ^ r * (2 ^ S * (C - D * y (r + 1))) := by rw [(hp r).2]
            _ = (2 ^ S) ^ (r + 1) * (C - D * y (r + 1)) := by rw [Nat.pow_succ]; ac_rfl
      apply Classical.byContradiction
      intro hne
      have hp0 : 1 ≤ C - D * y 0 := by omega
      have hdom := pow_dominates (2 ^ S) (3 ^ L) C h2S hlt hC
      obtain ⟨r, hr⟩ : ∃ r, r = C * 2 ^ S := ⟨_, rfl⟩
      rw [← hr] at hdom
      have h1 : (3 ^ L) ^ r ≤ (3 ^ L) ^ r * (C - D * y 0) := by
        calc (3 ^ L) ^ r = (3 ^ L) ^ r * 1 := by simp
          _ ≤ (3 ^ L) ^ r * (C - D * y 0) := Nat.mul_le_mul_left _ hp0
      have h2 : (2 ^ S) ^ r * (C - D * y r) ≤ (2 ^ S) ^ r * C :=
        Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      have h3 : (2 ^ S) ^ r * C = C * (2 ^ S) ^ r := Nat.mul_comm _ _
      rw [hpow r] at h1
      omega
    · -- case n_r := D y_r − C ≥ 0 : 2^S n_{r+1} = 3^L n_r, so (2^S)^r ∣ n_0 for all r
      have hn : ∀ r, C ≤ D * y r ∧ 2 ^ S * (D * y (r + 1) - C) = 3 ^ L * (D * y r - C) := by
        intro r; induction r with
        | zero => exact ⟨hge, (step_ge L S C _ _ h2S (key 0) hge).2⟩
        | succ r ih =>
          have h1 := step_ge L S C _ _ h2S (key r) ih.1
          exact ⟨h1.1, (step_ge L S C _ _ h2S (key (r + 1)) h1.1).2⟩
      have hpow : ∀ r, (2 ^ S) ^ r * (D * y r - C) = (3 ^ L) ^ r * (D * y 0 - C) := by
        intro r; induction r with
        | zero => simp
        | succ r ih =>
          calc (2 ^ S) ^ (r + 1) * (D * y (r + 1) - C)
              = (2 ^ S) ^ r * (2 ^ S * (D * y (r + 1) - C)) := by rw [Nat.pow_succ]; ac_rfl
            _ = (2 ^ S) ^ r * (3 ^ L * (D * y r - C)) := by rw [(hn r).2]
            _ = 3 ^ L * ((2 ^ S) ^ r * (D * y r - C)) := by ac_rfl
            _ = 3 ^ L * ((3 ^ L) ^ r * (D * y 0 - C)) := by rw [ih]
            _ = (3 ^ L) ^ (r + 1) * (D * y 0 - C) := by rw [Nat.pow_succ]; ac_rfl
      have hcop : ∀ r, Nat.Coprime ((2 ^ S) ^ r) ((3 ^ L) ^ r) := fun r =>
        Nat.Coprime.pow r r (Nat.Coprime.pow S L (by decide : Nat.Coprime 2 3))
      have hdvd : ∀ r, (2 ^ S) ^ r ∣ (D * y 0 - C) := fun r =>
        Nat.Coprime.dvd_of_dvd_mul_left (hcop r) ⟨D * y r - C, (hpow r).symm⟩
      apply Classical.byContradiction
      intro hne
      have hn0 : 0 < D * y 0 - C := by omega
      have hle := Nat.le_of_dvd hn0 (hdvd (D * y 0 - C))
      have h2 : 2 ≤ 2 ^ S := by
        calc 2 = 2 ^ 1 := by simp
          _ ≤ 2 ^ S := Nat.pow_le_pow_right (by decide) hS
      have hge2 : 2 ^ (D * y 0 - C) ≤ (2 ^ S) ^ (D * y 0 - C) := Nat.pow_le_pow_left h2 _
      have hlt2 : D * y 0 - C < 2 ^ (D * y 0 - C) := Nat.lt_two_pow_self
      omega
  -- Step 2: constancy. D * y r = C for all r, hence y r = y 0.
  have hconst : ∀ r, D * y r = C := by
    intro r; induction r with
    | zero => exact hsat
    | succ r ih =>
      have k := key r
      rw [ih] at k
      have : 2 ^ S * (D * y (r + 1)) = 2 ^ S * C := by omega
      exact Nat.eq_of_mul_eq_mul_left h2S this
  refine ⟨hlt, by rw [hDeq]; exact hsat, ?_⟩
  intro r
  have := hconst r
  rw [← hsat] at this
  exact Nat.eq_of_mul_eq_mul_left hDpos this

/-- Calibration: the minus fixed point `m = 1` (`L = S = C = 1`, constant chain) is accepted. -/
example : 2 ^ 1 < 3 ^ 1 ∧ (3 ^ 1 - 2 ^ 1) * 1 = 1 ∧ ∀ r : Nat, (fun _ => 1) r = (fun _ => 1) 0 :=
  minus_block_return_rigid 1 1 1 (fun _ => 1) (Nat.le_refl 1) (by decide) (fun _ => by decide)
    (fun _ => by decide)

end EOC.SignedBlock
