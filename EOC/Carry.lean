import EOC.ValuationWord

namespace EOC

open Finset

/-! ### Definition 5.1, part 2: the carry recursion and its closed form -/

/-- Carry recursion: `q_0 = 0`, `q_{j+1} = 3 q_j + 2^{s_j}`. -/
def q (d : ℕ → ℕ) : ℕ → ℕ :=
  fun n => Nat.rec 0 (fun j qj => 3 * qj + 2 ^ s d j) n

@[simp] theorem q_zero (d : ℕ → ℕ) : q d 0 = 0 := rfl
theorem q_succ (d : ℕ → ℕ) (j : ℕ) : q d (j + 1) = 3 * q d j + 2 ^ s d j := rfl

/-- Closed-form carry sum `C_N(D) = Σ_{j=0}^{N-1} 3^{N-1-j} 2^{s_j}` (Def 5.1). -/
def C (d : ℕ → ℕ) (N : ℕ) : ℕ := ∑ j ∈ range N, 3 ^ (N - 1 - j) * 2 ^ s d j

theorem C_zero (d : ℕ → ℕ) : C d 0 = 0 := by
  unfold C; simp

/-- "Constant factor distributes into a `range`-sum", proved directly by
induction rather than invoked from a general Mathlib lemma whose current
argument order I have not re-verified. -/
private theorem factor_mul_sum (M : ℕ) (f : ℕ → ℕ) :
    3 * (∑ j ∈ range M, f j) = ∑ j ∈ range M, 3 * f j := by
  induction M with
  | zero => simp
  | succ M ih => simp only [Finset.sum_range_succ, Nat.mul_add, ih]

/-- `q_N = C_N(D)`: the recursion and the closed form agree. -/
theorem q_eq_C (d : ℕ → ℕ) : ∀ N, q d N = C d N := by
  intro N
  induction N with
  | zero => rw [q_zero, C_zero]
  | succ N ih =>
    have hshift : 3 * C d N = ∑ j ∈ range N, 3 ^ (N - j) * 2 ^ s d j := by
      unfold C
      rw [factor_mul_sum N (fun j => 3 ^ (N - 1 - j) * 2 ^ s d j)]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      have hNj : N - j = (N - 1 - j) + 1 := by omega
      rw [hNj, pow_succ]
      ring
    have hC : C d (N + 1) = (∑ j ∈ range N, 3 ^ (N - j) * 2 ^ s d j) + 2 ^ s d N := by
      unfold C
      rw [Finset.sum_range_succ]
      simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
    rw [q_succ, ih, hshift, hC]

/-! ### The finite iterate identity, under per-step exact-divisibility -/

/-- **Conditional** finite iterate identity. Hypothesis: for every `i < N`,
`2^(d i)` exactly divides `3 * iter d m0 i + 1` — i.e. the formal division at
each step up to `N` is exact. This hypothesis is *assumed*, not derived, here;
Proposition 5.2 part (a) is precisely the theorem deriving it, for all `i < N`
at once, from the single aggregate condition at depth `S_N` (by descending
induction). Under this hypothesis, `2^(s_j) * iter d m0 j = 3^j * m0 + q_j`
for every `j ≤ N`. -/
theorem iter_carry_eq (d : ℕ → ℕ) (m0 N : ℕ)
    (hdvd : ∀ i < N, 2 ^ d i ∣ (3 * iter d m0 i + 1)) :
    ∀ j, j ≤ N → 2 ^ s d j * iter d m0 j = 3 ^ j * m0 + q d j := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ i ih =>
    intro hj
    have hiN : i < N := by omega
    have hIH : 2 ^ s d i * iter d m0 i = 3 ^ i * m0 + q d i := ih (le_of_lt hiN)
    obtain ⟨k, hk⟩ := hdvd i hiN
    have hiter_succ : iter d m0 (i + 1) = k := by
      rw [iter_succ, hk, Nat.mul_div_cancel_left k (by positivity)]
    rw [s_succ, q_succ, pow_add, hiter_succ, pow_succ]
    have step1 : 2 ^ s d i * 2 ^ d i * k = 3 * (2 ^ s d i * iter d m0 i) + 2 ^ s d i := by
      rw [show (2:ℕ) ^ s d i * 2 ^ d i * k = 2 ^ s d i * (2 ^ d i * k) from by ring, ← hk]
      ring
    rw [step1, hIH]
    ring

end EOC
