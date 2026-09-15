/-
White-run rigidity for 3-blocks (exact integer statements).

For a 3-block with local modulus `2^M` the centered residue `e = cres (λ·3^{-n}) M` of the block
angle satisfies, at the next block (modulus `2^{M'}`, `M' ≤ M`), the recurrence
`27 · e' ≡ e (mod 2^{M'})`.  From this alone:

* (A′) continuation: `27 ∣ e` and `|e| < 27·2^{M'-1}` force `e' = e / 27`;
* (B′) exit: `27 ∤ e` and `|e| ≤ 2^{M'-1}` force `|e'| ≥ 2^{M'}/54`;
* in the white regime `54|e_j| < 2^{M_{j+1}}` the size condition of (A′) is automatic, and a white
  run `j = 0, …, k` forces `e_k · 27^k = e_0`, so `27^k ∣ e_0` (Tao triangles made explicit).

Also: an interval residue count and a fibre-multiplicity bound for injective bounded maps.
-/
import Mathlib

namespace EOC
namespace WhiteRun

open Finset

/-! ## Coprimality helpers -/

theorem isCoprime_two_pow_27 (M : ℕ) : IsCoprime ((2 : ℤ) ^ M) 27 := by
  have h : IsCoprime (2 : ℤ) 27 := by
    rw [Int.isCoprime_iff_gcd_eq_one]; rfl
  exact h.pow_left

theorem isCoprime_two_pow_three_pow (M n : ℕ) : IsCoprime ((2 : ℤ) ^ M) (3 ^ n) := by
  have h : IsCoprime (2 : ℤ) 3 := by
    rw [Int.isCoprime_iff_gcd_eq_one]; rfl
  exact h.pow

/-! ## (A′) continuation and (B′) exit -/

/-- **(A′) Continuation.** If `2^{M'} ∣ 27 e' − e`, `27 ∣ e`, `e'` is centered (`2|e'| ≤ 2^{M'}`)
and `2|e| < 27·2^{M'}`, then `e' · 27 = e`. -/
theorem cont {M' : ℕ} {e e' : ℤ} (hd : (2 : ℤ) ^ M' ∣ 27 * e' - e) (h27 : (27 : ℤ) ∣ e)
    (he' : 2 * |e'| ≤ 2 ^ M') (he : 2 * |e| < 27 * 2 ^ M') : e' * 27 = e := by
  obtain ⟨f, rfl⟩ := h27
  have hd' : (2 : ℤ) ^ M' ∣ 27 * (e' - f) := by
    have : 27 * e' - 27 * f = 27 * (e' - f) := by ring
    rwa [this] at hd
  have hdiv : (2 : ℤ) ^ M' ∣ e' - f := (isCoprime_two_pow_27 M').dvd_of_dvd_mul_left hd'
  have hf : 2 * |f| < 2 ^ M' := by
    rw [abs_mul] at he
    have : |(27 : ℤ)| = 27 := by norm_num
    rw [this] at he
    linarith
  have hlt : |e' - f| < 2 ^ M' := by
    have := abs_sub (e') f
    linarith
  have h0 := Int.eq_zero_of_abs_lt_dvd hdiv hlt
  linarith

/-- **(B′) Exit.** If `2^{M'} ∣ 27 e' − e`, `27 ∤ e` and `2|e| ≤ 2^{M'}`, then
`2^{M'} ≤ 54 |e'|` (the next angle `|e'|/2^{M'}` is at least `1/54`). -/
theorem exit {M' : ℕ} {e e' : ℤ} (hd : (2 : ℤ) ^ M' ∣ 27 * e' - e) (h27 : ¬ (27 : ℤ) ∣ e)
    (he : 2 * |e| ≤ 2 ^ M') : 2 ^ M' ≤ 54 * |e'| := by
  obtain ⟨k, hk⟩ := hd
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply h27
    exact ⟨e', by linarith⟩
  have hk1 : 1 ≤ |k| := Int.one_le_abs hk0
  have hpos : (0 : ℤ) < 2 ^ M' := by positivity
  have habs : |(2 : ℤ) ^ M' * k| = 2 ^ M' * |k| := by
    rw [abs_mul, abs_of_pos hpos]
  have hge : (2 : ℤ) ^ M' ≤ |(2 : ℤ) ^ M' * k| := by
    rw [habs]; nlinarith
  have htri : |27 * e' - e| ≤ 27 * |e'| + |e| := by
    have h1 := abs_sub (27 * e') e
    rw [abs_mul] at h1
    have : |(27 : ℤ)| = 27 := by norm_num
    rw [this] at h1
    exact h1
  rw [← hk] at hge
  linarith

/-! ## White runs -/

section Run

variable (e : ℕ → ℤ) (M : ℕ → ℕ)

/-- Block `j` is white: its angle `|e_j|/2^{M_j}` is below `2^{-u_j}/54`,
i.e. `54|e_j| < 2^{M_{j+1}}`. -/
def white (j : ℕ) : Prop := 54 * |e j| < 2 ^ M (j + 1)

variable {e M}

/-- The size condition of (A′) is automatic in the white regime. -/
theorem size_automatic {j : ℕ} (hw : white e M j) : 2 * |e j| < 27 * 2 ^ M (j + 1) := by
  unfold white at hw
  have h0 : 0 ≤ |e j| := abs_nonneg _
  have hpos : (0 : ℤ) < 2 ^ M (j + 1) := by positivity
  nlinarith

/-- **Dichotomy step.** Two consecutive white blocks force `27 ∣ e_j` and `e_{j+1}·27 = e_j`. -/
theorem white_step (hrec : ∀ j, (2 : ℤ) ^ M (j + 1) ∣ 27 * e (j + 1) - e j)
    (hcen : ∀ j, 2 * |e j| ≤ 2 ^ M j) (hM : ∀ j, M (j + 1) ≤ M j) {j : ℕ}
    (hw : white e M j) (hw' : white e M (j + 1)) : (27 : ℤ) ∣ e j ∧ e (j + 1) * 27 = e j := by
  have hsmall : 2 * |e j| ≤ 2 ^ M (j + 1) := by
    unfold white at hw
    have := abs_nonneg (e j)
    linarith
  have h27 : (27 : ℤ) ∣ e j := by
    by_contra hn
    have hx := exit (hrec j) hn hsmall
    unfold white at hw'
    have hmono : (2 : ℤ) ^ M (j + 1 + 1) ≤ 2 ^ M (j + 1) :=
      pow_le_pow_right₀ (by norm_num) (hM (j + 1))
    linarith
  exact ⟨h27, cont (hrec j) h27 (hcen (j + 1)) (size_automatic hw)⟩

/-- **Run length.** A white run `j = 0, …, k` forces `e_k · 27^k = e_0`. -/
theorem run_length (hrec : ∀ j, (2 : ℤ) ^ M (j + 1) ∣ 27 * e (j + 1) - e j)
    (hcen : ∀ j, 2 * |e j| ≤ 2 ^ M j) (hM : ∀ j, M (j + 1) ≤ M j) :
    ∀ k : ℕ, (∀ j ≤ k, white e M j) → e k * 27 ^ k = e 0 := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hw
    have hk := ih (fun j hj => hw j (by omega))
    have hs := (white_step hrec hcen hM (hw k (by omega)) (hw (k + 1) le_rfl)).2
    rw [pow_succ, ← mul_assoc, ← hk, ← hs]; ring

/-- **Run-length divisibility.** A white run of length `k + 1` starting at `0` forces
`27^k ∣ e_0`. -/
theorem run_dvd (hrec : ∀ j, (2 : ℤ) ^ M (j + 1) ∣ 27 * e (j + 1) - e j)
    (hcen : ∀ j, 2 * |e j| ≤ 2 ^ M j) (hM : ∀ j, M (j + 1) ≤ M j) (k : ℕ)
    (hw : ∀ j ≤ k, white e M j) : (27 : ℤ) ^ k ∣ e 0 :=
  ⟨e k, by rw [← run_length hrec hcen hM k hw]; ring⟩

end Run

/-! ## Centered residues and the Collatz instance -/

/-- Centered residue of `x` modulo `2^M`: the representative in `(-2^M/2, 2^M/2]`. -/
def cres (x : ℤ) (M : ℕ) : ℤ :=
  if 2 * (x % 2 ^ M) ≤ 2 ^ M then x % 2 ^ M else x % 2 ^ M - 2 ^ M

theorem cres_dvd (x : ℤ) (M : ℕ) : (2 : ℤ) ^ M ∣ cres x M - x := by
  have hdef : x % 2 ^ M = x - 2 ^ M * (x / 2 ^ M) := Int.emod_def x _
  unfold cres
  split_ifs
  · exact ⟨-(x / 2 ^ M), by rw [hdef]; ring⟩
  · exact ⟨-(x / 2 ^ M) - 1, by rw [hdef]; ring⟩

theorem abs_cres_le (x : ℤ) (M : ℕ) : 2 * |cres x M| ≤ 2 ^ M := by
  have hpos : (0 : ℤ) < 2 ^ M := by positivity
  have h0 : 0 ≤ x % 2 ^ M := Int.emod_nonneg _ hpos.ne'
  have h1 : x % 2 ^ M < 2 ^ M := Int.emod_lt_of_pos _ hpos
  unfold cres
  split_ifs with h
  · rw [abs_of_nonneg h0]; exact h
  · rw [abs_of_neg (by linarith)]; linarith

/-- **Collatz instance of the recurrence.** If `w·3^{n+3} ≡ 1` and `v·3^n ≡ 1 (mod 2^M)` and
`M' ≤ M`, the centered residues `e' = cres (λ w) M'`, `e = cres (λ v) M` satisfy
`2^{M'} ∣ 27 e' − e`. -/
theorem cres_rec {lam w v : ℤ} {n M M' : ℕ} (hw : (2 : ℤ) ^ M ∣ w * 3 ^ (n + 3) - 1)
    (hv : (2 : ℤ) ^ M ∣ v * 3 ^ n - 1) (hM : M' ≤ M) :
    (2 : ℤ) ^ M' ∣ 27 * cres (lam * w) M' - cres (lam * v) M := by
  have hpow : (2 : ℤ) ^ M' ∣ 2 ^ M := pow_dvd_pow 2 hM
  have h27 : (2 : ℤ) ^ M ∣ 27 * w - v := by
    have hprod : (2 : ℤ) ^ M ∣ (27 * w - v) * 3 ^ n := by
      have : (27 * w - v) * 3 ^ n = (w * 3 ^ (n + 3) - 1) - (v * 3 ^ n - 1) := by ring
      rw [this]; exact dvd_sub hw hv
    exact (isCoprime_two_pow_three_pow M n).dvd_of_dvd_mul_right hprod
  have hsplit : 27 * cres (lam * w) M' - cres (lam * v) M =
      27 * (cres (lam * w) M' - lam * w) - (cres (lam * v) M - lam * v) + lam * (27 * w - v) := by
    ring
  rw [hsplit]
  refine dvd_add (dvd_sub (dvd_mul_of_dvd_right (cres_dvd _ _) _) ?_) ?_
  · exact hpow.trans (cres_dvd _ _)
  · exact dvd_mul_of_dvd_right (hpow.trans h27) _

/-! ## Counting -/

/-- **Interval residue count.** A length-`H` interval contains at most `H/q + 1` integers of a
given residue class. -/
theorem card_Ico_filter_mod_le (a H q c : ℕ) :
    ((Ico a (a + H)).filter (fun x => x % q = c)).card ≤ H / q + 1 := by
  have hmaps : ∀ x ∈ (Ico a (a + H)).filter (fun x => x % q = c),
      (x - a) / q ∈ range (H / q + 1) := by
    intro x hx
    simp only [mem_filter, mem_Ico] at hx
    rw [mem_range, Nat.lt_succ_iff]
    exact Nat.div_le_div_right (by omega)
  have hinj : Set.InjOn (fun x => (x - a) / q) ↑((Ico a (a + H)).filter (fun x => x % q = c)) := by
    intro x hx y hy hxy
    simp only [coe_filter, mem_Ico, Set.mem_ofPred_eq] at hx hy
    simp only at hxy
    have hmod : (x - a) % q = (y - a) % q := by
      have h1 : x - a + a ≡ y - a + a [MOD q] := by
        rw [Nat.sub_add_cancel hx.1.1, Nat.sub_add_cancel hy.1.1]
        exact hx.2.trans hy.2.symm
      exact Nat.ModEq.add_right_cancel' a h1
    have hx' := Nat.div_add_mod (x - a) q
    have hy' := Nat.div_add_mod (y - a) q
    rw [hxy, hmod] at hx'
    omega
  calc ((Ico a (a + H)).filter (fun x => x % q = c)).card ≤ (range (H / q + 1)).card :=
        card_le_card_of_injOn _ hmaps hinj
    _ = H / q + 1 := card_range _

/-- **Fibre multiplicity.** If `X` is injective on `T` with values `≤ Xmax`, each residue class
modulo `q` has at most `Xmax/q + 1` preimages in `T`. -/
theorem card_fibre_mod_le {ι : Type*} (T : Finset ι) (X : ι → ℕ) (Xmax q c : ℕ)
    (hinj : Set.InjOn X ↑T) (hX : ∀ i ∈ T, X i ≤ Xmax) :
    (T.filter fun i => X i % q = c).card ≤ Xmax / q + 1 := by
  have hmaps : ∀ i ∈ T.filter (fun i => X i % q = c), X i / q ∈ range (Xmax / q + 1) := by
    intro i hi
    simp only [mem_filter] at hi
    rw [mem_range, Nat.lt_succ_iff]
    exact Nat.div_le_div_right (hX i hi.1)
  have hinj' : Set.InjOn (fun i => X i / q) ↑(T.filter fun i => X i % q = c) := by
    intro i hi j hj hij
    simp only [coe_filter, Set.mem_ofPred_eq] at hi hj
    simp only at hij
    apply hinj hi.1 hj.1
    have h1 := Nat.div_add_mod (X i) q
    have h2 := Nat.div_add_mod (X j) q
    rw [hi.2] at h1; rw [hj.2, ← hij] at h2
    omega
  calc (T.filter fun i => X i % q = c).card ≤ (range (Xmax / q + 1)).card :=
        card_le_card_of_injOn _ hmaps hinj'
    _ = Xmax / q + 1 := card_range _

end WhiteRun
end EOC
