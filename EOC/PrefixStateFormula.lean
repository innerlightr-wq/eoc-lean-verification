import EOC.PrefixCollision

/-!
# Prefix end states: carry formula, collision criterion, Parseval identity

For a positive word `d`, prefix depth `j`, shell `σ = S_j`, least realizer `r = r_j` and end state
`m = T^j(r)`:

* `endState_carry` — `2^σ · m = 3^j · r + q_j` (the carry identity at the least realizer).
* `endState_modEq_iff` — **collision criterion**: for two words of the same shell `σ`,
  `m ≡ m' (mod 2^(t+1)) ↔ 3^j r + q_j ≡ 3^j r' + q'_j (mod 2^(σ+t+1))`.
* `endState_int_formula` — **prefix-state formula**: if `B : ℤ` satisfies
  `3^j (r + 2^(σ+1) B) ≡ 2^σ − q_j (mod 2^(σ+t+1))` (i.e. `r + 2^(σ+1)B` is the residue of the
  2-adic number `3^{−j}(2^σ − q_j)` modulo `2^(σ+t+1)`, so `B` is its bit block `[σ+1, σ+t]`),
  then `m ≡ 1 − 2·3^j·B (mod 2^(t+1))`; `exists_block` shows such `B` exists.
* `sum_sq_norm_eq_card_pairs` — **Parseval for collision counts**: for any finite family
  `β : ι → ℤ/n`, `∑_g ‖∑_{i∈T} e(g β_i / n)‖^2 = n · #{(i,i') ∈ T × T : β_i = β_{i'}}`.  With
  `β = betaP t` this is the characteristic-function form of the prefix collision quantity:
  `δ = 2^t Col − 1 = |P|^{-2} ∑_{g ≠ 0} |∑_P e(g β_P / 2^t)|^2`.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace PrefixStateFormula

open Finset SuffixTransport

variable {d e : ℕ → ℕ}

/-- The carry identity at the least realizer: `2^(S_j) · T^j(r_j) = 3^j · r_j + q_j`. -/
theorem endState_carry (j : ℕ) (hd : ∀ i < j, 1 ≤ d i) :
    2 ^ S d j * orbit (leastRealizer d j) j = 3 ^ j * leastRealizer d j + q d j :=
  realizes_carry (leastRealizer_realizes_all d j hd) le_rfl

/-- **Collision criterion.** For two positive words with the same prefix total `σ`,
`T^j r ≡ T^j r' (mod 2^(t+1))` iff `3^j r + q ≡ 3^j r' + q' (mod 2^(σ+t+1))`. -/
theorem endState_modEq_iff (j t : ℕ) (hd : ∀ i < j, 1 ≤ d i) (he : ∀ i < j, 1 ≤ e i)
    (hS : S d j = S e j) :
    orbit (leastRealizer d j) j ≡ orbit (leastRealizer e j) j [MOD 2 ^ (t + 1)] ↔
      3 ^ j * leastRealizer d j + q d j ≡ 3 ^ j * leastRealizer e j + q e j
        [MOD 2 ^ (S d j + t + 1)] := by
  rw [← endState_carry j hd, ← endState_carry j he, ← hS,
    show 2 ^ (S d j + t + 1) = 2 ^ S d j * 2 ^ (t + 1) by rw [← pow_add]; congr 1]
  constructor
  · exact fun h => Nat.ModEq.mul_left' _ h
  · exact fun h => Nat.ModEq.mul_left_cancel' (by positivity) h

/-- **Prefix-state formula (integer form).** If `2^σ m = 3^j r + q` and
`3^j (r + 2^(σ+1) B) ≡ 2^σ − q (mod 2^(σ+t+1))`, then `m ≡ 1 − 2·3^j B (mod 2^(t+1))`. -/
theorem endState_int_formula {σ t j : ℕ} {m r q : ℕ} {B : ℤ}
    (hcarry : 2 ^ σ * m = 3 ^ j * r + q)
    (hB : (3 : ℤ) ^ j * (r + 2 ^ (σ + 1) * B) ≡ 2 ^ σ - q [ZMOD 2 ^ (σ + t + 1)]) :
    (m : ℤ) ≡ 1 - 2 * 3 ^ j * B [ZMOD 2 ^ (t + 1)] := by
  have hc : (2 : ℤ) ^ σ * m = 3 ^ j * r + q := by exact_mod_cast hcarry
  rw [Int.modEq_iff_dvd] at hB ⊢
  -- 2^(σ+t+1) ∣ 2^σ − q − 3^j(r + 2^(σ+1)B) = 2^σ (1 − 2·3^j B − m)
  have hid : (2 : ℤ) ^ σ - q - 3 ^ j * (r + 2 ^ (σ + 1) * B) =
      2 ^ σ * (1 - 2 * 3 ^ j * B - m) := by
    rw [pow_succ]; linear_combination hc
  rw [hid, show σ + t + 1 = σ + (t + 1) by omega, pow_add] at hB
  exact (Int.dvd_of_mul_dvd_mul_left (by positivity) hB)

/-- The block `B` of the prefix-state formula exists. -/
theorem exists_block {σ t j : ℕ} {m r q : ℕ} (hcarry : 2 ^ σ * m = 3 ^ j * r + q)
    (hm : Odd m) :
    ∃ B : ℤ, (3 : ℤ) ^ j * (r + 2 ^ (σ + 1) * B) ≡ 2 ^ σ - q [ZMOD 2 ^ (σ + t + 1)] := by
  obtain ⟨k, hk⟩ := hm
  -- 3^j r + q − 2^σ = 2^(σ+1) k
  have hu : (3 : ℤ) ^ j * r + q - 2 ^ σ = 2 ^ (σ + 1) * k := by
    have : (2 : ℤ) ^ σ * m = 3 ^ j * r + q := by exact_mod_cast hcarry
    rw [hk] at this; push_cast at this; rw [pow_succ]; linear_combination -this
  -- choose B with 3^j B ≡ −k (mod 2^t)
  have hcop : IsCoprime ((3 : ℤ) ^ j) (2 ^ t) :=
    IsCoprime.pow (by rw [Int.isCoprime_iff_gcd_eq_one]; decide)
  obtain ⟨u, v, huv⟩ := hcop
  refine ⟨-k * u, ?_⟩
  rw [Int.modEq_iff_dvd]
  refine ⟨-(k * v), ?_⟩
  have : (2 : ℤ) ^ σ - q - 3 ^ j * (r + 2 ^ (σ + 1) * (-k * u)) =
      2 ^ (σ + 1) * k * (3 ^ j * u - 1) := by linear_combination -hu
  rw [this, show 3 ^ j * u - 1 = -(v * 2 ^ t) by linear_combination huv,
    show σ + t + 1 = σ + 1 + t by omega, pow_add]
  ring

/-! ## Parseval identity for collision counts -/

section Parseval

variable {ι : Type*} {n : ℕ} [NeZero n]

theorem norm_stdAddChar (x : ZMod n) : ‖(ZMod.stdAddChar x : ℂ)‖ = 1 := by
  rw [ZMod.stdAddChar_apply]; exact Circle.norm_coe _

/-- **Parseval for collision counts.**
`∑_g ‖∑_{i∈T} e(g β_i/n)‖^2 = n · #{(i,i') ∈ T×T : β_i = β_{i'}}`. -/
theorem sum_sq_norm_eq_card_pairs (T : Finset ι) (β : ι → ZMod n) :
    ∑ g : ZMod n, ‖∑ i ∈ T, (ZMod.stdAddChar (g * β i) : ℂ)‖ ^ 2 =
      n * (((T ×ˢ T).filter fun p => β p.1 = β p.2).card : ℝ) := by
  have hsq : ∀ g : ZMod n, (‖∑ i ∈ T, (ZMod.stdAddChar (g * β i) : ℂ)‖ ^ 2 : ℝ) =
      (∑ p ∈ T ×ˢ T, (ZMod.stdAddChar (g * (β p.1 - β p.2)) : ℂ)).re := by
    intro g
    set z := ∑ i ∈ T, (ZMod.stdAddChar (g * β i) : ℂ)
    have h1 : (‖z‖ ^ 2 : ℝ) = (z * (starRingEnd ℂ) z).re := by
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [h1, map_sum, sum_mul_sum, ← sum_product']
    congr 1
    refine sum_congr rfl fun p _ => ?_
    rw [← Complex.inv_eq_conj (norm_stdAddChar _), ← AddChar.map_neg_eq_inv,
      ← AddChar.map_add_eq_mul]
    congr 1; ring
  simp_rw [hsq]
  rw [← Complex.re_sum, sum_comm]
  have horth : ∀ p ∈ T ×ˢ T, ∑ g : ZMod n, (ZMod.stdAddChar (g * (β p.1 - β p.2)) : ℂ) =
      if β p.1 = β p.2 then (n : ℂ) else 0 := by
    intro p _
    rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar n), ZMod.card]
    by_cases h : β p.1 = β p.2 <;> simp [h, sub_eq_zero]
  rw [sum_congr rfl horth, ← sum_filter, sum_const, nsmul_eq_mul]
  simp [mul_comm]

end Parseval

end PrefixStateFormula
end EOC
