import EOC.Confinement
import EOC.TaoLike.Cylinder

/-!
# Exact one-step cylinder digit counting

**Part II of the Round 3 hypercuboid-transfer formalization** (see
`explorations/hypercuboid_transfer/ROUND3_FORMALIZATION_REPORT.md`).

This file formalizes, as an exact finite counting theorem (not a limiting/measure-theoretic
statement), the `q = 1` case of the exact one-step cylinder-lift digit law from
`ROUND1_REPORT.md` Part VI: among the `2^K` values of the lift parameter `k` in
`Finset.range (2^K)`, *exactly half* give a shifted realizer whose next valuation digit is `1`.

The general-`q` case (`P(\text{next digit}=q) = 2^{-q}` exactly, for every `q`) requires a
genuinely new 2-adic counting lemma not otherwise present in this repository; it is deferred with
a complete proof sketch to `ROUND3_DEFERRED_THEOREMS.md` rather than forced through this round.
The `q = 1` case proved here needs no such machinery: it reduces to a pure parity argument.

As throughout `EOC.TaoLike`, this is a statement about the cylinder-lift ensemble (the ambient
parameter `k`) only. It says nothing about any one fixed, predetermined Collatz seed's own actual
digit sequence.
-/

namespace EOC
namespace CylinderCounting

open Finset

/-- **Residue counting lemma.** Exactly half of `Finset.range (2 * M)` satisfy a fixed residue
condition mod `2`. Purely combinatorial; no connection to `a`/`T`/cylinders yet. -/
theorem card_filter_mod_two (M r : ℕ) (hr : r < 2) :
    ((Finset.range (2 * M)).filter (fun k => k % 2 = r)).card = M := by
  have himg : (Finset.range (2 * M)).filter (fun k => k % 2 = r)
      = (Finset.range M).image (fun j => 2 * j + r) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hk, hkr⟩
      exact ⟨k / 2, by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩
      omega
  have hinj : Function.Injective (fun j : ℕ => 2 * j + r) := by
    intro j1 j2 h
    simp only at h
    omega
  rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_range]

/-- `padicValNat 2 2 = 1`. -/
theorem padicValNat_two_two : padicValNat 2 2 = 1 := by
  have h := padicValNat_base_pow (p := 2) (by norm_num) 1
  simpa using h

/-- **One-step valuation dichotomy.** For `0 < B` even and `C` odd, `padicValNat 2 (B + 2*C*k)`
equals `1` exactly when `k`'s parity differs from `(B/2)`'s parity, and is `≠ 1` (in fact `≥ 2`)
otherwise. The specific odd value of `C` never matters, only its parity. -/
theorem padicValNat_affine_eq_one_iff_mod_two (B C k : ℕ) (hBpos : 0 < B) (hB : Even B)
    (hC : Odd C) :
    padicValNat 2 (B + 2 * C * k) = 1 ↔ k % 2 ≠ (B / 2) % 2 := by
  obtain ⟨B', hB'⟩ := hB
  have hB2 : B = 2 * B' := by omega
  have hBd2 : B / 2 = B' := by omega
  have hB'pos : 0 < B' := by omega
  rw [hBd2]
  have hfactor : B + 2 * C * k = 2 * (B' + C * k) := by rw [hB2]; ring
  rw [hfactor]
  set y : ℕ := B' + C * k with hy
  have hCmod : C % 2 = 1 := Nat.odd_iff.mp hC
  have hCk_mod : (C * k) % 2 = k % 2 := by
    conv_lhs => rw [Nat.mul_mod, hCmod]
    simp
  have hy_ne : y ≠ 0 := by
    rw [hy]
    omega
  rw [padicValNat.mul (by norm_num) hy_ne, padicValNat_two_two]
  constructor
  · intro heq
    have hyval0 : padicValNat 2 y = 0 := by omega
    by_contra hcon
    have hpar : k % 2 = B' % 2 := by omega
    have hymod : y % 2 = 0 := by rw [hy]; omega
    have hydvd : (2:ℕ) ∣ y := Nat.dvd_of_mod_eq_zero hymod
    rcases padicValNat.eq_zero_iff.mp hyval0 with h1 | h1 | h1
    · norm_num at h1
    · exact hy_ne h1
    · exact h1 hydvd
  · intro hne
    have hymod : y % 2 = 1 := by rw [hy]; omega
    have hyodd : Odd y := Nat.odd_iff.mpr hymod
    have hynotdvd : ¬ (2 ∣ y) := Nat.two_dvd_ne_zero.mpr hymod
    have hyval0 : padicValNat 2 y = 0 := padicValNat.eq_zero_of_not_dvd hynotdvd
    omega

/-- **Exact one-step marginal, `q = 1` case.** For `0 < B` even, `C` odd, `K ≥ 1`: among
`k ∈ Finset.range (2^K)`, exactly `2^(K-1)` give `padicValNat 2 (B + 2*C*k) = 1`. This is the
finite-counting form of the `q=1` instance of `P(\text{next digit}=1) = 2^{-1}`. -/
theorem card_filter_padicValNat_affine_eq_one (B C K : ℕ) (hBpos : 0 < B) (hB : Even B)
    (hC : Odd C) (hK : 1 ≤ K) :
    ((Finset.range (2 ^ K)).filter (fun k => padicValNat 2 (B + 2 * C * k) = 1)).card
      = 2 ^ (K - 1) := by
  have hpow : (2:ℕ) ^ K = 2 * 2 ^ (K - 1) := by
    conv_lhs => rw [show K = (K - 1) + 1 from by omega]
    rw [pow_succ]
    ring
  -- Pointwise iff + `filter_congr`, rather than rewriting an equality of predicates under the
  -- binder (which fails because `Finset.filter` carries a dependent `DecidablePred` instance).
  rw [Finset.filter_congr
      (fun k _ => padicValNat_affine_eq_one_iff_mod_two B C k hBpos hB hC), hpow]
  have htarget : (B / 2) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  set r : ℕ := (B / 2) % 2 with hr
  have hr' : 1 - r < 2 := by omega
  have hcompl : (Finset.range (2 * 2 ^ (K - 1))).filter (fun k => k % 2 ≠ r)
      = (Finset.range (2 * 2 ^ (K - 1))).filter (fun k => k % 2 = 1 - r) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    have hklt : k % 2 < 2 := Nat.mod_lt k (by norm_num)
    constructor
    · exact fun ⟨hk, hne⟩ => ⟨hk, by omega⟩
    · exact fun ⟨hk, heq⟩ => ⟨hk, by omega⟩
  rw [hcompl]
  exact card_filter_mod_two (2 ^ (K - 1)) (1 - r) hr'

/-- **Cylinder-lift form.** For a realizer `m` of a length-`t` prefix `d`, among the `2^K`
lift parameters `k ∈ Finset.range (2^K)`, exactly half (`2^(K-1)`) give a shifted realizer
`m + 2^(S d t + 1) * k` whose depth-`t` valuation digit equals `1`. This is the finite-counting
theorem underlying `P(d_t = 1) = 1/2` from `ROUND1_REPORT.md` Part VI, restricted to `q = 1`. -/
theorem cylinder_next_digit_eq_one_card (d : ℕ → ℕ) (t m K : ℕ) (h : Realizes d t m)
    (hK : 1 ≤ K) :
    ((Finset.range (2 ^ K)).filter
        (fun k => a (orbit (m + 2 ^ (S d t + 1) * k) t) = 1)).card
      = 2 ^ (K - 1) := by
  have hrestart : ∀ k, orbit (m + 2 ^ (S d t + 1) * k) t = orbit m t + 2 * 3 ^ t * k :=
    fun k => (cylinder_restart d t m k h).2
  -- With `x := orbit m t`, the restart law gives `orbit m' t = x + 2 * 3^t * k`, hence
  --   `3 * (x + 2 * 3^t * k) + 1 = (3 * x + 1) + 2 * 3^(t+1) * k`.
  -- The outer factor `3` multiplies the lift term too, so the affine lemma is applied with
  -- `B = 3 * x + 1` and odd coefficient `C = 3^(t+1)` (not `3^t`).
  have hiff : ∀ k ∈ Finset.range (2 ^ K), a (orbit (m + 2 ^ (S d t + 1) * k) t) = 1
      ↔ padicValNat 2 (3 * orbit m t + 1 + 2 * 3 ^ (t + 1) * k) = 1 := by
    intro k _
    rw [hrestart k]
    unfold a
    have heq2 : 3 * (orbit m t + 2 * 3 ^ t * k) + 1
        = 3 * orbit m t + 1 + 2 * 3 ^ (t + 1) * k := by ring
    rw [heq2]
  rw [Finset.filter_congr hiff]
  have hoddorbit : Odd (orbit m t) := by
    obtain ⟨hodd, _⟩ := h
    exact odd_orbit hodd t
  obtain ⟨j, hj⟩ := hoddorbit
  apply card_filter_padicValNat_affine_eq_one
  · omega
  · exact ⟨3 * j + 2, by omega⟩
  · exact Odd.pow ⟨1, rfl⟩
  · exact hK

end CylinderCounting
end EOC
