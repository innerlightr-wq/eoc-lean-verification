import EOC.ShellWeyl

/-!
# Prefix–suffix concatenation of least realizers and the bilinear collision bound

**Concatenation formula.** Split a positive word `d` at depth `j` (`1 ≤ j ≤ N`): prefix least
realizer `r_j`, prefix end state `m = T^j(r_j)`, suffix word `v = σ^j d` of length `N − j` and
total `S_v = S_N − S_j`, suffix least realizer `r_v`.  Then
`r_N = r_j + 2^(S_j+1)·k` where `k < 2^(S_v)` is the **unique** residue with
`m + 2·3^j·k ≡ r_v (mod 2^(S_v+1))`, i.e. `k ≡ ((r_v − m)/2)·3^{−j} (mod 2^(S_v))`
(`concat_modEq`, `concat_lt`, `concat_unique`).

Consequently `r_N < 2^K` (for `S_j < K ≤ S_N`) iff `k < 2^(K − S_j − 1)`: the archimedean cutoff
becomes an interval condition on `k ∈ ℤ/2^(S_v)` whose position is a *difference* of a
suffix-only quantity (`r_v`) and a prefix-only quantity (`m`).  For confined words the admissible
suffixes depend on the prefix only through `S_j` (the barrier is shifted by `S_j`), so the
post-fresh-bit count is a sum of **bilinear incidence counts** between the multiset of prefix end
states and the (collision-free) set of suffix least realizers.

**Bilinear collision bound** (`bilinear_incidence_sq_le`, elementary: Cauchy–Schwarz twice and
translation invariance; no Fourier analysis).  For a finite additive group `G`, a finset `Y`
(distinct points), a finset `I` and weights `N : G → ℝ` with mean `μ = (∑ N)/|G|`:
`(∑_{y∈Y} ∑_{i∈I} N(y − i) − |Y|·|I|·μ)^2 ≤ |I|^2 · |Y| · ∑_z (N z − μ)^2`.
Relative form: `(L − main)^2 / main^2 ≤ |G| · δ / |Y|`, `δ = |G| ∑ N^2 / (∑ N)^2 − 1`
(the relative collision excess of the prefix end states).

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace PrefixSuffixBilinear

open Finset SuffixTransport LiftDigits

variable {d : ℕ → ℕ}

/-! ## The concatenation formula -/

/-- The block of `r_N` above position `S_j`: `k = ⌊r_N / 2^(S_j+1)⌋`. -/
def concatBlock (d : ℕ → ℕ) (j N : ℕ) : ℕ := leastRealizer d N / 2 ^ (S d j + 1)

theorem leastRealizer_eq_concat {j N : ℕ} (hd : ∀ i < N, 1 ≤ d i) (hj : j ≤ N) :
    leastRealizer d N = leastRealizer d j + 2 ^ (S d j + 1) * concatBlock d j N := by
  rw [concatBlock, ← leastRealizer_mod hd hj, Nat.mod_add_div]

/-- `k < 2^(S_v)` with `S_v = S_N − S_j = S (σ^j d) (N − j)`. -/
theorem concat_lt {j N : ℕ} (hj : j ≤ N) :
    concatBlock d j N < 2 ^ (S (shiftWord d j) (N - j)) := by
  rw [S_shiftWord d hj, concatBlock, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
  have h := leastRealizer_lt d N
  have hS := S_mono d hj
  calc leastRealizer d N < 2 ^ (S d N + 1) := h
    _ = 2 ^ (S d N - S d j + (S d j + 1)) := by congr 1; omega

/-- **Concatenation congruence.** `T^j(r_j) + 2·3^j·k ≡ r_v (mod 2^(S_v+1))`. -/
theorem concat_modEq {j N : ℕ} (hj1 : 1 ≤ j) (hd : ∀ i < N, 1 ≤ d i) (hj : j ≤ N) :
    orbit (leastRealizer d j) j + 2 * 3 ^ j * concatBlock d j N ≡
      leastRealizer (shiftWord d j) (N - j) [MOD 2 ^ (S (shiftWord d j) (N - j) + 1)] := by
  have hrest := (EOC.cylinder_restart_leastRealizer d j (concatBlock d j N) hj1
    fun i hi => hd i (by omega)).2
  rw [← leastRealizer_eq_concat hd hj] at hrest
  rw [← hrest]
  exact modEq_leastRealizer_of_realizes
    (realizes_shiftWord (leastRealizer_realizes_all d N hd) hj)

/-- **Uniqueness.** `k` is the only residue below `2^(S_v)` satisfying the congruence, so
`k ≡ ((r_v − T^j r_j)/2) · 3^{−j} (mod 2^(S_v))`. -/
theorem concat_unique {j N k : ℕ} (hj1 : 1 ≤ j) (hd : ∀ i < N, 1 ≤ d i) (hj : j ≤ N)
    (hk : k < 2 ^ (S (shiftWord d j) (N - j)))
    (hmod : orbit (leastRealizer d j) j + 2 * 3 ^ j * k ≡
      leastRealizer (shiftWord d j) (N - j) [MOD 2 ^ (S (shiftWord d j) (N - j) + 1)]) :
    k = concatBlock d j N := by
  set t := S (shiftWord d j) (N - j)
  have h1 := concat_modEq hj1 hd hj
  have h2 : 2 * (3 ^ j * k) ≡ 2 * (3 ^ j * concatBlock d j N) [MOD 2 * 2 ^ t] := by
    have := Nat.ModEq.add_left_cancel' _ (hmod.trans h1.symm)
    rw [pow_succ, mul_comm (2 ^ t) 2] at this
    simpa [mul_assoc] using this
  have h3 := Nat.ModEq.mul_left_cancel' (by norm_num) h2
  have hcop : Nat.gcd (2 ^ t) (3 ^ j) = 1 :=
    Nat.Coprime.pow t j (by norm_num : Nat.Coprime 2 3)
  exact (Nat.ModEq.cancel_left_of_coprime hcop h3).eq_of_lt_of_lt hk (concat_lt hj)

/-- **Cutoff transfer.** For `S_j < K`, `r_N < 2^K ↔ k < 2^(K − S_j − 1)`. -/
theorem lt_pow_iff_concat {j N K : ℕ} (hd : ∀ i < N, 1 ≤ d i) (hj : j ≤ N) (hK : S d j < K) :
    leastRealizer d N < 2 ^ K ↔ concatBlock d j N < 2 ^ (K - S d j - 1) := by
  rw [leastRealizer_eq_concat hd hj]
  have hlt := leastRealizer_lt d j
  have hpow : 2 ^ K = 2 ^ (S d j + 1) * 2 ^ (K - S d j - 1) := by
    rw [← pow_add]; congr 1; omega
  rw [hpow]
  constructor
  · intro h
    by_contra hc
    replace hc := not_lt.mp hc
    have : 2 ^ (S d j + 1) * 2 ^ (K - S d j - 1) ≤ 2 ^ (S d j + 1) * concatBlock d j N :=
      Nat.mul_le_mul_left _ hc
    omega
  · intro h
    have : 2 ^ (S d j + 1) * (concatBlock d j N + 1) ≤ 2 ^ (S d j + 1) * 2 ^ (K - S d j - 1) :=
      Nat.mul_le_mul_left _ h
    rw [mul_add, mul_one] at this
    omega

/-! ## The bilinear collision bound -/

section Bilinear

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- **Bilinear incidence bound (squared form).**  With `μ = (∑_z N z)/|G|`,
`(∑_{y∈Y} ∑_{i∈I} N(y − i) − |Y|·|I|·μ)^2 ≤ |I|^2 · |Y| · ∑_z (N z − μ)^2`. -/
theorem bilinear_incidence_sq_le (Y I : Finset G) (N : G → ℝ) :
    (∑ y ∈ Y, ∑ i ∈ I, N (y - i) -
        (Y.card : ℝ) * I.card * ((∑ z, N z) / Fintype.card G)) ^ 2 ≤
      (I.card : ℝ) ^ 2 * Y.card * ∑ z, (N z - (∑ z, N z) / Fintype.card G) ^ 2 := by
  set μ := (∑ z, N z) / Fintype.card G
  set g : G → ℝ := fun z => N z - μ
  set F : G → ℝ := fun z => ∑ i ∈ I, g (z - i)
  have hL : ∑ y ∈ Y, ∑ i ∈ I, N (y - i) - (Y.card : ℝ) * I.card * μ = ∑ y ∈ Y, F y := by
    simp only [F, g, sum_sub_distrib, sum_const, nsmul_eq_mul]
    ring
  rw [hL]
  -- Cauchy–Schwarz over `Y`
  have hCS1 : (∑ y ∈ Y, F y) ^ 2 ≤ (Y.card : ℝ) * ∑ y ∈ Y, F y ^ 2 := by
    have := sum_mul_sq_le_sq_mul_sq Y (fun _ => (1 : ℝ)) F
    simpa using this
  -- extend to all of `G`
  have hext : ∑ y ∈ Y, F y ^ 2 ≤ ∑ z, F z ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (subset_univ Y) fun _ _ _ => sq_nonneg _
  -- Cauchy–Schwarz over `I`, then translation invariance
  have hCS2 : ∀ z, F z ^ 2 ≤ (I.card : ℝ) * ∑ i ∈ I, g (z - i) ^ 2 := by
    intro z
    have := sum_mul_sq_le_sq_mul_sq I (fun _ => (1 : ℝ)) fun i => g (z - i)
    simpa [F] using this
  have htrans : ∀ i : G, ∑ z, g (z - i) ^ 2 = ∑ z, g z ^ 2 := fun i =>
    Fintype.sum_equiv (Equiv.subRight i) _ _ fun _ => rfl
  have hall : ∑ z, F z ^ 2 ≤ (I.card : ℝ) ^ 2 * ∑ z, g z ^ 2 := by
    calc ∑ z, F z ^ 2 ≤ ∑ z, (I.card : ℝ) * ∑ i ∈ I, g (z - i) ^ 2 :=
          sum_le_sum fun z _ => hCS2 z
      _ = (I.card : ℝ) * ∑ i ∈ I, ∑ z, g (z - i) ^ 2 := by rw [← mul_sum, sum_comm]
      _ = (I.card : ℝ) * ∑ _i ∈ I, ∑ z, g z ^ 2 := by rw [sum_congr rfl fun i _ => htrans i]
      _ = (I.card : ℝ) ^ 2 * ∑ z, g z ^ 2 := by rw [sum_const, nsmul_eq_mul]; ring
  have hY : (0 : ℝ) ≤ Y.card := Nat.cast_nonneg _
  calc (∑ y ∈ Y, F y) ^ 2 ≤ (Y.card : ℝ) * ∑ y ∈ Y, F y ^ 2 := hCS1
    _ ≤ (Y.card : ℝ) * ((I.card : ℝ) ^ 2 * ∑ z, g z ^ 2) :=
        mul_le_mul_of_nonneg_left (hext.trans hall) hY
    _ = (I.card : ℝ) ^ 2 * Y.card * ∑ z, g z ^ 2 := by ring

/-- **Bilinear incidence bound (constant form).** If `∑_z (N z − μ)^2 ≤ ε^2 · |Y| · μ^2` —
equivalently `|G| · δ ≤ ε^2 · |Y|`, where `δ = |G| ∑ N^2/(∑ N)^2 − 1` is the relative collision
excess of the weights — then the incidence count is at most `(1 + ε)` times its mean
`|Y| |I| μ`. -/
theorem bilinear_incidence_le (Y I : Finset G) (N : G → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hμ : 0 ≤ (∑ z, N z) / Fintype.card G)
    (hcoll : ∑ z, (N z - (∑ z, N z) / Fintype.card G) ^ 2 ≤
      ε ^ 2 * Y.card * ((∑ z, N z) / Fintype.card G) ^ 2) :
    ∑ y ∈ Y, ∑ i ∈ I, N (y - i) ≤
      (1 + ε) * ((Y.card : ℝ) * I.card * ((∑ z, N z) / Fintype.card G)) := by
  set μ := (∑ z, N z) / Fintype.card G
  set L := ∑ y ∈ Y, ∑ i ∈ I, N (y - i)
  set main := (Y.card : ℝ) * I.card * μ
  have hsq := bilinear_incidence_sq_le Y I N
  have hmain : 0 ≤ main := by positivity
  have hbound : (L - main) ^ 2 ≤ (ε * main) ^ 2 := by
    calc (L - main) ^ 2 ≤ (I.card : ℝ) ^ 2 * Y.card * ∑ z, (N z - μ) ^ 2 := hsq
      _ ≤ (I.card : ℝ) ^ 2 * Y.card * (ε ^ 2 * Y.card * μ ^ 2) := by gcongr
      _ = (ε * main) ^ 2 := by simp only [main]; ring
  have hεm : 0 ≤ ε * main := mul_nonneg hε hmain
  have := abs_le_of_sq_le_sq' hbound hεm
  linarith [this.2]

end Bilinear

end PrefixSuffixBilinear
end EOC
