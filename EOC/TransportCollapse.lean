import EOC.SuffixTransport

/-!
# Transport-deficit quantities for genuine realizers: finite, 2-adic-free core

Finite (integer) content of the identification between the *Transport Deficits* note's
past–future matching framework and the repository's realizer geometry.

Paper-to-repo dictionary (paper 1-indexed `d_1, d_2, …` = repo `d 0, d 1, …`):
paper `S_j` = `S d j`, paper `C_j` = `q d j`, paper `χ_j` (exposed coarse anchor, `ξ_j mod 2^{S_j}`)
= `coarseAnchor d j (S d j)`, paper `r(D_j)` = `leastRealizer d j`, orbit state = `orbit n j`.

The paper works in `ℤ₂` with `T_j` (past tail) and `A_{j,∞}(n)` (future target of `n`'s actual
continuation). A direct computation (carry identity, then `m → ∞`) gives, for a genuine
realizer `n`, `A_{j,∞}(n) = −3^{−j} · orbit n j` and `T_j = −3^{−j} · μ_j` with the integer
anchor state `μ_j = (3^j χ_j + C_j) / 2^{S_j}` (`anchorState`). Hence the paper's mismatch state is
`X_j(n) = T_j − A_{j,∞}(n) = 3^{−j}(orbit n j − μ_j) = n / 2^{S_j}`.
That `ℤ₂` step is **not** formalized here. What is formalized is its exact integer content:

* `chi_eq_mod` — the coarse anchor of a realized prefix is `n mod 2^{S_j}` for **every** realizer.
* `orbit_eq_anchorState_add` — **collapse identity**: `orbit n j = μ_j + 3^j · (n / 2^{S_j})`.
* `chi_succ_eq` — the paper's one-step anchor update `χ_{j+1} = χ_j + 2^{S_j} K_j` holds with the
  transport residue `K_j = (n / 2^{S_j}) mod 2^{d_{j+1}}` — a block of binary digits of `n`.
* `chi_add_eq_iff` — the anchor is unchanged over `m` steps (paper: `m` zero-deficit steps) iff
  `2^{S_{j+m} − S_j} ∣ n / 2^{S_j}`.
* `high_matching_iff` — `2^M ∣ n / 2^{S_j}` iff `n ≡ χ_j (mod 2^{S_j+M})`: the high-matching
  realizers of a prefix form one residue class.
* `div_two_pow_mod_two` / `two_dvd_div_iff` — the parity of `n / 2^{S_j}` is the same for every
  realizer and is fixed by the lift bit: even iff `leastRealizer d j < 2^{S_j}`.
* `matching_eq_pair_split` — when `leastRealizer d j < 2^{S_j}`, the valuation of `n / 2^{S_j}` is
  a `PairValuation` split depth: `v₂(n / 2^{S_j}) + S_j = S_{j+m} + min a b` for the first
  divergence of `n`'s word from the least realizer's own word.
* `carry_pair_factorization` / `carry_pair_valuation` — **finite future-target pair valuation**:
  words agreeing below `m` and differing at `m` have carries with `v₂(q_L(e) − q_L(e')) =
  S_m + min (e m) (e' m)` for every `L ≥ m + 2` (the paper's finite target is
  `A_{j,L} = 3^{−(j+L)} q_L` of the future word, so this is target separation up to a 2-adic unit).

This proves nothing about EOC, `CriticalCrossing`, or the Collatz conjecture.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace TransportCollapse

open PairValuation SuffixTransport

/-- The paper's exposed coarse anchor `χ_j`. -/
abbrev chi (d : ℕ → ℕ) (j : ℕ) : ℕ := coarseAnchor d j (S d j)

/-- The anchor state `μ_j = (3^j χ_j + q_j) / 2^{S_j}` (an exact division). -/
def anchorState (d : ℕ → ℕ) (j : ℕ) : ℕ := (3 ^ j * chi d j + q d j) / 2 ^ S d j

theorem anchorState_spec (d : ℕ → ℕ) (j : ℕ) :
    2 ^ S d j * anchorState d j = 3 ^ j * chi d j + q d j :=
  Nat.mul_div_cancel' (coarseAnchor_dvd d j (S d j))

private theorem realizes_le {d : ℕ → ℕ} {N t n : ℕ} (h : Realizes d N n) (ht : t ≤ N) :
    Realizes d t n :=
  ⟨h.1, fun i hi => h.2 i (by omega)⟩

theorem two_pow_dvd_carry {d : ℕ → ℕ} {j n : ℕ} (h : Realizes d j n) :
    2 ^ S d j ∣ 3 ^ j * n + q d j :=
  ⟨orbit n j, (realizes_carry h le_rfl).symm⟩

/-! ## The coarse anchor is the low part of every realizer -/

/-- `χ_j = n mod 2^{S_j}` for every realizer `n` of the length-`j` prefix. -/
theorem chi_eq_mod {d : ℕ → ℕ} {j n : ℕ} (h : Realizes d j n) :
    chi d j = n % 2 ^ S d j := by
  symm
  apply coarseAnchor_unique d j (S d j) (n % 2 ^ S d j) (Nat.mod_lt _ (by positivity))
  have hdiv := two_pow_dvd_carry h
  have hn : n = n % 2 ^ S d j + 2 ^ S d j * (n / 2 ^ S d j) := (Nat.mod_add_div n _).symm
  have hsplit : 3 ^ j * n + q d j
      = (3 ^ j * (n % 2 ^ S d j) + q d j) + 2 ^ S d j * (3 ^ j * (n / 2 ^ S d j)) := by
    conv_lhs => rw [hn]
    ring
  rw [hsplit] at hdiv
  exact (Nat.dvd_add_left (dvd_mul_right _ _)).mp hdiv

/-- **Collapse identity.** For every realizer `n` of the length-`j` prefix,
`orbit n j = μ_j + 3^j · (n / 2^{S_j})`. -/
theorem orbit_eq_anchorState_add {d : ℕ → ℕ} {j n : ℕ} (h : Realizes d j n) :
    orbit n j = anchorState d j + 3 ^ j * (n / 2 ^ S d j) := by
  have hc := realizes_carry h le_rfl
  have hμ := anchorState_spec d j
  have hn : n = chi d j + 2 ^ S d j * (n / 2 ^ S d j) := by
    rw [chi_eq_mod h]; exact (Nat.mod_add_div n _).symm
  apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ S d j)
  rw [hc, mul_add, hμ]
  conv_lhs => rw [hn]
  ring

/-! ## Transport residues are binary digits of the realizer -/

/-- Splitting `n mod 2^{S_j + B}` into the anchor and the next `B` bits of `n`. -/
theorem mod_split {d : ℕ → ℕ} {j n : ℕ} (h : Realizes d j n) (B : ℕ) :
    n % 2 ^ (S d j + B) = chi d j + 2 ^ S d j * (n / 2 ^ S d j % 2 ^ B) := by
  rw [chi_eq_mod h, pow_add]
  exact Nat.mod_mul

/-- One-step anchor update with the transport residue identified as `n`'s next `d_j` bits:
`χ_{j+1} = χ_j + 2^{S_j} · ((n / 2^{S_j}) mod 2^{d j})`. -/
theorem chi_succ_eq {d : ℕ → ℕ} {j n : ℕ} (h : Realizes d (j + 1) n) :
    chi d (j + 1) = chi d j + 2 ^ S d j * (n / 2 ^ S d j % 2 ^ d j) := by
  rw [chi_eq_mod h, show S d (j + 1) = S d j + d j from s_succ d j]
  exact mod_split (realizes_le h (by omega)) (d j)

/-- The anchor is unchanged across `m` steps iff the `S_{j+m} − S_j` bits of `n` above position
`S_j` all vanish (the paper's `m` consecutive zero-deficit steps). -/
theorem chi_add_eq_iff {d : ℕ → ℕ} {j m n : ℕ} (h : Realizes d (j + m) n) :
    chi d (j + m) = chi d j ↔ 2 ^ (S d (j + m) - S d j) ∣ n / 2 ^ S d j := by
  have hle : S d j ≤ S d (j + m) := S_le_S (by omega)
  have hsplit := mod_split (realizes_le h (show j ≤ j + m by omega)) (S d (j + m) - S d j)
  rw [Nat.add_sub_cancel' hle] at hsplit
  rw [chi_eq_mod h, hsplit, Nat.dvd_iff_mod_eq_zero]
  constructor
  · intro heq
    have h0 : 2 ^ S d j * (n / 2 ^ S d j % 2 ^ (S d (j + m) - S d j)) = 0 := by omega
    exact (Nat.mul_eq_zero.mp h0).resolve_left (by positivity)
  · intro h0
    rw [h0, mul_zero, add_zero]

/-- **High-matching class.** `2^M ∣ n / 2^{S_j}` iff `n ≡ χ_j (mod 2^{S_j + M})`. -/
theorem high_matching_iff {d : ℕ → ℕ} {j n : ℕ} (h : Realizes d j n) (M : ℕ) :
    2 ^ M ∣ n / 2 ^ S d j ↔ n % 2 ^ (S d j + M) = chi d j := by
  rw [mod_split h M, Nat.dvd_iff_mod_eq_zero]
  constructor
  · intro h0
    rw [h0, mul_zero, add_zero]
  · intro heq
    have h0 : 2 ^ S d j * (n / 2 ^ S d j % 2 ^ M) = 0 := by omega
    exact (Nat.mul_eq_zero.mp h0).resolve_left (by positivity)

/-! ## The lift bit fixes the parity of the high part for every realizer -/

theorem div_two_pow_mod_two {d : ℕ → ℕ} {j n : ℕ} (h : Realizes d j n) :
    n / 2 ^ S d j % 2 = leastRealizer d j / 2 ^ S d j := by
  rw [← Nat.mod_mul_right_div_self, ← pow_succ, mod_eq_leastRealizer_of_realizes h]

/-- `n / 2^{S_j}` is even for one (equivalently every) realizer iff the least realizer lies below
`2^{S_j}` (paper: lift bit `β_j = 1`). -/
theorem two_dvd_div_iff {d : ℕ → ℕ} {j n : ℕ} (h : Realizes d j n) :
    2 ∣ n / 2 ^ S d j ↔ leastRealizer d j < 2 ^ S d j := by
  rw [Nat.dvd_iff_mod_eq_zero, div_two_pow_mod_two h, Nat.div_eq_zero_iff]
  constructor
  · rintro (h0 | hlt)
    · exact absurd h0 (by positivity)
    · exact hlt
  · exact Or.inr

/-! ## Matching precision as a pair split depth -/

/-- When the least realizer lies below `2^{S_j}`, it equals the anchor, and the 2-adic valuation of
`n / 2^{S_j}` is a `PairValuation` split depth against the least realizer's own word: if the words
of `r = leastRealizer d j` and `n` agree below `j + m` and differ at `j + m`, then
`v₂(n / 2^{S_j}) + S_j = S_{j+m} + min (a (orbit r (j+m))) (a (orbit n (j+m)))`. -/
theorem matching_eq_pair_split {d : ℕ → ℕ} {j m n : ℕ} (hn : Realizes d j n)
    (hβ : leastRealizer d j < 2 ^ S d j)
    (hagree : ∀ i < j + m, a (orbit (leastRealizer d j) i) = a (orbit n i))
    (hne : a (orbit (leastRealizer d j) (j + m)) ≠ a (orbit n (j + m))) :
    padicValInt 2 ((n / 2 ^ S d j : ℕ) : ℤ) + S d j
      = s (fun i => a (orbit (leastRealizer d j) i)) (j + m)
        + min (a (orbit (leastRealizer d j) (j + m))) (a (orbit n (j + m))) := by
  have hr : leastRealizer d j = n % 2 ^ S d j := by
    rcases leastRealizer_eq_or_eq_add d j with h1 | h1
    · rw [h1]; exact chi_eq_mod hn
    · omega
  have hdiff : (n : ℤ) - leastRealizer d j = 2 ^ S d j * ((n / 2 ^ S d j : ℕ) : ℤ) := by
    have := Nat.mod_add_div n (2 ^ S d j)
    rw [hr]
    have hz : ((n % 2 ^ S d j : ℕ) : ℤ) + 2 ^ S d j * ((n / 2 ^ S d j : ℕ) : ℤ) = n := by
      exact_mod_cast this
    linarith
  have hX : n / 2 ^ S d j ≠ 0 := by
    intro h0
    apply hne
    have : n = leastRealizer d j := by
      have := Nat.mod_add_div n (2 ^ S d j)
      rw [h0, mul_zero, add_zero] at this
      rw [hr, this]
    rw [this]
  have hv := orbit_pair_valuation (leastRealizer d j) n (j + m) hagree hne
  rw [hdiff, padicValInt.mul (by positivity) (by exact_mod_cast hX)] at hv
  have h2 : padicValInt 2 ((2 : ℤ) ^ S d j) = S d j := by
    have := padicValInt_two_pow_mul_odd (S d j) (Q := 1) odd_one
    rwa [mul_one] at this
  rw [h2] at hv
  omega

/-! ## Finite future-target (carry) pair valuation -/

/-- Words agreeing below `m` and differing at `m` have carries `q_L` separated by exactly
`2^{S_m + min (e m) (e' m)}` times an odd integer, for every `L ≥ m + 2`, provided the digits used
are positive. -/
theorem carry_pair_factorization (e e' : ℕ → ℕ) (m : ℕ)
    (hagree : ∀ i < m, e i = e' i) (hne : e m ≠ e' m) :
    ∀ t, (∀ i < m + 2 + t, 1 ≤ e i) → (∀ i < m + 2 + t, 1 ≤ e' i) →
      ∃ Q : ℤ, Odd Q ∧
        (q e (m + 2 + t) : ℤ) - q e' (m + 2 + t) = 2 ^ (S e m + min (e m) (e' m)) * Q := by
  have hq1 : q e (m + 1) = q e' (m + 1) := q_succ_eq_of_agree hagree
  have hs : s e m = s e' m := s_eq_of_prefix_agree hagree
  intro t
  induction t with
  | zero =>
    intro _ _
    refine ⟨2 ^ (e m - min (e m) (e' m)) - 2 ^ (e' m - min (e m) (e' m)), ?_, ?_⟩
    · have h := odd_two_pow_sub_two_pow (α := e' m) (β := e m) (y := 1) (y' := 1)
        odd_one odd_one (Ne.symm hne)
      rw [min_comm] at h
      simpa using h
    · rw [show m + 2 + 0 = (m + 1) + 1 from rfl, q_succ e (m + 1), q_succ e' (m + 1), hq1,
        s_succ e m, s_succ e' m, ← hs]
      push_cast
      have hpa : (2 : ℤ) ^ (s e m + e m)
          = 2 ^ (S e m + min (e m) (e' m)) * 2 ^ (e m - min (e m) (e' m)) := by
        rw [← pow_add]; congr 1; unfold S; omega
      have hpb : (2 : ℤ) ^ (s e m + e' m)
          = 2 ^ (S e m + min (e m) (e' m)) * 2 ^ (e' m - min (e m) (e' m)) := by
        rw [← pow_add]; congr 1; unfold S; omega
      rw [hpa, hpb]
      ring
  | succ t ih =>
    intro hp hp'
    obtain ⟨Q, hQ, hΔ⟩ := ih (fun i hi => hp i (by omega)) (fun i hi => hp' i (by omega))
    set V := S e m + min (e m) (e' m) with hV
    have hm2 : s e (m + 2) = s e m + e m + e (m + 1) := by rw [s_succ, s_succ]
    have hm2' : s e' (m + 2) = s e' m + e' m + e' (m + 1) := by rw [s_succ, s_succ]
    have hle : S e (m + 2) ≤ S e (m + 2 + t) := S_le_S (by omega)
    have hle' : S e' (m + 2) ≤ S e' (m + 2 + t) := S_le_S (by omega)
    have he1 : 1 ≤ e (m + 1) := hp (m + 1) (by omega)
    have he1' : 1 ≤ e' (m + 1) := hp' (m + 1) (by omega)
    have hsL : V + 1 ≤ s e (m + 2 + t) := by
      unfold S at hle hV; rw [hV]; omega
    have hsL' : V + 1 ≤ s e' (m + 2 + t) := by
      unfold S at hle' hV; rw [hV]; omega
    refine ⟨3 * Q + 2 * (2 ^ (s e (m + 2 + t) - (V + 1)) - 2 ^ (s e' (m + 2 + t) - (V + 1))),
      ?_, ?_⟩
    · have h3Q : Odd (3 * Q) := Int.odd_mul.mpr ⟨by decide, hQ⟩
      exact h3Q.add_even (even_two_mul _)
    · rw [show m + 2 + (t + 1) = (m + 2 + t) + 1 by omega, q_succ e (m + 2 + t),
        q_succ e' (m + 2 + t)]
      push_cast
      have hpa : (2 : ℤ) ^ s e (m + 2 + t) = 2 ^ V * (2 * 2 ^ (s e (m + 2 + t) - (V + 1))) := by
        rw [← pow_succ', ← pow_add]; congr 1; omega
      have hpb : (2 : ℤ) ^ s e' (m + 2 + t)
          = 2 ^ V * (2 * 2 ^ (s e' (m + 2 + t) - (V + 1))) := by
        rw [← pow_succ', ← pow_add]; congr 1; omega
      linear_combination 3 * hΔ + hpa - hpb

/-- **Finite future-target pair valuation.** For words agreeing below `m`, differing at `m`, with
positive digits below `L ≥ m + 2`: `v₂(q_L(e) − q_L(e')) = S_m + min (e m) (e' m)`. -/
theorem carry_pair_valuation (e e' : ℕ → ℕ) (m L : ℕ) (hL : m + 2 ≤ L)
    (hagree : ∀ i < m, e i = e' i) (hne : e m ≠ e' m)
    (hpos : ∀ i < L, 1 ≤ e i) (hpos' : ∀ i < L, 1 ≤ e' i) :
    padicValInt 2 ((q e L : ℤ) - q e' L) = S e m + min (e m) (e' m) := by
  obtain ⟨t, rfl⟩ : ∃ t, L = m + 2 + t := ⟨L - (m + 2), by omega⟩
  obtain ⟨Q, hQ, hfac⟩ := carry_pair_factorization e e' m hagree hne t hpos hpos'
  rw [hfac]
  exact padicValInt_two_pow_mul_odd _ hQ

end TransportCollapse
end EOC
