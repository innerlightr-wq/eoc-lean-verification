import EOC.TaoLike.Cylinder
import EOC.Confinement

/-!
# Exact 2-adic separation of realizers at the first differing digit

Two valuation words `d`, `e` that agree on indices `i < k` and first differ at index `k`
(repository 0-indexing: `a := d k`, `b := e k`, `S_k := S d k = ∑_{i<k} d i`) have realizers
whose difference has 2-adic valuation **exactly** `S_k + min a b`.

The mechanism is the carry identity `2^{S_j} m_j = 3^j m_0 + q_j` (`iter_carry_eq`, `Carry.lean`)
at depth `k+1`: the carry `q_{k+1}` only reads digits `< k` (`q_succ_eq_of_agree`), so it is
*identical* for both words and cancels on subtraction, leaving the exact pair carry identity

  `3^{k+1} (x' − x) = 2^{S_k} (2^b m'_{k+1} − 2^a m_{k+1})`,

where `m_{k+1}`, `m'_{k+1}` are the (always odd) orbit values after step `k+1`. For `a ≠ b` the
bracket is `2^{min a b}` times an odd number, and `3^{k+1}` is a 2-adic unit.

Main results:

* `orbit_pair_carry_identity` — the exact pair carry identity above, for **any** two natural
  seeds whose actual valuation words agree below `k` (no parity, minimality, confinement,
  length, or terminal-sum hypothesis).
* `orbit_pair_factorization` — `x' − x = 2^{S_k + min a b} · Q` with `Q` odd, and the odd
  cofactor identified exactly: `3^{k+1} Q = 2^{b − min a b} m'_{k+1} − 2^{a − min a b} m_{k+1}`.
* `orbit_pair_valuation` — `v₂(x' − x) = S_k + min a b` (as `padicValInt 2`).
* `realizes_pair_factorization` / `realizes_pair_valuation` / `realizes_pair_quotient_valuation`
  — the same for seeds realizing two prescribed words through step `k+1`; the quotient form is
  `2^{S_k+1} ∣ x' − x` and `v₂((x' − x) / 2^{S_k+1}) = min a b − 1`.
* `leastRealizer_pair_factorization` / `leastRealizer_pair_valuation` /
  `leastRealizer_pair_quotient_valuation` — the canonical-realizer corollaries, for words of
  **arbitrary, possibly different** lengths `N, M > k` and arbitrary terminal sums.

This sharpens `leastRealizer_succ_modEq_of_agree` (`RealizerLift.lean`), which gives only the
lower bound `v₂ ≥ S_k + 1`, to an exact value. It is exact arithmetic of realizer classes; it
says nothing about EOC, `CriticalCrossing`, or the Collatz conjecture.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace PairValuation

/-! ## Prefix-agreement bookkeeping -/

theorem s_eq_of_prefix_agree {d e : ℕ → ℕ} {k : ℕ} (hagree : ∀ i < k, d i = e i) :
    s d k = s e k := by
  unfold s
  exact Finset.sum_congr rfl (fun i hi => hagree i (Finset.mem_range.mp hi))

theorem q_eq_of_prefix_agree {d e : ℕ → ℕ} :
    ∀ k, (∀ i < k, d i = e i) → q d k = q e k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ n ih =>
    intro hagree
    have hagree' : ∀ i < n, d i = e i := fun i hi => hagree i (by omega)
    rw [q_succ, q_succ, ih hagree', s_eq_of_prefix_agree hagree']

/-- **The carry at depth `k+1` does not read digit `k`.** `q _ (k+1) = 3 q_k + 2^{s_k}` only
involves digits `< k`, so two words agreeing below `k` have equal carries at depth `k+1`,
whatever their digits at index `k`. -/
theorem q_succ_eq_of_agree {d e : ℕ → ℕ} {k : ℕ} (hagree : ∀ i < k, d i = e i) :
    q d (k + 1) = q e (k + 1) := by
  rw [q_succ, q_succ, q_eq_of_prefix_agree k hagree, s_eq_of_prefix_agree hagree]

/-! ## The carry identity along an actual orbit (no parity hypothesis) -/

/-- The carry identity for a seed's own valuation word: `2^{s_j} · orbit x j = 3^j x + q_j`.
Valid for every natural `x` (the exact divisibility `2^{a m} ∣ 3m + 1` holds by definition). -/
theorem orbit_carry (x j : ℕ) :
    2 ^ s (fun i => a (orbit x i)) j * orbit x j
      = 3 ^ j * x + q (fun i => a (orbit x i)) j := by
  have hbridge := orbit_eq_iter_of_orbit_valuation (fun i => a (orbit x i)) j x
    (fun _ _ => rfl)
  have hdvd : ∀ i < j, 2 ^ (fun i => a (orbit x i)) i
      ∣ (3 * iter (fun i => a (orbit x i)) x i + 1) := by
    intro i hi
    rw [← hbridge i hi.le]
    exact pow_padicValNat_dvd
  have h := iter_carry_eq (fun i => a (orbit x i)) x j hdvd j le_rfl
  rwa [← hbridge j le_rfl] at h

/-! ## A pure 2-adic lemma -/

/-- For odd `y, y'` and `α ≠ β`, the number `2^{β − min α β} y' − 2^{α − min α β} y` is odd:
exactly one of the two exponents is `0`. -/
theorem odd_two_pow_sub_two_pow {α β : ℕ} {y y' : ℤ} (hy : Odd y) (hy' : Odd y')
    (hne : α ≠ β) :
    Odd ((2 : ℤ) ^ (β - min α β) * y' - 2 ^ (α - min α β) * y) := by
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have hmin : min α β = α := min_eq_left h.le
    rw [hmin, Nat.sub_self, pow_zero, one_mul]
    have heven : Even ((2 : ℤ) ^ (β - α) * y') := by
      obtain ⟨t, ht⟩ : ∃ t, β - α = t + 1 := ⟨β - α - 1, by omega⟩
      rw [ht, pow_succ]
      exact ⟨2 ^ t * y', by ring⟩
    exact heven.sub_odd hy
  · have hmin : min α β = β := min_eq_right h.le
    rw [hmin, Nat.sub_self, pow_zero, one_mul]
    have heven : Even ((2 : ℤ) ^ (α - β) * y) := by
      obtain ⟨t, ht⟩ : ∃ t, α - β = t + 1 := ⟨α - β - 1, by omega⟩
      rw [ht, pow_succ]
      exact ⟨2 ^ t * y, by ring⟩
    exact hy'.sub_even heven

/-- `v₂(2^n · Q) = n` for odd `Q`. -/
theorem padicValInt_two_pow_mul_odd (n : ℕ) {Q : ℤ} (hQ : Odd Q) :
    padicValInt 2 ((2 : ℤ) ^ n * Q) = n := by
  have hQ0 : Q ≠ 0 := by
    have h := Int.odd_iff.mp hQ
    rintro rfl
    simp at h
  have hpow : ((2 : ℤ) ^ n) = ((2 ^ n : ℕ) : ℤ) := by push_cast; rfl
  have hQv : padicValInt 2 Q = 0 := by
    apply padicValInt.eq_zero_of_not_dvd
    intro h2
    exact (Int.not_even_iff_odd.mpr hQ) (even_iff_two_dvd.mpr (by exact_mod_cast h2))
  rw [padicValInt.mul (by positivity) hQ0, hQv, add_zero, hpow, padicValInt.of_nat,
    padicValNat.prime_pow]

/-! ## Orbit form: arbitrary natural seeds -/

/-- **Exact pair carry identity.** If the actual valuation words of `x` and `x'` agree below
`k`, then
`3^{k+1} (x' − x) = 2^{S_k} (2^{b} · orbit x' (k+1) − 2^{a} · orbit x (k+1))`
with `a = a (orbit x k)`, `b = a (orbit x' k)`. No parity, minimality, or distinctness
hypothesis. -/
theorem orbit_pair_carry_identity (x x' k : ℕ)
    (hagree : ∀ j < k, a (orbit x j) = a (orbit x' j)) :
    (3 : ℤ) ^ (k + 1) * ((x' : ℤ) - x)
      = 2 ^ s (fun i => a (orbit x i)) k
        * (2 ^ a (orbit x' k) * (orbit x' (k + 1) : ℤ)
          - 2 ^ a (orbit x k) * (orbit x (k + 1) : ℤ)) := by
  have h1 := orbit_carry x (k + 1)
  have h2 := orbit_carry x' (k + 1)
  have hq : q (fun i => a (orbit x i)) (k + 1) = q (fun i => a (orbit x' i)) (k + 1) :=
    q_succ_eq_of_agree hagree
  have hs : s (fun i => a (orbit x i)) k = s (fun i => a (orbit x' i)) k :=
    s_eq_of_prefix_agree hagree
  rw [s_succ, pow_add] at h1 h2
  rw [hq] at h1
  rw [← hs] at h2
  have h1' : ((2 : ℤ) ^ s (fun i => a (orbit x i)) k * 2 ^ a (orbit x k)
      * (orbit x (k + 1) : ℤ))
      = 3 ^ (k + 1) * (x : ℤ) + (q (fun i => a (orbit x' i)) (k + 1) : ℤ) := by
    exact_mod_cast h1
  have h2' : ((2 : ℤ) ^ s (fun i => a (orbit x i)) k * 2 ^ a (orbit x' k)
      * (orbit x' (k + 1) : ℤ))
      = 3 ^ (k + 1) * (x' : ℤ) + (q (fun i => a (orbit x' i)) (k + 1) : ℤ) := by
    exact_mod_cast h2
  linear_combination h1' - h2'

/-- **Structural factorization (orbit form).** If the actual valuation words of `x`, `x'`
agree below `k` and differ at `k` (`a ≠ b`), then `x' − x = 2^{S_k + min a b} · Q` for an odd
integer `Q`, which is determined exactly by the orbit values after step `k+1`:
`3^{k+1} Q = 2^{b − min a b} · orbit x' (k+1) − 2^{a − min a b} · orbit x (k+1)`. -/
theorem orbit_pair_factorization (x x' k : ℕ)
    (hagree : ∀ j < k, a (orbit x j) = a (orbit x' j))
    (hne : a (orbit x k) ≠ a (orbit x' k)) :
    ∃ Q : ℤ, Odd Q ∧
      (x' : ℤ) - x
        = 2 ^ (s (fun i => a (orbit x i)) k + min (a (orbit x k)) (a (orbit x' k))) * Q ∧
      (3 : ℤ) ^ (k + 1) * Q
        = 2 ^ (a (orbit x' k) - min (a (orbit x k)) (a (orbit x' k))) * (orbit x' (k + 1) : ℤ)
          - 2 ^ (a (orbit x k) - min (a (orbit x k)) (a (orbit x' k)))
            * (orbit x (k + 1) : ℤ) := by
  set A := a (orbit x k) with hA
  set B := a (orbit x' k) with hB
  set Sk := s (fun i => a (orbit x i)) k with hSk
  set m := min A B with hm
  set Q0 : ℤ := 2 ^ (B - m) * (orbit x' (k + 1) : ℤ) - 2 ^ (A - m) * (orbit x (k + 1) : ℤ)
    with hQ0
  have hy : Odd ((orbit x (k + 1) : ℕ) : ℤ) := by
    rw [orbit_succ]; exact (T_odd _).natCast
  have hy' : Odd ((orbit x' (k + 1) : ℕ) : ℤ) := by
    rw [orbit_succ]; exact (T_odd _).natCast
  have hQ0odd : Odd Q0 := odd_two_pow_sub_two_pow hy hy' hne
  -- the bracket of the pair carry identity is `2^m · Q0`
  have hbracket : (2 : ℤ) ^ B * (orbit x' (k + 1) : ℤ) - 2 ^ A * (orbit x (k + 1) : ℤ)
      = 2 ^ m * Q0 := by
    have hAm : A = m + (A - m) := by omega
    have hBm : B = m + (B - m) := by omega
    rw [hQ0]
    conv_lhs => rw [hBm, hAm]
    rw [pow_add, pow_add]
    ring
  have hid := orbit_pair_carry_identity x x' k hagree
  rw [← hA, ← hB, ← hSk, hbracket, ← mul_assoc, ← pow_add] at hid
  -- `3^{k+1}` is coprime to `2^{S_k+m}`, so it divides `Q0`
  have hcop : IsCoprime ((3 : ℤ) ^ (k + 1)) ((2 : ℤ) ^ (Sk + m)) := by
    apply IsCoprime.pow
    rw [Int.isCoprime_iff_gcd_eq_one]
    rfl
  have hdvd : (3 : ℤ) ^ (k + 1) ∣ Q0 :=
    hcop.dvd_of_dvd_mul_left ⟨(x' : ℤ) - x, hid.symm⟩
  obtain ⟨Q, hQ⟩ := hdvd
  refine ⟨Q, ?_, ?_, ?_⟩
  · rw [hQ] at hQ0odd
    exact (Int.odd_mul.mp hQ0odd).2
  · have h3 : (3 : ℤ) ^ (k + 1) ≠ 0 := by positivity
    apply mul_left_cancel₀ h3
    rw [hid, hQ]
    ring
  · exact hQ.symm

/-- **Exact pair valuation (orbit form).** If the actual valuation words of two natural seeds
`x`, `x'` agree below `k` and differ at `k`, then `v₂(x' − x) = S_k + min a b`. No parity
hypothesis on the seeds. -/
theorem orbit_pair_valuation (x x' k : ℕ)
    (hagree : ∀ j < k, a (orbit x j) = a (orbit x' j))
    (hne : a (orbit x k) ≠ a (orbit x' k)) :
    padicValInt 2 ((x' : ℤ) - x)
      = s (fun i => a (orbit x i)) k + min (a (orbit x k)) (a (orbit x' k)) := by
  obtain ⟨Q, hQodd, hfac, -⟩ := orbit_pair_factorization x x' k hagree hne
  rw [hfac]
  exact padicValInt_two_pow_mul_odd _ hQodd

/-! ## Word form: seeds realizing two prescribed words -/

/-- Transfer of realization data to the orbit words. -/
private theorem orbit_data_of_realizes {d e : ℕ → ℕ} {k x x' : ℕ}
    (hx : Realizes d (k + 1) x) (hx' : Realizes e (k + 1) x')
    (hagree : ∀ i < k, d i = e i) :
    (∀ j < k, a (orbit x j) = a (orbit x' j)) ∧
    s (fun i => a (orbit x i)) k = S d k ∧
    a (orbit x k) = d k ∧ a (orbit x' k) = e k := by
  refine ⟨fun j hj => ?_, ?_, hx.2 k (by omega), hx'.2 k (by omega)⟩
  · rw [hx.2 j (by omega), hx'.2 j (by omega), hagree j hj]
  · exact s_eq_of_prefix_agree (fun i hi => hx.2 i (by omega))

/-- **Structural factorization (word form).** Seeds `x`, `x'` realizing words `d`, `e` through
step `k+1`, where `d`, `e` agree below `k` and `d k ≠ e k`, satisfy
`x' − x = 2^{S_k + min (d k) (e k)} · Q` with `Q` odd and
`3^{k+1} Q = 2^{e k − min} · orbit x' (k+1) − 2^{d k − min} · orbit x (k+1)`. -/
theorem realizes_pair_factorization (d e : ℕ → ℕ) (k x x' : ℕ)
    (hx : Realizes d (k + 1) x) (hx' : Realizes e (k + 1) x')
    (hagree : ∀ i < k, d i = e i) (hne : d k ≠ e k) :
    ∃ Q : ℤ, Odd Q ∧
      (x' : ℤ) - x = 2 ^ (S d k + min (d k) (e k)) * Q ∧
      (3 : ℤ) ^ (k + 1) * Q
        = 2 ^ (e k - min (d k) (e k)) * (orbit x' (k + 1) : ℤ)
          - 2 ^ (d k - min (d k) (e k)) * (orbit x (k + 1) : ℤ) := by
  obtain ⟨hag, hs, hak, hak'⟩ := orbit_data_of_realizes hx hx' hagree
  have h := orbit_pair_factorization x x' k hag (by rw [hak, hak']; exact hne)
  rwa [hs, hak, hak'] at h

/-- **Exact pair valuation (word form).** -/
theorem realizes_pair_valuation (d e : ℕ → ℕ) (k x x' : ℕ)
    (hx : Realizes d (k + 1) x) (hx' : Realizes e (k + 1) x')
    (hagree : ∀ i < k, d i = e i) (hne : d k ≠ e k) :
    padicValInt 2 ((x' : ℤ) - x) = S d k + min (d k) (e k) := by
  obtain ⟨Q, hQodd, hfac, -⟩ := realizes_pair_factorization d e k x x' hx hx' hagree hne
  rw [hfac]
  exact padicValInt_two_pow_mul_odd _ hQodd

/-- **Normalized quotient (word form).** Under the hypotheses of `realizes_pair_valuation`,
`2^{S_k+1} ∣ x' − x` and the quotient has `v₂ = min (d k) (e k) − 1`. Here `min ≥ 1` is not
assumed: it follows from `Realizes` (realizing seeds are odd, so every realized digit is `≥ 1`). -/
theorem realizes_pair_quotient_valuation (d e : ℕ → ℕ) (k x x' : ℕ)
    (hx : Realizes d (k + 1) x) (hx' : Realizes e (k + 1) x')
    (hagree : ∀ i < k, d i = e i) (hne : d k ≠ e k) :
    (2 : ℤ) ^ (S d k + 1) ∣ ((x' : ℤ) - x) ∧
    padicValInt 2 (((x' : ℤ) - x) / 2 ^ (S d k + 1)) = min (d k) (e k) - 1 := by
  obtain ⟨Q, hQodd, hfac, -⟩ := realizes_pair_factorization d e k x x' hx hx' hagree hne
  have hdk : 1 ≤ d k := by
    rw [← hx.2 k (by omega)]; exact a_pos_of_odd (odd_orbit hx.1 k)
  have hek : 1 ≤ e k := by
    rw [← hx'.2 k (by omega)]; exact a_pos_of_odd (odd_orbit hx'.1 k)
  have hm : 1 ≤ min (d k) (e k) := le_min hdk hek
  have hsplit : (x' : ℤ) - x = 2 ^ (S d k + 1) * (2 ^ (min (d k) (e k) - 1) * Q) := by
    rw [hfac, ← mul_assoc, ← pow_add]
    congr 2
    omega
  refine ⟨⟨_, hsplit⟩, ?_⟩
  rw [hsplit, Int.mul_ediv_cancel_left _ (by positivity)]
  exact padicValInt_two_pow_mul_odd _ hQodd

/-! ## Canonical least realizers -/

private theorem realizes_restrict {d : ℕ → ℕ} {N t x : ℕ} (h : Realizes d N x) (ht : t ≤ N) :
    Realizes d t x :=
  ⟨h.1, fun j hj => h.2 j (by omega)⟩

/-- **Structural factorization for least realizers.** Positive words `d` (length `N`) and `e`
(length `M`) agreeing below `k` and differing at `k`, with `k < N` and `k < M`. Lengths and
terminal sums `S d N`, `S e M` are arbitrary and need not match. -/
theorem leastRealizer_pair_factorization (d e : ℕ → ℕ) (N M k : ℕ) (hkN : k < N) (hkM : k < M)
    (hd_pos : ∀ i < N, 1 ≤ d i) (he_pos : ∀ i < M, 1 ≤ e i)
    (hagree : ∀ i < k, d i = e i) (hne : d k ≠ e k) :
    ∃ Q : ℤ, Odd Q ∧
      (leastRealizer e M : ℤ) - leastRealizer d N = 2 ^ (S d k + min (d k) (e k)) * Q ∧
      (3 : ℤ) ^ (k + 1) * Q
        = 2 ^ (e k - min (d k) (e k)) * (orbit (leastRealizer e M) (k + 1) : ℤ)
          - 2 ^ (d k - min (d k) (e k)) * (orbit (leastRealizer d N) (k + 1) : ℤ) :=
  realizes_pair_factorization d e k _ _
    (realizes_restrict (leastRealizer_realizes d N (by omega) hd_pos) hkN)
    (realizes_restrict (leastRealizer_realizes e M (by omega) he_pos) hkM) hagree hne

/-- **Exact pair valuation for least realizers:**
`v₂(r(E) − r(D)) = S_k + min (d k) (e k)`. -/
theorem leastRealizer_pair_valuation (d e : ℕ → ℕ) (N M k : ℕ) (hkN : k < N) (hkM : k < M)
    (hd_pos : ∀ i < N, 1 ≤ d i) (he_pos : ∀ i < M, 1 ≤ e i)
    (hagree : ∀ i < k, d i = e i) (hne : d k ≠ e k) :
    padicValInt 2 ((leastRealizer e M : ℤ) - leastRealizer d N) = S d k + min (d k) (e k) :=
  realizes_pair_valuation d e k _ _
    (realizes_restrict (leastRealizer_realizes d N (by omega) hd_pos) hkN)
    (realizes_restrict (leastRealizer_realizes e M (by omega) he_pos) hkM) hagree hne

/-- **Normalized quotient for least realizers:** `2^{S_k+1} ∣ r(E) − r(D)` and
`v₂((r(E) − r(D)) / 2^{S_k+1}) = min (d k) (e k) − 1`. -/
theorem leastRealizer_pair_quotient_valuation (d e : ℕ → ℕ) (N M k : ℕ) (hkN : k < N)
    (hkM : k < M) (hd_pos : ∀ i < N, 1 ≤ d i) (he_pos : ∀ i < M, 1 ≤ e i)
    (hagree : ∀ i < k, d i = e i) (hne : d k ≠ e k) :
    (2 : ℤ) ^ (S d k + 1) ∣ ((leastRealizer e M : ℤ) - leastRealizer d N) ∧
    padicValInt 2 (((leastRealizer e M : ℤ) - leastRealizer d N) / 2 ^ (S d k + 1))
      = min (d k) (e k) - 1 :=
  realizes_pair_quotient_valuation d e k _ _
    (realizes_restrict (leastRealizer_realizes d N (by omega) hd_pos) hkN)
    (realizes_restrict (leastRealizer_realizes e M (by omega) he_pos) hkM) hagree hne

end PairValuation
end EOC
