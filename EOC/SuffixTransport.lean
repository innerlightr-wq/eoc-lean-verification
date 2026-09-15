import EOC.PairValuation
import EOC.Periodic

/-!
# Suffix transport of realizers, and the pair/suffix cofactor law

For a word `d` and `t ≤ N`, write `shiftWord d t := fun i => d (t + i)` (the suffix `σ^t d`,
repository 0-indexing). If `x` realizes `d` for `N` steps, then its `t`-th orbit value realizes
the suffix `σ^t d` for `N − t` steps, and therefore lies in the suffix's canonical realizer class:

  `orbit x t ≡ leastRealizer (σ^t d) (N − t)  [MOD 2^(S_N − S_t + 1)]`.

No power of `3` or affine factor appears: both sides realize the *same* word `σ^t d`, and any two
realizers of one positive word agree modulo `2^(S+1)` (`modEq_leastRealizer_of_realizes`, a direct
consequence of `realizerCongruence`). The seed-to-state map itself is the carry identity
`2^{S_t} · orbit x t = 3^t x + q_t` (`realizes_carry`). Neither minimality of `x`, confinement,
nor any terminal-sum condition is used. Positivity of the digits enters through
`realizerCongruence`, but for realizer-form statements it is automatic (`realizes_pos`); it is an
explicit hypothesis only where a least realizer must be shown to realize its word.

Main results:

* `realizes_shiftWord` — the `t`-th orbit value realizes the suffix word for `N − t` steps.
* `modEq_leastRealizer_of_realizes` / `mod_eq_leastRealizer_of_realizes` — every realizer of a
  positive word is congruent to (has residue equal to) the least realizer mod `2^(S_N+1)`.
* `realizes_carry` — `2^{S_t} · orbit x t = 3^t x + q_t` for realizers of `d`, `t ≤ N`.
* `suffix_transport` / `suffix_transport_structure` — the congruence above, and the exact
  decomposition `orbit x t = leastRealizer (σ^t d) (N−t) + 2^(S_N−S_t+1) · j` together with the
  carry identity.
* `leastRealizer_suffix_transport` / `leastRealizer_suffix_transport_mod` — the canonical case
  `x = leastRealizer d N` (any `N`, including `N = 0`).
* `pair_split_depth_shift` — at every shared step `t ≤ k`, the two orbit states are separated
  2-adically by exactly `S_k − S_t + min a b`: the split depth is consumed by `d t` per shared step.
* `pair_suffix_cofactor` — combining with `EOC.PairValuation`: for words first differing at
  index `k` (`a = d k`, `b = e k`, `m = min a b`, `τ = S_k + m`), the odd cofactor `Q` of
  `r(E) − r(D) = 2^τ Q` satisfies
  `3^{k+1} Q ≡ 2^{b−m} · r(σ^{k+1}E) − 2^{a−m} · r(σ^{k+1}D)`
  modulo `2^(min(S_N(D), S_M(E)) − τ + 1)`.
  The right-hand side and the modulus involve the common prefix **only through its length `k`**.

This is exact arithmetic of realizer classes; it proves nothing about EOC, `CriticalCrossing`,
or the Collatz conjecture.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace SuffixTransport

open PairValuation

/-- The suffix word `σ^t d`: drop the first `t` digits. -/
def shiftWord (d : ℕ → ℕ) (t : ℕ) : ℕ → ℕ := fun i => d (t + i)

/-! ## Valuation sums of suffixes -/

theorem s_add_shiftWord (d : ℕ → ℕ) (t : ℕ) :
    ∀ n, s d (t + n) = s d t + s (shiftWord d t) n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show t + (n + 1) = (t + n) + 1 from rfl, s_succ, ih, s_succ]
    simp only [shiftWord]
    ring

theorem S_shiftWord (d : ℕ → ℕ) {t N : ℕ} (ht : t ≤ N) :
    S (shiftWord d t) (N - t) = S d N - S d t := by
  have h := s_add_shiftWord d t (N - t)
  rw [Nat.add_sub_cancel' ht] at h
  unfold S
  omega

theorem S_le_S {d : ℕ → ℕ} {t N : ℕ} (ht : t ≤ N) : S d t ≤ S d N := by
  have h := s_add_shiftWord d t (N - t)
  rw [Nat.add_sub_cancel' ht] at h
  unfold S
  omega

/-! ## Realizer classes -/

/-- The `t`-th orbit value of a realizer of `d` realizes the suffix `σ^t d` for `N − t` steps. -/
theorem realizes_shiftWord {d : ℕ → ℕ} {N t x : ℕ} (h : Realizes d N x) (ht : t ≤ N) :
    Realizes (shiftWord d t) (N - t) (orbit x t) :=
  ⟨odd_orbit h.1 t, fun j hj => by
    rw [← orbit_add]
    exact h.2 (t + j) (by omega)⟩

/-- A realized word is automatically positive: realizing seeds are odd, hence so is every orbit
value, and `a` of an odd number is `≥ 1`. -/
theorem realizes_pos {d : ℕ → ℕ} {N y : ℕ} (hy : Realizes d N y) : ∀ i < N, 1 ≤ d i := by
  intro i hi
  rw [← hy.2 i hi]
  exact a_pos_of_odd (odd_orbit hy.1 i)

/-- Every realizer of a word is congruent to its least realizer mod `2^(S_N+1)`. (Positivity of
the word is not assumed: it follows from `Realizes`, see `realizes_pos`.) -/
theorem modEq_leastRealizer_of_realizes {d : ℕ → ℕ} {N y : ℕ} (hy : Realizes d N y) :
    y ≡ leastRealizer d N [MOD 2 ^ (S d N + 1)] := by
  have hd_pos := realizes_pos hy
  have hc := (realizerCongruence d N y hy.1 hd_pos).mp hy
  have h2 : 3 ^ N * y + q d N ≡ 3 ^ N * leastRealizer d N + q d N [MOD 2 ^ (S d N + 1)] :=
    hc.trans (leastRealizer_modEq d N).symm
  have h3 : 3 ^ N * y ≡ 3 ^ N * leastRealizer d N [MOD 2 ^ (S d N + 1)] :=
    Nat.ModEq.add_right_cancel (Nat.ModEq.refl (q d N)) h2
  have hcop : Nat.Coprime (2 ^ (S d N + 1)) (3 ^ N) :=
    Nat.Coprime.pow (S d N + 1) N (by decide)
  exact Nat.ModEq.cancel_left_of_coprime hcop h3

/-- Residue form: the least realizer is the residue of any realizer mod `2^(S_N+1)`. -/
theorem mod_eq_leastRealizer_of_realizes {d : ℕ → ℕ} {N y : ℕ} (hy : Realizes d N y) :
    y % 2 ^ (S d N + 1) = leastRealizer d N := by
  have h := modEq_leastRealizer_of_realizes hy
  rw [Nat.ModEq, Nat.mod_eq_of_lt (leastRealizer_lt d N)] at h
  exact h

/-- The least realizer realizes its (positive) word, for every length including `N = 0`. -/
theorem leastRealizer_realizes_all (d : ℕ → ℕ) (N : ℕ) (hd_pos : ∀ i < N, 1 ≤ d i) :
    Realizes d N (leastRealizer d N) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · refine ⟨?_, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    have h := leastRealizer_modEq d 0
    simp only [pow_zero, one_mul, q_zero, add_zero, S, s_zero, zero_add, pow_one] at h
    exact Nat.odd_iff.mpr h
  · exact leastRealizer_realizes d N hN hd_pos

/-- Carry identity for a realizer of `d`: `2^{S_t} · orbit x t = 3^t x + q_t`, `t ≤ N`. -/
theorem realizes_carry {d : ℕ → ℕ} {N x : ℕ} (h : Realizes d N x) {t : ℕ} (ht : t ≤ N) :
    2 ^ S d t * orbit x t = 3 ^ t * x + q d t := by
  have hag : ∀ i < t, a (orbit x i) = d i := fun i hi => h.2 i (by omega)
  have hc := orbit_carry x t
  rwa [s_eq_of_prefix_agree hag, q_eq_of_prefix_agree t hag] at hc

/-! ## Suffix transport -/

/-- **Suffix transport.** If `x` realizes the word `d` for `N` steps and `t ≤ N`, then
`orbit x t ≡ leastRealizer (σ^t d) (N − t)  [MOD 2^(S_N − S_t + 1)]`. -/
theorem suffix_transport {d : ℕ → ℕ} {N t x : ℕ} (hx : Realizes d N x) (ht : t ≤ N) :
    orbit x t ≡ leastRealizer (shiftWord d t) (N - t) [MOD 2 ^ (S d N - S d t + 1)] := by
  have h := modEq_leastRealizer_of_realizes (realizes_shiftWord hx ht)
  rwa [S_shiftWord d ht] at h

/-- **Suffix transport, structural form.** The seed-to-state map is the carry identity, and the
state lies in the suffix's canonical cylinder:
`2^{S_t} · orbit x t = 3^t x + q_t` and
`orbit x t = leastRealizer (σ^t d) (N − t) + 2^(S_N − S_t + 1) · j` for `j = orbit x t / 2^(…)`. -/
theorem suffix_transport_structure {d : ℕ → ℕ} {N t x : ℕ} (hx : Realizes d N x) (ht : t ≤ N) :
    2 ^ S d t * orbit x t = 3 ^ t * x + q d t ∧
    orbit x t = leastRealizer (shiftWord d t) (N - t)
      + 2 ^ (S d N - S d t + 1) * (orbit x t / 2 ^ (S d N - S d t + 1)) := by
  refine ⟨realizes_carry hx ht, ?_⟩
  have h := mod_eq_leastRealizer_of_realizes (realizes_shiftWord hx ht)
  rw [S_shiftWord d ht] at h
  have hdm := Nat.mod_add_div (orbit x t) (2 ^ (S d N - S d t + 1))
  rw [h] at hdm
  exact hdm.symm

/-- **Suffix transport for the least realizer.** -/
theorem leastRealizer_suffix_transport (d : ℕ → ℕ) (N t : ℕ) (ht : t ≤ N)
    (hd_pos : ∀ i < N, 1 ≤ d i) :
    orbit (leastRealizer d N) t
      ≡ leastRealizer (shiftWord d t) (N - t) [MOD 2 ^ (S d N - S d t + 1)] :=
  suffix_transport (leastRealizer_realizes_all d N hd_pos) ht

/-- Residue form: `orbit (r(D)) t mod 2^(S_N − S_t + 1)` *is* the suffix least realizer. -/
theorem leastRealizer_suffix_transport_mod (d : ℕ → ℕ) (N t : ℕ) (ht : t ≤ N)
    (hd_pos : ∀ i < N, 1 ≤ d i) :
    orbit (leastRealizer d N) t % 2 ^ (S d N - S d t + 1)
      = leastRealizer (shiftWord d t) (N - t) := by
  have h := mod_eq_leastRealizer_of_realizes
    (realizes_shiftWord (leastRealizer_realizes_all d N hd_pos) ht)
  rwa [S_shiftWord d ht] at h

/-! ## Shift covariance of the split depth -/

/-- **Split depth is consumed one digit at a time.** If `x`, `x'` realize words `d`, `e` through
step `k+1`, the words agree below `k` and differ at `k`, then for every shared step `t ≤ k` the two
orbit states satisfy `v₂(orbit x' t − orbit x t) = (S_k − S_t) + min (d k) (e k)`: the 2-adic
separation `S_k + min (d k) (e k)` of the seeds decreases by exactly `d t` at each shared step,
reaching `min (d k) (e k)` at the split step `t = k`. -/
theorem pair_split_depth_shift (d e : ℕ → ℕ) (k t x x' : ℕ) (ht : t ≤ k)
    (hx : Realizes d (k + 1) x) (hx' : Realizes e (k + 1) x')
    (hagree : ∀ i < k, d i = e i) (hne : d k ≠ e k) :
    padicValInt 2 ((orbit x' t : ℤ) - orbit x t) = (S d k - S d t) + min (d k) (e k) := by
  have hlen : k + 1 - t = (k - t) + 1 := by omega
  have hy := realizes_shiftWord hx (show t ≤ k + 1 by omega)
  have hy' := realizes_shiftWord hx' (show t ≤ k + 1 by omega)
  rw [hlen] at hy hy'
  have hkt : t + (k - t) = k := by omega
  have h := realizes_pair_valuation (shiftWord d t) (shiftWord e t) (k - t) _ _ hy hy'
    (fun i hi => hagree (t + i) (by omega))
    (by simp only [shiftWord]; rw [hkt]; exact hne)
  simp only [shiftWord, hkt] at h
  rw [h, S_shiftWord d ht]

/-! ## The pair/suffix cofactor law -/

/-- **Pair/suffix cofactor law.** Positive words `d` (length `N`) and `e` (length `M`) agreeing
below `k < min N M` and differing at `k`. With `m = min (d k) (e k)` and split depth
`τ = S_k + m`, the odd cofactor `Q` of `r(E) − r(D) = 2^τ Q` satisfies

`3^{k+1} Q ≡ 2^{e k − m} r(σ^{k+1} e) − 2^{d k − m} r(σ^{k+1} d)
   [ZMOD 2^(min (S_N(d)) (S_M(e)) − τ + 1)]`,

where `r(σ^{k+1} ·)` are the least realizers of the two post-split suffix words. -/
theorem pair_suffix_cofactor (d e : ℕ → ℕ) (N M k : ℕ) (hkN : k < N) (hkM : k < M)
    (hd_pos : ∀ i < N, 1 ≤ d i) (he_pos : ∀ i < M, 1 ≤ e i)
    (hagree : ∀ i < k, d i = e i) (hne : d k ≠ e k) :
    ∃ Q : ℤ, Odd Q ∧
      (leastRealizer e M : ℤ) - leastRealizer d N = 2 ^ (S d k + min (d k) (e k)) * Q ∧
      (3 : ℤ) ^ (k + 1) * Q ≡
        2 ^ (e k - min (d k) (e k)) * (leastRealizer (shiftWord e (k + 1)) (M - (k + 1)) : ℤ)
          - 2 ^ (d k - min (d k) (e k)) * (leastRealizer (shiftWord d (k + 1)) (N - (k + 1)) : ℤ)
        [ZMOD 2 ^ (min (S d N) (S e M) - (S d k + min (d k) (e k)) + 1)] := by
  obtain ⟨Q, hQodd, hfac, hQ⟩ :=
    leastRealizer_pair_factorization d e N M k hkN hkM hd_pos he_pos hagree hne
  refine ⟨Q, hQodd, hfac, ?_⟩
  rw [hQ]
  set m := min (d k) (e k) with hm
  -- exponent bookkeeping
  have hSkD : S d (k + 1) = S d k + d k := s_succ d k
  have hSkE : S e (k + 1) = S e k + e k := s_succ e k
  have hSeq : S d k = S e k := s_eq_of_prefix_agree hagree
  have hleD : S d (k + 1) ≤ S d N := S_le_S hkN
  have hleE : S e (k + 1) ≤ S e M := S_le_S hkM
  have hmD : m ≤ d k := min_le_left _ _
  have hmE : m ≤ e k := min_le_right _ _
  -- suffix transport on each branch, cast to `ℤ`
  have hD := leastRealizer_suffix_transport d N (k + 1) hkN hd_pos
  have hE := leastRealizer_suffix_transport e M (k + 1) hkM he_pos
  have hDz : (orbit (leastRealizer d N) (k + 1) : ℤ)
      ≡ (leastRealizer (shiftWord d (k + 1)) (N - (k + 1)) : ℤ)
        [ZMOD (2 : ℤ) ^ (S d N - S d (k + 1) + 1)] := by
    have := Int.natCast_modEq_iff.mpr hD
    push_cast at this
    exact this
  have hEz : (orbit (leastRealizer e M) (k + 1) : ℤ)
      ≡ (leastRealizer (shiftWord e (k + 1)) (M - (k + 1)) : ℤ)
        [ZMOD (2 : ℤ) ^ (S e M - S e (k + 1) + 1)] := by
    have := Int.natCast_modEq_iff.mpr hE
    push_cast at this
    exact this
  -- scale each branch and weaken to the common modulus
  have hD' := hDz.mul_left' (c := (2 : ℤ) ^ (d k - m))
  have hE' := hEz.mul_left' (c := (2 : ℤ) ^ (e k - m))
  rw [← pow_add] at hD' hE'
  have hdvdD : (2 : ℤ) ^ (min (S d N) (S e M) - (S d k + m) + 1)
      ∣ 2 ^ (d k - m + (S d N - S d (k + 1) + 1)) := pow_dvd_pow 2 (by omega)
  have hdvdE : (2 : ℤ) ^ (min (S d N) (S e M) - (S d k + m) + 1)
      ∣ 2 ^ (e k - m + (S e M - S e (k + 1) + 1)) := pow_dvd_pow 2 (by omega)
  exact (hE'.of_dvd hdvdE).sub (hD'.of_dvd hdvdD)

end SuffixTransport
end EOC
