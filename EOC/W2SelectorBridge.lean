import EOC.ChangZeroCorridor

/-!
# Exact bridges between the W=2 offset-zero program and the current realizer frontier

Companion to `docs/W2_REALIZER_SELECTOR_BRIDGE_AUDIT.md`.

The W=2 offset-zero pullback program studies the accelerated map restricted to digits `d ∈ {1,2}`,
selecting words by an Archimedean cutoff `r(A) < Y ≤ r(A) + 2^{S_A+1}` ("offset zero"). This file
formalizes the four elementary facts the audit needs in order to place that program against the
current moving-anchor / least-realizer problem. None of them is deep; all four are load-bearing.

* `offsetZero_iff_unique_lift` — the offset-zero condition says exactly that **precisely one**
  positive realizer of the word lies below the cutoff, i.e. it is the least-representative
  convention plus a no-double-counting cutoff. Nothing more.
* `lift_shift` — replacing the realizer `r` by another member `r + q·2^{S+1}` of its class shifts
  the terminal state by `2·q·3^N`. **The alphabet plays no role**: this holds for every valuation
  word, not only for `d ∈ {1,2}`.
* `lift_shift_injOn` — `q ↦ 2·3^N·q` is injective modulo `2^{T+1}` on `q < 2^T`, hence sweeps all
  `2^T` even residues. This is the general form of the note's Lemma 8 (lift-completion vanishing),
  and it too is alphabet-independent: the only input is that `3^N` is odd.
* `add_two_mul_highCount_le_S`, `two_mul_highCount_le` — the zero corridor's budget for
  high valuations: `N + 2·#{j < N : 3 ≤ d j} ≤ S_N ≤ ⌊αN⌋`, so high digits have density at most
  `(α−1)/2 = 0.2924…`. Bounded, but **not** sparse enough to force long `{1,2}` runs — and
  `ChangFullShift` exhibits a zero-confined sequence with a digit `3` every seven steps forever.

**What is deliberately not formalized**: the twisted transfer gap `|G_s(k)| ≤ C N^{1−δ}` (a Tier-2
target of the note, and a *population* statistic), and anything asserting that a character-sum
bound constrains an individual least realizer. §H of the audit explains why no such implication is
available.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace W2SelectorBridge

open Finset

/-! ## 1. What "offset zero" actually says -/

/-- **Offset zero is the least-representative convention with a cutoff.**

The positive realizers of a word whose exact cylinder is `r + M·ℕ` (here `M = 2^{S+1}`) are
`r, r + M, r + 2M, …`. Given `r < Y`, the extra hypothesis `Y ≤ r + M` is *equivalent* to saying
that `q = 0` is the only lift landing below the cutoff.

So "offset zero at cutoff `Y`" carries no arithmetic information beyond `r < Y` together with the
cylinder modulus: it is a bookkeeping convention that prevents one word from being counted twice.
-/
theorem offsetZero_iff_unique_lift {r Y M : ℕ} (hM : 0 < M) (hrY : r < Y) :
    (Y ≤ r + M) ↔ (∀ q : ℕ, r + q * M < Y ↔ q = 0) := by
  constructor
  · intro h q
    constructor
    · intro hq
      by_contra hq0
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      have : r + M ≤ r + (q' + 1) * M := by nlinarith
      omega
    · rintro rfl; simpa using hrY
  · intro h
    by_contra hlt
    have h1 : r + 1 * M < Y := by omega
    exact absurd ((h 1).mp h1) (by norm_num)

/-! ## 2. The lift shift law — alphabet-independent -/

/-- **Lift shift.**  If `2^S · m = 3^N · r + C` is the exact carry identity for a valuation word of
length `N` and total valuation `S`, then the realizer `r + q·2^(S+1)` of the same cylinder has
terminal state `m + 2·q·3^N`.

The proof uses nothing about the digits, so this is the *general* statement behind the W=2 note's
`m_A^0 ↦ m_A^0 + 2u·3^p`. It is the reason every harmonic observable of that program is either
`q`-invariant or `q`-periodic (audit §X). -/
theorem lift_shift (N S C r m q : ℕ) (h : 2 ^ S * m = 3 ^ N * r + C) :
    2 ^ S * (m + 2 * q * 3 ^ N) = 3 ^ N * (r + q * 2 ^ (S + 1)) + C := by
  have hpow : (2 : ℕ) ^ (S + 1) = 2 ^ S * 2 := by ring
  calc 2 ^ S * (m + 2 * q * 3 ^ N)
      = 2 ^ S * m + 2 ^ S * (2 * q * 3 ^ N) := by ring
    _ = (3 ^ N * r + C) + 2 ^ S * (2 * q * 3 ^ N) := by rw [h]
    _ = 3 ^ N * (r + q * 2 ^ (S + 1)) + C := by rw [hpow]; ring

/-- **General lift-completion sweep.**  `q ↦ 2 · 3^N · q` is injective modulo `2^(T+1)` on the
range `q < 2^T`, so the `2^T` lifts sweep all `2^T` even residues modulo `2^(T+1)`.

This is the alphabet-independent core of the note's Lemma 8: the complete lift fibre is balanced,
and the only input is that `3^N` is odd. The note proved it for `d ∈ {1,2}`; the restriction was
never used. -/
theorem lift_shift_injOn (N T : ℕ) :
    Set.InjOn (fun q : ℕ => (2 * 3 ^ N * q) % 2 ^ (T + 1)) {q | q < 2 ^ T} := by
  intro a ha b hb hab
  simp only [Set.mem_setOf_eq] at ha hb
  have hmod : (2 * 3 ^ N * a) ≡ (2 * 3 ^ N * b) [MOD 2 ^ (T + 1)] := hab
  have hre : ∀ c : ℕ, 2 * 3 ^ N * c = 2 * (3 ^ N * c) := fun c => by ring
  rw [hre, hre] at hmod
  have hpow : (2 : ℕ) ^ (T + 1) = 2 * 2 ^ T := by ring
  rw [hpow] at hmod
  -- cancel the factor 2 from both sides and from the modulus
  have h2 : (3 ^ N * a) ≡ (3 ^ N * b) [MOD 2 ^ T] :=
    Nat.ModEq.mul_left_cancel' (by norm_num) hmod
  -- `3^N` is a unit modulo `2^T`
  have hcop : Nat.gcd (2 ^ T) (3 ^ N) = 1 :=
    Nat.Coprime.pow T N (by decide : Nat.Coprime 2 3)
  have h3 : a ≡ b [MOD 2 ^ T] := Nat.ModEq.cancel_left_of_coprime hcop h2
  have h4 : a % 2 ^ T = b % 2 ^ T := h3
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h4

/-! ## 3. The zero-corridor budget for high valuations -/

/-- The number of high digits (`≥ 3`) among the first `k`. -/
def highCount (d : ℕ → ℕ) (k : ℕ) : ℕ :=
  ((range k).filter (fun t => 3 ≤ d t)).card

/-- Every word pays one unit per step and **two extra** per high digit. -/
theorem add_two_mul_highCount_le_S {d : ℕ → ℕ} (hd : ∀ i, 1 ≤ d i) (k : ℕ) :
    k + 2 * highCount d k ≤ s d k := by
  unfold highCount s
  have hcard : ((range k).filter (fun t => 3 ≤ d t)).card
      = ∑ t ∈ range k, (if 3 ≤ d t then 1 else 0) := by
    rw [Finset.card_filter]
  rw [hcard, Finset.mul_sum]
  calc k + ∑ t ∈ range k, 2 * (if 3 ≤ d t then 1 else 0)
      = ∑ t ∈ range k, (1 + 2 * (if 3 ≤ d t then 1 else 0)) := by
        rw [Finset.sum_add_distrib]; simp
    _ ≤ ∑ t ∈ range k, d t := by
        refine Finset.sum_le_sum fun t _ => ?_
        by_cases h : 3 ≤ d t
        · rw [if_pos h]; omega
        · rw [if_neg h]; have := hd t; omega

/-- **Zero-corridor high-digit budget.**  Under `S_k ≤ ⌊kα⌋` the high digits obey
`2·#{t < k : 3 ≤ d t} ≤ ⌊kα⌋ − k`, hence asymptotic density at most `(α−1)/2 = 0.2924…`.

The bound is real but weak: it caps the *density* of high digits and says nothing about their
*spacing*. `ChangFullShift.changSeq` (with `y ≡ true`) is zero-confined and has a digit `3` at every
index `≡ 6 (mod 7)`, i.e. density `1/7 < 0.2924`, so pure `{1,2}` runs there never exceed length
six. Zero confinement therefore does **not** imply eventual `W=2` survival. -/
theorem two_mul_highCount_le {d : ℕ → ℕ} (hd : ∀ i, 1 ≤ d i) (k : ℕ)
    (hconf : (s d k : ℤ) ≤ ⌊(k : ℝ) * alpha⌋) :
    (2 * highCount d k : ℤ) ≤ ⌊(k : ℝ) * alpha⌋ - k := by
  have h := add_two_mul_highCount_le_S hd k
  have h' : ((k : ℤ)) + 2 * (highCount d k : ℤ) ≤ (s d k : ℤ) := by exact_mod_cast h
  omega

end W2SelectorBridge
end EOC
