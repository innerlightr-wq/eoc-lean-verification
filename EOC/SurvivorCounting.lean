import EOC.UpperCertificates
import EOC.FiniteValuationWord

/-!
# Survivor-seed counting from realizer cylinders

Finite counting statements connecting valuation words, realizer residue classes, and the number of
seeds below `X` (the repo-native core of the exceptional-seed density bound).

* `card_realizers_le` — the realizers `μ < X` of a word `d` of length `N` number at most
  `X / 2^(S_N + 1) + 1` (they form one residue class modulo `2^(S_N+1)`).
* `card_realizers_eq_of_dvd` — **exact count in the fresh-bit regime**: for a positive word with
  `N ≥ 1`, if `2^(S_N+1) ∣ X` then there are exactly `X / 2^(S_N+1)` realizers below `X`.
* `prefixWord`, `realizes_prefixWord` — the first `N` valuations of `μ` as a finite word, which `μ`
  realizes.
* `card_seeds_le_sum` — for any property `P` of seeds and any finite set `W` of length-`N` words
  containing the prefix word of every odd `μ < X` with `P μ`:
  `#{μ < X : μ odd, P μ} ≤ ∑_{w ∈ W} (X / 2^(S_N(w)+1) + 1)`.

Taking `P` = "`c`-confined for `N` steps" and `W` = the `c`-confined words of length `N` gives
`#{μ < X confined N steps} ≤ (X/2)·∑_w 2^{−S_N(w)} + #W`, where `∑_w 2^{−S_N(w)}` is the Geom(2)
survival mass; combining with the Chernoff bound of `TaoLike.PersistenceModel` is recorded in the
research notes (not formalized here).

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace SurvivorCounting

open Finset SuffixTransport

/-- Realizers below `X` of a length-`N` word: at most `X / 2^(S_N+1) + 1`. -/
theorem card_realizers_le (d : ℕ → ℕ) (N X : ℕ) [DecidablePred (fun μ => Realizes d N μ)] :
    ((range X).filter (fun μ => Realizes d N μ)).card ≤ X / 2 ^ (S d N + 1) + 1 := by
  set Q := 2 ^ (S d N + 1) with hQdef
  have hQ : 0 < Q := by positivity
  have hsub : (range X).filter (fun μ => Realizes d N μ)
      ⊆ (range (X / Q + 1)).image (fun k => leastRealizer d N + Q * k) := by
    intro μ hμ
    rw [mem_filter, mem_range] at hμ
    rw [mem_image]
    refine ⟨μ / Q, ?_, ?_⟩
    · rw [mem_range]
      have : μ / Q ≤ X / Q := Nat.div_le_div_right hμ.1.le
      omega
    · have hmod := mod_eq_leastRealizer_of_realizes hμ.2
      have h := Nat.mod_add_div μ Q
      rw [hmod] at h
      exact h
  calc ((range X).filter (fun μ => Realizes d N μ)).card
      ≤ ((range (X / Q + 1)).image (fun k => leastRealizer d N + Q * k)).card := card_le_card hsub
    _ ≤ (range (X / Q + 1)).card := card_image_le
    _ = X / Q + 1 := card_range _

/-- **Exact count in the fresh-bit regime.** For a positive word with `N ≥ 1`, if `2^(S_N+1)`
divides `X`, the realizers below `X` are exactly `leastRealizer + 2^(S_N+1) k` with
`k < X / 2^(S_N+1)`. -/
theorem card_realizers_eq_of_dvd (d : ℕ → ℕ) (N X : ℕ) (hN : 1 ≤ N) (hd_pos : ∀ i < N, 1 ≤ d i)
    [DecidablePred (fun μ => Realizes d N μ)] (hdvd : 2 ^ (S d N + 1) ∣ X) :
    ((range X).filter (fun μ => Realizes d N μ)).card = X / 2 ^ (S d N + 1) := by
  set Q := 2 ^ (S d N + 1) with hQdef
  have hQ : 0 < Q := by positivity
  have hr := leastRealizer_lt d N
  obtain ⟨t, rfl⟩ := hdvd
  have hXQ : Q * t / Q = t := Nat.mul_div_cancel_left t hQ
  have heq : (range (Q * t)).filter (fun μ => Realizes d N μ)
      = (range t).image (fun k => leastRealizer d N + Q * k) := by
    ext μ
    rw [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hμX, hμ⟩
      refine ⟨μ / Q, ?_, ?_⟩
      · rw [mem_range]
        exact (Nat.div_lt_iff_lt_mul hQ).mpr (by rw [mul_comm]; exact hμX)
      · have hmod := mod_eq_leastRealizer_of_realizes hμ
        have h := Nat.mod_add_div μ Q
        rw [hmod] at h
        exact h
    · rintro ⟨k, hk, rfl⟩
      rw [mem_range] at hk
      refine ⟨?_, (cylinder_restart_leastRealizer d N k hN hd_pos).1⟩
      have : Q * k + Q ≤ Q * t := by
        have := Nat.mul_le_mul_left Q (show k + 1 ≤ t by omega)
        rw [mul_add, mul_one] at this
        exact this
      omega
  rw [heq, card_image_of_injective _ (fun k₁ k₂ h =>
    Nat.eq_of_mul_eq_mul_left hQ (Nat.add_left_cancel h)), card_range, hXQ]

/-- The first `N` valuations of `μ`, as a finite word. -/
noncomputable def prefixWord (N μ : ℕ) : FiniteValuationWord N := fun i => a (orbit μ i)

theorem realizes_prefixWord (N μ : ℕ) (hμ : Odd μ) :
    Realizes (FiniteValuationWord.toInfinite (prefixWord N μ)) N μ :=
  ⟨hμ, fun i hi => by
    rw [FiniteValuationWord.toInfinite_apply_of_lt _ hi]
    rfl⟩

/-- **Union bound over words.** Any finite set `W` of length-`N` words containing the prefix word
of every odd `μ < X` with property `P` bounds the number of such seeds by
`∑_{w ∈ W} (X / 2^(S_N(w)+1) + 1)`. -/
theorem card_seeds_le_sum (N X : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (W : Finset (FiniteValuationWord N))
    (hW : ∀ μ < X, Odd μ → P μ → prefixWord N μ ∈ W) :
    ((range X).filter (fun μ => Odd μ ∧ P μ)).card
      ≤ ∑ w ∈ W, (X / 2 ^ (S (FiniteValuationWord.toInfinite w) N + 1) + 1) := by
  classical
  have hsub : (range X).filter (fun μ => Odd μ ∧ P μ)
      ⊆ W.biUnion (fun w =>
          (range X).filter (fun μ => Realizes (FiniteValuationWord.toInfinite w) N μ)) := by
    intro μ hμ
    rw [mem_filter, mem_range] at hμ
    rw [mem_biUnion]
    exact ⟨prefixWord N μ, hW μ hμ.1 hμ.2.1 hμ.2.2,
      mem_filter.mpr ⟨mem_range.mpr hμ.1, realizes_prefixWord N μ hμ.2.1⟩⟩
  calc ((range X).filter (fun μ => Odd μ ∧ P μ)).card
      ≤ (W.biUnion (fun w =>
          (range X).filter (fun μ => Realizes (FiniteValuationWord.toInfinite w) N μ))).card :=
        card_le_card hsub
    _ ≤ ∑ w ∈ W, ((range X).filter
          (fun μ => Realizes (FiniteValuationWord.toInfinite w) N μ)).card := card_biUnion_le
    _ ≤ ∑ w ∈ W, (X / 2 ^ (S (FiniteValuationWord.toInfinite w) N + 1) + 1) :=
        sum_le_sum (fun w _ => card_realizers_le _ N X)

end SurvivorCounting
end EOC
