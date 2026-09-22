import EOC.ConstraintHeight
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Order.Interval.Set.Infinite

/-!
# Finite-cylinder impossibility and the countability barrier

Companion to `docs/GLOBAL_SINGLE_ORBIT_NONLOCAL_SEPARATION_AUDIT.md`.

The previous rounds established that at fixed finite `(D,N)` every arithmetic coordinate is
determined by the word. This file records the two exact reasons why *finite* information can never
decide the remaining question — positive-integer realizability — and one quantitative form of the
barrier.

* `exists_odd_positive_in_class` — every odd residue class mod `2^k` contains arbitrarily large
  positive odd integers. So a finite valuation prefix, which pins exactly one class mod
  `2^{S_N+1}` (`Realizer.realizerCongruence`), always has positive realizers: the statement
  `∀N ∃m_N` is free, and only `∃m ∀N` has content.
* `no_finite_precision_sign_separator` — no property of integers determined by finitely many
  2-adic digits can characterize positivity. This is the concrete arithmetic form of "positive
  integers are dense in `ℤ₂`", proved without any topology.
* `decreasing_infinite_inter_empty` — the König/compactness no-go: a decreasing chain of infinite
  sets of positive integers can have empty intersection. Nesting of the prefix realizer classes is
  therefore automatic and carries no information; what is missing is a *uniform bound*, which is
  exactly `ZCRERealizerGrowth.boundedPrefixRealizers_iff_positiveRealizer`.
* `famWord`, `famWord_injective`, `famWord_confined` — an explicit family of infinite valuation
  words, indexed by `Set ℕ`, every member of which is zero-confined (in the exact integer form
  `2^{S_j} ≤ 3^j`) and has `S_j ≤ 4j/3`, hence drift `R_j → −∞` linearly.
* `not_all_realizable_of_injective` — the countability barrier (Cantor): an injectively-indexed
  family of words cannot all have positive-integer realizers, because one integer realizes at most
  one word.
  Applied to `famWord`, **all but countably many** zero-confined words with `R_j → −∞` have no
  positive realizer. The divergent-orbit shadows shared by the family are therefore insufficient by
  cardinality alone. This does *not* say that no word-level property characterizes realization:
  `leastRealizer` is a function of the word, so `ZCRERealizerGrowth.
  boundedPrefixRealizers_iff_positiveRealizer` exhibits one that does. It escapes the barrier by
  not being shared by the family.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace GlobalSeparation

/-! ## 1. Finite cylinders always contain positive integers -/

/-- **Every residue class mod `2^k` contains arbitrarily large positive integers.** -/
theorem exists_positive_in_class (r k B : ℕ) (hr : r < 2 ^ k) :
    ∃ m, B < m ∧ m % 2 ^ k = r := by
  refine ⟨r + 2 ^ k * (B + 1), ?_, ?_⟩
  · have : B + 1 ≤ 2 ^ k * (B + 1) := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos k)
    omega
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]

/-- The same, preserving oddness: an odd class mod `2^k` (`k ≥ 1`) contains arbitrarily large
positive **odd** integers.

This is the exact reason the finite half of the realizer problem is vacuous. A valuation prefix of
length `N` determines one odd residue class mod `2^{S_N+1}`, so positive odd realizers of that
prefix exist and are unbounded — `∀N ∃m_N` is automatic, and only `∃m ∀N` has content. -/
theorem exists_odd_positive_in_class (r k B : ℕ) (hk : 1 ≤ k) (hr : r < 2 ^ k) (hodd : Odd r) :
    ∃ m, B < m ∧ Odd m ∧ m % 2 ^ k = r := by
  obtain ⟨m, hmB, hmr⟩ := exists_positive_in_class r k B hr
  refine ⟨m, hmB, ?_, hmr⟩
  have h2 : (2 : ℕ) ∣ 2 ^ k := dvd_pow_self 2 (by omega)
  have hmm : m % 2 = r % 2 := by
    rw [← Nat.mod_mod_of_dvd m h2, hmr]
  rw [Nat.odd_iff] at hodd ⊢
  omega

/-! ## 2. No finite precision separates the signs -/

/-- **No finite-precision property characterizes positivity.**

If a property `P` of integers depends only on the residue modulo `2^k` (`k ≥ 1`), then `P` cannot
be equivalent to `0 < x`: every class mod `2^k` contains integers of both signs.

This is the arithmetic content of "the positive integers are dense in `ℤ₂`", stated without any
topology, and it is why no condition read off finitely many bits of the compatible realizer can
decide ordinary positive realization. -/
theorem no_finite_precision_sign_separator (k : ℕ) (hk : 1 ≤ k) (P : ℤ → Prop)
    (hP : ∀ x y : ℤ, x % 2 ^ k = y % 2 ^ k → (P x ↔ P y)) :
    ¬ (∀ x : ℤ, P x ↔ 0 < x) := by
  intro hchar
  have hpow : (1 : ℤ) < 2 ^ k := by
    calc (1 : ℤ) = 2 ^ 0 := by norm_num
      _ < 2 ^ k := by
          refine pow_lt_pow_right₀ (by norm_num) ?_
          omega
  have hmod : (1 : ℤ) % 2 ^ k = (1 - 2 ^ k) % 2 ^ k := by
    conv_rhs => rw [show (1 : ℤ) - 2 ^ k = 1 + 2 ^ k * (-1) by ring]
    rw [Int.add_mul_emod_self_left]
  have h1 : P 1 := (hchar 1).mpr (by norm_num)
  have h2 : P (1 - 2 ^ k) := (hP 1 (1 - 2 ^ k) hmod).mp h1
  have h3 : (0 : ℤ) < 1 - 2 ^ k := (hchar _).mp h2
  omega

/-! ## 3. The compactness no-go -/

/-- **Nesting is not enough.** A decreasing chain of infinite sets of naturals can have empty
intersection, so "every prefix has a positive realizer, and the classes are nested" does not
produce an infinite positive realizer.

This is the right shape: the realizer classes `R_N = {m : m ≡ r_N mod 2^{S_N+1}}` are infinite and
nested, and their intersection is nonempty exactly when `r_N` stays bounded — which is
`ZCRERealizerGrowth.boundedPrefixRealizers_iff_positiveRealizer`, not a compactness argument. -/
theorem decreasing_infinite_inter_empty :
    ∃ R : ℕ → Set ℕ, (∀ N, (R N).Infinite) ∧ (∀ N, R (N + 1) ⊆ R N) ∧ (⋂ N, R N) = ∅ := by
  refine ⟨fun N => Set.Ici N, fun N => Set.Ici_infinite N, fun N m hm => ?_, ?_⟩
  · exact le_trans (Nat.le_succ N) hm
  · ext m
    simp only [Set.mem_iInter, Set.mem_Ici, Set.mem_empty_iff_false, iff_false, not_forall]
    exact ⟨m + 1, by omega⟩

/-! ## 4. An uncountable zero-confined family with linear negative drift -/

open scoped Classical in
/-- The family word, digits indexed from `0`: a free choice of `2` or `1` at every third position
(`i ≡ 2 mod 3`), and `1` elsewhere. Indexed by an arbitrary subset of `ℕ`. -/
noncomputable def famWord (b : Set ℕ) (i : ℕ) : ℕ :=
  if (i + 1) % 3 = 0 then (if i / 3 ∈ b then 2 else 1) else 1

/-- Every digit is at least `1`, so the word is admissible. -/
theorem famWord_pos (b : Set ℕ) (i : ℕ) : 1 ≤ famWord b i := by
  unfold famWord; split_ifs <;> omega

/-- The valuation sum of the family word is at most `n + n/3`. -/
theorem famWord_sum_le (b : Set ℕ) (n : ℕ) :
    ∑ i ∈ Finset.range n, famWord b i ≤ n + n / 3 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hstep : famWord b n ≤ if (n + 1) % 3 = 0 then 2 else 1 := by
        unfold famWord; split_ifs <;> omega
      split_ifs at hstep with h
      · have : n / 3 + 1 = (n + 1) / 3 := by omega
        omega
      · omega

/-- **Zero confinement, in exact integer form.** For an integer `S`, the corridor condition
`S ≤ ⌊αj⌋` with `α = log₂3` is *equivalent* to `2^S ≤ 3^j`, because `2^{αj} = 3^j`. The family
satisfies it, since its valuation sum is at most `j + j/3`.

The proof is pure arithmetic: cube both sides and use `16 ≤ 27`. -/
theorem famWord_confined (j : ℕ) : (2 : ℕ) ^ (j + j / 3) ≤ 3 ^ j := by
  have hcube : ((2 : ℕ) ^ (j + j / 3)) ^ 3 ≤ (3 ^ j) ^ 3 := by
    have h3 : 3 * (j + j / 3) ≤ 4 * j := by omega
    calc ((2 : ℕ) ^ (j + j / 3)) ^ 3 = 2 ^ (3 * (j + j / 3)) := by rw [← pow_mul, Nat.mul_comm]
      _ ≤ 2 ^ (4 * j) := Nat.pow_le_pow_right (by norm_num) h3
      _ = 16 ^ j := by
          rw [show (16 : ℕ) = 2 ^ 4 from by norm_num, ← pow_mul]
      _ ≤ 27 ^ j := Nat.pow_le_pow_left (by norm_num) j
      _ = ((3 : ℕ) ^ j) ^ 3 := by
          rw [show (27 : ℕ) = 3 ^ 3 from by norm_num, ← pow_mul, ← pow_mul]
          congr 1
          omega
  exact (Nat.pow_le_pow_iff_left (n := 3) (by norm_num)).mp hcube

/-- The family is indexed injectively by `Set ℕ`, hence has cardinality `2^ℵ₀`. -/
theorem famWord_injective : Function.Injective famWord := by
  intro b₁ b₂ h
  ext i
  have hi := congrFun h (3 * i + 2)
  unfold famWord at hi
  have h1 : (3 * i + 2 + 1) % 3 = 0 := by omega
  have h2 : (3 * i + 2) / 3 = i := by omega
  rw [if_pos h1, if_pos h1, h2] at hi
  by_cases hb₁ : i ∈ b₁ <;> by_cases hb₂ : i ∈ b₂ <;>
    simp only [hb₁, hb₂, if_true, if_false] at hi <;> tauto

/-! ## 5. The countability barrier -/

/-- **One integer realizes at most one infinite word**, so an injectively indexed family of words
cannot all be positively realizable.

Applied with `F = famWord`: the family of §4 has cardinality `2^ℵ₀`, every member is zero-confined
with valuation sum `≤ j + j/3` — hence drift `R_j ≤ (4/3 − α)j → −∞` linearly — and only countably
many of them can have a positive-integer realizer. So **all but countably many** members satisfy
the divergent-orbit shadows listed above while having no positive realizer.

Criteria depending only on those shared shadows are therefore defeated by cardinality, before any
arithmetic. Word-level criteria in general are not: see the module docstring. -/
theorem not_all_realizable_of_injective {W : Type} (realizes : ℕ → W → Prop)
    (huniq : ∀ m w₁ w₂, realizes m w₁ → realizes m w₂ → w₁ = w₂)
    (F : Set ℕ → W) (hF : Function.Injective F)
    (h : ∀ b, ∃ m, realizes m (F b)) : False := by
  choose g hg using h
  have hginj : Function.Injective g := by
    intro b₁ b₂ hb
    apply hF
    exact huniq (g b₁) _ _ (hg b₁) (hb ▸ hg b₂)
  exact Function.cantor_injective g hginj

end GlobalSeparation
end EOC
