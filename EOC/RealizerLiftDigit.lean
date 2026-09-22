import EOC.ZCRERealizerGrowth

/-!
# Successive realizer lift digits and the positivity coordinate

Companion to `docs/REALIZER_LIFT_DIGIT_POSITIVITY_AUDIT.md`.

For a valuation prefix of length `N` with total valuation `S_N`, the exact realizers form one
class modulo `2^(S_N+1)` (`Realizer.realizerCongruence`). Cylinder nesting gives
`r_{N+1} ≡ r_N (mod 2^(S_N+1))`, so there is a unique

```
t_N ∈ {0, …, 2^{d_N} − 1}     with     r_{N+1} = r_N + t_N · 2^(S_N+1)
```

— the **successive realizer lift digit**. This file formalizes what that coordinate is.

The headline is deflationary and is the point of the audit:

* `liftDigit_eq_bitBlock` — for a *fixed* natural number `m`, the lift digit is literally the
  block of binary digits of `m` occupying bit positions `S_N+1, …, S_{N+1}`. **Lift digits are
  grouped binary digits of the realizer**, nothing more.
* `liftDigit_eq_zero_iff` and `eventuallyZero_iff_eventuallyConstant` — eventual vanishing of the
  lift digits is *exactly* eventual constancy of the prefix realizers, hence (by
  `ZCRERealizerGrowth.boundedPrefixRealizers_iff_positiveRealizer`) exactly positive-integer
  realizability. **A new coordinate, not new information.**

The results are stated for an abstract nested sequence `r : ℕ → ℕ` rather than for
`leastRealizer` specifically, because that is the generality in which they are true and it keeps
the file free of any 2-adic infrastructure (see the audit's §AC on why none was built).

**What this coordinate is good for.** It is genuinely positivity-sensitive in the representational
sense — eventual zeros distinguish `ℕ` inside `ℤ₂`, and eventual *maximal* blocks distinguish the
negative integers (the all-`1`s valuation word is zero-confined and realized by `−1`). What it does
**not** supply is any theorem forcing infinitely many nonzero lift digits for an irregular
zero-confined word; §AB of the audit records that no such statement was found and that the obvious
candidate is equivalent to the problem itself.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace RealizerLiftDigit

/-! ## 1. The lift digit -/

/-- The successive realizer lift digit: `t_N = (r_{N+1} − r_N) / 2^(S_N+1)`. -/
def liftDigit (r S : ℕ → ℕ) (N : ℕ) : ℕ := (r (N + 1) - r N) / 2 ^ (S N + 1)

/-- **Range of the lift digit.**  If the next realizer stays below its own modulus
`2^(S_{N+1}+1)` and the valuation grows by `d`, then `t_N < 2^d`.

So `t_N` ranges over exactly the `2^{d_N}` values the refinement of the cylinder permits. -/
theorem liftDigit_lt {r S : ℕ → ℕ} {N d : ℕ}
    (hlt : r (N + 1) < 2 ^ (S (N + 1) + 1)) (hS : S (N + 1) = S N + d) :
    liftDigit r S N < 2 ^ d := by
  unfold liftDigit
  have hpos : 0 < 2 ^ (S N + 1) := Nat.two_pow_pos _
  rw [Nat.div_lt_iff_lt_mul hpos]
  calc r (N + 1) - r N ≤ r (N + 1) := Nat.sub_le _ _
    _ < 2 ^ (S (N + 1) + 1) := hlt
    _ = 2 ^ d * 2 ^ (S N + 1) := by rw [hS]; ring

/-- **The lift digit vanishes exactly when the realizer does not move.**

Needs the nesting divisibility `2^(S_N+1) ∣ r_{N+1} − r_N`, which is what the exact cylinder
supplies. -/
theorem liftDigit_eq_zero_iff {r S : ℕ → ℕ} {N : ℕ}
    (hmono : r N ≤ r (N + 1)) (hdvd : 2 ^ (S N + 1) ∣ (r (N + 1) - r N)) :
    liftDigit r S N = 0 ↔ r (N + 1) = r N := by
  unfold liftDigit
  constructor
  · intro h
    obtain ⟨c, hc⟩ := hdvd
    rw [hc] at h
    have hpos : 0 < 2 ^ (S N + 1) := Nat.two_pow_pos _
    rw [Nat.mul_div_cancel_left _ hpos] at h
    rw [h, Nat.mul_zero] at hc
    omega
  · intro h; rw [h, Nat.sub_self]; simp

/-! ## 2. Eventual vanishing is eventual constancy -/

/-- **Eventual lift-zero ⟺ eventual realizer constancy.**

This is the whole content of the coordinate. Combined with
`ZCRERealizerGrowth.boundedPrefixRealizers_iff_positiveRealizer` and
`leastRealizer_eventually_constant_of_bounded`, "the lift digits eventually vanish" is *exactly*
"the word has a positive-integer realizer" — the existing ZCRE statement in different letters. -/
theorem eventuallyZero_iff_eventuallyConstant {r S : ℕ → ℕ}
    (hmono : ∀ N, r N ≤ r (N + 1))
    (hdvd : ∀ N, 2 ^ (S N + 1) ∣ (r (N + 1) - r N)) :
    (∃ N₀, ∀ N, N₀ ≤ N → liftDigit r S N = 0) ↔ (∃ N₀, ∀ N, N₀ ≤ N → r N = r N₀) := by
  constructor
  · rintro ⟨N₀, h⟩
    refine ⟨N₀, ?_⟩
    intro N hN
    induction N with
    | zero =>
        have : N₀ = 0 := by omega
        rw [this]
    | succ n ih =>
        rcases Nat.lt_or_ge N₀ (n + 1) with hlt | hge
        · have hn : N₀ ≤ n := by omega
          have hstep : r (n + 1) = r n :=
            (liftDigit_eq_zero_iff (hmono n) (hdvd n)).mp (h n hn)
          rw [hstep]; exact ih hn
        · have : N₀ = n + 1 := by omega
          rw [this]
  · rintro ⟨N₀, h⟩
    refine ⟨N₀, fun N hN => ?_⟩
    have h1 : r (N + 1) = r N₀ := h (N + 1) (by omega)
    have h2 : r N = r N₀ := h N hN
    exact (liftDigit_eq_zero_iff (hmono N) (hdvd N)).mpr (by rw [h1, h2])

/-! ## 3. Lift digits are grouped binary digits -/

/-- **The deflationary theorem.**  If one fixed natural number `m` realizes every prefix — so that
`r_N = m mod 2^(S_N+1)`, which is what `ZCRERealizerGrowth.leastRealizer_eq_mod_of_realizes`
gives — then the lift digit is exactly the block of binary digits of `m` in positions
`S_N+1, …, S_N+d`.

Hence the successive-lift-digit sequence is nothing but the binary expansion of the realizer, read
in variable-length blocks cut at the valuation sums. Any statement about lift digits is a statement
about those bits, and carries no arithmetic content beyond them. -/
theorem liftDigit_eq_bitBlock (m a d : ℕ) :
    (m % 2 ^ (a + d) - m % 2 ^ a) / 2 ^ a = (m / 2 ^ a) % 2 ^ d := by
  have hpos : 0 < 2 ^ a := Nat.two_pow_pos _
  have hmod : m % 2 ^ a = (m % 2 ^ (a + d)) % 2 ^ a :=
    (Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (Nat.le_add_right a d))).symm
  have hx : ∀ x : ℕ, (x - x % 2 ^ a) / 2 ^ a = x / 2 ^ a := by
    intro x
    have hdm := Nat.div_add_mod x (2 ^ a)
    have hsub : x - x % 2 ^ a = 2 ^ a * (x / 2 ^ a) := by omega
    rw [hsub, Nat.mul_div_cancel_left _ hpos]
  rw [hmod, hx, pow_add, Nat.mod_mul_right_div_self]

/-- The same statement in the shape the audit uses: with `a = S_N + 1` and `d = d_N`, the lift
digit of a fixed realizer `m` is `(m / 2^(S_N+1)) mod 2^{d_N}`. -/
theorem liftDigit_of_fixed (m : ℕ) (S : ℕ → ℕ) (N d : ℕ) (hS : S (N + 1) = S N + d) :
    liftDigit (fun k => m % 2 ^ (S k + 1)) S N = (m / 2 ^ (S N + 1)) % 2 ^ d := by
  show (m % 2 ^ (S (N + 1) + 1) - m % 2 ^ (S N + 1)) / 2 ^ (S N + 1)
      = (m / 2 ^ (S N + 1)) % 2 ^ d
  rw [hS, show S N + d + 1 = (S N + 1) + d from by omega]
  exact liftDigit_eq_bitBlock m (S N + 1) d

end RealizerLiftDigit
end EOC
