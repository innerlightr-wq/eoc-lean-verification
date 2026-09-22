import EOC.DriftExit

/-!
# Separated returns: the episode decomposition of the corridor

Companion to `docs/SEPARATED_RETURNS_INVESTIGATION.md`.

The occupation functional `O_c(m₀) = #{n : R_n ≤ c}` decomposes into maximal contiguous
*episodes*. This file formalizes the three exact bridges that decomposition rests on.

* `sum_concat` — the **restart relation** `S_{a+k}(m₀) = S_a(m₀) + S_k(m_a)`, whose drift form is
  `R_{a+k}(m₀) = R_a(m₀) + R_k(m_a)`. An episode entered at time `a` is therefore the initial
  confined window of the *restarted* orbit at the **local** threshold `c − R_a(m₀)`, not at `c`.
* `upcrossing_band` — every return to the corridor lands in a band of multiplicative width `3/2`
  just above the level, because a single accelerated step multiplies by at most `3/2`. Together
  with injectivity this makes each return consume a distinct orbit value in that band.
* `count_le_of_summands_ge` — the **no-tradeoff** counting fact. If a sum of `P` terms, each at
  least `B > 0`, is at most `T`, then `P ≤ T / B`. Applied to the episode decomposition this says
  that a corridor-uniform single-window bound can give `O_c = O(log m₀)` *only* if the episode
  count is `O(1)`: no redistribution between episode count and episode length can substitute for
  bounding the count.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace SeparatedReturns

open OrbitLifetime

/-! ## 1. The restart relation -/

/-- **Valuation sums concatenate along the orbit.** If `d'` is the valuation sequence read from
index `a` onwards, then `S_{a+k} = S_a + S'_k`.

In drift form, subtracting `(a+k)α = aα + kα`, this is `R_{a+k}(m₀) = R_a(m₀) + R_k(m_a)`: the
restarted orbit carries its own drift, measured from zero at the restart. Hence the corridor
condition `R_{a+k} ≤ c` reads `R_k(m_a) ≤ c − R_a(m₀)` — a **local threshold** that widens exactly
as the drift at the entry point has fallen. -/
theorem sum_concat (d : ℕ → ℕ) (S : ℕ → ℕ) (hS0 : S 0 = 0)
    (hS : ∀ i, S (i + 1) = S i + d i) (a k : ℕ) :
    S (a + k) = S a + ∑ j ∈ Finset.range k, d (a + j) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hik : a + (k + 1) = (a + k) + 1 := by omega
      rw [hik, hS (a + k), ih, Finset.sum_range_succ]
      ring

/-! ## 2. Returns land in a bounded band -/

/-- **Up-crossing band.** A single accelerated step satisfies `2·m_{n+1} ≤ 3·m_n + 1`. So if the
orbit is strictly below a level `L` at time `n` and at or above it at time `n+1`, the landing value
satisfies

```
L ≤ m_{n+1}   and   2·m_{n+1} < 3·L + 1 ,
```

i.e. the return lands in a band of multiplicative width `3/2` just above `L`.

Since the orbit is injective wherever it has not yet cycled, distinct returns consume distinct
values of that band. That band is the natural "resource" a return is charged to — and
`docs/SEPARATED_RETURNS_INVESTIGATION.md` records why it is exponentially too large to force a
bounded number of returns. -/
theorem upcrossing_band {m d S C : ℕ → ℕ} (h : Orbit m d S C) (n L : ℕ)
    (hbelow : m n < L) (habove : L ≤ m (n + 1)) :
    L ≤ m (n + 1) ∧ 2 * m (n + 1) < 3 * L + 1 := by
  refine ⟨habove, ?_⟩
  have hstep := h.step n
  have hd : (2 : ℕ) ^ 1 ≤ 2 ^ d n := Nat.pow_le_pow_right (by norm_num) (h.dpos n)
  have h2 : 2 * m (n + 1) ≤ 2 ^ d n * m (n + 1) := by
    simpa using Nat.mul_le_mul_right (m (n + 1)) hd
  omega

/-! ## 3. The no-tradeoff counting fact -/

/-- **No tradeoff between episode count and episode length.**

If `P` quantities each of size at least `B > 0` sum to at most `T`, then `P·B ≤ T`.

Applied to the episode decomposition: a corridor-uniform single-window bound
`L_{c'}(m) ≤ K(log₂ m + c')` gives, for the episode entered at time `a`,

```
ℓ ≤ 1 + K(log₂ m_a + c − R_a) = 1 + K(log₂ m₀ + E_a + c − 2R_a),
```

and every one of those summands is at least `log₂ m₀ − c`. So any bound of the form
`O_c(m₀) ≤ T` obtained by summing them forces `P ≤ T/(log₂ m₀ − c)`. In particular
`T = O(log m₀)` forces `P = O(1)`: within this framework one cannot trade a larger episode count
against shorter episodes. Bounding count and length separately by `O(log m₀)` yields only
`O((log m₀)²)`. -/
theorem count_le_of_summands_ge {ι : Type} (s : Finset ι) (f : ι → ℝ) (B T : ℝ)
    (hB : 0 < B) (hge : ∀ i ∈ s, B ≤ f i) (hsum : ∑ i ∈ s, f i ≤ T) :
    (s.card : ℝ) * B ≤ T := by
  calc (s.card : ℝ) * B = ∑ _i ∈ s, B := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ s, f i := Finset.sum_le_sum hge
    _ ≤ T := hsum

end SeparatedReturns
end EOC
