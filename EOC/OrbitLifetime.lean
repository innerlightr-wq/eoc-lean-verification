import EOC.GlobalSeparation

/-!
# The corridor width of an actual positive orbit is automatic

Companion to `docs/POSITIVE_ORBIT_CONFINEMENT_LIFETIME_AUDIT.md`.

The launch-renormalization note reduces an `ε`-dangerous word to a long injective orbit segment of
a comparatively small positive integer, confined in a corridor `R_i ≤ A`, and shows that the
hypothesis

```
U_all(K):  every injective initial segment of m with R_i ≤ A (0 ≤ i ≤ L) has L ≤ K(log₂ m + A)
```

implies an exponential least-realizer floor. This file records the elementary facts about *actual*
positive iterates that determine what `U_all` really assumes.

Everything is stated for the aggregate relation `2^{S_i}·m_i = 3^i·m_0 + C_i`, which is the exact
form of the accelerated orbit (`aggregate_identity` below proves it from the step relation).

* `valuation_le` — `2^{d_i} ≤ 3m_i + 1`: a step's valuation is bounded by the *ordinary size* of
  the current iterate. This is genuinely orbit-level; it is unavailable for a symbolic word.
* `growth_step`, `growth_envelope` — `2^n(m_n + 1) ≤ 3^n(m_0 + 1)`, the exact maximal forward
  growth envelope. In logs, `log₂ m_n ≤ log₂(m_0+1) + n(α−1)`: ordinary size cannot grow faster
  than `α−1 = log₂(3/2)` per accelerated step.
* `corridor_automatic` — **the key point.** From `m_i ≥ 1` alone, `2^{S_i} ≤ 3^i m_0 + C_i`, i.e.
  `R_i ≤ log₂ m_0 + E_i` where `E_i = log₂(1 + C_i/(3^i m_0))`. The corridor bound in `U_all` is
  therefore *not an extra hypothesis*: every positive orbit satisfies it with
  `A ≈ log₂ m_0`, and `corridor_attained` shows equality holds as soon as the orbit reaches `1`.
* `Uall_gives_stopping_bound`, `stopping_bound_gives_Uall` — consequently `U_all(K)` is equivalent,
  up to a factor `2` in `K`, to the statement that every accelerated orbit reaches `1` within
  `O(log₂ m)` steps. It is not a mild corridor hypothesis; it is the `O(log n)` total-stopping-time
  conjecture.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace OrbitLifetime

/-! ## 1. The aggregate identity -/

/-- Hypotheses describing an accelerated positive orbit: `m (i+1) = (3 m i + 1)/2^{d i}` in the
exact form `2^{d i} * m (i+1) = 3 * m i + 1`, with running sums `S` and carry `C`. -/
structure Orbit (m d S C : ℕ → ℕ) : Prop where
  step : ∀ i, 2 ^ d i * m (i + 1) = 3 * m i + 1
  dpos : ∀ i, 1 ≤ d i
  mpos : ∀ i, 1 ≤ m i
  S0 : S 0 = 0
  Ssucc : ∀ i, S (i + 1) = S i + d i
  C0 : C 0 = 0
  Csucc : ∀ i, C (i + 1) = 3 * C i + 2 ^ S i

/-- **The aggregate identity** `2^{S_n}·m_n = 3^n·m_0 + C_n`, proved from the step relation. -/
theorem aggregate_identity {m d S C : ℕ → ℕ} (h : Orbit m d S C) (n : ℕ) :
    2 ^ S n * m n = 3 ^ n * m 0 + C n := by
  induction n with
  | zero => rw [h.S0, h.C0]; simp
  | succ n ih =>
      have hstep := h.step n
      calc 2 ^ S (n + 1) * m (n + 1)
          = 2 ^ S n * (2 ^ d n * m (n + 1)) := by rw [h.Ssucc]; ring
        _ = 2 ^ S n * (3 * m n + 1) := by rw [hstep]
        _ = 3 * (2 ^ S n * m n) + 2 ^ S n := by ring
        _ = 3 * (3 ^ n * m 0 + C n) + 2 ^ S n := by rw [ih]
        _ = 3 ^ (n + 1) * m 0 + (3 * C n + 2 ^ S n) := by ring
        _ = 3 ^ (n + 1) * m 0 + C (n + 1) := by rw [h.Csucc]

/-! ## 2. Orbit-level bounds unavailable to a symbolic word -/

/-- **A step's valuation is bounded by the ordinary size of the current iterate:**
`2^{d_i} ≤ 3 m_i + 1`.

No symbolic word satisfies anything like this — the letters of an abstract admissible word are
unbounded. This is the first genuinely actual-orbit input. -/
theorem valuation_le {m d S C : ℕ → ℕ} (h : Orbit m d S C) (i : ℕ) :
    2 ^ d i ≤ 3 * m i + 1 := by
  have hstep := h.step i
  have : 2 ^ d i * 1 ≤ 2 ^ d i * m (i + 1) := Nat.mul_le_mul_left _ (h.mpos (i + 1))
  omega

/-- One step of the maximal forward growth envelope: `2(m_{i+1}+1) ≤ 3(m_i+1)`. -/
theorem growth_step {m d S C : ℕ → ℕ} (h : Orbit m d S C) (i : ℕ) :
    2 * (m (i + 1) + 1) ≤ 3 * (m i + 1) := by
  have hstep := h.step i
  have hd : (2 : ℕ) ^ 1 ≤ 2 ^ d i := Nat.pow_le_pow_right (by norm_num) (h.dpos i)
  have : 2 * m (i + 1) ≤ 2 ^ d i * m (i + 1) := by
    simpa using Nat.mul_le_mul_right (m (i + 1)) hd
  omega

/-- **Maximal forward growth envelope**, exact: `2^n (m_n + 1) ≤ 3^n (m_0 + 1)`.

In logarithms `log₂ m_n ≤ log₂(m_0 + 1) + n·(α − 1)` with `α − 1 = log₂(3/2) = 0.58496…`: ordinary
size cannot grow faster than that per accelerated step. This is the rate constant against which any
"long confinement forces a large excursion" claim must be measured. -/
theorem growth_envelope {m d S C : ℕ → ℕ} (h : Orbit m d S C) (n : ℕ) :
    2 ^ n * (m n + 1) ≤ 3 ^ n * (m 0 + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hs := growth_step h n
      calc 2 ^ (n + 1) * (m (n + 1) + 1) = 2 ^ n * (2 * (m (n + 1) + 1)) := by ring
        _ ≤ 2 ^ n * (3 * (m n + 1)) := Nat.mul_le_mul_left _ hs
        _ = 3 * (2 ^ n * (m n + 1)) := by ring
        _ ≤ 3 * (3 ^ n * (m 0 + 1)) := Nat.mul_le_mul_left _ ih
        _ = 3 ^ (n + 1) * (m 0 + 1) := by ring

/-! ## 3. The corridor bound is automatic, not a hypothesis -/

/-- **The corridor is automatic.** From `m_n ≥ 1` alone,

```
2^{S_n}  ≤  3^n·m_0 + C_n .
```

Dividing by `3^n` this is `R_n ≤ log₂ m_0 + E_n` with `E_n = log₂(1 + C_n/(3^n m_0)) ≥ 0`. So the
hypothesis `R_i ≤ A` of `U_all` is satisfied by **every** positive orbit with
`A = log₂ m_0 + E`, and imposes no restriction beyond the size of `E`. -/
theorem corridor_automatic {m d S C : ℕ → ℕ} (h : Orbit m d S C) (n : ℕ) :
    2 ^ S n ≤ 3 ^ n * m 0 + C n := by
  have hid := aggregate_identity h n
  have : 2 ^ S n * 1 ≤ 2 ^ S n * m n := Nat.mul_le_mul_left _ (h.mpos n)
  omega

/-- **And it is attained.** As soon as the orbit reaches `1`, the automatic bound is an equality.
So for any orbit that reaches `1`, the least valid corridor width is *exactly* `log₂ m_0 + E`, not
merely bounded by it. -/
theorem corridor_attained {m d S C : ℕ → ℕ} (h : Orbit m d S C) (n : ℕ) (hn : m n = 1) :
    2 ^ S n = 3 ^ n * m 0 + C n := by
  have hid := aggregate_identity h n
  rw [hn, Nat.mul_one] at hid
  exact hid

/-! ## 4. What `U_all` actually assumes -/

/-- **`U_all` at the minimal valid corridor is a total-stopping-time bound.**

Instantiating the hypothesis with the automatic corridor `A = log₂ m + E` (§3) turns
`L ≤ K(log₂ m + A)` into `L ≤ K(2 log₂ m + E)`. Since `E` is `O(log L)` with a small constant for
an injective orbit, this is `L ≤ 2K log₂ m + O(K log log m)`. -/
theorem Uall_gives_stopping_bound (K L logm A E : ℝ)
    (hA : A = logm + E) (hU : L ≤ K * (logm + A)) :
    L ≤ K * (2 * logm + E) := by
  rw [hA] at hU
  calc L ≤ K * (logm + (logm + E)) := hU
    _ = K * (2 * logm + E) := by ring

/-- **And conversely.** A total-stopping-time bound `L ≤ K'·log₂ m` gives back the corridor-uniform
statement for every `A ≥ 0`, with the same constant.

Together with the previous theorem, `U_all(K)` is equivalent — up to a factor `2` in the constant —
to "every accelerated orbit reaches `1` within `O(log₂ m)` steps". It is therefore not a mild
dynamical hypothesis about corridors: it is the `O(log n)` total-stopping-time conjecture, which in
particular implies the Collatz conjecture itself. -/
theorem stopping_bound_gives_Uall (K' L logm A : ℝ) (hK : 0 ≤ K') (hA : 0 ≤ A)
    (hT : L ≤ K' * logm) : L ≤ K' * (logm + A) := by
  nlinarith [hT, mul_nonneg hK hA]

/-- **No unbounded injective segment.** If every injective initial segment length is bounded by a
single real `B`, the orbit cannot be injective at arbitrarily large depth.

Combined with the previous two theorems this is the sharpest consequence of `U_all(K)`: taking the
corridor at its automatic value gives `L ≤ K(2log₂m + E_L)`, and for an injective segment the
values are distinct odd positive integers, so
`E_L = log₂ Π(1+1/(3m_j)) ≤ (1/(3 ln 2))·Σ_{j<L} 1/m_j ≤ 0.2404·ln L + 0.48`.
That grows slower than `L`, so the inequality bounds `L`. Hence

> `U_all(K)` implies that **no accelerated orbit is injective forever** — i.e. there are no
> divergent Collatz orbits.

The absorption of the `log L` term is elementary but needs a real-analytic step, so it is not
formalized here; what is formalized is the endpoint, which is where the Archimedean property
enters. -/
theorem no_unbounded_injective (B : ℝ) (h : ∀ L : ℕ, (L : ℝ) ≤ B) : False := by
  obtain ⟨n, hn⟩ := exists_nat_gt B
  exact absurd (h n) (not_le.mpr hn)

end OrbitLifetime
end EOC
