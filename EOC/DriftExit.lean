import EOC.OrbitLifetime

/-!
# The time axis: drift exit, in exact integer form

Companion to `docs/TIME_AXIS_DRIFT_EXIT_IMPOSSIBILITY_AUDIT.md`.

For an accelerated positive orbit the drift is `R_n = S_n − nα`, `α = log₂3`. Since `S_n` is an
integer and `nα = log₂(3^n)`, the corridor conditions are **purely integral**:

```
R_n ≤ 0   ⟺   2^{S_n} ≤ 3^n ,        R_n > 0   ⟺   3^n < 2^{S_n} .
```

This file uses only that form, so no real-number reasoning is needed anywhere. Everything is
stated against `EOC.OrbitLifetime.Orbit`, whose aggregate identity `2^{S_n}m_n = 3^n m_0 + C_n` is
the only input.

* `carry_pos` — `C_n > 0` for `n ≥ 1`.
* `zeroCorridor_implies_seed_lt` — **the future-minimum theorem.** If `2^{S_n} ≤ 3^n` then
  `m_0 < m_n`. So an orbit that never exits the zero corridor has its seed as a *strict* minimum
  of its entire future.
* `driftExit_of_not_gt` — the contrapositive: `m_n ≤ m_0` already forces `3^n < 2^{S_n}`. Ordinary
  descent implies drift exit, and only the weak inequality `m_n ≤ m_0` is needed.
* `cycle_driftExit` — a genuine cycle has strictly positive period drift, so every point of a cycle
  exits. Drift exit is therefore **compatible with nontrivial cycles**: it is a divergence
  obstruction, not a cycle obstruction.
* `driftExit_of_valuation` — **the self-financing inequality.** One step with `2^d·m_0 > 3·m_n`
  achieves drift exit. The available valuation is capped by `2^d ≤ 3m_n + 1`
  (`OrbitLifetime.valuation_le`), which exceeds the sufficient threshold `3m_n/m_0` by a factor
  `≈ m_0`. Recovery capacity grows in lockstep with the drift depth it must repay.
* `realizerFloor_of_lifetime` — the residue/time transfer: a lifetime bound `L(m) ≤ F(m)` inverts
  to a least-realizer floor.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace DriftExit

open OrbitLifetime

/-! ## 1. The carry is positive -/

/-- `C_n > 0` for every `n ≥ 1`. -/
theorem carry_pos {m d S C : ℕ → ℕ} (h : Orbit m d S C) (n : ℕ) : 0 < C (n + 1) := by
  rw [h.Csucc]
  have : 0 < 2 ^ S n := Nat.two_pow_pos _
  omega

/-! ## 2. Zero corridor forces the seed to be a strict future minimum -/

/-- **Future-minimum theorem.** If the orbit is in the zero corridor at step `n+1`, i.e.
`2^{S_{n+1}} ≤ 3^{n+1}`, then `m_0 < m_{n+1}`.

Hence a positive orbit that never leaves the zero corridor has `m_0 < m_n` for every `n ≥ 1`: the
seed is a strict minimum of its whole future. This is the exact ordinary-arithmetic content of
indefinite zero confinement. -/
theorem zeroCorridor_implies_seed_lt {m d S C : ℕ → ℕ} (h : Orbit m d S C) (n : ℕ)
    (hc : 2 ^ S (n + 1) ≤ 3 ^ (n + 1)) : m 0 < m (n + 1) := by
  have hid := aggregate_identity h (n + 1)
  have hC := carry_pos h n
  have hpos : 0 < 2 ^ S (n + 1) := Nat.two_pow_pos _
  by_contra hle
  push_neg at hle
  have h1 : 2 ^ S (n + 1) * m (n + 1) ≤ 2 ^ S (n + 1) * m 0 :=
    Nat.mul_le_mul_left _ hle
  have h2 : 2 ^ S (n + 1) * m 0 ≤ 3 ^ (n + 1) * m 0 := Nat.mul_le_mul_right _ hc
  omega

/-- **Ordinary descent implies drift exit**, and only `m_{n+1} ≤ m_0` is needed — the weak
inequality suffices. This is the contrapositive of the previous theorem. -/
theorem driftExit_of_not_gt {m d S C : ℕ → ℕ} (h : Orbit m d S C) (n : ℕ)
    (hle : m (n + 1) ≤ m 0) : 3 ^ (n + 1) < 2 ^ S (n + 1) := by
  by_contra hc
  push_neg at hc
  exact absurd (zeroCorridor_implies_seed_lt h n hc) (by omega)

/-! ## 3. Cycles exit, so drift exit does not exclude them -/

/-- **A genuine cycle has strictly positive period drift.** If `m_{p+1} = m_0` then
`3^{p+1} < 2^{S_{p+1}}`.

So every point of a nontrivial positive cycle has a finite drift exit time, and a universal drift
exit statement is **fully compatible** with the existence of nontrivial cycles. The time axis is a
divergence obstruction only. -/
theorem cycle_driftExit {m d S C : ℕ → ℕ} (h : Orbit m d S C) (p : ℕ)
    (hcyc : m (p + 1) = m 0) : 3 ^ (p + 1) < 2 ^ S (p + 1) :=
  driftExit_of_not_gt h p (le_of_eq hcyc)

/-! ## 4. Recovery is self-financing -/

/-- **The self-financing inequality.** A single step of valuation `d` from state `m_n` achieves
drift exit as soon as

```
2^d · m_0  >  3 · m_n .
```

Compare with the hard cap on the available valuation, `2^d ≤ 3m_n + 1`
(`OrbitLifetime.valuation_le`): the cap exceeds the sufficient threshold `3m_n/m_0` by a factor of
about `m_0`. Since indefinite zero confinement forces `m_n > m_0` (§2) and hence
`log₂ m_n = log₂ m_0 − R_n + E_n`, the resource that permits a large valuation grows **at exactly
the rate** of the accumulated negative drift it would have to repay.

So the natural "deep excursions cannot be repaid" mechanism is blocked: recovery capacity is
self-financing, with surplus. -/
theorem driftExit_of_valuation {m d S C : ℕ → ℕ} (h : Orbit m d S C) (n : ℕ)
    (hgt : 2 ^ d n * m 0 > 3 * m n) : 3 ^ (n + 1) < 2 ^ S (n + 1) := by
  have hid := aggregate_identity h n
  have hmn : 0 < m n := h.mpos n
  have hkey : 3 ^ n * m 0 ≤ 2 ^ S n * m n := by omega
  have hstep : 2 ^ S (n + 1) = 2 ^ d n * 2 ^ S n := by
    rw [h.Ssucc, pow_add]; ring
  -- compare after multiplying by `m n`
  have hL : 3 ^ (n + 1) * m n < 2 ^ S (n + 1) * m n := by
    calc 3 ^ (n + 1) * m n = 3 * m n * 3 ^ n := by ring
      _ < 2 ^ d n * m 0 * 3 ^ n := by
          exact (Nat.mul_lt_mul_right (pow_pos (by norm_num : (0:ℕ) < 3) n)).mpr hgt
      _ = 2 ^ d n * (3 ^ n * m 0) := by ring
      _ ≤ 2 ^ d n * (2 ^ S n * m n) := Nat.mul_le_mul_left _ hkey
      _ = 2 ^ S (n + 1) * m n := by rw [hstep]; ring
  exact lt_of_mul_lt_mul_right hL (Nat.zero_le _)

/-! ## 5. Residue/time transfer -/

/-- **Lifetime bound inverts to a realizer floor.** If every seed below `B` exits the corridor
before depth `N`, then every seed whose orbit is confined through depth `N` is at least `B` — i.e.
the least realizer of a `0`-confined word of length `N` is at least `B`.

This is the exact inversion behind the residue/time duality: a lifetime bound `L(m) ≤ F(m)` gives
`r_min(N) ≥ min{m : F(m) ≥ N}`. Its quantitative content is entirely in how fast `F` grows. -/
theorem realizerFloor_of_lifetime (L : ℕ → ℕ) (N B : ℕ)
    (hsmall : ∀ m, m < B → L m < N) :
    ∀ m, N ≤ L m → B ≤ m := by
  intro m hm
  by_contra hlt
  push_neg at hlt
  exact absurd (hsmall m hlt) (by omega)

end DriftExit
end EOC
