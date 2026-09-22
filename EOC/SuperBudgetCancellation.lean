import EOC.TransportRegeneration
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Ring.GeomSum

/-!
# Forced versus excess 2-adic cancellation

Companion to `docs/SUPERBUDGET_CANCELLATION_EXTERNAL_ARITHMETIC_AUDIT.md`.

The transport note's regeneration quantity is `v₂(a_j − u_j)`, where `X_j = 2^{M_j}a_j` is the
mismatch and `K_j = 2^{M_j}u_j` the failure residue at a genuine first failure. Proposition 29
gives `X_j − K_j = 2^{d_{j+1}}X_{j+1}`, hence the exact split

```
v₂(a_j − u_j)  =  (d_{j+1} − M_j)   +   M_{j+1}
                  ‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾       ‾‾‾‾‾‾‾
                  forced by integrality    excess
```

so the **excess** cancellation is exactly the next matching precision `M_{j+1} = v₂(X_{j+1})`.

The audit's computation identifies `X_j` in closed form: along a genuine positive-integer orbit
with seed `n₀`, the full series `Z = Σ_{i≥0}2^{S_i}3^{−(i+1)}` equals `−n₀` in `ℤ₂`, so

```
χ_j = n₀ mod 2^{S_j},      X_j = ⌊n₀ / 2^{S_j}⌋,      M_j = v₂(⌊n₀ / 2^{S_j}⌋).
```

`M_j` is therefore the length of the run of zero bits of `n₀` beginning at position `S_j`. This
file formalizes the two consequences that are elementary, exact, and *not* restatements of the
open problems.

* `sum_excess_le` — at a failure the excess run ends before `S_{j+2}`, so the runs at distinct
  failures occupy **disjoint** bit intervals of `n₀`. Their total is therefore at most
  `⌊log₂ n₀⌋ + 1`. Cumulative excess regeneration along one genuine orbit is `O(log n₀)`.
* `periodic_floor`, `geom_closed_form` — for a periodic valuation word the carry `C` collapses to
  a **three-term** closed form with coefficients independent of the length, and the realizer
  congruence becomes `2^{Nσ} ∣ c₀ + χΔ` with `c₀, Δ` fixed. Either `c₀ + χΔ = 0` (the cycle case,
  `χ` a fixed small number) or `χ` is exponentially large. This is the fixed-anchor floor, proved
  without any Diophantine machinery.
* `floor_of_cumulative_gain` — the Open Problem C threshold, derived with `S_N ≥ N` rather than
  `S_N ≈ αN`: a cumulative-gain rate `θ < 1` gives the realizer floor with `ε = 1 − θ`.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace SuperBudget

/-! ## 1. The excess is a zero-run, and the runs are disjoint -/

/-- The excess cancellation available at bit position `k` of the seed: the number of zero bits of
`n` starting at position `k`. Equal to `M_j` when `k = S_j`. -/
noncomputable def excess (n k : ℕ) : ℕ := padicValNat 2 (n / 2 ^ k)

/-- **Disjointness telescopes.** If each excess run starting at `pos t` ends at or before the next
position — which is exactly what a *failure* at that step means (`M_{j+1} < d_{j+2}`) — then the
runs occupy disjoint bit intervals and their total is bounded by the span.

```
pos 0 + Σ_{t<r} excess n (pos t)  ≤  pos r.
```
-/
theorem sum_excess_le_span (n : ℕ) (pos : ℕ → ℕ) (r : ℕ)
    (hstep : ∀ t, t < r → pos t + excess n (pos t) ≤ pos (t + 1)) :
    pos 0 + ∑ t ∈ Finset.range r, excess n (pos t) ≤ pos r := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hr : pos 0 + ∑ t ∈ Finset.range r, excess n (pos t) ≤ pos r :=
        ih fun t ht => hstep t (by omega)
      have hlast := hstep r (by omega)
      rw [Finset.sum_range_succ]
      omega

/-- **Cumulative excess regeneration along one genuine orbit is `O(log n₀)`.**

Every excess run lives inside the binary expansion of the seed, so once the positions stay below
`⌊log₂ n₀⌋ + 1` the disjoint runs sum to at most that. Along a genuine positive-integer orbit the
positions are the valuation sums `S_j`, and `X_j = 0` — perfect transport forever — as soon as
`2^{S_j} > n₀`. Hence the number of failures is at most `log₂ n₀` and the total excess is too.

This is the audit's main positive theorem and it needs no external arithmetic. -/
theorem sum_excess_le (n : ℕ) (pos : ℕ → ℕ) (r : ℕ)
    (hstep : ∀ t, t < r → pos t + excess n (pos t) ≤ pos (t + 1))
    (hlast : pos r ≤ Nat.log 2 n + 1) :
    ∑ t ∈ Finset.range r, excess n (pos t) ≤ Nat.log 2 n + 1 := by
  have := sum_excess_le_span n pos r hstep
  omega

/-- The run at a position beyond the top bit of the seed is the whole tail: `n / 2^k = 0`, which
is the `M_j = ∞` branch of the perfect-tail dichotomy. Recorded as the exact side condition that
`sum_excess_le` needs its positions to avoid. -/
theorem div_eq_zero_of_log_lt {n k : ℕ} (h : Nat.log 2 n < k) : n / 2 ^ k = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact Nat.div_eq_of_lt (Nat.lt_pow_succ_log_self (by norm_num) n |>.trans_le
      (Nat.pow_le_pow_right (by norm_num) (by omega)))

/-! ## 2. The periodic sector collapses to three terms -/

/-- The geometric identity behind the periodic closed form:
`(x − y)·Σ_{k<N} x^{N−1−k} y^k = x^N − y^N`.

With `x = 3^p` and `y = 2^σ` this turns the length-`Np` carry sum — which has `Np` terms in
general — into a fixed three-term expression whose coefficients do not grow with `N`. That
collapse, not any Diophantine input, is what makes the periodic sector tractable. -/
theorem geom_closed_form (x y : ℤ) (N : ℕ) :
    (x - y) * ∑ k ∈ Finset.range N, x ^ (N - 1 - k) * y ^ k = x ^ N - y ^ N := by
  have h := geom_sum₂_mul y x N
  have hcomm : ∑ i ∈ Finset.range N, y ^ i * x ^ (N - 1 - i)
      = ∑ k ∈ Finset.range N, x ^ (N - 1 - k) * y ^ k :=
    Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [hcomm] at h
  linear_combination -h

/-- **The periodic fixed-anchor floor.** If a fixed nonzero combination `c₀ + χ·Δ` is divisible by
`2^m`, then either it vanishes — the cycle case, pinning `χ` to the single rational `−c₀/Δ` — or

```
2^m  ≤  |c₀| + |χ|·|Δ|,
```

so `χ` grows exponentially in `m`. For a periodic valuation word `m = Nσ = S_N`, and `c₀`, `Δ` are
determined by one period, so this *is* the realizer floor for that sector, with no linear forms in
logarithms, no S-units, and no subspace theorem. -/
theorem periodic_floor (c₀ Δ χ : ℤ) (m : ℕ) (hdvd : (2 : ℤ) ^ m ∣ c₀ + χ * Δ)
    (hne : c₀ + χ * Δ ≠ 0) : (2 : ℤ) ^ m ≤ |c₀| + |χ| * |Δ| := by
  have h1 : (2 : ℤ) ^ m ≤ |c₀ + χ * Δ| := Int.le_of_dvd (abs_pos.mpr hne) ((dvd_abs _ _).mpr hdvd)
  have h2 : |c₀ + χ * Δ| ≤ |c₀| + |χ * Δ| := abs_add_le _ _
  rw [abs_mul] at h2
  linarith

/-! ## 3. The Open Problem C threshold, taken in the safe direction -/

/-- **The cumulative-gain threshold for the realizer floor.**

From the previous round's bridge `S − log₂ r < H₁ + R₊ + 1`, a cumulative positive-gain bound
`R₊ ≤ θ·N` gives

```
log₂ r  >  (1 − θ)·N − (H₁ + 1).
```

The step uses only `S_N ≥ N`, which holds because every valuation `d_i ≥ 1`. It does **not** use
`S_N ≈ αN`: substituting the Beatty ceiling here would inflate the available depth by the corridor
deficit `⌊αN⌋ − S_N` and overstate the floor. So the safe threshold is `θ < 1`, giving `ε = 1 − θ`,
rather than the `θ < α − ε` that an `S_N ≈ αN` substitution would suggest. -/
theorem floor_of_cumulative_gain (N S : ℕ) (θ logr H₁ R : ℝ)
    (hS : (N : ℝ) ≤ (S : ℝ))
    (hgap : (S : ℝ) - logr < H₁ + R + 1)
    (hR : R ≤ θ * (N : ℝ)) :
    (1 - θ) * (N : ℝ) - (H₁ + 1) < logr := by
  nlinarith [hS, hgap, hR]

/-- The fixed-shell refinement: when the total valuation is pinned at `S`, the threshold is
`θ < S/N`, which is strictly better than `θ < 1` for heavy shells and reduces to it at the light
end `S = N`. The light shell is the binding case. -/
theorem floor_of_cumulative_gain_shell (N S : ℕ) (θ logr H₁ R : ℝ)
    (hgap : (S : ℝ) - logr < H₁ + R + 1)
    (hR : R ≤ θ * (N : ℝ)) :
    (S : ℝ) - θ * (N : ℝ) - (H₁ + 1) < logr := by
  linarith

end SuperBudget
end EOC
