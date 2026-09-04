import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Real.Basic

/-!
# Harmonic arithmetic-progression discrepancy (Tao-like EOC program, Milestone 2)

Finite, deterministic discrepancy estimates comparing the mass of one residue class modulo
`M` against `1/M` of the total mass, first for plain counting (Layer A) and then for
nonnegative decreasing weights (Layer B), specialized to harmonic weights `1/(A + D*j)`.

## Connection to `cylinder_restart` (Milestone 1)

This module is deliberately standalone: it proves a generic finite-sum fact and does not
import `EOC.TaoLike.Cylinder`. The bridge to Milestone 1 is only sketched here, in prose,
as scope for this milestone stops before formalizing it.

`EOC.TaoLike.Cylinder.cylinder_restart` shows that inside a realized prefix cylinder for a
word `d` of length `t`, every seed of the form `m = r + 2^(S d t + 1) * k` (for `r` the base
seed and `k : ℕ` arbitrary) also realizes `d`, and its `t`-th iterate is exactly translated:
`T^t(m) = orbit m t = orbit r t + 2 * 3^t * k`. Because `3^t` is odd, imposing a residue
condition on `T^t(m)` modulo a power of `2` is *equivalent* to a single residue condition on
the free parameter `k` modulo an appropriate power of `2` — i.e. exactly the arithmetic
progression `k ≡ u (mod M)` handled by `residue_count_discrepancy` /
`weighted_residue_discrepancy` above, with modulus `M` a power of `2`.

The natural harmonic weight to place on such seeds is `1/m = 1/(r + 2^(S d t + 1) * k)`,
which is precisely of the form `1/(A0 + D*k)` handled by `harmonic_ap_discrepancy`
(`A0 = r`, `D = 2^(S d t + 1)`, both meeting the theorem's hypotheses `A0 > 0`, `D ≥ 0`
whenever the base seed `r` is positive). So `harmonic_ap_discrepancy` gives an explicit,
unconditional bound on how far the harmonic mass of `{k : k ≡ u (mod M)}` among the first
`N` restarts can deviate from `1/M` of the total harmonic mass of all `N` restarts.

This is the finite analytic bridge:

```
Cylinder Restart (Milestone 1)
        │  m = r + 2^(S d t + 1) * k,  orbit m t = orbit r t + 2 * 3^t * k
        ▼
arithmetic progression in k (residue class mod a power of 2)
        │
        ▼
harmonic AP discrepancy (this file)
        │
        ▼
conditional residue total variation      [NEXT MILESTONE — not implemented here]
```

The final arrow (turning this deterministic discrepancy bound into a conditional
residue-TV estimate against a reference/limiting distribution) is explicitly out of scope
for this milestone and is not implemented in this file.
-/

namespace EOC

open Finset

/-! ### Layer A: residue-count discrepancy -/

private theorem exists_shift_residue (M k0 u : ℕ) (hM : 0 < M) :
    ∃ v0 < M, ∀ j : ℕ, (k0 + j) % M = u % M ↔ j % M = v0 := by
  have : NeZero M := ⟨hM.ne'⟩
  refine ⟨((u : ZMod M) - (k0 : ZMod M)).val, ZMod.val_lt _, fun j => ?_⟩
  set v0 : ZMod M := (u : ZMod M) - (k0 : ZMod M) with hv0def
  have hvv : v0.val % M = v0.val := Nat.mod_eq_of_lt (ZMod.val_lt v0)
  constructor
  · intro h
    have hmodeq : (k0 + j) ≡ u [MOD M] := h
    have hcast : ((k0 + j : ℕ) : ZMod M) = (u : ZMod M) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmodeq
    have heq : (j : ZMod M) = v0 := by
      push_cast at hcast
      rw [hv0def, eq_sub_iff_add_eq, add_comm]
      exact hcast
    have hv : ((v0.val : ℕ) : ZMod M) = v0 := ZMod.natCast_rightInverse v0
    have hcast2 : (j : ZMod M) = (v0.val : ZMod M) := by rw [hv, heq]
    have hme : j % M = v0.val % M := (ZMod.natCast_eq_natCast_iff j v0.val M).mp hcast2
    rwa [hvv] at hme
  · intro h
    have hmodeq : j ≡ v0.val [MOD M] := by
      show j % M = v0.val % M
      rw [hvv]; exact h
    have hcast : (j : ZMod M) = (v0.val : ZMod M) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmodeq
    have hv : ((v0.val : ℕ) : ZMod M) = v0 := ZMod.natCast_rightInverse v0
    rw [hv] at hcast
    have hgoal : ((k0 + j : ℕ) : ZMod M) = (u : ZMod M) := by
      push_cast
      rw [hcast, hv0def]
      ring
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hgoal

/-- **Residue count discrepancy.** For any modulus `M ≥ 1`, starting point `k0`, target
residue `u`, and window length `N`, the count of `j < N` with `k0 + j ≡ u (mod M)` differs
from the expected fraction `N / M` by at most `1`. -/
theorem residue_count_discrepancy (M : ℕ) (hM : 1 ≤ M) (k0 u N : ℕ) :
    |(((range N).filter (fun j => (k0 + j) % M = u % M)).card : ℝ)
        - (N : ℝ) / (M : ℝ)| ≤ (1 : ℝ) := by
  obtain ⟨v0, hv0M, hv0⟩ := exists_shift_residue M k0 u hM
  have hfilter : (range N).filter (fun j => (k0 + j) % M = u % M)
      = (range N).filter (fun j : ℕ => j ≡ v0 [MOD M]) := by
    apply Finset.filter_congr
    intro j _
    rw [hv0 j]
    show (j % M = v0) ↔ (j % M = v0 % M)
    rw [Nat.mod_eq_of_lt hv0M]
  have hcount : ((range N).filter (fun j : ℕ => j ≡ v0 [MOD M])).card
      = N / M + (if v0 % M < N % M then 1 else 0) := by
    rw [← Nat.count_eq_card_filter_range]
    exact Nat.count_modEq_card N hM v0
  rw [hfilter, hcount, Nat.mod_eq_of_lt hv0M]
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hNreal : (N : ℝ) = (M : ℝ) * ((N / M : ℕ) : ℝ) + ((N % M : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod N M).symm
  have hdiv : (N : ℝ) / (M : ℝ) = ((N / M : ℕ) : ℝ) + ((N % M : ℕ) : ℝ) / (M : ℝ) := by
    rw [hNreal, add_div, mul_div_cancel_left₀ _ hMR.ne']
  have hrlt : ((N % M : ℕ) : ℝ) < (M : ℝ) := by exact_mod_cast Nat.mod_lt N hM
  have hrnn : (0 : ℝ) ≤ ((N % M : ℕ) : ℝ) := by positivity
  rw [hdiv]
  push_cast
  split_ifs with hcond
  · rw [abs_of_nonneg (by
        have : ((N % M : ℕ) : ℝ) / (M : ℝ) < 1 := (div_lt_one hMR).mpr hrlt
        linarith)]
    have : ((N % M : ℕ) : ℝ) / (M : ℝ) ≥ 0 := by positivity
    linarith
  · rw [show ((N / M : ℕ) : ℝ) + 0 - (((N / M : ℕ) : ℝ) + ((N % M : ℕ) : ℝ) / (M : ℝ))
        = -(((N % M : ℕ) : ℝ) / (M : ℝ)) by ring]
    rw [abs_neg, abs_of_nonneg (by positivity)]
    have : ((N % M : ℕ) : ℝ) / (M : ℝ) < 1 := (div_lt_one hMR).mpr hrlt
    linarith

/-! ### Layer B: generic weighted discrepancy -/

private theorem telescoping_sub (g : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ range n, (g i - g (i + 1)) = g 0 - g n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

/-- **Generic weighted discrepancy (Abel summation).** If every prefix sum of `c` is bounded
by `1` in absolute value, and `g` is a nonnegative sequence that is decreasing on
`Finset.range N`, then the weighted sum `∑ j < N, c j * g j` is bounded by `g 0`. -/
theorem weighted_residue_discrepancy (c g : ℕ → ℝ) (N : ℕ)
    (hbound : ∀ n ≤ N, |∑ j ∈ range n, c j| ≤ 1)
    (hg0 : 0 ≤ g 0)
    (hg_nonneg : ∀ j < N, 0 ≤ g j)
    (hg_anti : ∀ i, i + 1 < N → g (i + 1) ≤ g i) :
    |∑ j ∈ range N, c j * g j| ≤ g 0 := by
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0; simpa using hg0
  have heq : ∑ j ∈ range N, c j * g j = ∑ j ∈ range N, g j * c j := by
    apply Finset.sum_congr rfl; intro j _; ring
  rw [heq]
  have key := Finset.sum_range_by_parts g c N
  simp only [smul_eq_mul] at key
  rw [key]
  have hgNle : 0 ≤ g (N - 1) := hg_nonneg (N - 1) (by omega)
  have hterm1 : |g (N - 1) * ∑ j ∈ range N, c j| ≤ g (N - 1) := by
    rw [abs_mul, abs_of_nonneg hgNle]
    calc g (N - 1) * |∑ j ∈ range N, c j| ≤ g (N - 1) * 1 :=
          mul_le_mul_of_nonneg_left (hbound N le_rfl) hgNle
      _ = g (N - 1) := mul_one _
  have hterm2 : |∑ i ∈ range (N - 1), (g (i + 1) - g i) * ∑ j ∈ range (i + 1), c j|
      ≤ g 0 - g (N - 1) := by
    have hstep : |∑ i ∈ range (N - 1), (g (i + 1) - g i) * ∑ j ∈ range (i + 1), c j|
        ≤ ∑ i ∈ range (N - 1), (g i - g (i + 1)) := by
      calc |∑ i ∈ range (N - 1), (g (i + 1) - g i) * ∑ j ∈ range (i + 1), c j|
          ≤ ∑ i ∈ range (N - 1), |(g (i + 1) - g i) * ∑ j ∈ range (i + 1), c j| :=
            abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ range (N - 1), (g i - g (i + 1)) := by
            apply Finset.sum_le_sum
            intro i hi
            have hile : i + 1 < N := by
              simp only [Finset.mem_range] at hi; omega
            have hanti : g (i + 1) ≤ g i := hg_anti i hile
            have hCle : |∑ j ∈ range (i + 1), c j| ≤ 1 := hbound (i + 1) (by omega)
            rw [abs_mul, abs_of_nonpos (by linarith), neg_sub]
            calc (g i - g (i + 1)) * |∑ j ∈ range (i + 1), c j| ≤ (g i - g (i + 1)) * 1 :=
                  mul_le_mul_of_nonneg_left hCle (by linarith)
              _ = g i - g (i + 1) := mul_one _
    rwa [telescoping_sub] at hstep
  calc |g (N - 1) * ∑ j ∈ range N, c j
        - ∑ i ∈ range (N - 1), (g (i + 1) - g i) * ∑ j ∈ range (i + 1), c j|
      ≤ |g (N - 1) * ∑ j ∈ range N, c j|
          + |∑ i ∈ range (N - 1), (g (i + 1) - g i) * ∑ j ∈ range (i + 1), c j| := by
        have h := abs_add_le (g (N - 1) * ∑ j ∈ range N, c j)
          (-(∑ i ∈ range (N - 1), (g (i + 1) - g i) * ∑ j ∈ range (i + 1), c j))
        rwa [← sub_eq_add_neg, abs_neg] at h
    _ ≤ g (N - 1) + (g 0 - g (N - 1)) := add_le_add hterm1 hterm2
    _ = g 0 := by ring

/-! ### Part 7: harmonic specialization -/

/-- **Harmonic arithmetic-progression discrepancy.** For a modulus `M ≥ 1`, starting point
`k0`, target residue `u`, window length `N`, and harmonic weight `1 / (A0 + D * j)` with
`A0 > 0` and `D ≥ 0`, the harmonic mass carried by one residue class differs from `1/M` of
the total harmonic mass by at most `1 / A0`. -/
theorem harmonic_ap_discrepancy (M : ℕ) (hM : 1 ≤ M) (k0 u N : ℕ) (A0 D : ℝ)
    (hA0 : 0 < A0) (hD : 0 ≤ D) :
    |∑ j ∈ range N, (if (k0 + j) % M = u % M then (1 : ℝ) / (A0 + D * j) else 0)
        - (1 / (M : ℝ)) * ∑ j ∈ range N, (1 : ℝ) / (A0 + D * j)| ≤ 1 / A0 := by
  set g : ℕ → ℝ := fun j => 1 / (A0 + D * j) with hgdef
  set c : ℕ → ℝ := fun j => (if (k0 + j) % M = u % M then (1 : ℝ) else 0) - 1 / (M : ℝ)
    with hcdef
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hden : ∀ j : ℕ, 0 < A0 + D * (j : ℝ) := fun j => by positivity
  have hg0 : 0 ≤ g 0 := by
    show 0 ≤ 1 / (A0 + D * (0 : ℕ)); positivity
  have hg_nonneg : ∀ j < N, 0 ≤ g j := fun j _ => by
    show 0 ≤ 1 / (A0 + D * (j : ℕ)); positivity
  have hg_anti : ∀ i, i + 1 < N → g (i + 1) ≤ g i := by
    intro i _
    show 1 / (A0 + D * ((i : ℕ) + 1 : ℕ)) ≤ 1 / (A0 + D * (i : ℕ))
    apply one_div_le_one_div_of_le (hden i)
    have : (0:ℝ) ≤ D := hD
    push_cast
    nlinarith
  have hcsum : ∀ n : ℕ, ∑ j ∈ range n, c j
      = (((range n).filter (fun j => (k0 + j) % M = u % M)).card : ℝ) - (n : ℝ) / (M : ℝ) := by
    intro n
    simp only [hcdef]
    rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one_div]
  have hbound : ∀ n ≤ N, |∑ j ∈ range n, c j| ≤ 1 := fun n _ => by
    rw [hcsum n]; exact residue_count_discrepancy M hM k0 u n
  have key := weighted_residue_discrepancy c g N hbound hg0 hg_nonneg hg_anti
  have hpt : ∀ j : ℕ, c j * g j
      = (if (k0 + j) % M = u % M then g j else 0) - (1 / (M : ℝ)) * g j := by
    intro j; simp only [hcdef]; split_ifs <;> ring
  have hsum_eq : ∑ j ∈ range N, c j * g j
      = ∑ j ∈ range N, (if (k0 + j) % M = u % M then g j else 0)
        - (1 / (M : ℝ)) * ∑ j ∈ range N, g j := by
    simp_rw [hpt]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hsum_eq] at key
  simpa only [hgdef, Nat.cast_zero, mul_zero, add_zero, one_div] using key

end EOC
