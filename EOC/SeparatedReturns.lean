import EOC.DriftExit
import EOC.ZCRERealizerGrowth

/-!
# Separated returns: the episode decomposition of the corridor

Companion to `docs/SEPARATED_RETURNS_INVESTIGATION.md`.

The occupation functional `O_c(m₀) = #{n : R_n ≤ c}` decomposes into maximal contiguous
*episodes*. This file records what is actually proved about that decomposition.

Throughout, `c : ℕ` and the corridor condition is used in its **exact integral form**

```
R_n ≤ c   ⟺   S_n − nα ≤ c   ⟺   2^{S_n} ≤ 2^c · 3^n ,
```

so no real-number reasoning is needed. `α = log₂ 3` never appears as a real number.

### What is proved here

* `sum_concat` — the **restart relation** `S_{a+k} = S_a + S'_k`, whose drift form is
  `R_{a+k}(m₀) = R_a(m₀) + R_k(m_a)`. An episode entered at time `a` is the initial confined
  window of the *restarted* orbit at the **local** threshold `c − R_a(m₀)`.

* `entry_digit_one`, `entry_threshold_pinned` — the **entry lemma**. At a genuine re-entry the
  valuation digit is forced to be `1`, and consequently the local threshold is *pinned*:
  `0 ≤ c − R_a < α − 1 = log₂(3/2)`. Every episode after the first therefore starts in a corridor
  of width less than `0.585`, **not** a corridor that widens with the accumulated drift.

* `corridor_excludes_one`, `corridor_time_lt_of_reaches_one`, `occupation_le_of_reaches_one` —
  once an orbit reaches `1`, no later time lies in the corridor (provided `2^c ≤ m₀`). Hence
  occupation is confined to the times before arrival at `1`, and **a total-stopping-time bound
  `n* = O(log m₀)` already bounds occupation**. No separate hypothesis on the number of returns
  is needed.

* `oscD`, `reentries`, `exists_horizon_many_reentries`, `exists_odd_seed_with_many_reentries` —
  the **refutation of uniformly bounded episode count**. The word that plays digit `2` inside the
  corridor and digit `1` outside it oscillates forever, and every finite prefix of it is realized
  by a positive odd integer. So for each `c` and each `B` there is an odd seed whose genuine
  accelerated orbit has more than `B` corridor re-entries.

* `count_le_of_summands_ge` — an elementary counting fact, applied here only to a *surrogate*
  sum of coarse per-episode upper bounds. It says nothing about actual episode lengths.

* `upcrossing_band` — a one-step growth statement about a **fixed integer level**. It is not a
  statement about the corridor threshold, which moves with the carry term.

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
condition `R_{a+k} ≤ c` reads `R_k(m_a) ≤ c − R_a(m₀)`, a **local threshold**.

How large that local threshold can be is settled by `entry_threshold_pinned` below: at a genuine
re-entry it is *less than* `α − 1`, not larger than `c`. -/
theorem sum_concat (d : ℕ → ℕ) (S : ℕ → ℕ) (hS0 : S 0 = 0)
    (hS : ∀ i, S (i + 1) = S i + d i) (a k : ℕ) :
    S (a + k) = S a + ∑ j ∈ Finset.range k, d (a + j) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hik : a + (k + 1) = (a + k) + 1 := by omega
      rw [hik, hS (a + k), ih, Finset.sum_range_succ]
      ring

/-! ## 2. The entry lemma: a re-entry forces digit `1`, and pins the local threshold -/

/-- **A genuine re-entry has valuation digit `1`.**

If the orbit is outside the corridor at time `n` (`2^c·3^n < 2^{S_n}`) and inside it at time
`n+1` (`2^{S_{n+1}} ≤ 2^c·3^{n+1}`), then `d_n = 1`.

Reason: a digit `d ≥ 2` multiplies `2^{S}` by at least `4`, while the moving bound `2^c·3^n`
multiplies by only `3`. A step that is already above the bound cannot come back under it while
growing faster than the bound does. In drift terms, `R_{n+1} = R_n + d_n − α` with `1 < α < 2`, so
only `d_n = 1` decreases the drift at all. -/
theorem entry_digit_one {m d S C : ℕ → ℕ} (h : Orbit m d S C) (c n : ℕ)
    (hout : 2 ^ c * 3 ^ n < 2 ^ S n)
    (hin : 2 ^ S (n + 1) ≤ 2 ^ c * 3 ^ (n + 1)) :
    d n = 1 := by
  by_contra hne
  have h2 : 2 ≤ d n := by have := h.dpos n; omega
  have h4 : (2 : ℕ) ^ 2 ≤ 2 ^ d n := Nat.pow_le_pow_right (by norm_num) h2
  have hA : 2 ^ S (n + 1) = 2 ^ d n * 2 ^ S n := by rw [h.Ssucc, pow_add]; ring
  have hB : 2 ^ c * 3 ^ (n + 1) = 3 * (2 ^ c * 3 ^ n) := by rw [pow_succ]; ring
  have hpos : 0 < 2 ^ S n := Nat.two_pow_pos _
  have hkey : 4 * 2 ^ S n ≤ 3 * (2 ^ c * 3 ^ n) := by
    calc 4 * 2 ^ S n = 2 ^ 2 * 2 ^ S n := by norm_num
      _ ≤ 2 ^ d n * 2 ^ S n := Nat.mul_le_mul_right _ h4
      _ = 2 ^ S (n + 1) := hA.symm
      _ ≤ 2 ^ c * 3 ^ (n + 1) := hin
      _ = 3 * (2 ^ c * 3 ^ n) := hB
  omega

/-- **The local threshold at a re-entry is pinned below `α − 1`.**

Integral form: at a genuine re-entry into the corridor at time `n+1`,

```
2 · (2^c · 3^{n+1})  <  3 · 2^{S_{n+1}} .
```

Dividing, `2^{S_{n+1}} / (2^c·3^{n+1}) > 2/3`, i.e. `R_{n+1} > c − log₂(3/2) = c − (α − 1)`.
Together with `R_{n+1} ≤ c` this gives

```
0  ≤  c − R_{n+1}  <  α − 1  =  0.58496… ,
```

a bound **independent of `c`, of `m₀`, and of how deep the drift went during the excursion**.

This corrects the earlier claim that a later episode is governed by a corridor that widens with the
accumulated drift. It does not: only the *first* episode has threshold `c`, and every re-entry is
pinned into a window of width `log₂(3/2)` immediately below `c`. Drift may of course go much deeper
*inside* an episode; that is a statement about the interior, not about the entry point. -/
theorem entry_threshold_pinned {m d S C : ℕ → ℕ} (h : Orbit m d S C) (c n : ℕ)
    (hout : 2 ^ c * 3 ^ n < 2 ^ S n)
    (hin : 2 ^ S (n + 1) ≤ 2 ^ c * 3 ^ (n + 1)) :
    2 * (2 ^ c * 3 ^ (n + 1)) < 3 * 2 ^ S (n + 1) := by
  have hd := entry_digit_one h c n hout hin
  have hA : 2 ^ S (n + 1) = 2 * 2 ^ S n := by rw [h.Ssucc, hd, pow_add]; ring
  have hB : 2 ^ c * 3 ^ (n + 1) = 3 * (2 ^ c * 3 ^ n) := by rw [pow_succ]; ring
  omega

/-- **The real-number reading of `entry_threshold_pinned`.** Once the integral lemma has forced the
entry digit to be `1`, the drift bound is pure arithmetic: `R_{n+1} = R_n + 1 − α` and `R_n > c`
give `c − R_{n+1} < α − 1`. -/
theorem entry_threshold_real (α c Rprev R : ℝ)
    (hstep : R = Rprev + 1 - α) (hout : c < Rprev) : c - R < α - 1 := by
  rw [hstep]; linarith

/-! ## 3. Arrival at `1` ends occupation, so a stopping bound already bounds occupation -/

/-- **The corridor excludes every time at which the orbit equals `1`** (for `2^c ≤ m₀`).

From the aggregate identity `2^{S_{n+1}}·m_{n+1} = 3^{n+1}m₀ + C_{n+1}` with `m_{n+1} = 1`,

```
2^{S_{n+1}} = 3^{n+1}·m₀ + C_{n+1}  >  3^{n+1}·m₀  ≥  2^c·3^{n+1} ,
```

using `C_{n+1} > 0` (`DriftExit.carry_pos`). So the time is outside the corridor. -/
theorem corridor_excludes_one {m d S C : ℕ → ℕ} (h : Orbit m d S C) (c n : ℕ)
    (hone : m (n + 1) = 1) (hm0 : 2 ^ c ≤ m 0) :
    2 ^ c * 3 ^ (n + 1) < 2 ^ S (n + 1) := by
  have hid := aggregate_identity h (n + 1)
  rw [hone, Nat.mul_one] at hid
  have hC := DriftExit.carry_pos h n
  have hle : 2 ^ c * 3 ^ (n + 1) ≤ 3 ^ (n + 1) * m 0 := by
    rw [Nat.mul_comm]
    exact Nat.mul_le_mul_left _ hm0
  omega

/-- **Every corridor time precedes arrival at `1`.** If the orbit is at `1` from time `n*` onwards
(which is automatic for the accelerated map, since `T 1 = 1`) and `2^c ≤ m₀`, then any time in the
corridor is `< n*`. -/
theorem corridor_time_lt_of_reaches_one {m d S C : ℕ → ℕ} (h : Orbit m d S C)
    (c nstar n : ℕ) (hnstar : 1 ≤ nstar) (hone : ∀ k, nstar ≤ k → m k = 1)
    (hm0 : 2 ^ c ≤ m 0) (hin : 2 ^ S n ≤ 2 ^ c * 3 ^ n) :
    n < nstar := by
  by_contra hge
  push_neg at hge
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  exact absurd hin (by
    have := corridor_excludes_one h c j (hone _ hge) hm0
    omega)

/-- **A total-stopping-time bound bounds occupation.** Occupation over any horizon `N` is at most
the arrival time `n*` at `1`.

Consequently the corridor-uniform single-window hypothesis `(U)`, which the lifetime audit shows is
equivalent to an `O(log m)` total-stopping-time bound, **already implies an `O(log m₀)` occupation
bound** for every seed with `m₀ ≥ 2^c`. No extra hypothesis bounding the number of returns is
required — and the earlier claim that `(U)` alone is insufficient is withdrawn. -/
theorem occupation_le_of_reaches_one {m d S C : ℕ → ℕ} (h : Orbit m d S C)
    (c nstar N : ℕ) (hnstar : 1 ≤ nstar) (hone : ∀ k, nstar ≤ k → m k = 1)
    (hm0 : 2 ^ c ≤ m 0) :
    ((Finset.range N).filter (fun n => 2 ^ S n ≤ 2 ^ c * 3 ^ n)).card ≤ nstar := by
  have hsub : ((Finset.range N).filter (fun n => 2 ^ S n ≤ 2 ^ c * 3 ^ n))
      ⊆ Finset.range nstar := by
    intro n hn
    rw [Finset.mem_filter] at hn
    exact Finset.mem_range.mpr
      (corridor_time_lt_of_reaches_one h c nstar n hnstar hone hm0 hn.2)
  calc ((Finset.range N).filter (fun n => 2 ^ S n ≤ 2 ^ c * 3 ^ n)).card
      ≤ (Finset.range nstar).card := Finset.card_le_card hsub
    _ = nstar := Finset.card_range nstar

/-! ## 4. Refuting a uniform bound on the number of episodes

The word below plays digit `2` while inside the corridor and digit `1` while outside it. Digit `2`
raises the drift by `2 − α > 0` and digit `1` lowers it by `α − 1 > 0`, so the drift oscillates
across the level `c` forever. Every finite prefix is realized by a positive odd integer
(`EOC.leastRealizer`), which turns the symbolic oscillation into genuine orbits with arbitrarily
many corridor re-entries. -/

/-- Running valuation sum of the oscillating word: digit `2` inside the corridor, `1` outside. -/
def oscS (c : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => oscS c n + (if 2 ^ oscS c n ≤ 2 ^ c * 3 ^ n then 2 else 1)

/-- The oscillating valuation word itself. -/
def oscD (c n : ℕ) : ℕ := if 2 ^ oscS c n ≤ 2 ^ c * 3 ^ n then 2 else 1

/-- "Time `n` lies in the corridor", for the oscillating word. -/
def InC (c n : ℕ) : Prop := 2 ^ oscS c n ≤ 2 ^ c * 3 ^ n

instance (c n : ℕ) : Decidable (InC c n) := Nat.decLe _ _

theorem oscS_succ (c n : ℕ) : oscS c (n + 1) = oscS c n + oscD c n := rfl

theorem oscD_eq_two {c n : ℕ} (h : InC c n) : oscD c n = 2 := if_pos h

theorem oscD_eq_one {c n : ℕ} (h : ¬ InC c n) : oscD c n = 1 := if_neg h

theorem oscD_pos (c n : ℕ) : 1 ≤ oscD c n := by
  by_cases h : InC c n
  · rw [oscD_eq_two h]; omega
  · rw [oscD_eq_one h]

/-- The repository's prefix sum `S` of the oscillating word is `oscS`. -/
theorem S_oscD (c n : ℕ) : S (oscD c) n = oscS c n := by
  induction n with
  | zero => simp [S, s_zero, oscS]
  | succ n ih => rw [S, s_succ, ← S, ih, oscS_succ]

/-- **Global invariant:** `3·2^{S_n} ≤ 4·(2^c·3^n)`, i.e. the drift never rises more than
`log₂(4/3)` above the level `c`. -/
theorem osc_invariant (c n : ℕ) : 3 * 2 ^ oscS c n ≤ 4 * (2 ^ c * 3 ^ n) := by
  induction n with
  | zero =>
      have : (1 : ℕ) ≤ 2 ^ c := Nat.one_le_two_pow
      simp only [oscS, pow_zero, Nat.mul_one]
      omega
  | succ n ih =>
      have hB : 2 ^ c * 3 ^ (n + 1) = 3 * (2 ^ c * 3 ^ n) := by rw [pow_succ]; ring
      by_cases h : InC c n
      · have hA : 2 ^ oscS c (n + 1) = 4 * 2 ^ oscS c n := by
          rw [oscS_succ, oscD_eq_two h, pow_add]; ring
        have hc : 2 ^ oscS c n ≤ 2 ^ c * 3 ^ n := h
        omega
      · have hA : 2 ^ oscS c (n + 1) = 2 * 2 ^ oscS c n := by
          rw [oscS_succ, oscD_eq_one h, pow_add]; ring
        omega

/-- **Re-entry is immediate.** A single digit-`1` step from outside the corridor lands back
inside it: the drift falls by `α − 1 = log₂(3/2)`, and by the invariant it was at most
`log₂(4/3)` above the level. -/
theorem reentry_immediate {c n : ℕ} (h : ¬ InC c n) : InC c (n + 1) := by
  have hinv := osc_invariant c n
  have hA : 2 ^ oscS c (n + 1) = 2 * 2 ^ oscS c n := by
    rw [oscS_succ, oscD_eq_one h, pow_add]; ring
  have hB : 2 ^ c * 3 ^ (n + 1) = 3 * (2 ^ c * 3 ^ n) := by rw [pow_succ]; ring
  change 2 ^ oscS c (n + 1) ≤ 2 ^ c * 3 ^ (n + 1)
  omega

/-- Bernoulli in the form needed: `(4/3)^j ≥ 1 + j/3`. -/
private theorem bernoulli_four_three (j : ℕ) : 3 ^ j * (3 + j) ≤ 3 * 4 ^ j := by
  induction j with
  | zero => norm_num
  | succ j ih =>
      have h34 : (3 : ℕ) ^ j ≤ 4 ^ j := Nat.pow_le_pow_left (by norm_num) j
      calc 3 ^ (j + 1) * (3 + (j + 1)) = 3 * (3 ^ j * (3 + j)) + 3 * 3 ^ j := by ring
        _ ≤ 3 * (3 * 4 ^ j) + 3 * 4 ^ j := by
            exact Nat.add_le_add (Nat.mul_le_mul_left _ ih) (Nat.mul_le_mul_left _ h34)
        _ = 3 * 4 ^ (j + 1) := by ring

/-- **The oscillation never stops:** there is an exit from the corridor at or after every time.

If the orbit stayed in the corridor from `n` onwards it would take digit `2` forever, multiplying
`2^{S}` by `4` per step while the bound `2^c·3^n` multiplies by only `3`. The ratio `(4/3)^j` grows
without bound, so the corridor condition fails after at most `3·2^c·3^n` further steps. -/
theorem exists_exit_ge (c n : ℕ) : ∃ k, n ≤ k ∧ ¬ InC c k := by
  by_contra hcon
  push_neg at hcon
  have hstep : ∀ j, oscS c (n + j) = oscS c n + 2 * j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        have hj : InC c (n + j) := hcon _ (Nat.le_add_right _ _)
        have hone : oscS c (n + j + 1) = oscS c (n + j) + 2 := by
          rw [oscS_succ, oscD_eq_two hj]
        rw [show n + (j + 1) = (n + j) + 1 from by omega, hone, ih]
        ring
  set Y : ℕ := 2 ^ c * 3 ^ n with hY
  have hYpos : 0 < Y := by positivity
  have hin : InC c (n + 3 * Y) := hcon _ (Nat.le_add_right _ _)
  have hval : (2 : ℕ) ^ oscS c (n + 3 * Y) = 2 ^ oscS c n * 4 ^ (3 * Y) := by
    rw [hstep, pow_add]
    congr 1
    rw [pow_mul]
    norm_num
  have hbnd : (2 : ℕ) ^ c * 3 ^ (n + 3 * Y) = Y * 3 ^ (3 * Y) := by
    rw [pow_add, hY]; ring
  have hle : (4 : ℕ) ^ (3 * Y) ≤ Y * 3 ^ (3 * Y) := by
    have h1 : (1 : ℕ) * 4 ^ (3 * Y) ≤ 2 ^ oscS c n * 4 ^ (3 * Y) :=
      Nat.mul_le_mul_right _ Nat.one_le_two_pow
    have h2 : (2 : ℕ) ^ oscS c (n + 3 * Y) ≤ 2 ^ c * 3 ^ (n + 3 * Y) := hin
    rw [hval] at h2
    rw [hbnd] at h2
    omega
  have hber := bernoulli_four_three (3 * Y)
  have hpos : 0 < (3 : ℕ) ^ (3 * Y) := by positivity
  have hchain : 3 ^ (3 * Y) * (3 + 3 * Y) ≤ 3 ^ (3 * Y) * (3 * Y) := by
    calc 3 ^ (3 * Y) * (3 + 3 * Y) ≤ 3 * 4 ^ (3 * Y) := hber
      _ ≤ 3 * (Y * 3 ^ (3 * Y)) := Nat.mul_le_mul_left _ hle
      _ = 3 ^ (3 * Y) * (3 * Y) := by ring
  have := Nat.le_of_mul_le_mul_left hchain hpos
  omega

/-- The `i`-th exit time of the oscillating word. -/
def exitTime (c : ℕ) : ℕ → ℕ
  | 0 => Nat.find (exists_exit_ge c 0)
  | i + 1 => Nat.find (exists_exit_ge c (exitTime c i + 1))

theorem exitTime_not_mem (c i : ℕ) : ¬ InC c (exitTime c i) := by
  cases i with
  | zero => exact (Nat.find_spec (exists_exit_ge c 0)).2
  | succ i => exact (Nat.find_spec (exists_exit_ge c (exitTime c i + 1))).2

theorem exitTime_lt_succ (c i : ℕ) : exitTime c i < exitTime c (i + 1) := by
  have := (Nat.find_spec (exists_exit_ge c (exitTime c i + 1))).1
  exact lt_of_lt_of_le (Nat.lt_succ_self _) this

theorem exitTime_strictMono (c : ℕ) : StrictMono (exitTime c) :=
  strictMono_nat_of_lt_succ (exitTime_lt_succ c)

/-- The re-entry times of the oscillating word before horizon `N`: times at which the orbit is
outside the corridor and inside it one step later. The initial episode is *not* a re-entry. -/
def reentries (c N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun n => ¬ InC c n ∧ InC c (n + 1))

/-- **Arbitrarily many re-entries occur before a finite horizon.** -/
theorem exists_horizon_many_reentries (c B : ℕ) :
    ∃ N, 1 ≤ N ∧ B ≤ (reentries c N).card := by
  refine ⟨exitTime c B + 1, by omega, ?_⟩
  have hmaps : ∀ i ∈ Finset.range B, exitTime c i ∈ reentries c (exitTime c B + 1) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [reentries, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, exitTime_not_mem c i, reentry_immediate (exitTime_not_mem c i)⟩
    have := exitTime_strictMono c hi
    omega
  have hinj : Set.InjOn (exitTime c) (Finset.range B) :=
    fun x _ y _ hxy => (exitTime_strictMono c).injective hxy
  calc B = (Finset.range B).card := (Finset.card_range B).symm
    _ ≤ (reentries c (exitTime c B + 1)).card := Finset.card_le_card_of_injOn _ hmaps hinj

/-- **The refutation of a uniform episode bound.**

For every threshold `c` and every `B` there is a positive odd integer `m₀` whose *genuine*
accelerated orbit follows the oscillating word for `N` steps and has at least `B` corridor
re-entries before time `N`. The orbit's own prefix sums coincide with `oscS`, so the re-entry count
is a statement about that orbit's drift, not about a symbolic word.

Hence the hypothesis "`P_c(m₀) ≤ P₀` for all odd `m₀` with `P₀` independent of `m₀`" is **false**
for every `c`.

Two scope points, both essential:

* the realizing seed grows with `B` — nothing here bounds it from above by anything useful, and
  `leastRealizer_lt` only gives `m₀ < 2^{S_N+1}`;
* the count is a **finite-horizon** count of re-entries before time `N`. Nothing is claimed about
  the total occupation of these seeds, nor about infinite realization. -/
theorem exists_odd_seed_with_many_reentries (c B : ℕ) :
    ∃ N m0 : ℕ, 1 ≤ N ∧ Odd m0 ∧
      (∀ i < N, a (orbit m0 i) = oscD c i) ∧
      (∀ n ≤ N, S (fun i => a (orbit m0 i)) n = oscS c n) ∧
      B ≤ (reentries c N).card := by
  obtain ⟨N, hN, hcard⟩ := exists_horizon_many_reentries c B
  have hd_pos : ∀ i < N, 1 ≤ oscD c i := fun i _ => oscD_pos c i
  set m0 : ℕ := leastRealizer (oscD c) N with hm0
  have hodd : Odd m0 := leastRealizer_odd (oscD c) N hN hd_pos
  have hreal : Realizes (oscD c) N m0 :=
    (realizerCongruence (oscD c) N m0 hodd hd_pos).mpr (leastRealizer_modEq (oscD c) N)
  have hword : ∀ i < N, a (orbit m0 i) = oscD c i := hreal.2
  refine ⟨N, m0, hN, hodd, hword, ?_, hcard⟩
  intro n hn
  have : S (fun i => a (orbit m0 i)) n = S (oscD c) n := by
    unfold S s
    exact Finset.sum_congr rfl fun i hi =>
      hword i (lt_of_lt_of_le (Finset.mem_range.mp hi) hn)
  rw [this, S_oscD]

/-! ## 4b. The genuine orbit stays at `1`, and the post-arrival tail is short

Two gaps in the chain "(U) ⟹ EOC" are closed here. The third is *not*, and is named in §4c. -/

/-- `T 1 = 1`: the accelerated map fixes `1`, since `a 1 = ν₂(4) = 2` and `4/2² = 1`. -/
theorem a_one : a 1 = 2 := by
  have h4 : 3 * 1 + 1 = 2 ^ 2 := by norm_num
  unfold a
  rw [h4]
  exact padicValNat.prime_pow 2

theorem T_one : T 1 = 1 := by
  unfold T
  rw [a_one]
  norm_num

/-- **Once the genuine orbit reaches `1` it stays there.** This discharges, for the actual
accelerated map, the hypothesis `∀ k ≥ n*, m k = 1` used by the occupation bounds below. -/
theorem orbit_one_of_one (m0 n : ℕ) (h : orbit m0 n = 1) : ∀ k, n ≤ k → orbit m0 k = 1 := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact h
  | succ j _ ih => rw [orbit_succ, ih, T_one]

/-- On the tail at `1` every valuation digit is `2`, since `2^{d}·1 = 3·1+1 = 4`. -/
theorem tail_digit_two {m d S C : ℕ → ℕ} (h : Orbit m d S C) (k : ℕ)
    (hk : m k = 1) (hk1 : m (k + 1) = 1) : d k = 2 := by
  have hstep := h.step k
  rw [hk, hk1, Nat.mul_one] at hstep
  have : (2 : ℕ) ^ d k = 2 ^ 2 := by omega
  exact Nat.pow_right_injective (le_refl 2) this

/-- **The post-arrival tail contributes at most `3·2^c` corridor times.**

Once `m_n = 1` the digits are all `2`, so `2^{S}` gains a factor `4` per step while the bound
`2^c·3^n` gains only `3`. Since `2^{S_{n*}} = 3^{n*}m₀ + C_{n*} ≥ 3^{n*}`, being in the corridor at
`n* + k` forces `4^k ≤ 2^c·3^k`, and Bernoulli bounds `k`.

The bound `3·2^c` is far from sharp (the truth is about `2.41·c`), but it is a **constant in `m₀`**,
which is what an occupation statement at fixed `c` needs. Crucially this holds for *every* seed
reaching `1`, with **no** hypothesis `m₀ ≥ 2^c`: it is what removes the finitely many small seeds
that `corridor_excludes_one` cannot reach. -/
theorem tail_corridor_bound {m d S C : ℕ → ℕ} (h : Orbit m d S C) (c nstar k : ℕ)
    (hone : ∀ j, nstar ≤ j → m j = 1)
    (hin : 2 ^ S (nstar + k) ≤ 2 ^ c * 3 ^ (nstar + k)) : k ≤ 3 * 2 ^ c := by
  have hS : ∀ j, S (nstar + j) = S nstar + 2 * j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        have hd : d (nstar + j) = 2 :=
          tail_digit_two h _ (hone _ (Nat.le_add_right _ _)) (hone _ (by omega))
        rw [show nstar + (j + 1) = (nstar + j) + 1 from by omega, h.Ssucc, hd, ih]
        ring
  have hbase : (3 : ℕ) ^ nstar ≤ 2 ^ S nstar := by
    have hid := aggregate_identity h nstar
    rw [hone nstar le_rfl, Nat.mul_one] at hid
    have : (1 : ℕ) ≤ m 0 := h.mpos 0
    have : (3 : ℕ) ^ nstar * 1 ≤ 3 ^ nstar * m 0 := Nat.mul_le_mul_left _ this
    omega
  rw [hS k] at hin
  have hsplit : (2 : ℕ) ^ (S nstar + 2 * k) = 2 ^ S nstar * 4 ^ k := by
    rw [pow_add, pow_mul]; norm_num
  have hbnd : (2 : ℕ) ^ c * 3 ^ (nstar + k) = 3 ^ nstar * (2 ^ c * 3 ^ k) := by
    rw [pow_add]; ring
  have hkey : (3 : ℕ) ^ nstar * 4 ^ k ≤ 3 ^ nstar * (2 ^ c * 3 ^ k) := by
    calc (3 : ℕ) ^ nstar * 4 ^ k ≤ 2 ^ S nstar * 4 ^ k := Nat.mul_le_mul_right _ hbase
      _ = 2 ^ (S nstar + 2 * k) := hsplit.symm
      _ ≤ 2 ^ c * 3 ^ (nstar + k) := hin
      _ = 3 ^ nstar * (2 ^ c * 3 ^ k) := hbnd
  have h4 : (4 : ℕ) ^ k ≤ 2 ^ c * 3 ^ k :=
    Nat.le_of_mul_le_mul_left hkey (by positivity)
  have hber := bernoulli_four_three k
  have hpos : 0 < (3 : ℕ) ^ k := by positivity
  have : 3 ^ k * (3 + k) ≤ 3 ^ k * (3 * 2 ^ c) := by
    calc 3 ^ k * (3 + k) ≤ 3 * 4 ^ k := hber
      _ ≤ 3 * (2 ^ c * 3 ^ k) := Nat.mul_le_mul_left _ h4
      _ = 3 ^ k * (3 * 2 ^ c) := by ring
  have := Nat.le_of_mul_le_mul_left this hpos
  omega

/-- **Occupation is bounded by the arrival time, for every seed reaching `1`.**

No hypothesis `m₀ ≥ 2^c`: the small seeds are covered by `tail_corridor_bound`. This is the
*bridge* — it converts a total-stopping-time bound into an occupation bound. It is not by itself
the implication from `(U)`; see §4c. -/
theorem occupation_le_of_reaches_one_general {m d S C : ℕ → ℕ} (h : Orbit m d S C)
    (c nstar N : ℕ) (hone : ∀ j, nstar ≤ j → m j = 1) :
    ((Finset.range N).filter (fun n => 2 ^ S n ≤ 2 ^ c * 3 ^ n)).card
      ≤ nstar + 3 * 2 ^ c + 1 := by
  have hsub : ((Finset.range N).filter (fun n => 2 ^ S n ≤ 2 ^ c * 3 ^ n))
      ⊆ Finset.range (nstar + 3 * 2 ^ c + 1) := by
    intro n hn
    rw [Finset.mem_filter] at hn
    rw [Finset.mem_range]
    rcases lt_or_ge n nstar with hlt | hge
    · omega
    · obtain ⟨k, rfl⟩ : ∃ k, n = nstar + k := ⟨n - nstar, by omega⟩
      have := tail_corridor_bound h c nstar k hone hn.2
      omega
  calc ((Finset.range N).filter (fun n => 2 ^ S n ≤ 2 ^ c * 3 ^ n)).card
      ≤ (Finset.range (nstar + 3 * 2 ^ c + 1)).card := Finset.card_le_card hsub
    _ = nstar + 3 * 2 ^ c + 1 := Finset.card_range _

/-! ## 4c. What is **not** formalized in "(U) ⟹ EOC"

The implication has three layers, and only two of them are in this file.

1. **(U) ⟹ an `O(log m)` total-stopping-time bound.** *Not formalized.* It is imported from
   `docs/POSITIVE_ORBIT_CONFINEMENT_LIFETIME_AUDIT.md`, whose argument instantiates `U_all` at the
   automatic corridor and then absorbs an `E_L = O(log L)` term. `OrbitLifetime.no_unbounded_injective`
   records only the endpoint; its docstring states explicitly that the absorption step "is elementary
   but needs a real-analytic step, so it is not formalized here".
2. **A stopping bound ⟹ an occupation bound.** *Formalized*, twice:
   `occupation_le_of_reaches_one` (sharp, needs `m₀ ≥ 2^c`, tail contributes nothing) and
   `occupation_le_of_reaches_one_general` (every seed, tail contributes `≤ 3·2^c`).
3. **The orbit stays at `1` after arrival.** *Formalized* for the genuine map (`orbit_one_of_one`);
   for the abstract `Orbit` structure it is taken as the hypothesis `hone`, since that structure
   does not force oddness and so admits `1 ↦ 2`.

So "(U) ⟹ EOC" is a **proved bridge plus an imported, unformalized first layer** — not a single
formalized implication. -/

/-! ## 4d. From unboundedly many episodes to a linear rate

`exists_odd_seed_with_many_reentries` gives *unboundedly many* episodes and nothing more. To say
anything about the **rate** in `log₂ m₀` one needs two quantitative facts: that exits recur at a
bounded gap, and that the realizing seed is not too large. Both are proved below. -/

/-- After an exit, the drift is at least `log₂(3/2)` below the level: `2·(2^c3^{e+1}) < 3·2^{S_{e+1}}`.
This is the oscillating-word instance of `entry_threshold_pinned`. -/
theorem post_exit_lower {c e : ℕ} (h : ¬ InC c e) :
    2 * (2 ^ c * 3 ^ (e + 1)) < 3 * 2 ^ oscS c (e + 1) := by
  have hA : 2 ^ oscS c (e + 1) = 2 * 2 ^ oscS c e := by
    rw [oscS_succ, oscD_eq_one h, pow_add]; ring
  have hB : 2 ^ c * 3 ^ (e + 1) = 3 * (2 ^ c * 3 ^ e) := by rw [pow_succ]; ring
  have hout : 2 ^ c * 3 ^ e < 2 ^ oscS c e := by
    have : ¬ (2 ^ oscS c e ≤ 2 ^ c * 3 ^ e) := h
    omega
  omega

/-- **Exits recur within three steps.** After an exit at `e` the word re-enters at `e+1`
(`reentry_immediate`) with the drift pinned `> log₂(3/2)` below the level, and two digit-`2` steps
raise it by `2·log₂(4/3) > log₂(3/2)`. So it cannot still be inside at both `e+2` and `e+3`. -/
theorem exit_within_three {c e : ℕ} (h : ¬ InC c e) :
    ¬ InC c (e + 2) ∨ ¬ InC c (e + 3) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h2, h3⟩ := hcon
  have h1 : InC c (e + 1) := reentry_immediate h
  have hA : 2 ^ oscS c (e + 2) = 4 * 2 ^ oscS c (e + 1) := by
    rw [show e + 2 = (e + 1) + 1 from rfl, oscS_succ, oscD_eq_two h1, pow_add]; ring
  have hB : 2 ^ oscS c (e + 3) = 4 * 2 ^ oscS c (e + 2) := by
    rw [show e + 3 = (e + 2) + 1 from rfl, oscS_succ, oscD_eq_two h2, pow_add]; ring
  have hC : 2 ^ c * 3 ^ (e + 3) = 9 * (2 ^ c * 3 ^ (e + 1)) := by
    rw [show e + 3 = (e + 1) + 1 + 1 from rfl, pow_succ, pow_succ]; ring
  have hlow := post_exit_lower h
  have hin3 : 2 ^ oscS c (e + 3) ≤ 2 ^ c * 3 ^ (e + 3) := h3
  have hYpos : 0 < 2 ^ c * 3 ^ (e + 1) := by positivity
  omega

theorem exitTime_le_add_three (c i : ℕ) : exitTime c (i + 1) ≤ exitTime c i + 3 := by
  have hspec := exit_within_three (exitTime_not_mem c i)
  show Nat.find (exists_exit_ge c (exitTime c i + 1)) ≤ exitTime c i + 3
  rcases hspec with h2 | h3
  · exact le_trans (Nat.find_le ⟨by omega, h2⟩) (by omega)
  · exact Nat.find_le ⟨by omega, h3⟩

theorem exitTime_le_linear (c i : ℕ) : exitTime c i ≤ exitTime c 0 + 3 * i := by
  induction i with
  | zero => omega
  | succ i ih => have := exitTime_le_add_three c i; omega

theorem oscS_le (c n : ℕ) : oscS c n ≤ 2 * n := by
  induction n with
  | zero => simp [oscS]
  | succ n ih =>
      have : oscD c n ≤ 2 := by
        by_cases h : InC c n
        · rw [oscD_eq_two h]
        · rw [oscD_eq_one h]; omega
      rw [oscS_succ]; omega

/-- **The quantitative form: many episodes, in a seed that is only exponentially large in `B`, with
prefix occupation only linear in `B`.**

Writing `e₀ = exitTime c 0` (a constant depending on `c` alone):

* at least `B` re-entries before the horizon `N`;
* `m₀ < 2^{6B + 2e₀ + 3}`, so `B ≥ (log₂ m₀ − 2e₀ − 3)/6` — the episode count of these seeds grows
  **at least linearly in `log₂ m₀`**;
* the number of corridor times *within the realized prefix* is at most `e₀ + 2B`.

**Scope — three things that are deliberately not claimed.**

* The last bound is `O(B)`, **not** `O(log m₀)`. The seed estimate bounds `m₀` from *above*, which
  bounds `B` from *below*; it gives no upper bound on `B`, so it does not license replacing
  `e₀ + 2B` by `O(log m₀)`. The accounting loss is instead stated as a *ratio*, in
  `surrogate_ratio_lower`.
* Every statement here is about the **finite prefix** `[0, N)`. Nothing is claimed about the
  *total* occupation of these seeds, which depends on the orbit beyond `N`; the measured values in
  the companion report are computational only.
* `P = Θ(log m₀)` is **not** claimed — only the lower bound `Ω`, which is the direction the argument
  needs. -/
theorem many_reentries_with_small_seed (c B : ℕ) :
    ∃ N m0 : ℕ, 1 ≤ N ∧ Odd m0 ∧
      (∀ i < N, a (orbit m0 i) = oscD c i) ∧
      B ≤ (reentries c N).card ∧
      m0 < 2 ^ (6 * B + 2 * exitTime c 0 + 3) ∧
      ((Finset.range N).filter (InC c)).card ≤ exitTime c 0 + 2 * B := by
  set N : ℕ := exitTime c B + 1 with hNdef
  have hNle : N ≤ exitTime c 0 + 3 * B + 1 := by
    have := exitTime_le_linear c B; omega
  have hN1 : 1 ≤ N := by omega
  have hd_pos : ∀ i < N, 1 ≤ oscD c i := fun i _ => oscD_pos c i
  set m0 : ℕ := leastRealizer (oscD c) N with hm0def
  have hodd : Odd m0 := leastRealizer_odd (oscD c) N hN1 hd_pos
  have hreal : Realizes (oscD c) N m0 :=
    (realizerCongruence (oscD c) N m0 hodd hd_pos).mpr (leastRealizer_modEq (oscD c) N)
  -- (i) at least `B` re-entries
  have hmaps : ∀ i ∈ Finset.range B, exitTime c i ∈ reentries c N := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [reentries, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, exitTime_not_mem c i, reentry_immediate (exitTime_not_mem c i)⟩
    have := exitTime_strictMono c hi; omega
  have hcard : B ≤ (reentries c N).card := by
    calc B = (Finset.range B).card := (Finset.card_range B).symm
      _ ≤ (reentries c N).card :=
          Finset.card_le_card_of_injOn _ hmaps
            (fun x _ y _ hxy => (exitTime_strictMono c).injective hxy)
  -- (ii) the seed is at most exponentially large in `B`
  have hsize : m0 < 2 ^ (6 * B + 2 * exitTime c 0 + 3) := by
    have h1 : m0 < 2 ^ (S (oscD c) N + 1) := leastRealizer_lt (oscD c) N
    have h2 : S (oscD c) N ≤ 2 * N := by rw [S_oscD]; exact oscS_le c N
    exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) (by omega))
  -- (iii) prefix occupation is linear in `B`
  have hexits : B + 1 ≤ ((Finset.range N).filter (fun n => ¬ InC c n)).card := by
    have hmaps' : ∀ i ∈ Finset.range (B + 1),
        exitTime c i ∈ (Finset.range N).filter (fun n => ¬ InC c n) := by
      intro i hi
      rw [Finset.mem_range] at hi
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, exitTime_not_mem c i⟩
      rcases Nat.lt_or_ge i B with h | h
      · have := exitTime_strictMono c h; omega
      · have : i = B := by omega
        subst this; omega
    calc B + 1 = (Finset.range (B + 1)).card := (Finset.card_range (B + 1)).symm
      _ ≤ _ := Finset.card_le_card_of_injOn _ hmaps'
                 (fun x _ y _ hxy => (exitTime_strictMono c).injective hxy)
  have hocc : ((Finset.range N).filter (InC c)).card ≤ exitTime c 0 + 2 * B := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := Finset.range N) (p := InC c)
    rw [Finset.card_range] at hsplit
    omega
  exact ⟨N, m0, hN1, hodd, hreal.2, hcard, hsize, hocc⟩

/-! ## 4e. Unbounded realizing seeds, and the accounting ratio

`many_reentries_with_small_seed` bounds the realizing seed from **above**. That gives
`B = Ω(log₂ m₀)`, but it does **not** bound `B` from above, so it does *not* license concluding
that the prefix occupation `≤ e₀ + 2B` is `O(log m₀)`. That inference is withdrawn.

What replaces it is a **ratio** statement, and for it to be non-vacuous the realizing seeds must be
unbounded. That is established here unconditionally: realizers of a fixed prefix form a full
residue class, so arbitrarily large ones exist. -/

/-- **Realizers of a prefix are a full residue class, so arbitrarily large ones exist.**

If `m₀` realizes a prefix then so does `m₀ + t·2^{S_N+1}` for every `t`, since `Realizes` depends
only on the residue mod `2^{S_N+1}` (`realizerCongruence`) and adding a multiple of the modulus
preserves both the congruence and oddness. -/
theorem exists_large_realizer (d : ℕ → ℕ) (N M : ℕ) (hN : 1 ≤ N) (hd : ∀ i < N, 1 ≤ d i) :
    ∃ m0, M < m0 ∧ Odd m0 ∧ Realizes d N m0 := by
  obtain ⟨w, hw⟩ := leastRealizer_odd d N hN hd
  obtain ⟨j, hj⟩ : ∃ j, (2 : ℕ) ^ (S d N + 1) = 2 * j := ⟨2 ^ S d N, by rw [pow_succ]; ring⟩
  have hodd : Odd (leastRealizer d N + 2 ^ (S d N + 1) * (M + 1)) :=
    ⟨w + j * (M + 1), by rw [hw, hj]; ring⟩
  refine ⟨leastRealizer d N + 2 ^ (S d N + 1) * (M + 1), ?_, hodd, ?_⟩
  · have h1 : M + 1 ≤ 2 ^ (S d N + 1) * (M + 1) :=
      Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
    omega
  · refine (realizerCongruence d N _ hodd hd).mpr ?_
    have hexp : 3 ^ N * (leastRealizer d N + 2 ^ (S d N + 1) * (M + 1)) + q d N
        = (3 ^ N * leastRealizer d N + q d N) + 2 ^ (S d N + 1) * (3 ^ N * (M + 1)) := by ring
    show (3 ^ N * (leastRealizer d N + 2 ^ (S d N + 1) * (M + 1)) + q d N) % 2 ^ (S d N + 1)
        = 2 ^ S d N % 2 ^ (S d N + 1)
    rw [hexp, Nat.add_mul_mod_self_left]
    exact leastRealizer_modEq d N

/-- **The same episode data, in arbitrarily large seeds.**

Identical to `many_reentries_with_small_seed` except that the seed is bounded **below** by an
arbitrary `M` instead of above. Both the re-entry count and the prefix occupation depend only on the
word, which any realizer of the prefix reproduces, so they are unchanged.

This is what makes the accounting-ratio statement below non-vacuous: it exhibits an *unbounded*
sequence of realizing seeds, rather than inferring unboundedness from an upper bound. -/
theorem many_reentries_with_large_seed (c B M : ℕ) :
    ∃ N m0 : ℕ, 1 ≤ N ∧ Odd m0 ∧ M < m0 ∧
      (∀ i < N, a (orbit m0 i) = oscD c i) ∧
      B ≤ (reentries c N).card ∧
      ((Finset.range N).filter (InC c)).card ≤ exitTime c 0 + 2 * B := by
  obtain ⟨N, m0, hN, -, hword, hcard, -, hocc⟩ := many_reentries_with_small_seed c B
  obtain ⟨m1, hM, hodd1, hreal1⟩ :=
    exists_large_realizer (oscD c) N M hN (fun i _ => oscD_pos c i)
  exact ⟨N, m1, hN, hodd1, hM, hreal1.2, hcard, hocc⟩

/-- **The accounting ratio.**

Suppose a coarse per-episode estimate charges at least `B + 1` episodes a cost of at least
`L − c` each, so the surrogate total is `Q ≥ (B+1)(L−c)`, while the quantity it is bounding is
`O ≤ e₀ + 2B`. Then

```
O · (L − c)  ≤  (2 + e₀) · Q ,        i.e.        Q / O  ≥  (L − c) / (2 + e₀) ,
```

because `(2+e₀)(B+1) ≥ e₀ + 2B` for all `B, e₀ ≥ 0`. (Stated multiplicatively, so it holds without
a positivity side condition on `O`.) The bound is independent of `B`, so along the
seeds of `many_reentries_with_large_seed` — where `L = log₂ m₀` is unbounded and `e₀` depends only
on `c` — the overestimate factor is `Ω(log m₀)`.

Note what is *not* claimed: nothing here bounds `O` by `O(log m₀)`. `O ≤ e₀ + 2B` bounds it in terms
of the episode count, and the episode count is bounded below, not above. Only the *ratio* is
controlled. -/
theorem surrogate_ratio_lower (L c e0 B Q O : ℝ)
    (hB : 0 ≤ B) (he0 : 0 ≤ e0) (hLc : c ≤ L)
    (hQ : (B + 1) * (L - c) ≤ Q) (hOle : O ≤ e0 + 2 * B) :
    O * (L - c) ≤ (2 + e0) * Q := by
  have hD : 0 ≤ L - c := by linarith
  have h1 : O * (L - c) ≤ (e0 + 2 * B) * (L - c) := mul_le_mul_of_nonneg_right hOle hD
  have h2 : (e0 + 2 * B) * (L - c) ≤ ((2 + e0) * (B + 1)) * (L - c) := by
    refine mul_le_mul_of_nonneg_right ?_ hD
    nlinarith
  have h3 : ((2 + e0) * (B + 1)) * (L - c) ≤ (2 + e0) * Q := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hQ (by linarith)
  linarith

/-! ## 5. What the counting fact does and does not say -/

/-- **An elementary counting fact.** If `P` quantities each of size at least `B > 0` sum to at most
`T`, then `P·B ≤ T`.

**Scope, corrected.** In `docs/SEPARATED_RETURNS_INVESTIGATION.md` this is applied to the sum of the
*coarse upper bounds* `1 + K(log₂ m_{a_i} + c_i)` assigned to the episodes, not to the episode
lengths themselves. It therefore says only this: *if one attempts to bound occupation by summing
those particular coarse estimates, and wants the result to be `O(log m₀)`, then the number of
episodes must be `O(1)`.*

It does **not** say that occupation is `O(log m₀)` only when the episode count is bounded. A lower
bound on an upper-bound expression is not a lower bound on the quantity it bounds: the actual
episodes may be far shorter than the estimate, and many short episodes can perfectly well sum to
`O(log m₀)`. Indeed `exists_odd_seed_with_many_reentries` produces orbits with unboundedly many
episodes, and `occupation_le_of_reaches_one` shows occupation is still controlled by the stopping
time. The earlier claim that bounding the surrogate sum is "equivalent" to bounding the episode
count is withdrawn; only the stated one-way implication holds. -/
theorem count_le_of_summands_ge {ι : Type} (s : Finset ι) (f : ι → ℝ) (B T : ℝ)
    (hB : 0 < B) (hge : ∀ i ∈ s, B ≤ f i) (hsum : ∑ i ∈ s, f i ≤ T) :
    (s.card : ℝ) * B ≤ T := by
  calc (s.card : ℝ) * B = ∑ _i ∈ s, B := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ s, f i := Finset.sum_le_sum hge
    _ ≤ T := hsum

/-- **One-step growth across a fixed integer level.** A single accelerated step satisfies
`2·m_{n+1} ≤ 3·m_n + 1`, so a crossing of a *fixed* level `L` lands in `[L, (3L+1)/2)`.

**Scope, corrected.** The corridor threshold is `Λ_n = m₀·2^{E_n−c}`, which *moves with `n`*
through the carry term `E_n`. This lemma is about a fixed integer level and is not, by itself, a
statement about corridor re-entries; landings at different re-entry times belong to different
bands, and their union is not controlled by this lemma. What re-entry does force, exactly, is
`d_n = 1` (`entry_digit_one`), i.e. `2·m_{n+1} = 3·m_n + 1` — the maximal-growth step. -/
theorem upcrossing_band {m d S C : ℕ → ℕ} (h : Orbit m d S C) (n L : ℕ)
    (hbelow : m n < L) (habove : L ≤ m (n + 1)) :
    L ≤ m (n + 1) ∧ 2 * m (n + 1) < 3 * L + 1 := by
  refine ⟨habove, ?_⟩
  have hstep := h.step n
  have hd : (2 : ℕ) ^ 1 ≤ 2 ^ d n := Nat.pow_le_pow_right (by norm_num) (h.dpos n)
  have h2 : 2 * m (n + 1) ≤ 2 ^ d n * m (n + 1) := by
    simpa using Nat.mul_le_mul_right (m (n + 1)) hd
  omega

end SeparatedReturns
end EOC
