import EOC.TerminalZeroGap
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# The transport budget, the realizer-depth bridge, and the regeneration envelope

Companion to `docs/TRANSPORT_REGENERATION_REALIZER_BRIDGE_AUDIT.md`.

The transport-deficit note introduces, for a valuation prefix of length `j` with total valuation
`S_j`, the coordinates

```
χ_j = ξ_j mod 2^{S_j}        r(D_j) = χ_j + (1 − β_j)·2^{S_j}
F_j = S_j − log₂ χ_j         E_j = S_j − log₂ r(D_j)
M_j = v₂(T_j − A_{j,∞})      H_j = F_j + M_j      (the *transport budget*)
```

and proves: `H` is **conserved** on every zero-deficit ("perfect") step, and changes at a failure
by `ΔH = v₂(a−u) − δ_fail`. This file formalizes the four exact links the audit needs, and — the
point of the audit — the **refutation of the pointwise-envelope reading** of Open Problem 37.

* `depth_le_anchor`, `discreteGap_lt_budget_add_one` — the *bridge*. A dangerous realizer (a long
  terminal zero gap `g = discreteGap S r`) forces a large transport budget: `g < F + M + 1`.
  This is the one direction the chain needs and it is unconditional.
* `no_perfect_tail` — the *dichotomy*. Perfect transport cannot persist forever with finite
  matching precision, so every non-2-adic trajectory has **infinitely many** failures.
* `no_negative_drift` — positivity of `H` forbids a uniformly negative failure drift. Hence
  "failures destroy budget on average" is false along *every* infinite trajectory, including
  periodic ones: a whole class of contradiction strategies is dead on arrival.
* `envelope_diverges`, `sqrt_envelope_insufficient` — **Gate 10.** A pointwise envelope
  `G_max(H) = o(H)` is *not* sufficient to bound `H`. What matters is a floor on gains together
  with the number of budget-increasing events, not the shape of the envelope in `H`.
* `sqrt_envelope_allows_any_linear_rate` — the sharp form of Gate 10: a `√H` envelope is
  compatible with *every* linear growth rate of the budget, including rates above `α`.
* `bddAbove_iff_partialSums` — budget boundedness is *equivalent* to boundedness of the cumulative
  gain, so that particular cumulative statement is a restatement rather than a weaker hypothesis.
* `cumulative`, `cumulative_regeneration_lower_bound` — both coordinates telescope, and `M ≥ 0`
  turns the matching-precision telescoping into a **forced lower bound** `Σw ≥ S_N − M_0` on
  cumulative regeneration. Regeneration is mandatory at linear rate, not exceptional.
* `discreteGap_lt_of_cumulative_gain` — the whole chain in one statement: a bound `B` on the
  cumulative failure gain bounds the terminal zero gap by `H_0 + B + 1`. `B = (α−ε)N` is
  Open Problem C; `B = H₂(ρ_c)S_N + o(N)` is Open Problem E.

Everything here is stated for abstract sequences of reals and naturals. That is the generality in
which these statements are true, and it keeps the file independent of any 2-adic infrastructure
(which this repository does not have; see §AC of the previous audit).

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace TransportRegeneration

open Filter Real

/-! ## 1. The discrete gap against the real depth

`discreteGap S r = S − ⌊log₂ r⌋` (from `EOC.TerminalZeroGap`) is the integer count of zero bits
above the top bit of the realizer; `E = S − log₂ r` is the note's real-valued depth. They differ
by the fractional part of `log₂ r`, so `E ≤ g < E + 1` — never more. -/

/-- `⌊log₂ r⌋ ≤ log₂ r`, as reals. -/
theorem natLog_le_logb {r : ℕ} (hr : 0 < r) :
    ((Nat.log 2 r : ℕ) : ℝ) ≤ Real.logb 2 (r : ℝ) := by
  have hpow : (2 : ℕ) ^ Nat.log 2 r ≤ r := Nat.pow_log_le_self 2 hr.ne'
  have hR : (2 : ℝ) ^ Nat.log 2 r ≤ (r : ℝ) := by exact_mod_cast hpow
  have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hR
  simpa [Real.logb_pow, Real.logb_self_eq_one] using this

/-- `log₂ r < ⌊log₂ r⌋ + 1`, as reals. -/
theorem logb_lt_natLog_add_one {r : ℕ} (hr : 0 < r) :
    Real.logb 2 (r : ℝ) < ((Nat.log 2 r : ℕ) : ℝ) + 1 := by
  have hpow : r < 2 ^ (Nat.log 2 r + 1) := Nat.lt_pow_succ_log_self (by norm_num) r
  have hR : (r : ℝ) < (2 : ℝ) ^ (Nat.log 2 r + 1) := by exact_mod_cast hpow
  have := Real.logb_lt_logb (b := 2) (by norm_num) (by exact_mod_cast hr) hR
  simpa [Real.logb_pow, Real.logb_self_eq_one] using this

/-- **The discrete gap brackets the real depth**: `E ≤ g < E + 1`, where `E = S − log₂ r` and
`g = discreteGap S r`.

This is the exact statement the previous round's report got wrong (§Z of
`REALIZER_LIFT_DIGIT_POSITIVITY_AUDIT.md` said `E` *is* the terminal zero-run length; it is not).
-/
theorem discreteGap_bracket {S r : ℕ} (hr : 0 < r) (hle : Nat.log 2 r ≤ S) :
    (S : ℝ) - Real.logb 2 (r : ℝ) ≤ ((TerminalZeroGap.discreteGap S r : ℕ) : ℝ) ∧
      ((TerminalZeroGap.discreteGap S r : ℕ) : ℝ) < (S : ℝ) - Real.logb 2 (r : ℝ) + 1 := by
  have hcast : ((TerminalZeroGap.discreteGap S r : ℕ) : ℝ) = (S : ℝ) - ((Nat.log 2 r : ℕ) : ℝ) := by
    unfold TerminalZeroGap.discreteGap
    push_cast [Nat.cast_sub hle]
    ring
  rw [hcast]
  exact ⟨by linarith [natLog_le_logb hr], by linarith [logb_lt_natLog_add_one hr]⟩

/-! ## 2. The realizer-depth → transport-budget bridge

The note's Corollary 3 splits on the lift bit `β_j`: when `β_j = 1` the exact realizer *is* the
coarse anchor, `E_j = F_j`; when `β_j = 0` the realizer sits in the shallow strip `E_j ∈ (−1, 0]`.
Both cases are subsumed by the single monotone fact `r(D_j) ≥ χ_j`, which is what (5) gives. -/

/-- **`E ≤ F` unconditionally.** The exact realizer is never smaller than the coarse anchor
(`r = χ` or `r = χ + 2^S`), so the true prefix depth never exceeds the coarse-anchor depth. No
case split on the lift bit `β` is needed. -/
theorem depth_le_anchor {S χ r : ℕ} (hχ : 0 < χ) (hr : χ ≤ r) :
    (S : ℝ) - Real.logb 2 (r : ℝ) ≤ (S : ℝ) - Real.logb 2 (χ : ℝ) := by
  have : Real.logb 2 (χ : ℝ) ≤ Real.logb 2 (r : ℝ) :=
    Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hχ) (by exact_mod_cast hr)
  linarith

/-- **The bridge.** A dangerous realizer forces a large transport budget:

```
discreteGap S r  <  F + M + 1  =  H + 1.
```

Stated from the two facts that actually carry it — `E ≤ F` (`depth_le_anchor`) and `M ≥ 0` (a
2-adic valuation) — so it holds at every step, perfect or failed, and for either value of the
lift bit. Contrapositive: a bounded transport budget bounds the terminal zero gap, hence bounds
how small the exact realizer can be. This is the direction Open Problems C and E need. -/
theorem discreteGap_lt_budget_add_one {S χ r : ℕ} {F M : ℝ}
    (hχ : 0 < χ) (hr : χ ≤ r) (hrpos : 0 < r) (hle : Nat.log 2 r ≤ S)
    (hF : F = (S : ℝ) - Real.logb 2 (χ : ℝ)) (hM : 0 ≤ M) :
    ((TerminalZeroGap.discreteGap S r : ℕ) : ℝ) < F + M + 1 := by
  have h1 := (discreteGap_bracket hrpos hle).2
  have h2 := depth_le_anchor (S := S) hχ hr
  rw [hF]
  linarith

/-! ## 3. The perfect-tail dichotomy

Theorem 18 of the note: on a perfect step `M_{j+1} = M_j − d_{j+1}`. Since `d ≥ 1` and `M ≥ 0`,
that cannot go on forever. -/

/-- **No trajectory is perfect from some point on.** If matching precision decreases by the
step valuation at every step past `j₀`, and every valuation is at least `1`, the precision runs
out. Hence along any trajectory whose mismatch `X_j` is nonzero, failures recur **infinitely
often**.

Consequence for the audit: the count of budget-changing events along an infinite trajectory is
infinite, which is precisely what makes a pointwise envelope useless (see §5). -/
theorem no_perfect_tail (M d : ℕ → ℕ) (j₀ : ℕ) (hd : ∀ m, 1 ≤ d m)
    (hM : ∀ m, j₀ ≤ m → M m = M (m + 1) + d (m + 1)) : False := by
  have key : ∀ n : ℕ, M (j₀ + n) + n ≤ M j₀ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hstep : M (j₀ + n) = M (j₀ + n + 1) + d (j₀ + n + 1) :=
          hM (j₀ + n) (Nat.le_add_right _ _)
        have := hd (j₀ + n + 1)
        have hadd : j₀ + (n + 1) = j₀ + n + 1 := by omega
        rw [hadd]
        omega
  have := key (M j₀ + 1)
  omega

/-! ## 4. Positivity forbids a negative failure drift

`F_j > 0` (Lemma 1 of the note: `χ_j` is odd, so `1 ≤ χ_j < 2^{S_j}`) and `M_j ≥ 0`, hence the
budget is strictly positive at every step. Since the budget is conserved on perfect steps, its
whole history is the partial sums of the failure gains — and those partial sums are therefore
bounded below. -/

/-- **A uniformly negative drift is impossible.** If the budget lost at least a fixed `c > 0` at
each event, it would become negative, contradicting `H > 0`.

This kills the most natural contradiction strategy for Open Problems C and E — "failures destroy
transport budget, so deep excursions cannot recur" — *before* any arithmetic is attempted. The
statement is not about Collatz: it is forced by `F > 0`, `M ≥ 0` and conservation on perfect
steps alone, and it holds for the trivial cycle too. -/
theorem no_negative_drift (H : ℕ → ℝ) (c : ℝ) (hpos : ∀ k, 0 < H k) (hc : 0 < c)
    (hdrift : ∀ k, H (k + 1) ≤ H k - c) : False := by
  have key : ∀ n : ℕ, H n ≤ H 0 - n * c := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have := hdrift n
        push_cast
        nlinarith [ih, this]
  obtain ⟨n, hn⟩ := exists_nat_gt (H 0 / c)
  have h1 := key n
  have h2 := hpos n
  have : H 0 / c < n := hn
  rw [div_lt_iff₀ hc] at this
  nlinarith

/-! ## 5. Gate 10 — a pointwise envelope `G_max(H) = o(H)` is **not** sufficient

Open Problem 37 asks for the asymptotics of `G_max(H)`, and contrasts `G_max(H) ∼ cH`,
`G_max(H) = o(H)` and `G_max(H) < 0` eventually. The tempting reading is that the middle regime
already forbids unbounded budget. It does not.

The budget at the `k`-th failure is `H_0 + Σ_{i<k} G_i`. Divergence of that sum needs only a
**positive floor on the gains together with infinitely many events** — and `no_perfect_tail`
supplies the infinitely many events. The *shape* of the envelope in `H` is irrelevant: it
constrains the growth rate in `k`, never the fact of divergence. Only `G_max(H) < 0` eventually —
regime (72) — actually bounds the budget. -/

/-- **A positive floor on the gains diverges, whatever the envelope.** No hypothesis relates the
gain to `H` at all. -/
theorem envelope_diverges (H : ℕ → ℝ) (c : ℝ) (hc : 0 < c) (hstep : ∀ k, H k + c ≤ H (k + 1)) :
    Tendsto H atTop atTop := by
  have key : ∀ n : ℕ, H 0 + n * c ≤ H n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have := hstep n
        push_cast
        nlinarith [ih, this]
  refine tendsto_atTop_mono key ?_
  exact tendsto_atTop_add_const_left _ _
    (Filter.Tendsto.atTop_mul_const hc tendsto_natCast_atTop_atTop)

/-- **Gate 10, sharp form: a sublinear envelope permits *every* linear growth rate.**

For each `c > 0` there is a strictly positive budget sequence obeying the envelope
`ΔH ≤ √H` — emphatically `o(H)` — whose budget is exactly `c·n + c²`, i.e. whose cumulative
failure gain grows at rate `c`, which may be taken larger than `α`.

This is the decisive statement. Open Problem C needs the cumulative gain to grow at a rate
**strictly below `α`** (§ the audit's `T_C`). A pointwise envelope in `H` places no constraint
whatsoever on that rate: the two quantify different things — size *per event* versus size
*per accelerated step*. Regime (71) of Open Problem 37 therefore carries none of the force it
appears to, and only regime (72), `G_max(H) < 0` eventually, actually bounds the budget. -/
theorem sqrt_envelope_allows_any_linear_rate (c : ℝ) (hc : 0 < c) :
    ∃ H : ℕ → ℝ, (∀ k, 0 < H k) ∧ (∀ k, H (k + 1) - H k ≤ Real.sqrt (H k)) ∧
      (∀ n, H n = c * n + c ^ 2) := by
  refine ⟨fun k => c * k + c ^ 2, fun k => by positivity, fun k => ?_, fun n => rfl⟩
  have hk : (0 : ℝ) ≤ c * k := by positivity
  have h1 : c ^ 2 ≤ c * (k : ℝ) + c ^ 2 := by linarith
  have h2 : Real.sqrt (c ^ 2) ≤ Real.sqrt (c * (k : ℝ) + c ^ 2) := Real.sqrt_le_sqrt h1
  rw [Real.sqrt_sq hc.le] at h2
  push_cast
  linarith

/-- **The explicit Gate 10 counterexample.** There is a strictly positive budget sequence whose
one-step gain is bounded by `√H` — an envelope that is emphatically `o(H)` — and which still
diverges.

So `G_max(H) = o(H)` does not bound the transport budget, does not bound the coarse depth `F`,
and therefore does not imply Open Problem C or E. Any argument that reads regime (71) as
"regeneration cannot keep pace" is invalid. -/
theorem sqrt_envelope_insufficient :
    ∃ H : ℕ → ℝ, (∀ k, 0 < H k) ∧ (∀ k, H (k + 1) - H k ≤ Real.sqrt (H k)) ∧
      Tendsto H atTop atTop := by
  refine ⟨fun k => (k : ℝ) + 1, fun k => by positivity, fun k => ?_, ?_⟩
  · have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have h1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith
    have : Real.sqrt 1 ≤ Real.sqrt ((k : ℝ) + 1) := Real.sqrt_le_sqrt h1
    rw [Real.sqrt_one] at this
    push_cast
    linarith
  · exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop

/-! ## 6. The weakest cumulative statement is a restatement

Since the budget only moves at failures, its boundedness *is* the boundedness of the partial sums
of the gains. Any "weakest cumulative regeneration theorem" that bounds the budget is therefore
logically equivalent to the conclusion, not a weaker hypothesis one could hope to prove
independently. The genuine content has to come from somewhere else — a bound on the *number* of
budget-increasing failures, not on their size. -/

/-- The budget is its initial value plus the partial sums of the gains. -/
theorem budget_eq_partialSum (H G : ℕ → ℝ) (hrec : ∀ k, H (k + 1) = H k + G k) (n : ℕ) :
    H n = H 0 + ∑ k ∈ Finset.range n, G k := by
  induction n with
  | zero => simp
  | succ n ih => rw [hrec n, ih, Finset.sum_range_succ]; ring

/-- **Boundedness of the budget ⟺ boundedness of the cumulative gain.** -/
theorem bddAbove_iff_partialSums (H G : ℕ → ℝ) (hrec : ∀ k, H (k + 1) = H k + G k) :
    BddAbove (Set.range H) ↔ BddAbove (Set.range fun n => ∑ k ∈ Finset.range n, G k) := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B - H 0, ?_⟩
    rintro _ ⟨n, rfl⟩
    have h := hB (Set.mem_range_self n)
    rw [budget_eq_partialSum H G hrec n] at h
    linarith
  · rintro ⟨B, hB⟩
    refine ⟨H 0 + B, ?_⟩
    rintro _ ⟨n, rfl⟩
    have h := hB (Set.mem_range_self n)
    rw [budget_eq_partialSum H G hrec n]
    linarith

/-! ## 7. The two cumulative identities, and what they force

Both coordinates obey a `+ gain − loss` recurrence, so both telescope exactly:

```
F_N = F_0 + (S_N − S_0) − Σ δ        (equation (14) of the note)
M_N = M_0 − (S_N − S_0) + Σ w        (Theorem 18 + Proposition 30)
```

where `w_{k+1}` is `0` on a perfect step and `v₂(a−u)` at a first failure. The second identity
is not in the note and is the audit's main new exact statement: combined with `M ≥ 0` it turns
into a **forced lower bound on cumulative regeneration**. -/

/-- Exact telescoping of a `+ p − q` recurrence. -/
theorem cumulative (X p q : ℕ → ℝ) (h : ∀ k, X (k + 1) = X k + p k - q k) (n : ℕ) :
    X n = X 0 + (∑ k ∈ Finset.range n, p k) - ∑ k ∈ Finset.range n, q k := by
  induction n with
  | zero => simp
  | succ n ih => rw [h n, ih, Finset.sum_range_succ, Finset.sum_range_succ]; ring

/-- **Regeneration is mandatory, not optional.** Matching precision loses the step valuation at
every step and is replenished only at failures; since it can never go negative, the cumulative
cancellation precision must exceed the cumulative valuation, up to the initial precision:

```
Σ_{k<n} w_k  ≥  S_n − M_0.
```

Along a zero-confined trajectory `S_n` grows linearly, so the total regeneration over failures is
forced to grow **at least linearly** in `n`. This is the exact quantitative form of
`no_negative_drift`, and it is the reason no "failures exhaust the budget" argument can work. -/
theorem cumulative_regeneration_lower_bound (M d w : ℕ → ℝ)
    (h : ∀ k, M (k + 1) = M k + w k - d k) (hM : ∀ k, 0 ≤ M k) (n : ℕ) :
    (∑ k ∈ Finset.range n, d k) - M 0 ≤ ∑ k ∈ Finset.range n, w k := by
  have := cumulative M w d h n
  have h0 := hM n
  linarith

/-- **The audit's headline: the full chain in one statement.**

Given the note's coordinates (`F = S − log₂ χ`, `H = F + M`, `M ≥ 0`, `H` moving only by the
failure gains `G`), a bound `B` on the *cumulative* gain up to time `n` bounds the terminal zero
gap of the exact realizer:

```
discreteGap (S n) (r n)  <  H 0 + B + 1.
```

Taking `B = (α − ε)·n` gives Open Problem C, and `B = H₂(ρ_c)·S n + o(n)` gives Open Problem E.
The hypothesis is a statement about the cumulative gain **per accelerated step**; it is *not*
implied by any envelope on the gain per failure event (`sqrt_envelope_allows_any_linear_rate`). -/
theorem discreteGap_lt_of_cumulative_gain
    (S χ r : ℕ → ℕ) (F M H G : ℕ → ℝ) (B : ℝ) (n : ℕ)
    (hF : ∀ k, F k = (S k : ℝ) - Real.logb 2 ((χ k : ℕ) : ℝ))
    (hH : ∀ k, H k = F k + M k)
    (hMnn : ∀ k, 0 ≤ M k)
    (hrec : ∀ k, H (k + 1) = H k + G k)
    (hsum : ∑ k ∈ Finset.range n, G k ≤ B)
    (hχ : 0 < χ n) (hr : χ n ≤ r n) (hrpos : 0 < r n) (hle : Nat.log 2 (r n) ≤ S n) :
    ((TerminalZeroGap.discreteGap (S n) (r n) : ℕ) : ℝ) < H 0 + B + 1 := by
  have hbridge := discreteGap_lt_budget_add_one (S := S n) (χ := χ n) (r := r n)
    (F := F n) (M := M n) hχ hr hrpos hle (hF n) (hMnn n)
  have hbud := budget_eq_partialSum H G hrec n
  have : F n + M n = H n := (hH n).symm
  linarith

end TransportRegeneration
end EOC
