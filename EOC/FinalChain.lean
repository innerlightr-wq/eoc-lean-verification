import EOC.ConditionalChain
import EOC.ShellCounts
import EOC.BinomialTail

/-!
# The exceptional-set bound from the arithmetic frontier, with explicit counting inputs

`ConditionalChain.exceptional_bound_of_pairInputs` left three abstract inputs besides the
arithmetic Prop: the split shell inequality `hsplit` (which divides by `|V_{σ,s}|` and contains a
high-shell sieve sum), the sieve split `N_u` with its size condition `hX`, and `hweight`.  This file
removes all three.

* **`hsplit_of_allShells`** — with the frontier Prop on **all** frequency shells `u ≤ σ + t`
  (so the high-shell sieve sum is empty), `hsplit` follows from the explicit binomial inequality
  `(1 + (σ+1)/2)(σ+t+1)·4·4^t·L ≤ ε² C(t−1, L−1) 2^{γ j}`, `L = N − j`, via
  `ShellCounts.choose_le_mul_card_shellV`.
* `hX_one` — the trivial split `N_u = 1` satisfies `hX` as soon as `U ≤ σ + t`.
* `ExplicitPairData` — every per-pair input as an explicit numerical inequality, plus the frontier
  Prop at `Us = σ + t`; **`pairInputs_of_explicit`** — it implies `PairInputs`.
* **`hweight_of_badMass`** — for `c s σ = if good s σ then 1 + ε else 2^{s+1−K}`, `hweight` holds with
  `C = 1 + ε + κ` whenever the words of the bad pairs number at most `κ` times the Haar mass
  (`BadPairMassBound`, a pure lattice-path count).
* **`exceptional_bound_of_powerOfTwoSparsity`** — `ExplicitPairData` on the good pairs and
  `BadPairMassBound` give `#(E_U ∩ [0, 2^K)) ≤ ((1+ε+κ) e^{λ* U}/2)(2^K)^{1 − I₀ A}`.

No `sorry`, `admit`, `axiom`, `opaque`, or `native_decide`.
-/

namespace EOC
namespace FinalChain

open Finset CapacityBounds FiniteValuationWord PrefixCollision ShellwiseChain

/-! ## 1. `hsplit` with all frequency shells treated as low -/

theorem hX_one {U σ t : ℕ} (hU : U ≤ σ + t) :
    2 * PsiSieve.Xmax (collatzBarrier U) 1 ≤ 2 ^ (σ + 1 + t) := by
  have hb : collatzBarrier U 0 = U := by
    unfold collatzBarrier; simp
  simp only [PsiSieve.Xmax, range_one, sum_singleton, Nat.sub_self, pow_zero, one_mul, hb]
  calc 2 * 2 ^ U = 2 ^ (U + 1) := by ring
    _ ≤ 2 ^ (σ + 1 + t) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **`hsplit` from an explicit binomial inequality** (high-shell sum empty). -/
theorem hsplit_of_allShells {U N j s σ : ℕ} {ε γ : ℝ} (Nsplit : ℕ → ℕ)
    (hjN : j < N) (hσj : σ ≤ collatzBarrier U j) (_hσs : σ ≤ s)
    (hLt : N - j ≤ s - σ) (ht : s - σ ≤ collatzBarrier U N - σ)
    (hnum : (1 + ((σ + 1 : ℕ) : ℝ) / 2) * (((σ + (s - σ) : ℕ) : ℝ) + 1) * 4 * 4 ^ (s - σ) *
        ((N - j : ℕ) : ℝ) ≤
      ε ^ 2 * (Nat.choose (s - σ - 1) (N - j - 1) : ℝ) * (2 : ℝ) ^ (γ * j)) :
    (1 + ((σ + 1 : ℕ) : ℝ) / 2) *
        ((((σ + (s - σ) : ℕ) : ℝ) + 1) * 2 ^ (s - σ) *
            (4 * (2 : ℝ) ^ (-(γ * j)) * ((shellP (collatzBarrier U) j σ).card : ℝ) ^ 2)
          + ∑ u ∈ range (σ + 1 + (s - σ)), (if σ + (s - σ) < u then
              min 1 (2 ^ (s - σ) / (2 * 2 ^ u)) *
                (2 * PsiShellBound.sieveBound (collatzBarrier U) j σ (Nsplit u) (2 ^ u) ^ 2)
              else 0)) ≤
      ε ^ 2 * ((shellP (collatzBarrier U) j σ).card : ℝ) ^ 2 *
        (shellV (collatzBarrier U) N j σ (s - σ)).card / 2 ^ (s - σ) := by
  set t := s - σ with ht_def
  set L := N - j with hL_def
  set P : ℝ := ((shellP (collatzBarrier U) j σ).card : ℝ)
  set V : ℝ := ((shellV (collatzBarrier U) N j σ t).card : ℝ)
  have hzero : ∑ u ∈ range (σ + 1 + t), (if σ + t < u then
      min 1 (2 ^ t / (2 * 2 ^ u)) *
        (2 * PsiShellBound.sieveBound (collatzBarrier U) j σ (Nsplit u) (2 ^ u) ^ 2)
      else (0 : ℝ)) = 0 := by
    refine sum_eq_zero fun u hu => ?_
    have := mem_range.mp hu
    simp [show ¬ σ + t < u by omega]
  rw [hzero, add_zero]
  -- |V| lower bound
  have hVlow : (Nat.choose (t - 1) (L - 1) : ℝ) ≤ L * V := by
    have h := ShellCounts.choose_le_mul_card_shellV (U := U) (σ := σ) (t := t) hjN hσj hLt ht
    have h' := (Nat.cast_le (α := ℝ)).mpr h
    simpa [Nat.cast_mul] using h'
  have hLpos : (0 : ℝ) < L := by
    have : 1 ≤ L := by omega
    exact_mod_cast this
  have h2t : (0 : ℝ) < 2 ^ t := by positivity
  have hg : (0 : ℝ) < (2 : ℝ) ^ (γ * j) := Real.rpow_pos_of_pos (by norm_num) _
  have hneg : (2 : ℝ) ^ (-(γ * j)) = ((2 : ℝ) ^ (γ * j))⁻¹ := Real.rpow_neg (by norm_num) _
  have h4 : (4 : ℝ) ^ t = 2 ^ t * 2 ^ t := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
  set A : ℝ := (1 + ((σ + 1 : ℕ) : ℝ) / 2) * (((σ + t : ℕ) : ℝ) + 1) with hA
  have hA0 : 0 ≤ A := by positivity
  have hP2 : 0 ≤ P ^ 2 := sq_nonneg P
  -- target after clearing denominators: A * 4 * 2^t * 2^t * P^2 ≤ ε² P² V * 2^{γ j}
  have hmain : A * 4 * 4 ^ t ≤ ε ^ 2 * V * (2 : ℝ) ^ (γ * j) := by
    have h1 : A * 4 * 4 ^ t * L ≤ ε ^ 2 * (Nat.choose (t - 1) (L - 1) : ℝ) * (2 : ℝ) ^ (γ * j) := by
      simpa [hA, mul_assoc] using hnum
    have h2 : ε ^ 2 * (Nat.choose (t - 1) (L - 1) : ℝ) * (2 : ℝ) ^ (γ * j) ≤
        ε ^ 2 * (L * V) * (2 : ℝ) ^ (γ * j) := by
      have := mul_le_mul_of_nonneg_left hVlow (sq_nonneg ε)
      exact mul_le_mul_of_nonneg_right this hg.le
    have h3 : A * 4 * 4 ^ t * L ≤ (ε ^ 2 * V * (2 : ℝ) ^ (γ * j)) * L := by nlinarith
    exact le_of_mul_le_mul_right h3 hLpos
  rw [hneg]
  have lhs_eq : (1 + ((σ + 1 : ℕ) : ℝ) / 2) * ((((σ + t : ℕ) : ℝ) + 1) * 2 ^ t *
      (4 * ((2 : ℝ) ^ (γ * j))⁻¹ * P ^ 2)) =
      (A * 4 * 4 ^ t * P ^ 2) * ((2 : ℝ) ^ (γ * j))⁻¹ / 2 ^ t := by
    rw [hA, h4]; field_simp
  rw [lhs_eq, div_le_div_iff_of_pos_right h2t]
  calc A * 4 * 4 ^ t * P ^ 2 * ((2 : ℝ) ^ (γ * j))⁻¹
      ≤ (ε ^ 2 * V * (2 : ℝ) ^ (γ * j)) * P ^ 2 * ((2 : ℝ) ^ (γ * j))⁻¹ := by
        gcongr
    _ = ε ^ 2 * P ^ 2 * V := by field_simp

/-! ## 2. Explicit per-pair data -/

/-- **All per-pair inputs as explicit numerical conditions**, plus the arithmetic frontier Prop on
all frequency shells `u ≤ σ + t`. -/
def ExplicitPairData (U N j s σ : ℕ) (ε : ℝ) : Prop :=
  ∃ (δ K N0 Kb k n : ℕ) (d ca cb A θ' ν γ : ℝ),
    300 ≤ j ∧ 2 ∣ j ∧ collatzBarrier 0 j ≤ σ + δ ∧ δ ≤ j / 300 ∧ σ ≤ collatzBarrier U j ∧
    63 * σ + 37 ≤ 100 * j ∧ 0 < K ∧ (K : ℝ) ≤ A * Real.logb 2 j + 1 ∧ 0 ≤ ca ∧ 0 ≤ cb ∧
    0 ≤ A ∧ Kb + 31 * j / 100 + σ / (N0 + 2) ≤ j / 2 ∧ k + n ≤ Kb ∧ 2 ≤ N0 ∧ 0 ≤ d ∧ d ≤ 1 / 2 ∧
    1 / 6 < θ' ∧
    (3 * (2 + 3 / 5 * ca + 4 / 5 * A + (2 + 3 / 5 * cb + 4 / 5 * 1) / 8) / (θ' - 1 / 6)) ^ 2 ≤ j ∧
    ν * j ≤ n ∧ θ' + γ ≤ ν * Real.logb 2 ((1 + 3) / 2) ∧ γ * j ≤ ((j / 300 - δ : ℕ) : ℝ) ∧
    γ * j * Real.log 2 ≤ 8 * k * d ^ 2 / N0 ∧
    -- counting / size conditions (no abstract sieve, no |V|)
    j < N ∧ σ ≤ s ∧ N - j ≤ s - σ ∧ s - σ ≤ collatzBarrier U N - σ ∧ U ≤ σ ∧
    (1 + ((σ + 1 : ℕ) : ℝ) / 2) * (((σ + (s - σ) : ℕ) : ℝ) + 1) * 4 * 4 ^ (s - σ) *
        ((N - j : ℕ) : ℝ) ≤
      ε ^ 2 * (Nat.choose (s - σ - 1) (N - j - 1) : ℝ) * (2 : ℝ) ^ (γ * j) ∧
    -- the arithmetic input, on all shells
    FrontierRegion.PowerOfTwoDangerousWindowSparsityAt U j σ (s - σ) (σ + (s - σ)) K d ca cb

theorem pairInputs_of_explicit {U N j s σ : ℕ} {ε : ℝ} (h : ExplicitPairData U N j s σ ε) :
    ConditionalChain.PairInputs U N j s σ ε := by
  obtain ⟨δ, K, N0, Kb, k, n, d, ca, cb, A, θ', ν, γ, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, hjN, hσs, hLt, ht, hU, hnum,
    hfr⟩ := h
  refine ⟨δ, σ + (s - σ), K, N0, Kb, k, n, d, ca, cb, A, θ', ν, γ, fun _ => 1, h1, h2, h3, h4, h5,
    h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
    fun _ _ => le_rfl, fun _ _ => show 1 < j by omega, fun _ _ => hX_one (by omega), ?_, hfr⟩
  exact hsplit_of_allShells (fun _ => 1) hjN h5 hσs hLt ht hnum

/-! ## 3. `hweight` from a bad-pair word count -/

open Classical in
/-- The words of length `N`, total `≥ K`, whose pair `(s, σ)` is **not** good. -/
noncomputable def badMass (U N j0 K : ℕ) (good : ℕ → ℕ → Prop) : ℝ :=
  ∑ s ∈ Icc K (collatzBarrier U N), ∑ σ ∈ range K,
    if good s σ then 0 else
      ((shellP (collatzBarrier U) j0 σ).card : ℝ) * (shellV (collatzBarrier U) N j0 σ (s - σ)).card

/-- The Haar mass of the post-fresh confined words. -/
noncomputable def haarMass (U N K : ℕ) : ℝ :=
  ∑ w ∈ (confinedWords N (collatzBarrier U)).filter (fun w => K ≤ w.total),
    (2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (w.total + 1)

/-- **Named counting input.** The bad pairs carry at most `κ` times the Haar mass, counted as words. -/
def BadPairMassBound (U N j0 K : ℕ) (good : ℕ → ℕ → Prop) (κ : ℝ) : Prop :=
  badMass U N j0 K good ≤ κ * haarMass U N K

open Classical in
theorem hweight_of_badMass (U N K j0 : ℕ) (good : ℕ → ℕ → Prop) (ε κ : ℝ) (hε : 0 ≤ ε)
    (hj1 : 1 ≤ j0) (hjN : j0 < N) (hbK : collatzBarrier U j0 < K)
    (hbad : BadPairMassBound U N j0 K good κ) :
    ∑ s ∈ Icc K (collatzBarrier U N), ∑ σ ∈ range K,
        (if good s σ then 1 + ε else (2 : ℝ) ^ (s + 1 - K)) *
          haarShare (collatzBarrier U) N j0 K s σ ≤
      (1 + ε + κ) * ∑ w ∈ (confinedWords N (collatzBarrier U)).filter (fun w => K ≤ w.total),
        (2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (w.total + 1) := by
  have hmass := haar_mass_eq (collatzBarrier U) hj1 hjN hbK
  have hterm : ∀ s ∈ Icc K (collatzBarrier U N), ∀ σ ∈ range K,
      (if good s σ then 1 + ε else (2 : ℝ) ^ (s + 1 - K)) *
          haarShare (collatzBarrier U) N j0 K s σ ≤
        (1 + ε) * haarShare (collatzBarrier U) N j0 K s σ +
          (if good s σ then 0 else
            ((shellP (collatzBarrier U) j0 σ).card : ℝ) *
              (shellV (collatzBarrier U) N j0 σ (s - σ)).card) := by
    intro s hs σ _
    have hKs : K ≤ s := (mem_Icc.mp hs).1
    have h0 := haarShare_nonneg (collatzBarrier U) N j0 K s σ
    split_ifs
    · simp
    · rw [haarShare_eq]
      have hone : (2 : ℝ) ^ (s + 1 - K) * ((2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (s + 1)) = 1 := by
        rw [one_div_pow, ← mul_assoc, ← pow_add, show s + 1 - K + K = s + 1 by omega]
        field_simp
      have hP : (0 : ℝ) ≤ ((shellP (collatzBarrier U) j0 σ).card : ℝ) *
          (shellV (collatzBarrier U) N j0 σ (s - σ)).card := by positivity
      have hS : (0 : ℝ) ≤ (1 + ε) * (((shellP (collatzBarrier U) j0 σ).card : ℝ) *
          (shellV (collatzBarrier U) N j0 σ (s - σ)).card * ((2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (s + 1))) := by
        positivity
      calc (2 : ℝ) ^ (s + 1 - K) * (((shellP (collatzBarrier U) j0 σ).card : ℝ) *
              (shellV (collatzBarrier U) N j0 σ (s - σ)).card * ((2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (s + 1)))
          = ((shellP (collatzBarrier U) j0 σ).card : ℝ) *
              (shellV (collatzBarrier U) N j0 σ (s - σ)).card *
              ((2 : ℝ) ^ (s + 1 - K) * ((2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (s + 1))) := by ring
        _ = _ := by rw [hone, mul_one]
        _ ≤ _ := le_add_of_nonneg_left hS
  calc _ ≤ ∑ s ∈ Icc K (collatzBarrier U N), ∑ σ ∈ range K,
        ((1 + ε) * haarShare (collatzBarrier U) N j0 K s σ +
          (if good s σ then 0 else
            ((shellP (collatzBarrier U) j0 σ).card : ℝ) *
              (shellV (collatzBarrier U) N j0 σ (s - σ)).card)) :=
        sum_le_sum fun s hs => sum_le_sum fun σ hσ => hterm s hs σ hσ
    _ = (1 + ε) * ∑ s ∈ Icc K (collatzBarrier U N), ∑ σ ∈ range K,
          haarShare (collatzBarrier U) N j0 K s σ + badMass U N j0 K good := by
        unfold badMass
        rw [mul_sum]
        simp_rw [mul_sum, sum_add_distrib]
    _ ≤ (1 + ε) * haarMass U N K + κ * haarMass U N K := by
        have hbad' := hbad
        unfold BadPairMassBound haarMass at hbad'
        rw [hmass] at hbad'
        rw [haarMass, hmass]
        exact add_le_add le_rfl hbad'
    _ = _ := by unfold haarMass; ring

/-! ## 3b. `BadPairMassBound` from a single binomial tail inequality -/

/-- Hockey stick with an indicator: `∑_{t ≤ T, L ≤ t} C(t−1, L−1) ≤ C(T, L)` for `L ≥ 1`. -/
theorem sum_range_choose_le {L : ℕ} (hL : 1 ≤ L) (T : ℕ) :
    ∑ t ∈ range (T + 1), (if L ≤ t then Nat.choose (t - 1) (L - 1) else 0) ≤ Nat.choose T L := by
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  induction T with
  | zero => simp
  | succ T ih =>
    rw [sum_range_succ, Nat.choose_succ_succ']
    by_cases h : L' + 1 ≤ T + 1
    · rw [if_pos h, Nat.add_sub_cancel]; omega
    · rw [if_neg h]; omega

open Classical in
/-- **Bad-pair count from a binomial tail.**  Suppose every pair with prefix deficit
`b j0 − σ ≤ x*` and nonempty suffix shell is good.  Then `BadPairMassBound` follows from the
explicit inequality
`N · ∑_{σ < K, σ + x* < b j0} C(σ−1, j0−1) C(b N − σ, L) ≤ κ · C(b N − 1, N − 1) · 2^K 2^{−(b N + 1)}`. -/
theorem badPairMassBound_of_binomialTail {U N j0 K xs : ℕ} {κ : ℝ} (good : ℕ → ℕ → Prop)
    (hj1 : 1 ≤ j0) (hjN : j0 < N) (hKN : K ≤ collatzBarrier U N)
    (hgood : ∀ s σ, K ≤ s → σ < K → collatzBarrier U j0 ≤ σ + xs → N - j0 ≤ s - σ →
      s - σ ≤ collatzBarrier U N - σ → good s σ)
    (htail : (N : ℝ) * ∑ σ ∈ range K, (if σ + xs < collatzBarrier U j0 then
        (Nat.choose (σ - 1) (j0 - 1) : ℝ) * Nat.choose (collatzBarrier U N - σ) (N - j0) else 0) ≤
      κ * Nat.choose (collatzBarrier U N - 1) (N - 1) *
        ((2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (collatzBarrier U N + 1))) :
    BadPairMassBound U N j0 K good κ := by
  set B := collatzBarrier U N
  set L := N - j0
  have hL : 1 ≤ L := by omega
  have hN : 1 ≤ N := by omega
  -- 1. per-pair bound
  have hterm : ∀ s ∈ Icc K B, ∀ σ ∈ range K,
      (if good s σ then (0 : ℝ) else
        ((shellP (collatzBarrier U) j0 σ).card : ℝ) * (shellV (collatzBarrier U) N j0 σ (s - σ)).card) ≤
      (if σ + xs < collatzBarrier U j0 then (Nat.choose (σ - 1) (j0 - 1) : ℝ) *
        (if L ≤ s - σ ∧ s - σ ≤ B - σ then (Nat.choose (s - σ - 1) (L - 1) : ℝ) else 0) else 0) := by
    intro s hs σ hσ
    have hKs := (mem_Icc.mp hs).1
    have hσK := mem_range.mp hσ
    have hPle : ((shellP (collatzBarrier U) j0 σ).card : ℝ) ≤ Nat.choose (σ - 1) (j0 - 1) := by
      by_cases hjσ : j0 ≤ σ
      · exact_mod_cast ShellCounts.card_shellP_le_choose _ hj1 hjσ
      · rw [show shellP (collatzBarrier U) j0 σ = ∅ from
          ShellCounts.filter_total_eq_empty_of_lt hj1 _ (by omega)]
        simp
    by_cases hrange : L ≤ s - σ ∧ s - σ ≤ B - σ
    · by_cases hx : σ + xs < collatzBarrier U j0
      · rw [if_pos hx, if_pos hrange]
        split_ifs
        · positivity
        · have hV : ((shellV (collatzBarrier U) N j0 σ (s - σ)).card : ℝ) ≤
              Nat.choose (s - σ - 1) (L - 1) := by
            exact_mod_cast ShellCounts.card_shellV_le_choose _ hjN hrange.1
          exact mul_le_mul hPle hV (by positivity) (by positivity)
      · have hg := hgood s σ hKs hσK (by omega) hrange.1 hrange.2
        rw [if_pos hg, if_neg hx]
    · have hV0 : shellV (collatzBarrier U) N j0 σ (s - σ) = ∅ := by
        by_cases h1 : s - σ < L
        · exact ShellCounts.shellV_eq_empty_of_lt _ hjN h1
        · refine eq_empty_of_forall_notMem fun w hw => ?_
          obtain ⟨hW, htot⟩ := mem_filter.mp hw
          have hc := total_le_of_barrierConfined (by omega) ((mem_confinedWords (by omega)).mp hW).2
          have hK' : shiftBarrier (collatzBarrier U) j0 σ (N - j0) = B - σ := by
            unfold shiftBarrier; rw [show j0 + (N - j0) = N by omega]
          rw [hK'] at hc
          omega
      split_ifs <;> simp [hV0]
  -- 2. sum and hockey stick
  have hbad : badMass U N j0 K good ≤ ∑ σ ∈ range K, (if σ + xs < collatzBarrier U j0 then
      (Nat.choose (σ - 1) (j0 - 1) : ℝ) * Nat.choose (B - σ) L else 0) := by
    unfold badMass
    refine (sum_le_sum fun s hs => sum_le_sum fun σ hσ => hterm s hs σ hσ).trans ?_
    rw [sum_comm]
    refine sum_le_sum fun σ hσ => ?_
    split_ifs with hx
    · rw [← mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      -- ∑_{s ∈ Icc K B} [L ≤ s−σ ≤ B−σ] C(s−σ−1, L−1) ≤ C(B−σ, L)
      have hσK := mem_range.mp hσ
      have hsub : ∑ s ∈ Icc K B, (if L ≤ s - σ ∧ s - σ ≤ B - σ then
          (Nat.choose (s - σ - 1) (L - 1) : ℝ) else 0) ≤
          ∑ t ∈ range (B - σ + 1), (if L ≤ t then (Nat.choose (t - 1) (L - 1) : ℝ) else 0) := by
        have himg : ∀ s ∈ Icc K B, s - σ ∈ range (B - σ + 1) := by
          intro s hs; have := mem_Icc.mp hs; exact mem_range.mpr (by omega)
        have hinj : Set.InjOn (fun s => s - σ) (Icc K B : Finset ℕ) := by
          intro a ha b hb hab
          have := mem_Icc.mp ha; have := mem_Icc.mp hb
          simp only at hab; omega
        calc ∑ s ∈ Icc K B, (if L ≤ s - σ ∧ s - σ ≤ B - σ then
              (Nat.choose (s - σ - 1) (L - 1) : ℝ) else 0)
            ≤ ∑ s ∈ Icc K B, (fun t => if L ≤ t then (Nat.choose (t - 1) (L - 1) : ℝ) else 0)
                (s - σ) := by
              refine sum_le_sum fun s _ => ?_
              simp only
              by_cases h1 : L ≤ s - σ
              · by_cases h2 : s - σ ≤ B - σ
                · simp [h1, h2]
                · simp [h1, h2]
              · simp [h1]
          _ = ∑ t ∈ (Icc K B).image (fun s => s - σ),
                (if L ≤ t then (Nat.choose (t - 1) (L - 1) : ℝ) else 0) := by
              rw [sum_image hinj]
          _ ≤ _ := sum_le_sum_of_subset_of_nonneg
                (fun t ht => by
                  obtain ⟨s, hs, rfl⟩ := mem_image.mp ht; exact himg s hs)
                (fun _ _ _ => by split_ifs <;> positivity)
      refine hsub.trans ?_
      have h := sum_range_choose_le hL (B - σ)
      have h' : ((∑ t ∈ range (B - σ + 1), (if L ≤ t then Nat.choose (t - 1) (L - 1) else 0) : ℕ) : ℝ)
          ≤ (Nat.choose (B - σ) L : ℝ) := by exact_mod_cast h
      push_cast [Nat.cast_ite] at h'
      exact h'
    · simp
  -- 3. Haar mass lower bound from the top shell
  have hmass : (Nat.choose (B - 1) (N - 1) : ℝ) * ((2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (B + 1)) ≤
      N * haarMass U N K := by
    have hshell := collatz_shell_lower U hN (le_collatzBarrier U N) (le_refl B)
    have hsub : (confinedWords N (collatzBarrier U)).filter (fun w => w.total = B) ⊆
        (confinedWords N (collatzBarrier U)).filter (fun w => K ≤ w.total) := by
      intro w hw
      obtain ⟨h1, h2⟩ := mem_filter.mp hw
      exact mem_filter.mpr ⟨h1, by omega⟩
    have hle : (((confinedWords N (collatzBarrier U)).filter (fun w => w.total = B)).card : ℝ) *
        ((2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (B + 1)) ≤ haarMass U N K := by
      unfold haarMass
      calc (((confinedWords N (collatzBarrier U)).filter (fun w => w.total = B)).card : ℝ) *
            ((2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (B + 1))
          = ∑ w ∈ (confinedWords N (collatzBarrier U)).filter (fun w => w.total = B),
              (2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (w.total + 1) := by
            rw [sum_congr rfl fun w hw => by rw [(mem_filter.mp hw).2], sum_const, nsmul_eq_mul]
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    have hc : (Nat.choose (B - 1) (N - 1) : ℝ) ≤
        N * (((confinedWords N (collatzBarrier U)).filter (fun w => w.total = B)).card : ℝ) := by
      exact_mod_cast hshell
    have hw0 : (0 : ℝ) ≤ (2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (B + 1) := by positivity
    calc (Nat.choose (B - 1) (N - 1) : ℝ) * ((2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (B + 1))
        ≤ (N * (((confinedWords N (collatzBarrier U)).filter (fun w => w.total = B)).card : ℝ)) *
            ((2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (B + 1)) := mul_le_mul_of_nonneg_right hc hw0
      _ ≤ N * haarMass U N K := by rw [mul_assoc]; gcongr
  -- 4. combine
  unfold BadPairMassBound
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  by_cases hκ : 0 ≤ κ
  · have h1 : (N : ℝ) * badMass U N j0 K good ≤ κ * (N * haarMass U N K) := by
      calc (N : ℝ) * badMass U N j0 K good
          ≤ N * ∑ σ ∈ range K, (if σ + xs < collatzBarrier U j0 then
              (Nat.choose (σ - 1) (j0 - 1) : ℝ) * Nat.choose (B - σ) L else 0) :=
            mul_le_mul_of_nonneg_left hbad hNpos.le
        _ ≤ κ * Nat.choose (B - 1) (N - 1) * ((2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (B + 1)) := htail
        _ ≤ κ * (N * haarMass U N K) := by
            rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hmass hκ
    nlinarith
  · -- κ < 0 forces the left side of htail to be ≤ a negative number: contradiction unless 0
    exfalso
    have hl : (0 : ℝ) ≤ (N : ℝ) * ∑ σ ∈ range K, (if σ + xs < collatzBarrier U j0 then
        (Nat.choose (σ - 1) (j0 - 1) : ℝ) * Nat.choose (B - σ) L else 0) := by
      refine mul_nonneg hNpos.le (sum_nonneg fun _ _ => by split_ifs <;> positivity)
    have hr : κ * Nat.choose (B - 1) (N - 1) * ((2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (B + 1)) < 0 := by
      have hc : (0 : ℝ) < Nat.choose (B - 1) (N - 1) := by
        exact_mod_cast Nat.choose_pos (by have := le_collatzBarrier U N; omega)
      have hw : (0 : ℝ) < (2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (B + 1) := by positivity
      calc κ * Nat.choose (B - 1) (N - 1) * ((2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (B + 1))
          = κ * ((Nat.choose (B - 1) (N - 1) : ℝ) * ((2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (B + 1))) := by ring
        _ < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hκ) (mul_pos hc hw)
    linarith

/-! ## 4. The final conditional theorem -/

open Classical in
/-- **Exceptional-set bound from the arithmetic frontier.**  Choose any set of good pairs `(s, σ)`.
On good pairs assume `ExplicitPairData` (explicit numerical inequalities + the frontier Prop on all
frequency shells).  Bound the bad pairs by the lattice-path count `BadPairMassBound`.  Then
`#(E_U ∩ [0, 2^K)) ≤ ((1+ε+κ) e^{λ* U}/2) (2^K)^{1 − I₀ A}` for `N ≥ A K`. -/
theorem exceptional_bound_of_powerOfTwoSparsity (U K j0 : ℕ) {N : ℕ} (A ε κ : ℝ)
    (good : ℕ → ℕ → Prop) (hε : 0 ≤ ε) (hκ : 0 ≤ κ) (hj1 : 1 ≤ j0) (hjN : j0 < N)
    (hbK : collatzBarrier U j0 < K) (hNA : A * K ≤ N)
    (hgood : ∀ s σ, K ≤ s → σ < K → good s σ → ExplicitPairData U N j0 s σ ε)
    (hbad : BadPairMassBound U N j0 K good κ) :
    (((range (2 ^ K)).filter fun μ =>
        Odd μ ∧ ∀ M, Confined (U : ℝ) (fun i => a (orbit μ i)) M).card : ℝ) ≤
      (1 + ε + κ) * Real.exp (TaoExternal.lambdaStar * U) / 2 *
        ((2 ^ K : ℕ) : ℝ) ^ (1 - TaoExternal.I0 * A) := by
  refine ConditionalChain.exceptional_bound_of_pairInputs U K j0 A (1 + ε + κ)
    (fun s σ => if good s σ then 1 + ε else (2 : ℝ) ^ (s + 1 - K)) (by linarith) hj1 hjN hbK hNA
    ?_ (hweight_of_badMass U N K j0 good ε κ hε hj1 hjN hbK hbad)
  intro s σ hKs hσK
  by_cases hg : good s σ
  · left
    exact ⟨ε, hε, by simp [hg], pairInputs_of_explicit (hgood s σ hKs hσK hg)⟩
  · right
    simp [hg]

end FinalChain
end EOC

namespace EOC
namespace FinalChain

open Finset CapacityBounds FiniteValuationWord PrefixCollision ShellwiseChain

open Classical in
/-- **Packaged form.**  Good pairs are those with prefix deficit `b j0 − σ ≤ x*` and nonempty suffix
range `L ≤ t ≤ b N − σ`.  Assume `ExplicitPairData` (explicit inequalities + the arithmetic frontier)
on every good pair, and the single binomial tail inequality.  Then
`#(E_U ∩ [0, 2^K)) ≤ ((1+ε+κ) e^{λ* U}/2)(2^K)^{1 − I₀ A}`. -/
theorem exceptional_bound_of_frontier_and_tail (U K j0 xs : ℕ) {N : ℕ} (A ε κ : ℝ)
    (hε : 0 ≤ ε) (hκ : 0 ≤ κ) (hj1 : 1 ≤ j0) (hjN : j0 < N)
    (hbK : collatzBarrier U j0 < K) (hKN : K ≤ collatzBarrier U N) (hNA : A * K ≤ N)
    (hgood : ∀ s σ, K ≤ s → σ < K → collatzBarrier U j0 ≤ σ + xs → N - j0 ≤ s - σ →
      s - σ ≤ collatzBarrier U N - σ → ExplicitPairData U N j0 s σ ε)
    (htail : (N : ℝ) * ∑ σ ∈ range K, (if σ + xs < collatzBarrier U j0 then
        (Nat.choose (σ - 1) (j0 - 1) : ℝ) * Nat.choose (collatzBarrier U N - σ) (N - j0) else 0) ≤
      κ * Nat.choose (collatzBarrier U N - 1) (N - 1) *
        ((2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (collatzBarrier U N + 1))) :
    (((range (2 ^ K)).filter fun μ =>
        Odd μ ∧ ∀ M, Confined (U : ℝ) (fun i => a (orbit μ i)) M).card : ℝ) ≤
      (1 + ε + κ) * Real.exp (TaoExternal.lambdaStar * U) / 2 *
        ((2 ^ K : ℕ) : ℝ) ^ (1 - TaoExternal.I0 * A) := by
  set good : ℕ → ℕ → Prop := fun s σ => collatzBarrier U j0 ≤ σ + xs ∧ N - j0 ≤ s - σ ∧
    s - σ ≤ collatzBarrier U N - σ
  refine exceptional_bound_of_powerOfTwoSparsity U K j0 A ε κ good hε hκ hj1 hjN hbK hNA
    (fun s σ hKs hσK hg => hgood s σ hKs hσK hg.1 hg.2.1 hg.2.2) ?_
  exact badPairMassBound_of_binomialTail good hj1 hjN hKN
    (fun s σ _ _ h1 h2 h3 => ⟨h1, h2, h3⟩) htail

open Classical in
/-- **Final form with a scalar tail condition.**  The binomial tail inequality is implied by
`N · ∏_{y ≤ x*} fbar y / (1 − fbar (x*+1)) ≤ κ · 2^K 2^{−(B+1)}` with
`fbar y = (b−j0)/(b−1) · (M0+y)/(M0+y−L)`, `b = b_U j0`, `B = b_U N`, `M0 = B − b + 1`, `L = N − j0`. -/
theorem exceptional_bound_of_frontier_and_scalar (U K j0 xs : ℕ) {N : ℕ} (A ε κ : ℝ)
    (hε : 0 ≤ ε) (hκ : 0 ≤ κ) (hj2 : 2 ≤ j0) (hjN : j0 < N)
    (hbK : collatzBarrier U j0 < K) (hKN : K ≤ collatzBarrier U N) (hNA : A * K ≤ N)
    (hL : N - j0 < collatzBarrier U N - collatzBarrier U j0 + 1)
    (hρ : BinomialTail.fbar j0 (collatzBarrier U j0) (N - j0)
      (collatzBarrier U N - collatzBarrier U j0 + 1) (xs + 1) < 1)
    (hscalar : (N : ℝ) * (∏ y ∈ range (xs + 1), BinomialTail.fbar j0 (collatzBarrier U j0) (N - j0)
        (collatzBarrier U N - collatzBarrier U j0 + 1) y) /
        (1 - BinomialTail.fbar j0 (collatzBarrier U j0) (N - j0)
          (collatzBarrier U N - collatzBarrier U j0 + 1) (xs + 1)) ≤
      κ * ((2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (collatzBarrier U N + 1)))
    (hgood : ∀ s σ, K ≤ s → σ < K → collatzBarrier U j0 ≤ σ + xs → N - j0 ≤ s - σ →
      s - σ ≤ collatzBarrier U N - σ → ExplicitPairData U N j0 s σ ε) :
    (((range (2 ^ K)).filter fun μ =>
        Odd μ ∧ ∀ M, Confined (U : ℝ) (fun i => a (orbit μ i)) M).card : ℝ) ≤
      (1 + ε + κ) * Real.exp (TaoExternal.lambdaStar * U) / 2 *
        ((2 ^ K : ℕ) : ℝ) ^ (1 - TaoExternal.I0 * A) := by
  have hjb : j0 ≤ collatzBarrier U j0 := le_collatzBarrier U j0
  have hbB : collatzBarrier U j0 ≤ collatzBarrier U N := ShellCounts.collatzBarrier_mono U hjN.le
  refine exceptional_bound_of_frontier_and_tail U K j0 xs A ε κ hε hκ (by omega) hjN hbK hKN hNA
    hgood ?_
  have ht := BinomialTail.deficit_tail_le (K := K) xs hj2 hjb (by omega) hbB hjN hL hρ
  set P := ∏ y ∈ range (xs + 1), BinomialTail.fbar j0 (collatzBarrier U j0) (N - j0)
    (collatzBarrier U N - collatzBarrier U j0 + 1) y
  set ρ := BinomialTail.fbar j0 (collatzBarrier U j0) (N - j0)
    (collatzBarrier U N - collatzBarrier U j0 + 1) (xs + 1)
  set Cc : ℝ := ((collatzBarrier U N - 1).choose (N - 1) : ℝ)
  have hC0 : 0 ≤ Cc := by positivity
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  calc (N : ℝ) * ∑ σ ∈ range K, (if σ + xs < collatzBarrier U j0 then
        ((σ - 1).choose (j0 - 1) : ℝ) * ((collatzBarrier U N - σ).choose (N - j0) : ℝ) else 0)
      ≤ N * (Cc * P / (1 - ρ)) := mul_le_mul_of_nonneg_left ht hN0
    _ = Cc * (N * P / (1 - ρ)) := by ring
    _ ≤ Cc * (κ * ((2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (collatzBarrier U N + 1))) :=
        mul_le_mul_of_nonneg_left hscalar hC0
    _ = _ := by ring

end FinalChain
end EOC
