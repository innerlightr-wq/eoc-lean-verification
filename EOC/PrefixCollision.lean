import EOC.PrefixSuffixBilinear
import EOC.RealizerLift

/-!
# Prefix–suffix gluing and the prefix-collision ⇒ exponent chain

Fix a barrier `b` (e.g. `collatzBarrier U`), a split depth `1 ≤ j0 < N`, and write every word
`w` of length `N` as `concat N (pre j0 w) (suf j0 w)`.

* `pre`, `suf`, `concat`, `shiftBarrier`; `pre_concat`, `suf_concat`, `concat_pre_suf`.
* `shellP b j0 σ` (confined prefixes of total `σ`), `shellV b N j0 σ t` (suffixes of total `t`,
  confined under the barrier `i ↦ b (j0 + i) − σ`).
* `mem_split`, `sum_shell_eq_sum_split` — **word-level gluing**: for any `F`,
  `∑_{w ∈ W_b(N), S_w = s} F w = ∑_{σ ≤ s} ∑_{P ∈ P_{j0,σ}} ∑_{v ∈ V_{σ,s}} F (P·v)`.
  Confinement couples prefix and suffix only through `σ`.
* `leastRealizer_concat_pre`, `S_concat_pre`, `leastRealizer_concat_suf`, `S_concat_suf` —
  least realizers and valuation sums of `P·v` restrict to those of `P` and of `v`.
* `endState P = T^{j0}(r_P)`; `invThree j0 t = 3^{−j0} ∈ ℤ/2^t`;
  `alphaV j0 t v = 3^{−j0}(r_v − 1)/2`, `betaP t P = 3^{−j0}(m_P − 1)/2` in `ℤ/2^t`.
* `concatBlock_cast` — the concatenation block is `k ≡ α_v − β_P (mod 2^t)`, `t = S_v`.
* `lt_pow_iff_incidence` — **incidence form**: for `S_P < K`,
  `r_{P·v} < 2^K ↔ (α_v − β_P) mod 2^t < 2^(K − S_P − 1)`.
* `alphaV_injOn` — suffix coordinates are distinct on a suffix shell.
* `prefixCount`, `PrefixCollisionBound` — the prefix collision hypothesis
  `2^t ∑_z N(z)^2 ≤ |P_{j0,σ}|^2 (1 + ε^2 |V_{σ,s}| / 2^t)` for all `s ≥ K > σ`, i.e. relative
  collision excess `δ = 2^t Col − 1 ≤ ε^2 |V| / 2^t` of `m_P mod 2^(t+1)`.
* `split_count_le`, `shell_count_le_of_collision` — per `(σ, s)` and per word shell, via
  `PrefixSuffixBilinear.bilinear_incidence_le`.
* `leastRealizerBound_of_prefixCollision` — the hypothesis of
  `ResidueDiscrepancy.exceptional_count_le_of_leastRealizerBound` with `C = 1 + ε`.
* `exceptional_count_le_of_prefixCollision` — **full chain**: prefix collision bound at a split
  depth with `⌊j0 α + U⌋ < K` and `N ≥ A K` ⇒
  `#(E_U ∩ [0, 2^K)) ≤ ((1 + ε) e^{λ* U}/2) · (2^K)^{1 − I₀ A}`.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace PrefixCollision

open Finset CapacityBounds FiniteValuationWord SuffixTransport LiftDigits PrefixSuffixBilinear

/-! ## Prefix, suffix, concatenation -/

/-- The first `j0` digits of a word. -/
def pre (j0 : ℕ) {N : ℕ} (w : FiniteValuationWord N) : FiniteValuationWord j0 :=
  fun i => w.toInfinite i

/-- The digits `j0, …, N−1` of a word. -/
def suf (j0 : ℕ) {N : ℕ} (w : FiniteValuationWord N) : FiniteValuationWord (N - j0) :=
  fun i => w.toInfinite (j0 + i)

/-- Concatenation of a length-`j0` prefix and a length-`(N − j0)` suffix. -/
def concat (N : ℕ) {j0 : ℕ} (P : FiniteValuationWord j0) (v : FiniteValuationWord (N - j0)) :
    FiniteValuationWord N :=
  fun i => if (i : ℕ) < j0 then P.toInfinite i else v.toInfinite (i - j0)

/-- The barrier seen by a suffix after a prefix of length `j0` and total `σ`. -/
def shiftBarrier (b : ℕ → ℕ) (j0 σ : ℕ) : ℕ → ℕ := fun i => b (j0 + i) - σ

section Basic

variable {N j0 : ℕ}

theorem pre_toInfinite (w : FiniteValuationWord N) {i : ℕ} (hi : i < j0) :
    (pre j0 w).toInfinite i = w.toInfinite i := by
  rw [toInfinite_apply_of_lt _ hi]; rfl

theorem suf_toInfinite (w : FiniteValuationWord N) {i : ℕ} (hi : i < N - j0) :
    (suf j0 w).toInfinite i = shiftWord w.toInfinite j0 i := by
  rw [toInfinite_apply_of_lt _ hi]; rfl

theorem concat_toInfinite_lt (P : FiniteValuationWord j0) (v : FiniteValuationWord (N - j0))
    (hj : j0 ≤ N) {i : ℕ} (hi : i < j0) : (concat N P v).toInfinite i = P.toInfinite i := by
  rw [toInfinite_apply_of_lt _ (by omega)]
  simp [concat, hi]

theorem concat_toInfinite_ge (P : FiniteValuationWord j0) (v : FiniteValuationWord (N - j0))
    {i : ℕ} (hi : j0 ≤ i) (hiN : i < N) :
    (concat N P v).toInfinite i = v.toInfinite (i - j0) := by
  rw [toInfinite_apply_of_lt _ hiN]
  simp [concat, Nat.not_lt.mpr hi]

theorem pre_concat (P : FiniteValuationWord j0) (v : FiniteValuationWord (N - j0))
    (hj : j0 ≤ N) : pre j0 (concat N P v) = P := by
  funext i
  simp only [pre]
  rw [concat_toInfinite_lt P v hj i.isLt, toInfinite_apply_of_lt _ i.isLt]

theorem suf_concat (P : FiniteValuationWord j0) (v : FiniteValuationWord (N - j0))
    (hj : j0 ≤ N) : suf j0 (concat N P v) = v := by
  funext i
  simp only [suf]
  rw [concat_toInfinite_ge P v (by omega) (by omega), toInfinite_apply_of_lt _ (by omega)]
  congr 1; ext; simp

theorem concat_pre_suf (w : FiniteValuationWord N) (hj : j0 ≤ N) :
    concat N (pre j0 w) (suf j0 w) = w := by
  funext i
  by_cases hi : (i : ℕ) < j0
  · simp only [concat, hi, ite_true]
    rw [pre_toInfinite w hi, toInfinite_apply_of_lt _ i.isLt]
  · simp only [concat, hi, ite_false]
    rw [suf_toInfinite w (by omega), shiftWord, show j0 + (i - j0) = i by omega,
      toInfinite_apply_of_lt _ i.isLt]

/-- `s` depends only on the digits below its length. -/
theorem s_congr {d d' : ℕ → ℕ} {n : ℕ} (h : ∀ i < n, d i = d' i) : s d n = s d' n :=
  Finset.sum_congr rfl fun i hi => h i (Finset.mem_range.mp hi)

theorem prefixSum_pre (w : FiniteValuationWord N) (hj : j0 ≤ N) {i : ℕ} (hi : i ≤ j0) :
    (pre j0 w).prefixSum i = w.prefixSum i := by
  rw [prefixSum_eq_s _ hi, prefixSum_eq_s _ (by omega)]
  exact s_congr fun k hk => pre_toInfinite w (by omega)

theorem prefixSum_suf (w : FiniteValuationWord N) (hj : j0 ≤ N) {i : ℕ} (hi : i ≤ N - j0) :
    (suf j0 w).prefixSum i + w.prefixSum j0 = w.prefixSum (j0 + i) := by
  rw [prefixSum_eq_s _ hi, prefixSum_eq_s _ hj, prefixSum_eq_s _ (by omega),
    s_add_shiftWord w.toInfinite j0 i, s_congr fun k hk => suf_toInfinite w (by omega)]
  ring

theorem total_pre (w : FiniteValuationWord N) (hj : j0 ≤ N) :
    (pre j0 w).total = w.prefixSum j0 := prefixSum_pre w hj le_rfl

theorem total_suf (w : FiniteValuationWord N) (hj : j0 ≤ N) :
    (suf j0 w).total + w.prefixSum j0 = w.total := by
  have h := prefixSum_suf w hj (i := N - j0) le_rfl
  rw [show j0 + (N - j0) = N by omega] at h
  exact h

theorem positive_pre {w : FiniteValuationWord N} (hw : w.Positive) (hj : j0 ≤ N) :
    (pre j0 w).Positive := fun i => by
  simp only [pre]; rw [toInfinite_apply_of_lt _ (by omega)]; exact hw _

theorem positive_suf {w : FiniteValuationWord N} (hw : w.Positive) :
    (suf j0 w).Positive := fun i => by
  simp only [suf]; rw [toInfinite_apply_of_lt _ (by omega)]; exact hw _

theorem positive_concat {P : FiniteValuationWord j0} {v : FiniteValuationWord (N - j0)}
    (hP : P.Positive) (hv : v.Positive) : (concat N P v).Positive := fun i => by
  simp only [concat]
  split_ifs with h
  · rw [toInfinite_apply_of_lt _ h]; exact hP _
  · rw [toInfinite_apply_of_lt _ (by omega)]; exact hv _

theorem prefixSum_ge_of_positive {n : ℕ} {w : FiniteValuationWord n} (hw : w.Positive)
    {i : ℕ} (hi : i ≤ n) : i ≤ w.prefixSum i := by
  rw [prefixSum_eq_s _ hi]
  calc i = ∑ _k ∈ range i, 1 := by simp
    _ ≤ s w.toInfinite i := Finset.sum_le_sum fun k hk => by
        rw [toInfinite_apply_of_lt _ (by have := Finset.mem_range.mp hk; omega)]; exact hw _

end Basic

/-! ## Word-level gluing -/

section Gluing

variable {N j0 : ℕ}

/-- Prefix shell `P_{j0,σ}`. -/
def shellP (b : ℕ → ℕ) (j0 σ : ℕ) : Finset (FiniteValuationWord j0) :=
  (confinedWords j0 b).filter fun P => P.total = σ

/-- Suffix shell `V_{σ,s}` (suffix total `t = s − σ`, shifted barrier). -/
def shellV (b : ℕ → ℕ) (N j0 σ t : ℕ) : Finset (FiniteValuationWord (N - j0)) :=
  (confinedWords (N - j0) (shiftBarrier b j0 σ)).filter fun v => v.total = t

theorem mem_split (b : ℕ → ℕ) (hj1 : 1 ≤ j0) (hjN : j0 < N) {s σ : ℕ}
    {w : FiniteValuationWord N} :
    (w ∈ (confinedWords N b).filter (fun w => w.total = s) ∧ (pre j0 w).total = σ) ↔
      (pre j0 w ∈ shellP b j0 σ ∧ suf j0 w ∈ shellV b N j0 σ (s - σ) ∧ σ ≤ s) := by
  have hj : j0 ≤ N := hjN.le
  simp only [shellP, shellV, mem_filter, mem_confinedWords (by omega : 1 ≤ N),
    mem_confinedWords hj1, mem_confinedWords (by omega : 1 ≤ N - j0), BarrierConfined,
    Finset.mem_Icc, shiftBarrier]
  have htp := total_pre w hj
  have hts := total_suf w hj
  constructor
  · rintro ⟨⟨⟨hpos, hbar⟩, htot⟩, hσ⟩
    refine ⟨⟨⟨positive_pre hpos hj, fun i hi => ?_⟩, hσ⟩, ⟨⟨positive_suf hpos, fun i hi => ?_⟩,
      by omega⟩, by omega⟩
    · rw [prefixSum_pre w hj hi.2]; exact hbar i ⟨hi.1, by omega⟩
    · have h1 := prefixSum_suf w hj (i := i) hi.2
      have h2 := hbar (j0 + i) ⟨by omega, by omega⟩
      omega
  · rintro ⟨⟨⟨hPpos, hPbar⟩, hPσ⟩, ⟨⟨hvpos, hvbar⟩, hvt⟩, hσs⟩
    have hpos : w.Positive := by
      rw [← concat_pre_suf w hj]; exact positive_concat hPpos hvpos
    refine ⟨⟨⟨hpos, fun i hi => ?_⟩, by omega⟩, hPσ⟩
    by_cases hij : i ≤ j0
    · rw [← prefixSum_pre w hj hij]; exact hPbar i ⟨hi.1, hij⟩
    · have h1 := prefixSum_suf w hj (i := i - j0) (by omega)
      have h2 := hvbar (i - j0) ⟨by omega, by omega⟩
      have h3 := prefixSum_ge_of_positive (positive_suf (j0 := j0) hpos)
        (i := i - j0) (by omega)
      rw [show j0 + (i - j0) = i by omega] at h1 h2
      omega

/-- **Word-level gluing.** A shell of confined words of length `N` is the disjoint union over the
prefix total `σ` of products `P_{j0,σ} × V_{σ,s}` (prefix confined, suffix confined under the
barrier shifted by `σ`), via `concat`. -/
theorem sum_shell_eq_sum_split {R : Type*} [AddCommMonoid R] (b : ℕ → ℕ) (hj1 : 1 ≤ j0)
    (hjN : j0 < N) (s : ℕ) (F : FiniteValuationWord N → R) :
    ∑ w ∈ (confinedWords N b).filter (fun w => w.total = s), F w =
      ∑ σ ∈ range (s + 1), ∑ P ∈ shellP b j0 σ, ∑ v ∈ shellV b N j0 σ (s - σ),
        F (concat N P v) := by
  have hj : j0 ≤ N := hjN.le
  set W := (confinedWords N b).filter (fun w => w.total = s)
  have hmaps : ∀ w ∈ W, (pre j0 w).total ∈ range (s + 1) := by
    intro w hw
    have hts := total_suf w hj
    have htp := total_pre w hj
    have : w.total = s := (mem_filter.mp hw).2
    exact mem_range.mpr (by omega)
  rw [← sum_fiberwise_of_maps_to hmaps]
  refine sum_congr rfl fun σ hσ => ?_
  have hσs : σ ≤ s := by have := mem_range.mp hσ; omega
  rw [← sum_product']
  refine sum_nbij' (fun w => (pre j0 w, suf j0 w)) (fun x => concat N x.1 x.2) ?_ ?_ ?_ ?_ ?_
  · intro w hw
    have h := (mem_split b hj1 hjN).mp (mem_filter.mp hw)
    exact mem_product.mpr ⟨h.1, h.2.1⟩
  · intro x hx
    obtain ⟨hP, hv⟩ := mem_product.mp hx
    have h := (mem_split b hj1 hjN (w := concat N x.1 x.2) (s := s) (σ := σ)).mpr
      ⟨by rw [pre_concat _ _ hj]; exact hP, by rw [suf_concat _ _ hj]; exact hv, hσs⟩
    exact mem_filter.mpr h
  · intro w _; exact concat_pre_suf w hj
  · intro x _; rw [pre_concat _ _ hj, suf_concat _ _ hj]
  · intro w _; rw [concat_pre_suf w hj]

end Gluing


/-! ## Least-realizer compatibility and the incidence form -/

section Incidence

variable {N j0 : ℕ}

/-- The prefix end state `m_P = T^{j0}(r_P)`. -/
noncomputable def endState (P : FiniteValuationWord j0) : ℕ :=
  orbit (leastRealizer P.toInfinite j0) j0

/-- `3^{-j0}` in `ZMod (2^t)`. -/
noncomputable def invThree (j0 t : ℕ) : ZMod (2 ^ t) := ((3 ^ j0 : ℕ) : ZMod (2 ^ t))⁻¹

theorem three_pow_mul_invThree (j0 t : ℕ) :
    ((3 ^ j0 : ℕ) : ZMod (2 ^ t)) * invThree j0 t = 1 :=
  ZMod.coe_mul_inv_eq_one _ (Nat.Coprime.pow j0 t (by norm_num : Nat.Coprime 3 2))

/-- Suffix coordinate `α_v = 3^{-j0} (r_v − 1)/2 ∈ ℤ/2^t`. -/
noncomputable def alphaV (j0 t : ℕ) {L : ℕ} (v : FiniteValuationWord L) : ZMod (2 ^ t) :=
  invThree j0 t * (((leastRealizer v.toInfinite L - 1) / 2 : ℕ) : ZMod (2 ^ t))

/-- Prefix coordinate `β_P = 3^{-j0} (m_P − 1)/2 ∈ ℤ/2^t`. -/
noncomputable def betaP (t : ℕ) (P : FiniteValuationWord j0) : ZMod (2 ^ t) :=
  invThree j0 t * (((endState P - 1) / 2 : ℕ) : ZMod (2 ^ t))

theorem positive_toInfinite_of_positive {n : ℕ} {w : FiniteValuationWord n} (hw : w.Positive) :
    ∀ i < n, 1 ≤ w.toInfinite i := (positive_iff_toInfinite w).mp hw

/-- Prefix data of a concatenation are those of the prefix. -/
theorem leastRealizer_concat_pre (P : FiniteValuationWord j0) (v : FiniteValuationWord (N - j0))
    (hj : j0 ≤ N) :
    leastRealizer (concat N P v).toInfinite j0 = leastRealizer P.toInfinite j0 :=
  leastRealizer_eq_of_agree _ _ j0 fun _ hi => concat_toInfinite_lt P v hj hi

theorem S_concat_pre (P : FiniteValuationWord j0) (v : FiniteValuationWord (N - j0))
    (hj : j0 ≤ N) : S (concat N P v).toInfinite j0 = P.total := by
  rw [← ResidueDiscrepancy.total_eq_S P]
  exact s_congr fun _ hi => concat_toInfinite_lt P v hj hi

theorem shift_concat_agree (P : FiniteValuationWord j0) (v : FiniteValuationWord (N - j0))
    (hj : j0 ≤ N) : ∀ i < N - j0, shiftWord (concat N P v).toInfinite j0 i = v.toInfinite i :=
  fun i _ => by
    simp only [shiftWord]
    rw [concat_toInfinite_ge P v (by omega) (by omega), Nat.add_sub_cancel_left]

theorem leastRealizer_concat_suf (P : FiniteValuationWord j0) (v : FiniteValuationWord (N - j0))
    (hj : j0 ≤ N) :
    leastRealizer (shiftWord (concat N P v).toInfinite j0) (N - j0) =
      leastRealizer v.toInfinite (N - j0) :=
  leastRealizer_eq_of_agree _ _ _ (shift_concat_agree P v hj)

theorem S_concat_suf (P : FiniteValuationWord j0) (v : FiniteValuationWord (N - j0))
    (hj : j0 ≤ N) : S (shiftWord (concat N P v).toInfinite j0) (N - j0) = v.total := by
  rw [← ResidueDiscrepancy.total_eq_S v]
  exact s_congr (shift_concat_agree P v hj)

theorem odd_leastRealizer_of_positive {n : ℕ} {w : FiniteValuationWord n} (hw : w.Positive) :
    Odd (leastRealizer w.toInfinite n) :=
  (leastRealizer_realizes_all _ n (positive_toInfinite_of_positive hw)).1

/-- The key congruence in `ZMod (2^t)`: the concatenation block `k` equals `α_v − β_P`. -/
theorem concatBlock_cast (P : FiniteValuationWord j0) (v : FiniteValuationWord (N - j0))
    (hj1 : 1 ≤ j0) (hjN : j0 < N) (hP : P.Positive) (hv : v.Positive) :
    ((concatBlock (concat N P v).toInfinite j0 N : ℕ) : ZMod (2 ^ v.total)) =
      alphaV j0 v.total v - betaP v.total P := by
  have hj : j0 ≤ N := hjN.le
  set d := (concat N P v).toInfinite
  have hd : ∀ i < N, 1 ≤ d i := positive_toInfinite_of_positive (positive_concat hP hv)
  have h := concat_modEq hj1 hd hj
  rw [S_concat_suf P v hj, leastRealizer_concat_suf P v hj,
    leastRealizer_concat_pre P v hj] at h
  set k := concatBlock d j0 N
  set t := v.total
  set m := endState P
  set r := leastRealizer v.toInfinite (N - j0)
  have hm : Odd m := odd_orbit (odd_leastRealizer_of_positive hP) j0
  have hr : Odd r := odd_leastRealizer_of_positive hv
  obtain ⟨a, ha⟩ := hm
  obtain ⟨c, hc⟩ := hr
  have h' : m + 2 * 3 ^ j0 * k ≡ r [MOD 2 ^ (t + 1)] := h
  rw [ha, hc, show 2 * a + 1 + 2 * 3 ^ j0 * k = 2 * (a + 3 ^ j0 * k) + 1 by ring,
    pow_succ, mul_comm (2 ^ t) 2] at h'
  have h2 := Nat.ModEq.mul_left_cancel' (by norm_num) (Nat.ModEq.add_right_cancel' 1 h')
  have h3 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h2
  have hma : (m - 1) / 2 = a := by omega
  have hrc : (r - 1) / 2 = c := by omega
  simp only [alphaV, betaP]
  change _ = invThree j0 t * ((((r - 1) / 2 : ℕ)) : ZMod (2 ^ t)) -
    invThree j0 t * ((((m - 1) / 2 : ℕ)) : ZMod (2 ^ t))
  rw [hma, hrc, ← h3, ← mul_sub]
  have h4 : ((3 : ZMod (2 ^ t)) ^ j0) * invThree j0 t = 1 := by
    have := three_pow_mul_invThree j0 t
    push_cast at this
    exact this
  push_cast
  rw [add_sub_cancel_left, ← mul_assoc, mul_comm (invThree j0 t), h4, one_mul]

/-- **Incidence form.** For `S_P = σ < K ≤ s = σ + t`, the concatenation `P·v` has least
realizer below `2^K` iff `(α_v − β_P) mod 2^t < 2^(K − σ − 1)`. -/
theorem lt_pow_iff_incidence (P : FiniteValuationWord j0) (v : FiniteValuationWord (N - j0))
    (hj1 : 1 ≤ j0) (hjN : j0 < N) (hP : P.Positive) (hv : v.Positive) {K : ℕ}
    (hK : P.total < K) :
    leastRealizer (concat N P v).toInfinite N < 2 ^ K ↔
      (alphaV j0 v.total v - betaP v.total P).val < 2 ^ (K - P.total - 1) := by
  have hj : j0 ≤ N := hjN.le
  set d := (concat N P v).toInfinite
  have hd : ∀ i < N, 1 ≤ d i := positive_toInfinite_of_positive (positive_concat hP hv)
  have hS := S_concat_pre P v hj
  rw [lt_pow_iff_concat hd hj (by rw [hS]; exact hK), hS, ← concatBlock_cast P v hj1 hjN hP hv,
    ZMod.val_cast_of_lt]
  have := concat_lt (d := d) hj
  rwa [S_concat_suf P v hj] at this

/-- Distinct suffix words of the same shell have distinct coordinates `α_v`. -/
theorem alphaV_injOn {L j0 t : ℕ} (V : Finset (FiniteValuationWord L))
    (hV : ∀ v ∈ V, v.Positive ∧ v.total = t) :
    Set.InjOn (alphaV j0 t) (↑V : Set (FiniteValuationWord L)) := by
  intro v hv v' hv' heq
  obtain ⟨hvp, hvt⟩ := hV v hv
  obtain ⟨hvp', hvt'⟩ := hV v' hv'
  simp only [alphaV] at heq
  have h1 := congrArg (fun x => ((3 ^ j0 : ℕ) : ZMod (2 ^ t)) * x) heq
  simp only [← mul_assoc, three_pow_mul_invThree, one_mul] at h1
  have hr := odd_leastRealizer_of_positive hvp
  have hr' := odd_leastRealizer_of_positive hvp'
  have hlt := leastRealizer_lt v.toInfinite L
  have hlt' := leastRealizer_lt v'.toInfinite L
  rw [ResidueDiscrepancy.total_eq_S, hvt] at hlt
  rw [ResidueDiscrepancy.total_eq_S, hvt'] at hlt'
  have hpow : 2 ^ (t + 1) = 2 * 2 ^ t := by ring
  have hx := ZMod.val_cast_of_lt (n := 2 ^ t)
    (a := (leastRealizer v.toInfinite L - 1) / 2) (by omega)
  have hx' := ZMod.val_cast_of_lt (n := 2 ^ t)
    (a := (leastRealizer v'.toInfinite L - 1) / 2) (by omega)
  have heqn : (leastRealizer v.toInfinite L - 1) / 2 = (leastRealizer v'.toInfinite L - 1) / 2 := by
    rw [← hx, ← hx', h1]
  have hreq : leastRealizer v.toInfinite L = leastRealizer v'.toInfinite L := by
    obtain ⟨a, ha⟩ := hr; obtain ⟨b, hb⟩ := hr'; omega
  have hR := leastRealizer_realizes_all _ L (positive_toInfinite_of_positive hvp)
  have hR' := leastRealizer_realizes_all _ L (positive_toInfinite_of_positive hvp')
  rw [hreq] at hR
  exact ResidueDiscrepancy.word_eq_of_realizes hR hR'

end Incidence

/-! ## The prefix-collision chain -/

section Chain

variable {N j0 : ℕ}

/-- Prefix-state multiplicities `N(z) = #{P ∈ P_{j0,σ} : β_P = z}` in `ℤ/2^t`. -/
noncomputable def prefixCount (b : ℕ → ℕ) (j0 σ t : ℕ) (z : ZMod (2 ^ t)) : ℝ :=
  (((shellP b j0 σ).filter fun P => betaP t P = z).card : ℝ)

theorem sum_prefixCount (b : ℕ → ℕ) (j0 σ t : ℕ) :
    ∑ z, prefixCount b j0 σ t z = ((shellP b j0 σ).card : ℝ) := by
  unfold prefixCount
  rw [← Nat.cast_sum, ← card_eq_sum_card_fiberwise (fun P _ => mem_univ (betaP t P))]

/-- **Prefix collision bound** with constant `ε`: for every post-fresh word shell `s ≥ K` and
every fresh prefix shell `σ < K`, with `t = s − σ`, the relative collision excess
`δ = 2^t ∑_z N(z)^2 / |P_{j0,σ}|^2 − 1` of the prefix coordinates `β_P ∈ ℤ/2^t` (equivalently of
the end states `m_P mod 2^(t+1)`) is at most `ε^2 |V_{σ,s}| / 2^t` (stated multiplied out). -/
def PrefixCollisionBound (b : ℕ → ℕ) (N j0 K : ℕ) (ε : ℝ) : Prop :=
  ∀ s σ, K ≤ s → σ < K →
    (2 : ℝ) ^ (s - σ) * ∑ z : ZMod (2 ^ (s - σ)), prefixCount b j0 σ (s - σ) z ^ 2 ≤
      ((shellP b j0 σ).card : ℝ) ^ 2 *
        (1 + ε ^ 2 * (shellV b N j0 σ (s - σ)).card / 2 ^ (s - σ))

theorem mem_shellP {b : ℕ → ℕ} (hj1 : 1 ≤ j0) {σ : ℕ} {P : FiniteValuationWord j0}
    (hP : P ∈ shellP b j0 σ) : P.Positive ∧ BarrierConfined b P ∧ P.total = σ := by
  simp only [shellP, mem_filter, mem_confinedWords hj1] at hP
  exact ⟨hP.1.1, hP.1.2, hP.2⟩

theorem mem_shellV {b : ℕ → ℕ} (hjN : j0 < N) {σ t : ℕ} {v : FiniteValuationWord (N - j0)}
    (hv : v ∈ shellV b N j0 σ t) : v.Positive ∧ v.total = t := by
  simp only [shellV, mem_filter, mem_confinedWords (by omega : 1 ≤ N - j0)] at hv
  exact ⟨hv.1.1, hv.2⟩

/-- The dyadic interval `{0, …, M−1} ⊆ ℤ/2^t`. -/
theorem mem_image_range_iff {t M : ℕ} (hM : M ≤ 2 ^ t) (x : ZMod (2 ^ t)) :
    x ∈ (range M).image (fun i : ℕ => (i : ZMod (2 ^ t))) ↔ x.val < M := by
  constructor
  · intro hx
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    rw [ZMod.val_cast_of_lt (by have := mem_range.mp hi; omega)]
    exact mem_range.mp hi
  · intro hx
    exact mem_image.mpr ⟨x.val, mem_range.mpr hx, ZMod.natCast_zmod_val x⟩

theorem card_image_range {t M : ℕ} (hM : M ≤ 2 ^ t) :
    ((range M).image (fun i : ℕ => (i : ZMod (2 ^ t)))).card = M := by
  rw [card_image_of_injOn, card_range]
  intro i hi j hj hij
  have hi' := mem_range.mp (mem_coe.mp hi)
  have hj' := mem_range.mp (mem_coe.mp hj)
  have := congrArg ZMod.val hij
  simp only at this
  rwa [ZMod.val_cast_of_lt (by omega), ZMod.val_cast_of_lt (by omega)] at this

/-- **One prefix shell × one suffix shell.** Under the collision bound at `(s, σ)`, the number of
pairs `(P, v)` whose concatenation has least realizer below `2^K` is at most `(1 + ε)` times the
Haar share. -/
theorem split_count_le (b : ℕ → ℕ) (hj1 : 1 ≤ j0) (hjN : j0 < N) {K s σ : ℕ} (ε : ℝ)
    (hε : 0 ≤ ε) (hKs : K ≤ s) (hσK : σ < K)
    (hcoll : (2 : ℝ) ^ (s - σ) * ∑ z : ZMod (2 ^ (s - σ)), prefixCount b j0 σ (s - σ) z ^ 2 ≤
      ((shellP b j0 σ).card : ℝ) ^ 2 *
        (1 + ε ^ 2 * (shellV b N j0 σ (s - σ)).card / 2 ^ (s - σ))) :
    (∑ P ∈ shellP b j0 σ, ∑ v ∈ shellV b N j0 σ (s - σ),
        (if leastRealizer (concat N P v).toInfinite N < 2 ^ K then 1 else 0 : ℝ)) ≤
      (1 + ε) * ∑ _P ∈ shellP b j0 σ, ∑ _v ∈ shellV b N j0 σ (s - σ),
        (2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (s + 1) := by
  set t := s - σ with ht
  set M := 2 ^ (K - σ - 1) with hMdef
  set PS := shellP b j0 σ
  set VS := shellV b N j0 σ t
  set Y := VS.image (alphaV j0 t)
  set I := (range M).image (fun i : ℕ => (i : ZMod (2 ^ t)))
  set Nf := prefixCount b j0 σ t
  have hMt : M ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)
  -- step 1: incidence form
  have hinc : ∀ P ∈ PS, ∀ v ∈ VS,
      (if leastRealizer (concat N P v).toInfinite N < 2 ^ K then 1 else 0 : ℝ) =
        if (alphaV j0 t v - betaP t P).val < M then 1 else 0 := by
    intro P hP v hv
    obtain ⟨hPp, -, hPt⟩ := mem_shellP hj1 hP
    obtain ⟨hvp, hvt⟩ := mem_shellV hjN hv
    have h := lt_pow_iff_incidence P v hj1 hjN hPp hvp (K := K) (by omega)
    rw [hvt, hPt] at h
    simp only [h]
    rfl
  rw [sum_congr rfl fun P hP => sum_congr rfl fun v hv => hinc P hP v hv, sum_comm]
  -- step 2: pass to the image `Y`
  have hinj : Set.InjOn (alphaV j0 t) (↑VS : Set (FiniteValuationWord (N - j0))) :=
    alphaV_injOn VS fun v hv => mem_shellV hjN hv
  have hY : ∑ v ∈ VS, ∑ P ∈ PS, (if (alphaV j0 t v - betaP t P).val < M then 1 else 0 : ℝ) =
      ∑ y ∈ Y, ∑ i ∈ I, Nf (y - i) := by
    rw [sum_image fun x hx y hy h => hinj hx hy h]
    refine sum_congr rfl fun v _ => ?_
    simp only [Nf, prefixCount, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
      Nat.cast_zero]
    rw [sum_comm]
    refine sum_congr rfl fun P _ => ?_
    have hiff : ∀ i : ZMod (2 ^ t), (betaP t P = alphaV j0 t v - i) ↔
        (i = alphaV j0 t v - betaP t P) := fun i => by
      constructor <;> intro h <;> rw [h] <;> ring
    simp only [hiff]
    rw [sum_ite_eq' I (alphaV j0 t v - betaP t P) (fun _ => (1 : ℝ))]
    by_cases hm : (alphaV j0 t v - betaP t P).val < M
    · have hin : alphaV j0 t v - betaP t P ∈ I := (mem_image_range_iff hMt _).mpr hm
      simp [hm, hin]
    · have hn : alphaV j0 t v - betaP t P ∉ I := fun h => hm ((mem_image_range_iff hMt _).mp h)
      simp [hm, hn]
  rw [hY]
  -- step 3: the bilinear bound
  have hsumN : ∑ z, Nf z = (PS.card : ℝ) := sum_prefixCount b j0 σ t
  have hcardG : (Fintype.card (ZMod (2 ^ t)) : ℝ) = 2 ^ t := by
    rw [ZMod.card]; push_cast; ring
  have hμ : 0 ≤ (∑ z, Nf z) / Fintype.card (ZMod (2 ^ t)) := by
    rw [hsumN, hcardG]; positivity
  have hYc : (Y.card : ℝ) = VS.card := by
    rw [card_image_of_injOn hinj]
  have hIc : (I.card : ℝ) = M := by rw [card_image_range hMt]
  have hpos : (0 : ℝ) < 2 ^ t := by positivity
  have hvar : ∑ z, (Nf z - (∑ z, Nf z) / Fintype.card (ZMod (2 ^ t))) ^ 2 ≤
      ε ^ 2 * Y.card * ((∑ z, Nf z) / Fintype.card (ZMod (2 ^ t))) ^ 2 := by
    rw [hsumN, hcardG, hYc]
    set p := (PS.card : ℝ)
    have hexp : ∑ z, (Nf z - p / 2 ^ t) ^ 2 = ∑ z, Nf z ^ 2 - p ^ 2 / 2 ^ t := by
      simp only [sub_sq, sum_add_distrib, sum_sub_distrib, ← sum_mul, ← mul_sum, sum_const,
        card_univ, nsmul_eq_mul]
      rw [hcardG, hsumN]
      field_simp
      ring
    rw [hexp]
    have h1 := hcoll
    have h2 : ∑ z, Nf z ^ 2 ≤ p ^ 2 * (1 + ε ^ 2 * VS.card / 2 ^ t) / 2 ^ t := by
      rw [le_div_iff₀ hpos]; linarith
    calc ∑ z, Nf z ^ 2 - p ^ 2 / 2 ^ t ≤ p ^ 2 * (1 + ε ^ 2 * VS.card / 2 ^ t) / 2 ^ t
          - p ^ 2 / 2 ^ t := by linarith
      _ = ε ^ 2 * VS.card * (p / 2 ^ t) ^ 2 := by field_simp; ring
  have hbil := bilinear_incidence_le Y I Nf ε hε hμ hvar
  refine hbil.trans (le_of_eq ?_)
  rw [hsumN, hcardG, hYc, hIc]
  simp only [sum_const, nsmul_eq_mul]
  have hexpo : (M : ℝ) / 2 ^ t = 2 ^ K * (1 / 2 : ℝ) ^ (s + 1) := by
    have h1 : (M : ℝ) * 2 ^ (s + 1) = 2 ^ K * 2 ^ t := by
      rw [hMdef]; push_cast; rw [← pow_add, ← pow_add]; congr 1; omega
    rw [one_div_pow, mul_one_div, div_eq_div_iff (by positivity) (by positivity)]
    exact h1
  calc (1 + ε) * (VS.card * (M : ℝ) * (PS.card / 2 ^ t))
      = (1 + ε) * (PS.card * (VS.card * ((M : ℝ) / 2 ^ t))) := by ring
    _ = _ := by rw [hexpo]

/-- Prefix shells above the barrier value `b j0` are empty. -/
theorem shellP_eq_empty {b : ℕ → ℕ} (hj1 : 1 ≤ j0) {σ : ℕ} (hσ : b j0 < σ) :
    shellP b j0 σ = ∅ := by
  ext P
  simp only [Finset.notMem_empty, iff_false]
  intro hP
  obtain ⟨-, hbar, ht⟩ := mem_shellP hj1 hP
  have := hbar j0 (Finset.mem_Icc.mpr ⟨hj1, le_rfl⟩)
  rw [← ht] at hσ
  exact absurd this (by unfold FiniteValuationWord.total at hσ; omega)

/-- **One word shell.** Under the prefix collision bound, the post-fresh words of total `s ≥ K`
whose least realizer lies below `2^K` are at most `(1 + ε)` times their Haar share. -/
theorem shell_count_le_of_collision (b : ℕ → ℕ) (hj1 : 1 ≤ j0) (hjN : j0 < N) {K s : ℕ}
    (hbK : b j0 < K) (ε : ℝ) (hε : 0 ≤ ε) (hKs : K ≤ s)
    (hcoll : PrefixCollisionBound b N j0 K ε) :
    (∑ w ∈ (confinedWords N b).filter (fun w => w.total = s),
        (if leastRealizer w.toInfinite N < 2 ^ K then 1 else 0 : ℝ)) ≤
      (1 + ε) * ∑ _w ∈ (confinedWords N b).filter (fun w => w.total = s),
        (2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (s + 1) := by
  rw [sum_shell_eq_sum_split b hj1 hjN s, sum_shell_eq_sum_split b hj1 hjN s, mul_sum]
  refine sum_le_sum fun σ _ => ?_
  by_cases hσK : σ < K
  · exact split_count_le b hj1 hjN ε hε hKs hσK (hcoll s σ hKs hσK)
  · rw [shellP_eq_empty hj1 (by omega)]
    simp

open Classical in
/-- **Prefix collision bound ⇒ least-realizer counting bound** (the hypothesis of
`ResidueDiscrepancy.exceptional_count_le_of_leastRealizerBound`, with `C = 1 + ε`). -/
theorem leastRealizerBound_of_prefixCollision (U N K j0 : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hj1 : 1 ≤ j0) (hjN : j0 < N) (hbK : collatzBarrier U j0 < K)
    (hcoll : PrefixCollisionBound (collatzBarrier U) N j0 K ε) :
    ((((confinedWords N (collatzBarrier U)).filter fun w =>
        K ≤ w.total ∧ leastRealizer w.toInfinite N < 2 ^ K).card : ℕ) : ℝ) ≤
      (1 + ε) * ∑ w ∈ (confinedWords N (collatzBarrier U)).filter (fun w => K ≤ w.total),
        (2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (w.total + 1) := by
  set W := confinedWords N (collatzBarrier U)
  set D := W.filter fun w => K ≤ w.total
  set T := D.image fun w => w.total
  have hmap : ∀ w ∈ D, w.total ∈ T := fun w hw => mem_image_of_mem _ hw
  have hL : ((W.filter fun w => K ≤ w.total ∧ leastRealizer w.toInfinite N < 2 ^ K).card : ℝ) =
      ∑ w ∈ D, (if leastRealizer w.toInfinite N < 2 ^ K then 1 else 0 : ℝ) := by
    rw [sum_boole, filter_filter]
  rw [hL, ← sum_fiberwise_of_maps_to hmap, ← sum_fiberwise_of_maps_to hmap, mul_sum]
  refine sum_le_sum fun s hs => ?_
  obtain ⟨w0, hw0, rfl⟩ := mem_image.mp hs
  have hK : K ≤ w0.total := (mem_filter.mp hw0).2
  have hfib : D.filter (fun w => w.total = w0.total) =
      W.filter fun w => w.total = w0.total := by
    ext w
    simp only [D, mem_filter]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3 ▸ hK⟩, h3⟩
  rw [hfib]
  have hmass : ∑ w ∈ W.filter (fun w => w.total = w0.total),
      (2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (w.total + 1) =
      ∑ _w ∈ W.filter (fun w => w.total = w0.total), (2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (w0.total + 1) :=
    sum_congr rfl fun w hw => by rw [(mem_filter.mp hw).2]
  rw [hmass]
  exact shell_count_le_of_collision _ hj1 hjN hbK ε hε hK hcoll

open Classical in
/-- **The full chain: prefix collision bound ⇒ exceptional exponent.** If the prefix end states
at depth `j0` (with `⌊j0 α + U⌋ < K`, i.e. all prefixes fresh) satisfy the collision bound with
constant `ε`, and `N ≥ A K`, then
`#(E_U ∩ [0, 2^K)) ≤ ((1 + ε) e^{λ* U}/2) · (2^K)^{1 − I₀ A}`. -/
theorem exceptional_count_le_of_prefixCollision (U K j0 : ℕ) {N : ℕ} (A ε : ℝ) (hε : 0 ≤ ε)
    (hj1 : 1 ≤ j0) (hjN : j0 < N) (hbK : collatzBarrier U j0 < K) (hNA : A * K ≤ N)
    (hcoll : PrefixCollisionBound (collatzBarrier U) N j0 K ε) :
    (((range (2 ^ K)).filter fun μ =>
        Odd μ ∧ ∀ M, Confined (U : ℝ) (fun i => a (orbit μ i)) M).card : ℝ) ≤
      (1 + ε) * Real.exp (TaoExternal.lambdaStar * U) / 2 *
        ((2 ^ K : ℕ) : ℝ) ^ (1 - TaoExternal.I0 * A) :=
  ResidueDiscrepancy.exceptional_count_le_of_leastRealizerBound U K (by omega) A (1 + ε)
    (by linarith) hNA (leastRealizerBound_of_prefixCollision U N K j0 ε hε hj1 hjN hbK hcoll)

end Chain

end PrefixCollision
end EOC
