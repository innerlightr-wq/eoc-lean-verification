import EOC.ShellwiseChain
import EOC.TwistExpansion
import EOC.PrefixStateFormula
import EOC.SwapCollatz

/-!
# The weighted chain: one analytic hypothesis ⇒ exceptional exponent

Closes the formal glue between `TwistExpansion`, `ShellwiseChain`, `PrefixStateFormula` and
`SwapCollatz`, so that the whole chain rests on a single analytic hypothesis per shell pair.

Prefix data (`P ∈ shellP b j0 σ`, `t` arbitrary, `m = σ+1+t`):
* `yPrime j0 σ t P` — the residue of `3^{−j0}(2^σ − q_{j0}(P))` modulo `2^m`; `yPrime_lt`,
  `yPrime_spec` (`3^{j0} y' ≡ 2^σ − q (mod 2^m)`), `yPrime_mod` (`y' mod 2^(σ+1) = r_P`).
* `topB j0 σ t P = ⌊y'_P / 2^(σ+1)⌋ < 2^t` (`topB_lt`), and **`betaP_eq_neg_topB`**:
  `β_P = −B_P` in `ZMod (2^t)`.
* `sum_sq_fiber_card`, `betaP_eq_iff`, **`sum_sq_prefixCount`**: the prefix collision count
  `∑_z N(z)^2` equals the top-block collision count of the family `y'_P`.

The analytic hypothesis and the chain:
* `WeightedFourier b N j0 s σ ε` (`t = s − σ`):
  `(1 + (σ+1)/2) ∑_{1≤g<2^t} ∑_{k<2^(σ+1)} ‖coef(g + 2^t k)‖ ‖Ψ(g + 2^t k)‖^2
   ≤ ε^2 |P_σ|^2 |V_{σ,s}| / 2^t`, with `Ψ = Psi (shellP b j0 σ) (σ+1) t (yPrime j0 σ t)`.
* `collisionAt_of_weightedFourier` — `WeightedFourier … ε → CollisionAt … ε`.
* **`weighted_phi_decay_implies_exceptional_bound`** — for every `K ≤ s ≤ b N`, `σ < K`: either
  `WeightedFourier` with `ε ≥ 0`, `1 + ε ≤ c s σ`, or `2^(s+1−K) ≤ c s σ`; plus the Haar-weighted
  condition `∑ c · haarShare ≤ C · (Haar mass)`; then
  `#(E_U ∩ [0, 2^K)) ≤ (C e^{λ* U}/2) · (2^K)^{1 − I₀ A}` for `N ≥ A K`.

`Ψ = Φ` and the resonance count:
* `uInv m i = 3^{−(i+1)} mod 2^m`, `cSig m j0 σ = 3^{−j0} 2^σ mod 2^m`;
  `yPrime_zmod`: `y'_P = c_σ − ∑_{i<j0} u_i 2^{S_i(P)}` in `ZMod (2^m)`.
* **`Psi_eq_pathProduct`** — `Ψ(λ) = e(λ c_σ / 2^m) · ∑_P ∏_{i<j0} e(collatzPhase λ m u i S_i(P))`;
  `norm_Psi_eq` (`‖Ψ‖ = ‖Φ‖`); `norm_Psi_le_G` (domination by the swap DP of `SwapBound`).
* `card_filter_dvd_le`, **`card_resonant_le`**: `#{λ < 2^t : 3^k ∣ λ} ≤ 2^t / 3^k + 1`.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace WeightedChain

open Finset CapacityBounds FiniteValuationWord PrefixCollision ShellwiseChain TwistExpansion

variable {j0 : ℕ}

/-- `y'_P ∈ [0, 2^(σ+1+t))`: the residue of `3^{-j0} (2^σ − q_{j0}(P))` modulo `2^(σ+1+t)`. -/
noncomputable def yPrime (j0 σ t : ℕ) (P : FiniteValuationWord j0) : ℕ :=
  ((((3 ^ j0 : ℕ) : ZMod (2 ^ (σ + 1 + t)))⁻¹ *
    (((2 ^ σ : ℕ) : ZMod (2 ^ (σ + 1 + t))) - ((q P.toInfinite j0 : ℕ) : ZMod (2 ^ (σ + 1 + t)))))
    ).val

theorem yPrime_lt (j0 σ t : ℕ) (P : FiniteValuationWord j0) :
    yPrime j0 σ t P < 2 ^ (σ + 1 + t) :=
  ZMod.val_lt _

/-- The defining congruence `3^{j0} y'_P ≡ 2^σ − q (mod 2^(σ+1+t))`. -/
theorem yPrime_spec (j0 σ t : ℕ) (P : FiniteValuationWord j0) :
    (3 : ℤ) ^ j0 * (yPrime j0 σ t P : ℤ) ≡ 2 ^ σ - (q P.toInfinite j0 : ℤ)
      [ZMOD ((2 ^ (σ + 1 + t) : ℕ) : ℤ)] := by
  rw [← ZMod.intCast_eq_intCast_iff]
  have hu : ((3 ^ j0 : ℕ) : ZMod (2 ^ (σ + 1 + t))) *
      ((3 ^ j0 : ℕ) : ZMod (2 ^ (σ + 1 + t)))⁻¹ = 1 :=
    ZMod.coe_mul_inv_eq_one _ (Nat.Coprime.pow j0 _ (by norm_num : Nat.Coprime 3 2))
  push_cast
  rw [yPrime, ZMod.natCast_zmod_val]
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hu ⊢
  rw [← mul_assoc, hu, one_mul]

variable {b : ℕ → ℕ} {σ : ℕ}

theorem pos_of_shellP (hj1 : 1 ≤ j0) {P : FiniteValuationWord j0} (hP : P ∈ shellP b j0 σ) :
    ∀ i < j0, 1 ≤ P.toInfinite i :=
  positive_toInfinite_of_positive (mem_shellP hj1 hP).1

theorem S_of_shellP (hj1 : 1 ≤ j0) {P : FiniteValuationWord j0} (hP : P ∈ shellP b j0 σ) :
    S P.toInfinite j0 = σ := by
  rw [ResidueDiscrepancy.total_eq_S]; exact (mem_shellP hj1 hP).2.2

/-- The carry identity on the prefix shell: `2^σ m_P = 3^{j0} r_P + q`. -/
theorem carry_of_shellP (hj1 : 1 ≤ j0) {P : FiniteValuationWord j0} (hP : P ∈ shellP b j0 σ) :
    2 ^ σ * endState P = 3 ^ j0 * leastRealizer P.toInfinite j0 + q P.toInfinite j0 := by
  have h := PrefixStateFormula.endState_carry (d := P.toInfinite) j0 (pos_of_shellP hj1 hP)
  rwa [S_of_shellP hj1 hP] at h

theorem endState_odd (hj1 : 1 ≤ j0) {P : FiniteValuationWord j0} (hP : P ∈ shellP b j0 σ) :
    Odd (endState P) :=
  odd_orbit (odd_leastRealizer_of_positive (mem_shellP hj1 hP).1) j0

theorem leastRealizer_lt_shellP (hj1 : 1 ≤ j0) {P : FiniteValuationWord j0}
    (hP : P ∈ shellP b j0 σ) : leastRealizer P.toInfinite j0 < 2 ^ (σ + 1) := by
  have h := leastRealizer_lt P.toInfinite j0
  rwa [S_of_shellP hj1 hP] at h

/-- **Low part:** `y'_P mod 2^(σ+1) = r_P`. -/
theorem yPrime_mod (t : ℕ) (hj1 : 1 ≤ j0) {P : FiniteValuationWord j0}
    (hP : P ∈ shellP b j0 σ) :
    yPrime j0 σ t P % 2 ^ (σ + 1) = leastRealizer P.toInfinite j0 := by
  set r := leastRealizer P.toInfinite j0
  set y := yPrime j0 σ t P
  set qq := q P.toInfinite j0
  obtain ⟨k, hk⟩ := endState_odd hj1 hP
  have hc := carry_of_shellP hj1 hP
  -- 2^(σ+1) ∣ 3^j (y − r)
  have h1 : ((2 ^ (σ + 1) : ℕ) : ℤ) ∣ (2 ^ σ - (qq : ℤ)) - (3 : ℤ) ^ j0 * y := by
    have := Int.modEq_iff_dvd.mp (yPrime_spec j0 σ t P)
    exact (Int.natCast_dvd_natCast.mpr (pow_dvd_pow 2 (by omega : σ + 1 ≤ σ + 1 + t))).trans
      this
  have h2 : ((2 ^ (σ + 1) : ℕ) : ℤ) ∣ (3 : ℤ) ^ j0 * r - (2 ^ σ - (qq : ℤ)) := by
    refine ⟨k, ?_⟩
    have hc' : (2 : ℤ) ^ σ * (endState P : ℤ) = 3 ^ j0 * r + qq := by exact_mod_cast hc
    rw [hk] at hc'
    push_cast at hc' ⊢; rw [pow_succ]; linear_combination -hc'
  have h3 : ((2 ^ (σ + 1) : ℕ) : ℤ) ∣ (3 : ℤ) ^ j0 * ((r : ℤ) - y) := by
    have := dvd_add h1 h2
    rw [show (2 ^ σ - (qq : ℤ)) - (3 : ℤ) ^ j0 * y + ((3 : ℤ) ^ j0 * r - (2 ^ σ - (qq : ℤ))) =
      (3 : ℤ) ^ j0 * ((r : ℤ) - y) by ring] at this
    exact this
  have hcop : IsCoprime (((2 ^ (σ + 1) : ℕ) : ℤ)) ((3 : ℤ) ^ j0) := by
    push_cast
    exact IsCoprime.pow (by rw [Int.isCoprime_iff_gcd_eq_one]; decide)
  have h4 : ((2 ^ (σ + 1) : ℕ) : ℤ) ∣ (r : ℤ) - y := hcop.dvd_of_dvd_mul_left h3
  have hmod : (y : ℤ) % ((2 ^ (σ + 1) : ℕ) : ℤ) = (r : ℤ) % ((2 ^ (σ + 1) : ℕ) : ℤ) :=
    (Int.ModEq.symm (Int.modEq_iff_dvd.mpr h4)).symm
  have hr : (r : ℤ) % ((2 ^ (σ + 1) : ℕ) : ℤ) = r :=
    Int.emod_eq_of_lt (by positivity) (by exact_mod_cast leastRealizer_lt_shellP hj1 hP)
  rw [hr] at hmod
  have : ((y % 2 ^ (σ + 1) : ℕ) : ℤ) = (r : ℤ) := by push_cast; exact_mod_cast hmod
  exact_mod_cast this

/-- The top block `B_P = ⌊y'_P / 2^(σ+1)⌋`. -/
noncomputable def topB (j0 σ t : ℕ) (P : FiniteValuationWord j0) : ℕ :=
  yPrime j0 σ t P / 2 ^ (σ + 1)

theorem topB_lt (j0 σ t : ℕ) (P : FiniteValuationWord j0) : topB j0 σ t P < 2 ^ t := by
  unfold topB
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, add_comm t]
  exact yPrime_lt j0 σ t P

/-- **`β_P = −B_P`** in `ZMod (2^t)`. -/
theorem betaP_eq_neg_topB (t : ℕ) (hj1 : 1 ≤ j0) {P : FiniteValuationWord j0}
    (hP : P ∈ shellP b j0 σ) : betaP t P = -((topB j0 σ t P : ℕ) : ZMod (2 ^ t)) := by
  have hmod : yPrime j0 σ t P % 2 ^ (σ + 1) = leastRealizer P.toInfinite j0 := yPrime_mod t hj1 hP
  have hyrB : (yPrime j0 σ t P : ℤ) =
      (leastRealizer P.toInfinite j0 : ℤ) + 2 ^ (σ + 1) * (topB j0 σ t P : ℤ) := by
    have := Nat.mod_add_div (yPrime j0 σ t P) (2 ^ (σ + 1))
    rw [hmod] at this
    unfold topB
    exact_mod_cast this.symm
  have hB : (3 : ℤ) ^ j0 * ((leastRealizer P.toInfinite j0 : ℤ) +
      2 ^ (σ + 1) * (topB j0 σ t P : ℤ)) ≡ 2 ^ σ - (q P.toInfinite j0 : ℤ)
      [ZMOD 2 ^ (σ + t + 1)] := by
    have h := yPrime_spec j0 σ t P
    rw [hyrB, show σ + 1 + t = σ + t + 1 by omega] at h
    push_cast at h
    exact h
  have hm := PrefixStateFormula.endState_int_formula (carry_of_shellP hj1 hP) hB
  obtain ⟨k, hk⟩ := endState_odd hj1 hP
  have hdvd : ((2 ^ t : ℕ) : ℤ) ∣ (3 : ℤ) ^ j0 * (topB j0 σ t P : ℤ) + k := by
    have h1 := Int.modEq_iff_dvd.mp hm.symm
    rw [show ((endState P : ℕ) : ℤ) = 2 * k + 1 by rw [hk]; push_cast; ring,
      show (2 * (k : ℤ) + 1) - (1 - 2 * 3 ^ j0 * (topB j0 σ t P : ℤ)) =
        2 * ((3 : ℤ) ^ j0 * (topB j0 σ t P : ℤ) + k) by ring,
      pow_succ, mul_comm ((2 : ℤ) ^ t) 2] at h1
    push_cast
    exact Int.dvd_of_mul_dvd_mul_left (by norm_num) h1
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (2 ^ t)).mpr hdvd
  push_cast at hz
  have hkm : (endState P - 1) / 2 = k := by omega
  unfold betaP
  rw [hkm]
  have hk' : ((k : ℕ) : ZMod (2 ^ t)) =
      -(((3 ^ j0 : ℕ) : ZMod (2 ^ t)) * ((topB j0 σ t P : ℕ) : ZMod (2 ^ t))) := by
    push_cast; linear_combination hz
  rw [hk', mul_neg, ← mul_assoc, mul_comm (invThree j0 t), three_pow_mul_invThree, one_mul]

/-! ## Collision identification -/

/-- `∑_z #{i : f i = z}^2 = #{(i,j) : f i = f j}` for any finite family. -/
theorem sum_sq_fiber_card {ι α : Type*} [Fintype α] [DecidableEq α] (T : Finset ι) (f : ι → α) :
    ∑ z, (((T.filter fun i => f i = z).card : ℕ) : ℝ) ^ 2 =
      ((((T ×ˢ T).filter fun p => f p.1 = f p.2).card : ℕ) : ℝ) := by
  rw [card_eq_sum_card_fiberwise (f := fun p => f p.1) (t := univ) (fun _ _ => mem_univ _)]
  push_cast
  refine sum_congr rfl fun z _ => ?_
  have hset : ((T ×ˢ T).filter fun p => f p.1 = f p.2).filter (fun p => f p.1 = z) =
      (T.filter fun i => f i = z) ×ˢ (T.filter fun i => f i = z) := by
    ext p
    simp only [mem_filter, mem_product]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩; exact ⟨⟨h1, h4⟩, h2, h3 ▸ h4⟩
    · rintro ⟨⟨h1, h4⟩, h2, h5⟩; exact ⟨⟨⟨h1, h2⟩, h4.trans h5.symm⟩, h4⟩
  rw [hset, card_product]
  push_cast
  ring

/-- On the prefix shell, `β_P = β_Q ↔ B_P = B_Q`. -/
theorem betaP_eq_iff (t : ℕ) (hj1 : 1 ≤ j0) {P Q : FiniteValuationWord j0}
    (hP : P ∈ shellP b j0 σ) (hQ : Q ∈ shellP b j0 σ) :
    betaP t P = betaP t Q ↔ topB j0 σ t P = topB j0 σ t Q := by
  rw [betaP_eq_neg_topB t hj1 hP, betaP_eq_neg_topB t hj1 hQ, neg_inj,
    ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (topB_lt _ _ _ _),
    Nat.mod_eq_of_lt (topB_lt _ _ _ _)]

/-- **Collision identification:** the prefix collision count is the top-block collision count of
the family `y'_P`. -/
theorem sum_sq_prefixCount (t : ℕ) (hj1 : 1 ≤ j0) :
    ∑ z : ZMod (2 ^ t), prefixCount b j0 σ t z ^ 2 =
      (((((shellP b j0 σ) ×ˢ (shellP b j0 σ)).filter fun p =>
        yPrime j0 σ t p.1 / 2 ^ (σ + 1) = yPrime j0 σ t p.2 / 2 ^ (σ + 1)).card : ℕ) : ℝ) := by
  unfold prefixCount
  rw [sum_sq_fiber_card]
  congr 2
  refine filter_congr fun p hp => ?_
  rw [mem_product] at hp
  exact betaP_eq_iff t hj1 hp.1 hp.2

/-! ## The single analytic hypothesis -/

/-- **Weighted Fourier-energy hypothesis** for the pair `(σ, s)`, `t = s − σ`: the twist-weighted
energy of the additive characters of `y'_P` is at most `ε^2 |P_σ|^2 |V_{σ,s}| / 2^t`. -/
def WeightedFourier (b : ℕ → ℕ) (N j0 s σ : ℕ) (ε : ℝ) : Prop :=
  (1 + ((σ + 1 : ℕ) : ℝ) / 2) * ∑ g ∈ Ico 1 (2 ^ (s - σ)), ∑ k ∈ range (2 ^ (σ + 1)),
      ‖coef (σ + 1) (s - σ) (g + 2 ^ (s - σ) * k)‖ *
        ‖Psi (shellP b j0 σ) (σ + 1) (s - σ) (yPrime j0 σ (s - σ)) (g + 2 ^ (s - σ) * k)‖ ^ 2 ≤
    ε ^ 2 * ((shellP b j0 σ).card : ℝ) ^ 2 * (shellV b N j0 σ (s - σ)).card / 2 ^ (s - σ)

/-- **Weighted Fourier bound ⇒ collision bound.** -/
theorem collisionAt_of_weightedFourier {N s : ℕ} {ε : ℝ} (hj1 : 1 ≤ j0)
    (hW : WeightedFourier b N j0 s σ ε) : CollisionAt b N j0 s σ ε := by
  unfold CollisionAt
  rw [sum_sq_prefixCount (s - σ) hj1]
  have hw := collision_le_weighted (shellP b j0 σ) (σ + 1) (s - σ) (yPrime j0 σ (s - σ))
    (fun P _ => yPrime_lt j0 σ (s - σ) P)
  unfold WeightedFourier at hW
  have hpos : (0 : ℝ) < 2 ^ (s - σ) := by positivity
  calc (2 : ℝ) ^ (s - σ) * _ ≤ _ := hw
    _ ≤ ((shellP b j0 σ).card : ℝ) ^ 2 +
        ε ^ 2 * ((shellP b j0 σ).card : ℝ) ^ 2 * (shellV b N j0 σ (s - σ)).card / 2 ^ (s - σ) := by
      linarith
    _ = ((shellP b j0 σ).card : ℝ) ^ 2 *
        (1 + ε ^ 2 * (shellV b N j0 σ (s - σ)).card / 2 ^ (s - σ)) := by ring

open Classical in
/-- **The whole chain with one analytic hypothesis.** For each post-fresh word shell `s` and fresh
prefix shell `σ < K`, either the weighted Fourier bound holds with some `ε ≥ 0`, `1 + ε ≤ c s σ`,
or `c s σ ≥ 2^(s+1−K)` (trivial counting); if the Haar-weighted average of `c` is at most `C`,
then `#(E_U ∩ [0, 2^K)) ≤ (C e^{λ* U}/2) · (2^K)^{1 − I₀ A}` whenever `N ≥ A K`. -/
theorem weighted_phi_decay_implies_exceptional_bound (U K j0 : ℕ) {N : ℕ} (A C : ℝ)
    (c : ℕ → ℕ → ℝ) (hC : 1 ≤ C) (hj1 : 1 ≤ j0) (hjN : j0 < N) (hbK : collatzBarrier U j0 < K)
    (hNA : A * K ≤ N)
    (hpair : ∀ s σ, K ≤ s → σ < K →
      (∃ ε : ℝ, 0 ≤ ε ∧ 1 + ε ≤ c s σ ∧ WeightedFourier (collatzBarrier U) N j0 s σ ε) ∨
        (2 : ℝ) ^ (s + 1 - K) ≤ c s σ)
    (hweight : ∑ s ∈ Icc K (collatzBarrier U N), ∑ σ ∈ range K,
        c s σ * haarShare (collatzBarrier U) N j0 K s σ ≤
      C * ∑ w ∈ (confinedWords N (collatzBarrier U)).filter (fun w => K ≤ w.total),
        (2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (w.total + 1)) :
    (((range (2 ^ K)).filter fun μ =>
        Odd μ ∧ ∀ M, Confined (U : ℝ) (fun i => a (orbit μ i)) M).card : ℝ) ≤
      C * Real.exp (TaoExternal.lambdaStar * U) / 2 *
        ((2 ^ K : ℕ) : ℝ) ^ (1 - TaoExternal.I0 * A) := by
  refine exceptional_count_le_of_shellwise U K j0 A C c hC hj1 hjN hbK hNA ?_ hweight
  intro s σ hKs hσK
  refine incCount_le_of_collision_or_trivial _ hj1 hjN hKs hσK ?_
  rcases hpair s σ hKs hσK with ⟨ε, hε, hc, hW⟩ | h
  · exact Or.inl ⟨ε, hε, hc, collisionAt_of_weightedFourier hj1 hW⟩
  · exact Or.inr h

/-! ## `Ψ = Φ`: the additive characters of `y'_P` are the Collatz path products -/

/-- `u_i = 3^{−(i+1)} mod 2^m` as a natural number. -/
noncomputable def uInv (m i : ℕ) : ℕ := (((3 ^ (i + 1) : ℕ) : ZMod (2 ^ m))⁻¹).val

/-- `c_σ = 3^{−j0} 2^σ mod 2^m` as a natural number. -/
noncomputable def cSig (m j0 σ : ℕ) : ℕ :=
  ((((3 ^ j0 : ℕ) : ZMod (2 ^ m))⁻¹) * ((2 ^ σ : ℕ) : ZMod (2 ^ m))).val

theorem three_pow_mul_inv (m a : ℕ) :
    (3 : ZMod (2 ^ m)) ^ a * ((3 : ZMod (2 ^ m)) ^ a)⁻¹ = 1 := by
  have h := ZMod.coe_mul_inv_eq_one (n := 2 ^ m) (3 ^ a)
    (Nat.Coprime.pow a _ (by norm_num : Nat.Coprime 3 2))
  simp only [Nat.cast_pow, Nat.cast_ofNat] at h
  exact h

/-- In `ZMod (2^m)`: `y'_P = c_σ − ∑_{i<j0} u_i 2^{S_i(P)}` (all `P`, `m = σ+1+t`). -/
theorem yPrime_zmod (σ t : ℕ) (P : FiniteValuationWord j0) :
    ((yPrime j0 σ t P : ℕ) : ZMod (2 ^ (σ + 1 + t))) =
      ((cSig (σ + 1 + t) j0 σ : ℕ) : ZMod (2 ^ (σ + 1 + t))) -
        ∑ i ∈ range j0, ((uInv (σ + 1 + t) i : ℕ) : ZMod (2 ^ (σ + 1 + t))) *
          2 ^ (P.prefixSum i) := by
  have hq : ((q P.toInfinite j0 : ℕ) : ZMod (2 ^ (σ + 1 + t))) =
      ∑ i ∈ range j0, (3 : ZMod (2 ^ (σ + 1 + t))) ^ (j0 - 1 - i) * 2 ^ (P.prefixSum i) := by
    rw [q_eq_C]
    unfold C
    push_cast
    refine sum_congr rfl fun i hi => ?_
    rw [prefixSum_eq_s P (by have := mem_range.mp hi; omega)]
  rw [yPrime, cSig, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  simp only [uInv, ZMod.natCast_zmod_val, Nat.cast_pow, Nat.cast_ofNat]
  rw [hq, mul_sub, mul_sum]
  congr 1
  refine sum_congr rfl fun i hi => ?_
  have hi' := mem_range.mp hi
  have hsplit : (3 : ZMod (2 ^ (σ + 1 + t))) ^ j0 =
      3 ^ (j0 - 1 - i) * 3 ^ (i + 1) := by
    rw [← pow_add]; congr 1; omega
  have hA := three_pow_mul_inv (σ + 1 + t) j0
  have hC := three_pow_mul_inv (σ + 1 + t) (i + 1)
  have key : ((3 : ZMod (2 ^ (σ + 1 + t))) ^ j0)⁻¹ * 3 ^ (j0 - 1 - i) =
      ((3 : ZMod (2 ^ (σ + 1 + t))) ^ (i + 1))⁻¹ := by
    linear_combination (-(((3 : ZMod (2 ^ (σ + 1 + t))) ^ j0)⁻¹ * 3 ^ (j0 - 1 - i))) * hC +
      ((3 : ZMod (2 ^ (σ + 1 + t))) ^ (i + 1))⁻¹ * hA -
      (((3 : ZMod (2 ^ (σ + 1 + t))) ^ (i + 1))⁻¹ * ((3 : ZMod (2 ^ (σ + 1 + t))) ^ j0)⁻¹) *
        hsplit
  rw [← mul_assoc, key]

theorem ee_neg_fract (x : ℝ) : SwapBound.ee (-Int.fract x) = SwapBound.ee (-x) := by
  rw [show -Int.fract x = -x + ((⌊x⌋ : ℤ) : ℝ) by rw [Int.fract]; ring, ee_add, ee_int, mul_one]

theorem prod_ee (s : Finset ℕ) (f : ℕ → ℝ) :
    ∏ i ∈ s, SwapBound.ee (f i) = SwapBound.ee (∑ i ∈ s, f i) := by
  unfold SwapBound.ee
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [mul_sum]

/-- **`Ψ = Φ` (exact).** The twist-expansion characters of the family `y'_P` are, up to a
unimodular factor, the Collatz path products with phases
`−frac(λ u_i 2^{S_i} / 2^m)`, `u_i = 3^{−(i+1)} mod 2^m`, `m = σ+1+t`. -/
theorem Psi_eq_pathProduct (σ t lam : ℕ) :
    Psi (shellP b j0 σ) (σ + 1) t (yPrime j0 σ t) lam =
      SwapBound.ee ((lam : ℝ) * cSig (σ + 1 + t) j0 σ / 2 ^ (σ + 1 + t)) *
        ∑ P ∈ shellP b j0 σ, ∏ i ∈ range j0,
          SwapBound.ee (SwapCollatz.collatzPhase lam (σ + 1 + t) (uInv (σ + 1 + t)) i
            (P.prefixSum i)) := by
  unfold Psi
  rw [mul_sum]
  refine sum_congr rfl fun P _ => ?_
  simp only [SwapCollatz.collatzPhase, ee_neg_fract]
  rw [prod_ee]
  -- the integer relation y' = c − Σ u_i 2^{S_i} + 2^M z
  set M := σ + 1 + t
  have hz := yPrime_zmod (j0 := j0) σ t P
  have hdvd : ((2 ^ M : ℕ) : ℤ) ∣ (yPrime j0 σ t P : ℤ) - ((cSig M j0 σ : ℤ) -
      ∑ i ∈ range j0, (uInv M i : ℤ) * 2 ^ (P.prefixSum i)) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hz]; ring
  obtain ⟨z, hzz⟩ := hdvd
  have hy : (yPrime j0 σ t P : ℝ) = (cSig M j0 σ : ℝ) -
      ∑ i ∈ range j0, (uInv M i : ℝ) * 2 ^ (P.prefixSum i) + 2 ^ M * z := by
    have : (yPrime j0 σ t P : ℤ) = (cSig M j0 σ : ℤ) -
        ∑ i ∈ range j0, (uInv M i : ℤ) * 2 ^ (P.prefixSum i) + 2 ^ M * z := by
      push_cast at hzz; linarith
    exact_mod_cast this
  have hM : (0 : ℝ) < 2 ^ M := by positivity
  rw [← ee_add]
  have hs : ∑ i ∈ range j0, -(((lam * uInv M i * 2 ^ (P.prefixSum i) : ℕ) : ℝ) / 2 ^ M) =
      -((lam : ℝ) * ∑ i ∈ range j0, (uInv M i : ℝ) * 2 ^ (P.prefixSum i)) / 2 ^ M := by
    rw [neg_div, mul_sum, sum_div, ← sum_neg_distrib]
    refine sum_congr rfl fun i _ => ?_
    push_cast
    ring
  have : (lam : ℝ) * (yPrime j0 σ t P : ℝ) / 2 ^ M =
      (lam : ℝ) * cSig M j0 σ / 2 ^ M +
        ∑ i ∈ range j0, -(((lam * uInv M i * 2 ^ (P.prefixSum i) : ℕ) : ℝ) / 2 ^ M) +
          ((lam * z : ℤ) : ℝ) := by
    rw [hs, hy]
    push_cast
    field_simp
    ring
  rw [this, ee_add, ee_int, mul_one]

/-- `‖Ψ‖ = ‖Φ‖`. -/
theorem norm_Psi_eq (σ t lam : ℕ) :
    ‖Psi (shellP b j0 σ) (σ + 1) t (yPrime j0 σ t) lam‖ =
      ‖∑ P ∈ shellP b j0 σ, ∏ i ∈ range j0,
          SwapBound.ee (SwapCollatz.collatzPhase lam (σ + 1 + t) (uInv (σ + 1 + t)) i
            (P.prefixSum i))‖ := by
  rw [Psi_eq_pathProduct, norm_mul, SwapBound.norm_ee, one_mul]

/-- The characteristic sums in the hypothesis are dominated by the swap DP of `SwapBound`. -/
theorem norm_Psi_le_G (σ t lam : ℕ) :
    ‖Psi (shellP b j0 σ) (σ + 1) t (yPrime j0 σ t) lam‖ ≤
      SwapBound.G b (SwapCollatz.collatzPhase lam (σ + 1 + t) (uInv (σ + 1 + t))) σ 0 j0 0 := by
  rw [norm_Psi_eq]
  exact SwapCollatz.norm_sum_shellP_le_G b σ lam (σ + 1 + t) (uInv (σ + 1 + t)) j0

/-! ## Resonance count -/

/-- `#{λ < n : d ∣ λ} ≤ n / d + 1`. -/
theorem card_filter_dvd_le (n d : ℕ) (hd : 0 < d) :
    ((range n).filter fun lam => d ∣ lam).card ≤ n / d + 1 := by
  have hsub : (range n).filter (fun lam => d ∣ lam) ⊆
      (range (n / d + 1)).image fun j => d * j := by
    intro x hx
    obtain ⟨hxn, j, rfl⟩ := by simpa using hx
    refine mem_image.mpr ⟨j, mem_range.mpr ?_, rfl⟩
    have : d * j / d = j := Nat.mul_div_cancel_left j hd
    have h2 : d * j / d ≤ n / d := Nat.div_le_div_right hxn.le
    omega
  exact (card_le_card hsub).trans (card_image_le.trans (by simp))

/-- **Resonance count:** `#{λ < 2^t : 3^k ∣ λ} ≤ 2^t / 3^k + 1`. -/
theorem card_resonant_le (t k : ℕ) :
    ((range (2 ^ t)).filter fun lam => 3 ^ k ∣ lam).card ≤ 2 ^ t / 3 ^ k + 1 :=
  card_filter_dvd_le _ _ (by positivity)

end WeightedChain
end EOC
