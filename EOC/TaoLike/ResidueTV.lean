import EOC.TaoLike.Cylinder
import EOC.TaoLike.HarmonicAP
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Conditional residue total variation (Tao-like EOC program, Milestone 3)

The first finite statistical bridge: conditioned on a realized valuation prefix, the
restarted state inside a Collatz cylinder is quantitatively close to uniform on odd
residue classes modulo `2^Q`, with an explicit finite error of scale `2^(Q+S) / Y`.
-/

namespace EOC

open Finset

/-! ### Oddness of the restarted state -/

/-- The accelerated orbit is odd after at least one step: `orbit m0 t = T (orbit m0 (t-1))`
and `T` always produces an odd cofactor. -/
theorem orbit_odd_of_pos (m0 t : ℕ) (ht : 1 ≤ t) : Odd (orbit m0 t) := by
  have hteq : t = (t - 1) + 1 := by omega
  rw [hteq, orbit_succ]
  exact T_odd _

/-! ### Residue-class reduction under restart -/

/-- **Restart residue reduction.** Fix an odd base value `C` (typically `C = orbit r t`)
and an odd target residue `v`. For `Q ≥ 1`, the restarted-state condition
`C + 2 * 3^t * k ≡ v (mod 2^Q)` is equivalent to a *single* residue condition on `k` modulo
`2^(Q-1)` — one power of `2` less than the naive guess `2^Q`, because the restart map
`2 * 3^t * k` carries a forced factor of `2` while `3^t` is a unit modulo `2^(Q-1)`. -/
theorem restart_residue_iff (C : ℕ) (hCodd : Odd C) (t Q v : ℕ) (hvodd : Odd v) (hQ : 1 ≤ Q) :
    ∃ u_v < 2 ^ (Q - 1), ∀ k : ℕ,
      (C + 2 * 3 ^ t * k) % 2 ^ Q = v % 2 ^ Q ↔ k % 2 ^ (Q - 1) = u_v := by
  set n := 2 ^ (Q - 1) with hndef
  have hn : 0 < n := by positivity
  have : NeZero n := ⟨hn.ne'⟩
  have h2Q : 2 ^ Q = 2 * n := by
    have hQeq : Q = (Q - 1) + 1 := by omega
    rw [hQeq, pow_succ, hndef]
    ring
  have h3cop : Nat.Coprime 3 n := by
    rw [hndef]
    exact Nat.Coprime.pow_right _ (by decide)
  have h3unit : IsUnit (3 : ZMod n) := (ZMod.isUnit_iff_coprime 3 n).mpr h3cop
  have h3tunit : IsUnit ((3 : ZMod n) ^ t) := h3unit.pow t
  obtain ⟨C', hC'⟩ := hCodd
  obtain ⟨v', hv'⟩ := hvodd
  have hred : ∀ k : ℕ, (C + 2 * 3 ^ t * k) ≡ v [MOD 2 * n]
      ↔ (C' + 3 ^ t * k) ≡ v' [MOD n] := by
    intro k
    have hCeq : C + 2 * 3 ^ t * k = 2 * (C' + 3 ^ t * k) + 1 := by rw [hC']; ring
    have hveq : v = 2 * v' + 1 := hv'
    rw [hCeq, hveq]
    constructor
    · intro h
      have h' : 2 * (C' + 3 ^ t * k) ≡ 2 * v' [MOD 2 * n] :=
        Nat.ModEq.add_right_cancel' 1 h
      exact (Nat.ModEq.mul_left_cancel_iff' (two_ne_zero)).mp h'
    · intro h
      have h' : 2 * (C' + 3 ^ t * k) ≡ 2 * v' [MOD 2 * n] := Nat.ModEq.mul_left' 2 h
      exact h'.add_right 1
  obtain ⟨u0, hu0lt, hu0⟩ :
      ∃ u0 < n, ∀ k : ℕ, (C' + 3 ^ t * k) % n = v' % n ↔ k % n = u0 := by
    set ainv : ZMod n := ((h3tunit.unit⁻¹ : (ZMod n)ˣ) : ZMod n) with hainvdef
    refine ⟨(((v' : ZMod n) - (C' : ZMod n)) * ainv).val, ZMod.val_lt _, fun k => ?_⟩
    set u0 : ZMod n := ((v' : ZMod n) - (C' : ZMod n)) * ainv with hu0def
    have hvv : u0.val % n = u0.val := Nat.mod_eq_of_lt (ZMod.val_lt u0)
    have hau : (3 : ZMod n) ^ t * ainv = 1 := by
      have hspec : (↑h3tunit.unit : ZMod n) = (3 : ZMod n) ^ t := h3tunit.unit_spec
      calc (3 : ZMod n) ^ t * ainv
          = (↑h3tunit.unit : ZMod n) * ainv := by rw [hspec]
        _ = (↑h3tunit.unit : ZMod n) * (↑h3tunit.unit⁻¹ : ZMod n) := by rw [hainvdef]
        _ = ↑(h3tunit.unit * h3tunit.unit⁻¹) := by rw [Units.val_mul]
        _ = ↑(1 : (ZMod n)ˣ) := by rw [mul_inv_cancel]
        _ = 1 := Units.val_one
    constructor
    · intro h
      have hmodeq : (C' + 3 ^ t * k) ≡ v' [MOD n] := h
      have hcast : ((C' + 3 ^ t * k : ℕ) : ZMod n) = (v' : ZMod n) :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmodeq
      have heq : (k : ZMod n) = u0 := by
        push_cast at hcast
        rw [hu0def]
        have hk : (3 : ZMod n) ^ t * (k : ZMod n) = (v' : ZMod n) - (C' : ZMod n) := by
          linear_combination hcast
        calc (k : ZMod n) = 1 * (k : ZMod n) := by ring
          _ = ((3 : ZMod n) ^ t * ainv) * (k : ZMod n) := by rw [hau]
          _ = ainv * ((3 : ZMod n) ^ t * (k : ZMod n)) := by ring
          _ = ainv * ((v' : ZMod n) - (C' : ZMod n)) := by rw [hk]
          _ = ((v' : ZMod n) - (C' : ZMod n)) * ainv := by ring
      have hv2 : ((u0.val : ℕ) : ZMod n) = u0 := ZMod.natCast_rightInverse u0
      have hcast2 : (k : ZMod n) = (u0.val : ZMod n) := by rw [hv2, heq]
      have hme : k % n = u0.val % n := (ZMod.natCast_eq_natCast_iff k u0.val n).mp hcast2
      rwa [hvv] at hme
    · intro h
      have hmodeq : k ≡ u0.val [MOD n] := by
        show k % n = u0.val % n
        rw [hvv]; exact h
      have hcast : (k : ZMod n) = (u0.val : ZMod n) :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmodeq
      have hv2 : ((u0.val : ℕ) : ZMod n) = u0 := ZMod.natCast_rightInverse u0
      rw [hv2] at hcast
      have hgoal : ((C' + 3 ^ t * k : ℕ) : ZMod n) = (v' : ZMod n) := by
        push_cast
        rw [hcast, hu0def]
        calc (C' : ZMod n) + (3 : ZMod n) ^ t * (((v' : ZMod n) - (C' : ZMod n)) * ainv)
            = (C' : ZMod n) + ((3 : ZMod n) ^ t * ainv) * ((v' : ZMod n) - (C' : ZMod n)) := by
              ring
          _ = (C' : ZMod n) + 1 * ((v' : ZMod n) - (C' : ZMod n)) := by rw [hau]
          _ = (v' : ZMod n) := by ring
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hgoal
  refine ⟨u0, hu0lt, fun k => ?_⟩
  rw [h2Q]
  constructor
  · intro h
    exact (hu0 k).mp ((hred k).mp h)
  · intro h
    exact (hred k).mpr ((hu0 k).mpr h)

/-! ### Unnormalized harmonic residue discrepancy -/

/-- **Unnormalized harmonic residue discrepancy.** Fix a realized prefix `d` of length
`t ≥ 1` with base seed `r`. Reindex cylinder seeds as `m_{kmin+j} = r + 2^(S d t + 1) *
(kmin + j)` for `j < N`. For any odd target residue `v` modulo `2^Q` (`Q ≥ 1`), the
harmonic mass carried by `{k : orbit m_k t ≡ v (mod 2^Q)}` among the first `N` restarts
differs from `1/2^(Q-1)` of the total harmonic mass by at most `1 / m_{kmin}`. -/
theorem residue_harmonic_mass_discrepancy
    (d : ℕ → ℕ) (t r : ℕ) (h : Realizes d t r) (ht : 1 ≤ t)
    (Q : ℕ) (hQ : 1 ≤ Q) (v : ℕ) (hvodd : Odd v)
    (kmin N : ℕ) :
    |∑ j ∈ range N,
        (if orbit (r + 2 ^ (S d t + 1) * (kmin + j)) t % 2 ^ Q = v % 2 ^ Q
          then (1 : ℝ) / ((r : ℝ) + (2 ^ (S d t + 1) : ℝ) * ((kmin : ℝ) + j)) else 0)
      - (1 / (2 ^ (Q - 1) : ℝ)) *
          ∑ j ∈ range N, (1 : ℝ) / ((r : ℝ) + (2 ^ (S d t + 1) : ℝ) * ((kmin : ℝ) + j))|
      ≤ 1 / ((r : ℝ) + (2 ^ (S d t + 1) : ℝ) * (kmin : ℝ)) := by
  have hrodd : Odd r := h.1
  have hrpos : 0 < r := by obtain ⟨c, hc⟩ := hrodd; omega
  set Dcyl := 2 ^ (S d t + 1) with hDcyldef
  have hCodd : Odd (orbit r t) := orbit_odd_of_pos r t ht
  obtain ⟨u_v, hu_v_lt, hu_v⟩ := restart_residue_iff (orbit r t) hCodd t Q v hvodd hQ
  have horb : ∀ k : ℕ, orbit (r + Dcyl * k) t = orbit r t + 2 * 3 ^ t * k :=
    fun k => (cylinder_restart d t r k h).2
  have hindic : ∀ k : ℕ,
      (orbit (r + Dcyl * k) t % 2 ^ Q = v % 2 ^ Q) ↔ (k % 2 ^ (Q - 1) = u_v % 2 ^ (Q - 1)) := by
    intro k
    rw [horb k, Nat.mod_eq_of_lt hu_v_lt]
    exact hu_v k
  have hA0 : (0 : ℝ) < (r : ℝ) + (Dcyl : ℝ) * (kmin : ℝ) := by positivity
  have hDnn : (0 : ℝ) ≤ (Dcyl : ℝ) := by positivity
  have key := harmonic_ap_discrepancy (2 ^ (Q - 1)) Nat.one_le_two_pow kmin u_v N
    ((r : ℝ) + (Dcyl : ℝ) * (kmin : ℝ)) (Dcyl : ℝ) hA0 hDnn
  have hcongr : ∀ j : ℕ,
      (if (kmin + j) % 2 ^ (Q - 1) = u_v % 2 ^ (Q - 1)
        then (1 : ℝ) / ((r : ℝ) + (Dcyl : ℝ) * (kmin : ℝ) + (Dcyl : ℝ) * (j : ℕ))
        else 0)
      = (if orbit (r + Dcyl * (kmin + j)) t % 2 ^ Q = v % 2 ^ Q
        then (1 : ℝ) / ((r : ℝ) + (Dcyl : ℝ) * ((kmin : ℝ) + j)) else 0) := by
    intro j
    by_cases hc : orbit (r + Dcyl * (kmin + j)) t % 2 ^ Q = v % 2 ^ Q
    · rw [if_pos hc, if_pos ((hindic (kmin + j)).mp hc)]
      push_cast; ring
    · rw [if_neg hc, if_neg (fun hh => hc ((hindic (kmin + j)).mpr hh))]
  have hsum1 : ∑ j ∈ range N,
      (if (kmin + j) % 2 ^ (Q - 1) = u_v % 2 ^ (Q - 1)
        then (1 : ℝ) / ((r : ℝ) + (Dcyl : ℝ) * (kmin : ℝ) + (Dcyl : ℝ) * (j : ℕ)) else 0)
      = ∑ j ∈ range N, (if orbit (r + Dcyl * (kmin + j)) t % 2 ^ Q = v % 2 ^ Q
        then (1 : ℝ) / ((r : ℝ) + (Dcyl : ℝ) * ((kmin : ℝ) + j)) else 0) :=
    Finset.sum_congr rfl (fun j _ => hcongr j)
  have hsum2 : ∑ j ∈ range N, (1 : ℝ) / ((r : ℝ) + (Dcyl : ℝ) * (kmin : ℝ) + (Dcyl : ℝ) * (j : ℕ))
      = ∑ j ∈ range N, (1 : ℝ) / ((r : ℝ) + (Dcyl : ℝ) * ((kmin : ℝ) + j)) :=
    Finset.sum_congr rfl (fun j _ => by push_cast; ring_nf)
  have hM2Q : (1 : ℝ) / ((2 ^ (Q - 1) : ℕ) : ℝ) = 1 / (2 ^ (Q - 1) : ℝ) := by push_cast; ring
  rw [hsum1, hsum2, hM2Q, hDcyldef] at key
  push_cast at key
  exact key

/-! ### Total variation over odd residues (TV convention) -/

/-- The `2^(Q-1)` odd residue classes modulo `2^Q`, `Q ≥ 1`. This is the support of the
uniform target distribution `U(v) = 1/2^(Q-1)`. -/
def oddResidues (Q : ℕ) : Finset ℕ := (range (2 ^ Q)).filter (fun v => v % 2 = 1)

/-- There are exactly `2^(Q-1)` odd residues modulo `2^Q`, for `Q ≥ 1` — an *exact* count
(no discrepancy term), since `2 ∣ 2^Q`. -/
theorem oddResidues_card (Q : ℕ) (hQ : 1 ≤ Q) : (oddResidues Q).card = 2 ^ (Q - 1) := by
  unfold oddResidues
  have hfilter_eq : (range (2 ^ Q)).filter (fun v => v % 2 = 1)
      = (range (2 ^ Q)).filter (fun v : ℕ => v ≡ 1 [MOD 2]) := by
    apply Finset.filter_congr
    intro v _
    simp [Nat.ModEq]
  rw [hfilter_eq, ← Nat.count_eq_card_filter_range, Nat.count_modEq_card (2 ^ Q) (by norm_num) 1]
  have h2Qmod : 2 ^ Q % 2 = 0 := by
    have hdvd : 2 ∣ 2 ^ Q := dvd_pow_self 2 (by omega : Q ≠ 0)
    omega
  have hsplit : 2 ^ Q = 2 ^ (Q - 1) * 2 := by
    have hQeq : Q = (Q - 1) + 1 := by omega
    conv_lhs => rw [hQeq]
    rw [pow_succ]
  rw [h2Qmod]
  simp only [show ¬ (1 % 2 < 0) from by omega, if_false, add_zero]
  rw [hsplit, Nat.mul_div_cancel _ (by norm_num : 0 < 2)]

/-- **Conditional residue total variation (TV convention fixed here).** With
`dTV(P,U) := (1/2) * ∑_{v odd mod 2^Q} |P(v) - U(v)|`, `P(v) := W_v / W` the normalized
conditional harmonic mass on residue class `v` and `U(v) := 1/2^(Q-1)` the uniform
distribution on odd residues, this is the explicit finite TV bound: conditioned on the
realized prefix `d` (length `t ≥ 1`, base seed `r`), the restarted state's residue modulo
`2^Q` is within `2^(Q-1) / (2 * m_{kmin} * W)` of uniform on odd residues, where
`W = ∑_{j<N} 1/m_{kmin+j}` is the total conditional harmonic mass in the window. -/
theorem conditional_residue_tv_explicit
    (d : ℕ → ℕ) (t r : ℕ) (h : Realizes d t r) (ht : 1 ≤ t)
    (Q : ℕ) (hQ : 1 ≤ Q) (kmin N : ℕ)
    (W : ℝ) (hW : 0 < W)
    (hWeq : W = ∑ j ∈ range N, (1 : ℝ) / ((r : ℝ) + (2 ^ (S d t + 1) : ℝ) * ((kmin : ℝ) + j))) :
    (1 / 2 : ℝ) * ∑ v ∈ oddResidues Q,
        |(∑ j ∈ range N,
            (if orbit (r + 2 ^ (S d t + 1) * (kmin + j)) t % 2 ^ Q = v % 2 ^ Q
              then (1 : ℝ) / ((r : ℝ) + (2 ^ (S d t + 1) : ℝ) * ((kmin : ℝ) + j)) else 0)) / W
          - 1 / (2 ^ (Q - 1) : ℝ)|
      ≤ (2 ^ (Q - 1) : ℝ) / (2 * ((r : ℝ) + (2 ^ (S d t + 1) : ℝ) * (kmin : ℝ)) * W) := by
  have hrodd : Odd r := h.1
  have hrpos : 0 < r := by obtain ⟨c, hc⟩ := hrodd; omega
  have hA0 : (0 : ℝ) < (r : ℝ) + (2 ^ (S d t + 1) : ℝ) * (kmin : ℝ) := by positivity
  have hbound : ∀ v ∈ oddResidues Q,
      |(∑ j ∈ range N,
          (if orbit (r + 2 ^ (S d t + 1) * (kmin + j)) t % 2 ^ Q = v % 2 ^ Q
            then (1 : ℝ) / ((r : ℝ) + (2 ^ (S d t + 1) : ℝ) * ((kmin : ℝ) + j)) else 0)) / W
        - 1 / (2 ^ (Q - 1) : ℝ)|
      ≤ 1 / (((r : ℝ) + (2 ^ (S d t + 1) : ℝ) * (kmin : ℝ)) * W) := by
    intro v hv
    have hvodd : Odd v := by
      have := (Finset.mem_filter.mp hv).2
      exact Nat.odd_iff.mpr this
    have hkey := residue_harmonic_mass_discrepancy d t r h ht Q hQ v hvodd kmin N
    rw [← hWeq] at hkey
    have hdiv : |(∑ j ∈ range N,
          (if orbit (r + 2 ^ (S d t + 1) * (kmin + j)) t % 2 ^ Q = v % 2 ^ Q
            then (1 : ℝ) / ((r : ℝ) + (2 ^ (S d t + 1) : ℝ) * ((kmin : ℝ) + j)) else 0)) / W
        - 1 / (2 ^ (Q - 1) : ℝ)|
        = |(∑ j ∈ range N,
            (if orbit (r + 2 ^ (S d t + 1) * (kmin + j)) t % 2 ^ Q = v % 2 ^ Q
              then (1 : ℝ) / ((r : ℝ) + (2 ^ (S d t + 1) : ℝ) * ((kmin : ℝ) + j)) else 0))
          - (1 / (2 ^ (Q - 1) : ℝ)) * W| / W := by
      rw [show (∑ j ∈ range N,
            (if orbit (r + 2 ^ (S d t + 1) * (kmin + j)) t % 2 ^ Q = v % 2 ^ Q
              then (1 : ℝ) / ((r : ℝ) + (2 ^ (S d t + 1) : ℝ) * ((kmin : ℝ) + j)) else 0)) / W
          - 1 / (2 ^ (Q - 1) : ℝ)
          = ((∑ j ∈ range N,
              (if orbit (r + 2 ^ (S d t + 1) * (kmin + j)) t % 2 ^ Q = v % 2 ^ Q
                then (1 : ℝ) / ((r : ℝ) + (2 ^ (S d t + 1) : ℝ) * ((kmin : ℝ) + j)) else 0))
            - (1 / (2 ^ (Q - 1) : ℝ)) * W) / W from by field_simp,
        abs_div, abs_of_pos hW]
    rw [hdiv, show (1:ℝ) / (((r:ℝ) + (2 ^ (S d t + 1) : ℝ) * (kmin:ℝ)) * W)
        = (1 / ((r:ℝ) + (2 ^ (S d t + 1) : ℝ) * (kmin:ℝ))) / W from (div_div 1 _ W).symm]
    gcongr
  calc (1 / 2 : ℝ) * ∑ v ∈ oddResidues Q,
        |(∑ j ∈ range N,
            (if orbit (r + 2 ^ (S d t + 1) * (kmin + j)) t % 2 ^ Q = v % 2 ^ Q
              then (1 : ℝ) / ((r : ℝ) + (2 ^ (S d t + 1) : ℝ) * ((kmin : ℝ) + j)) else 0)) / W
          - 1 / (2 ^ (Q - 1) : ℝ)|
      ≤ (1 / 2 : ℝ) * ∑ _v ∈ oddResidues Q,
          1 / (((r : ℝ) + (2 ^ (S d t + 1) : ℝ) * (kmin : ℝ)) * W) := by
        apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum hbound) (by norm_num)
    _ = (1 / 2 : ℝ) * ((oddResidues Q).card *
          (1 / (((r : ℝ) + (2 ^ (S d t + 1) : ℝ) * (kmin : ℝ)) * W))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (2 ^ (Q - 1) : ℝ) / (2 * ((r : ℝ) + (2 ^ (S d t + 1) : ℝ) * (kmin : ℝ)) * W) := by
        rw [oddResidues_card Q hQ]
        push_cast
        field_simp

/-! ### Cylinder-point count in a window (Part 5) -/

/-- **Cylinder window reindexing.** For a window `Y ≤ m < Z` (with `r ≤ Y ≤ Z`), the
cylinder points `m = r + Dcyl * k` landing in the window are exactly `r + Dcyl*(kmin+j)` for
`j < N`, for an explicit `kmin` and `N` satisfying the explicit lower bound
`Z - Y ≤ (N + 2) * Dcyl`. No asymptotic notation: `N ≥ (Z-Y)/Dcyl - 2` is exact and finite. -/
theorem cylinder_window_reindex (r Dcyl Y Z : ℕ) (hDcyl : 0 < Dcyl) (hYr : r ≤ Y) (hYZ : Y ≤ Z) :
    ∃ kmin N : ℕ,
      (∀ j < N, Y ≤ r + Dcyl * (kmin + j) ∧ r + Dcyl * (kmin + j) < Z) ∧
      (Z : ℝ) - (Y : ℝ) ≤ ((N : ℝ) + 2) * (Dcyl : ℝ) := by
  set kmin := (Y - r + Dcyl - 1) / Dcyl with hkmindef
  have hstep1 : Dcyl * kmin ≤ Y - r + Dcyl - 1 := Nat.mul_div_le (Y - r + Dcyl - 1) Dcyl
  have hdvm : Y - r + Dcyl - 1 = Dcyl * kmin + (Y - r + Dcyl - 1) % Dcyl := by
    rw [hkmindef]; exact (Nat.div_add_mod (Y - r + Dcyl - 1) Dcyl).symm
  have hmodlt : (Y - r + Dcyl - 1) % Dcyl < Dcyl := Nat.mod_lt _ hDcyl
  have hkmin_ge : Y ≤ r + Dcyl * kmin := by omega
  have hkmin_lt : r + Dcyl * kmin < Y + Dcyl := by omega
  set A0 := r + Dcyl * kmin with hA0def
  set N := (Z - A0) / Dcyl with hNdef
  have hdvm2 : Z - A0 = Dcyl * N + (Z - A0) % Dcyl := by
    rw [hNdef]; exact (Nat.div_add_mod (Z - A0) Dcyl).symm
  have hmodlt2 : (Z - A0) % Dcyl < Dcyl := Nat.mod_lt _ hDcyl
  have hcount : ∀ j < N, A0 + Dcyl * j < Z := by
    intro j hj
    by_cases hZA0 : A0 ≤ Z
    · have hjN : j + 1 ≤ N := hj
      have hmulle : Dcyl * (j + 1) ≤ Dcyl * N := Nat.mul_le_mul_left Dcyl hjN
      have hexp : Dcyl * (j + 1) = Dcyl * j + Dcyl := by ring
      omega
    · push_neg at hZA0
      have hZA0eq : Z - A0 = 0 := by omega
      have hN0 : N = 0 := by rw [hNdef, hZA0eq]; simp
      omega
  refine ⟨kmin, N, ?_, ?_⟩
  · intro j hj
    have hc := hcount j hj
    constructor
    · nlinarith [hkmin_ge]
    · nlinarith [hc]
  · have hA0Y : (A0 : ℝ) - (Y : ℝ) < (Dcyl : ℝ) := by
      have : (A0 : ℝ) < (Y : ℝ) + (Dcyl : ℝ) := by exact_mod_cast hkmin_lt
      linarith
    by_cases hZA0 : A0 ≤ Z
    · have hZA0cast : (Z : ℝ) - (A0 : ℝ) = ((Z - A0 : ℕ) : ℝ) := by
        rw [Nat.cast_sub hZA0]
      have hNub : ((Z - A0 : ℕ) : ℝ) < (Dcyl : ℝ) * ((N : ℝ) + 1) := by
        have hnat : Z - A0 < Dcyl * (N + 1) := by
          have hexp : Dcyl * (N + 1) = Dcyl * N + Dcyl := by ring
          omega
        have hcast2 : ((Z - A0 : ℕ) : ℝ) < ((Dcyl * (N + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
        rwa [show ((Dcyl * (N + 1) : ℕ) : ℝ) = (Dcyl : ℝ) * ((N : ℝ) + 1) by
          push_cast; ring] at hcast2
      linarith
    · push_neg at hZA0
      have hZA0' : (Z : ℝ) < (A0 : ℝ) := by exact_mod_cast hZA0
      have hNnn : (0 : ℝ) ≤ (N : ℝ) := by positivity
      nlinarith [hDcyl]

/-! ### Thick-window corollary (Part 10) -/

/-- **Thick-window conditional residue TV.** For a window `Y ≤ m < Y + H` with `H ≥ η * Y`
(`η > 0` an explicit thickness parameter) inside a realized cylinder, the conditional
residue distribution on odd residues modulo `2^Q` is within an explicit, finite bound of
uniform. This is the fixed-ratio-window analogue of `conditional_residue_tv_explicit`,
avoiding real-valued `λ` acting on `ℕ` interval endpoints (`Y ≤ m < λY`) in favour of the
equivalent, Lean-friendlier `H ≥ ηY` parameterization: taking `η := λ - 1` and `H := (λ-1)Y`
recovers exactly the paper's fixed-ratio window `Y ≤ m < λY = Y + H`. The extra hypothesis
`2 * 2^(S d t + 1) < η * Y` ("the window is thick relative to the cylinder spacing") is what
guarantees the window contains at least one cylinder point, i.e. `W > 0`; without some such
hypothesis the intersection can genuinely be empty (Part 13's "empty cylinder intersection"
edge case), so this is stated honestly as a hypothesis rather than derived. -/
theorem thick_window_conditional_residue_tv
    (d : ℕ → ℕ) (t r : ℕ) (h : Realizes d t r) (ht : 1 ≤ t)
    (Q : ℕ) (hQ : 1 ≤ Q) (Y H : ℕ) (hYr : r ≤ Y) (η : ℝ) (hη : 0 < η)
    (hH : η * (Y : ℝ) ≤ (H : ℝ))
    (hthick : 2 * (2 ^ (S d t + 1) : ℝ) < η * (Y : ℝ)) :
    ∃ kmin N : ℕ, ∃ W : ℝ, 0 < W ∧
      W = ∑ j ∈ range N, (1 : ℝ) / ((r : ℝ) + (2 ^ (S d t + 1) : ℝ) * ((kmin : ℝ) + j)) ∧
      (1 / 2 : ℝ) * ∑ v ∈ oddResidues Q,
          |(∑ j ∈ range N,
              (if orbit (r + 2 ^ (S d t + 1) * (kmin + j)) t % 2 ^ Q = v % 2 ^ Q
                then (1 : ℝ) / ((r : ℝ) + (2 ^ (S d t + 1) : ℝ) * ((kmin : ℝ) + j)) else 0)) / W
            - 1 / (2 ^ (Q - 1) : ℝ)|
        ≤ (2 ^ (Q - 1) : ℝ) / (2 * ((r : ℝ) + (2 ^ (S d t + 1) : ℝ) * (kmin : ℝ)) * W) := by
  have hrodd : Odd r := h.1
  have hrpos : 0 < r := by obtain ⟨c, hc⟩ := hrodd; omega
  have hDcylpos : 0 < 2 ^ (S d t + 1) := by positivity
  obtain ⟨kmin, N, hmem, hNlb⟩ :=
    cylinder_window_reindex r (2 ^ (S d t + 1)) Y (Y + H) hDcylpos hYr (Nat.le_add_right Y H)
  have hHDcyl : 2 * (2 ^ (S d t + 1) : ℝ) < (H : ℝ) := lt_of_lt_of_le hthick hH
  set W := ∑ j ∈ range N, (1 : ℝ) / ((r : ℝ) + (2 ^ (S d t + 1) : ℝ) * ((kmin : ℝ) + j)) with hWdef
  have hWpos : 0 < W := by
    rcases Nat.eq_zero_or_pos N with hN0 | hNpos
    · exfalso
      rw [hN0] at hNlb
      push_cast at hNlb
      linarith
    · apply Finset.sum_pos
      · intro j _
        have : (0:ℝ) < (r:ℝ) + (2 ^ (S d t + 1) : ℝ) * ((kmin:ℝ) + j) := by positivity
        positivity
      · exact ⟨0, Finset.mem_range.mpr hNpos⟩
  exact ⟨kmin, N, W, hWpos, hWdef,
    conditional_residue_tv_explicit d t r h ht Q hQ kmin N W hWpos hWdef⟩

end EOC
