import EOC.TransportCollapse
import EOC.BoundedDrift
import EOC.FinitePrefixPacking

/-!
# Prescribed-future matching against the anchor future

For a past prefix `d` of length `j`, the *Transport Deficits* note's matching precision against
an independently prescribed future `e` is `M_j(D_j, e) = v₂(T_j − A_{j,∞}(e))`. Since
`T_j = −3^{−j} μ_j` and `A_{j,∞}(e) = −3^{−j} y(e)` (with `μ_j = anchorState d j` and `y(e)` the
2-adic realizer of `e`; a `ℤ₂` computation that is **not** formalized here),
`M_j(D_j, e) = v₂(y(e) − μ_j)`. A finite prescribed block `e_1, …, e_m` fixes `y(e)` modulo
`2^(S_m(e)+1)` through its least realizer, so the finite, repo-native object is
`v₂(leastRealizer e m − anchorState d j)`.

The **anchor future** is the anchor state's own valuation word, `anchorWord d j`.

Main results:

* `prescribed_matching_split` — if the block `e` (length `m`) first differs from the anchor word at
  `k < m`, then `v₂(leastRealizer e m − μ_j) = S_k(e) + min (e⋆ k) (e k)`: prescribed matching is
  the split depth between `e` and the anchor future. No parity hypothesis (if `μ_j` is even, the
  anchor word starts with `0` and the value is `0`).
* `prescribed_full_match_iff` — for odd `μ_j`, the block certifies the maximal detectable precision
  `S_m(e) + 1` iff it coincides with the anchor word on all `m` digits.
* `confined_prescribed_matching_le` — **forced-divergence bound**: if the block is `c`-confined and
  the anchor word already violates `c`-confinement at step `L + 1 ≤ m`, the prescribed matching is
  at most `c + (L + 1)·log₂3`.
* `anchor_exits_corridor` / `corridor_prescribed_diverges` — **unconditional**: for odd `μ_j`, the
  anchor word leaves every two-sided drift corridor, so no corridor-constrained prescribed future
  can follow it forever (from `leastRealizer_unbounded_of_two_sided_drift`).
* `shadow_injective_floor_bound` — **quantitative**: a prescribed future with drift floor `−g` that
  follows the anchor word for `2^L` digits along an injective anchor window forces
  `2^(2(L+1)) ≤ 2^g · μ_j · 3^(L+1)` (from `finite_prefix_injective_drift_depth_power_bound`).

None of this proves EOC, `CriticalCrossing`, or the Collatz conjecture.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace PrescribedMatching

open PairValuation SuffixTransport TransportCollapse

/-- The anchor future `e⋆(D_j)`: the valuation word of the anchor state `μ_j`. -/
noncomputable def anchorWord (d : ℕ → ℕ) (j : ℕ) : ℕ → ℕ := fun i => a (orbit (anchorState d j) i)

private theorem R_eq_of_agree {d e : ℕ → ℕ} {t : ℕ} (h : ∀ i < t, d i = e i) :
    R d t = R e t := by
  unfold R
  rw [s_eq_of_prefix_agree h]

/-! ## Prescribed matching is split depth against the anchor future -/

/-- **Prescribed matching = split depth.** A positive block `e` of length `m` whose first
disagreement with the anchor word is at `k < m` satisfies
`v₂(leastRealizer e m − μ_j) = S_k(e) + min (e⋆ k) (e k)`. -/
theorem prescribed_matching_split (d e : ℕ → ℕ) (j m k : ℕ) (hk : k < m)
    (he : ∀ i < m, 1 ≤ e i)
    (hagree : ∀ i < k, anchorWord d j i = e i) (hne : anchorWord d j k ≠ e k) :
    padicValInt 2 ((leastRealizer e m : ℤ) - anchorState d j)
      = S e k + min (anchorWord d j k) (e k) := by
  have hr := leastRealizer_realizes_all e m he
  have hag' : ∀ i < k, a (orbit (anchorState d j) i) = a (orbit (leastRealizer e m) i) := by
    intro i hi
    rw [hr.2 i (by omega)]
    exact hagree i hi
  have hne' : a (orbit (anchorState d j) k) ≠ a (orbit (leastRealizer e m) k) := by
    rw [hr.2 k hk]
    exact hne
  have h := orbit_pair_valuation (anchorState d j) (leastRealizer e m) k hag' hne'
  rw [h, hr.2 k hk]
  change s (anchorWord d j) k + min (anchorWord d j k) (e k) = S e k + min (anchorWord d j k) (e k)
  rw [s_eq_of_prefix_agree hagree]
  rfl

/-- **Full-block detectability.** For odd `μ_j`, a positive block `e` of length `m` satisfies
`leastRealizer e m ≡ μ_j (mod 2^(S_m(e)+1))` iff it equals the anchor word on all `m` digits. -/
theorem prescribed_full_match_iff (d e : ℕ → ℕ) (j m : ℕ) (he : ∀ i < m, 1 ≤ e i)
    (hodd : Odd (anchorState d j)) :
    leastRealizer e m ≡ anchorState d j [MOD 2 ^ (S e m + 1)]
      ↔ ∀ i < m, anchorWord d j i = e i := by
  constructor
  · intro hmod
    have hcong : 3 ^ m * anchorState d j + q e m ≡ 2 ^ S e m [MOD 2 ^ (S e m + 1)] :=
      ((hmod.symm.mul_left (3 ^ m)).add_right (q e m)).trans (leastRealizer_modEq e m)
    have hreal := (realizerCongruence e m (anchorState d j) hodd he).mpr hcong
    exact fun i hi => hreal.2 i hi
  · intro hag
    have hreal : Realizes e m (anchorState d j) := ⟨hodd, fun i hi => hag i hi⟩
    exact (modEq_leastRealizer_of_realizes hreal).symm

/-! ## Confined prescribed futures: forced divergence -/

/-- **Forced-divergence bound for confined prescribed futures.** If the positive block `e`
(length `m`) is `c`-confined and the anchor word violates `c`-confinement at step `L + 1 ≤ m`,
then `v₂(leastRealizer e m − μ_j) ≤ c + (L + 1)·log₂3`. -/
theorem confined_prescribed_matching_le (d e : ℕ → ℕ) (j m L : ℕ) (c : ℝ) (hLm : L + 1 ≤ m)
    (he : ∀ i < m, 1 ≤ e i) (hconf : Confined c e m)
    (hviol : c < R (anchorWord d j) (L + 1)) :
    ((padicValInt 2 ((leastRealizer e m : ℤ) - anchorState d j) : ℕ) : ℝ)
      ≤ c + ((L + 1 : ℕ) : ℝ) * alpha := by
  classical
  have hex : ∃ i, anchorWord d j i ≠ e i ∧ i < L + 1 := by
    by_contra hno
    push Not at hno
    have hag : ∀ i < L + 1, anchorWord d j i = e i := by
      intro i hi
      by_contra hne
      exact absurd (hno i hne) (by omega)
    have := hconf (L + 1) hLm
    rw [← R_eq_of_agree hag] at this
    linarith
  set k := Nat.find hex with hkdef
  have hkspec := Nat.find_spec hex
  have hkmin : ∀ i < k, anchorWord d j i = e i := by
    intro i hi
    by_contra hne
    exact Nat.find_min hex hi ⟨hne, by omega⟩
  have hsplit := prescribed_matching_split d e j m k (by omega) he hkmin hkspec.1
  rw [hsplit]
  have hmin : S e k + min (anchorWord d j k) (e k) ≤ s e (k + 1) := by
    rw [s_succ]
    have := min_le_right (anchorWord d j k) (e k)
    unfold S
    omega
  have hRk := hconf (k + 1) (by omega)
  unfold R at hRk
  have hα : 0 < alpha := lt_trans one_pos one_lt_alpha
  have hkL : ((k + 1 : ℕ) : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : k + 1 ≤ L + 1)
  calc ((S e k + min (anchorWord d j k) (e k) : ℕ) : ℝ)
      ≤ (s e (k + 1) : ℝ) := by exact_mod_cast hmin
    _ ≤ c + ((k + 1 : ℕ) : ℝ) * alpha := by linarith
    _ ≤ c + ((L + 1 : ℕ) : ℝ) * alpha := by nlinarith

/-! ## Two-sided corridors: unconditional forced divergence -/

/-- **The anchor future leaves every two-sided drift corridor.** For odd `μ_j`, no bounds
`−G ≤ R_N ≤ c` can hold for every `N` along the anchor word. -/
theorem anchor_exits_corridor (d : ℕ → ℕ) (j : ℕ) (hodd : Odd (anchorState d j)) (c G : ℝ) :
    ¬ (∀ N, R (anchorWord d j) N ≤ c ∧ -G ≤ R (anchorWord d j) N) := by
  intro h
  have hpos : ∀ i, 1 ≤ anchorWord d j i := hd_pos_of_orbit hodd
  obtain ⟨N, hN⟩ := leastRealizer_unbounded_of_two_sided_drift c G (anchorWord d j) hpos
    (fun N => (h N).1) (fun N => (h N).2) (anchorState d j)
  have hreal : Realizes (anchorWord d j) N (anchorState d j) := ⟨hodd, fun i _ => rfl⟩
  have hle : leastRealizer (anchorWord d j) N ≤ anchorState d j := by
    rw [← mod_eq_leastRealizer_of_realizes hreal]
    exact Nat.mod_le _ _
  omega

/-- No prescribed future confined to a two-sided corridor can agree with the anchor future at
every digit. -/
theorem corridor_prescribed_diverges (d e : ℕ → ℕ) (j : ℕ) (hodd : Odd (anchorState d j))
    (c G : ℝ) (he : ∀ N, R e N ≤ c ∧ -G ≤ R e N) :
    ∃ i, anchorWord d j i ≠ e i := by
  by_contra hno
  push Not at hno
  apply anchor_exits_corridor d j hodd c G
  intro N
  rw [R_eq_of_agree (fun i _ => hno i)]
  exact he N

/-! ## Quantitative shadowing bound on injective anchor windows -/

/-- A prescribed future with drift floor `−g` that follows the anchor word for `2^L` digits, along
an anchor orbit that is injective on `[0, 2^L]`, forces `2^(2(L+1)) ≤ 2^g · μ_j · 3^(L+1)`. -/
theorem shadow_injective_floor_bound (d e : ℕ → ℕ) (j L g : ℕ) (hL : 1 ≤ L)
    (hodd : Odd (anchorState d j))
    (hagree : ∀ i < 2 ^ L, anchorWord d j i = e i)
    (hinj : ∀ i ≤ 2 ^ L, ∀ i' ≤ 2 ^ L,
      orbit (anchorState d j) i = orbit (anchorState d j) i' → i = i')
    (hlow : ∀ t ≤ 2 ^ L, -((g : ℝ)) ≤ R e t) :
    2 ^ (2 * (L + 1)) ≤ 2 ^ g * anchorState d j * 3 ^ (L + 1) := by
  apply finite_prefix_injective_drift_depth_power_bound (anchorState d j) L g hL hodd hinj
  intro t ht
  have h := hlow t ht
  rw [← R_eq_of_agree (fun i hi => hagree i (by omega))] at h
  exact h

end PrescribedMatching
end EOC
