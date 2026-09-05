import EOC.TaoLike.PrefixPartition

/-!
# Restart law alignment (Milestone 10)

Closes Milestone 9's remaining obstruction: `cylinder_window_reindex` (`ResidueTV.lean`) proves
only the *sufficient* direction of its window parametrization (every `r + D*(kmin+j)`, `j < N`,
lies in `[Y,Z)`), not the *exhaustive* direction (every point of the residue class in `[Y,Z)`
is one of these). This file proves a fresh, self-contained exhaustive arithmetic-progression
window lemma (via `Nat.find`, not by extending `cylinder_window_reindex`), then uses it to align
the true harmonic prefix-conditional law with the existing `conditionalRestartLaw`.

This is deterministic arithmetic plus finite harmonic normalization: no `TaoMixingHypothesis`
anywhere in this file.
-/

namespace EOC
namespace TaoExternal

open Finset

/-! ## Part 1: the exhaustive arithmetic-progression window theorem -/

/-- **Exhaustive AP window parametrization.** For a residue class `r mod D` and a window
`[Y,Z)` with `r ≤ Y ≤ Z`, there is an explicit `kmin, N` such that a point `m ∈ [Y,Z)` lies in
the class **iff** it is one of the `N` explicit points `r + D*(kmin+j)`. Proved fresh via
`Nat.find` (least-witness), independent of `cylinder_window_reindex`'s internal construction. -/
theorem modEq_window_exact (r D Y Z : ℕ) (hD : 0 < D) (hYr : r ≤ Y) (_hYZ : Y ≤ Z) :
    ∃ kmin N : ℕ, (∀ j < N, Y ≤ r + D * (kmin + j) ∧ r + D * (kmin + j) < Z) ∧
      ∀ m : ℕ, Y ≤ m → m < Z →
      (m ≡ r [MOD D] ↔ ∃ j < N, m = r + D * (kmin + j)) := by
  classical
  have hex_kmin : ∃ k, Y ≤ r + D * k := ⟨Y, by nlinarith⟩
  set kmin := Nat.find hex_kmin with hkmin_def
  have hkmin_ge : Y ≤ r + D * kmin := Nat.find_spec hex_kmin
  have hkmin_min : ∀ k < kmin, ¬ (Y ≤ r + D * k) := fun k hk => Nat.find_min hex_kmin hk
  have hex_N : ∃ n, Z ≤ r + D * (kmin + n) := ⟨Z, by nlinarith⟩
  set N := Nat.find hex_N with hN_def
  have hN_ge : Z ≤ r + D * (kmin + N) := Nat.find_spec hex_N
  have hN_min : ∀ n < N, ¬ (Z ≤ r + D * (kmin + n)) := fun n hn => Nat.find_min hex_N hn
  have hmem : ∀ j < N, Y ≤ r + D * (kmin + j) ∧ r + D * (kmin + j) < Z := by
    intro j hjN
    have hge : Y ≤ r + D * (kmin + j) := by
      have : D * kmin ≤ D * (kmin + j) := Nat.mul_le_mul_left D (by omega)
      omega
    have hlt : r + D * (kmin + j) < Z := by
      by_contra hge'
      push_neg at hge'
      exact hN_min j hjN hge'
    exact ⟨hge, hlt⟩
  refine ⟨kmin, N, hmem, ?_⟩
  intro m hmY hmZ
  constructor
  · intro hmeq
    have hmr : r ≤ m := le_trans hYr hmY
    obtain ⟨k, hk⟩ : D ∣ (m - r) := (Nat.modEq_iff_dvd' hmr).mp hmeq.symm
    have hmeq2 : m = r + D * k := by omega
    have hkge : kmin ≤ k := by
      by_contra hklt
      push_neg at hklt
      have hnot := hkmin_min k hklt
      apply hnot
      omega
    refine ⟨k - kmin, ?_, ?_⟩
    · by_contra hjge
      push_neg at hjge
      have hmono2 : r + D * (kmin + N) ≤ r + D * k := by
        have hle : kmin + N ≤ k := by omega
        have : D * (kmin + N) ≤ D * k := Nat.mul_le_mul_left D hle
        omega
      omega
    · have hkeq : kmin + (k - kmin) = k := by omega
      rw [hmeq2, hkeq]
  · rintro ⟨j, hjN, hmeq⟩
    rw [hmeq]
    have hle : r ≤ r + D * (kmin + j) := Nat.le_add_right r _
    exact ((Nat.modEq_iff_dvd' hle).mpr ⟨kmin + j, by omega⟩).symm

/-- **Exhaustive AP window parametrization, with an explicit size lower bound on `N`.** Same
`kmin, N` and conclusions as `modEq_window_exact`, plus the extra fact that the window length
`Z - Y` is controlled by `N` from above (`(Z:ℝ) - Y ≤ (N+2)*D`) — the exact size bound
`cylinder_window_reindex` (`ResidueTV.lean`) exposes for its own, separately-constructed
`kmin, N`. Needed so Milestone 10's exhaustively-constructed `kmin, N` can be fed directly into
the `_at_window` theorems built on `cylinder_window_reindex`'s two conclusions. Proved by a
fresh, self-contained `Nat.find` argument (not by reusing `modEq_window_exact` as a black box,
since the bound needs the internal minimality facts `hkmin_min`/`hN_min`, which are not part of
`modEq_window_exact`'s exposed conclusion). -/
theorem modEq_window_exact_with_bound (r D Y Z : ℕ) (hD : 0 < D) (hYr : r ≤ Y) (hYZ : Y ≤ Z) :
    ∃ kmin N : ℕ, (∀ j < N, Y ≤ r + D * (kmin + j) ∧ r + D * (kmin + j) < Z) ∧
      (∀ m : ℕ, Y ≤ m → m < Z →
        (m ≡ r [MOD D] ↔ ∃ j < N, m = r + D * (kmin + j))) ∧
      ((Z : ℝ) - (Y : ℝ) ≤ ((N : ℝ) + 2) * (D : ℝ)) := by
  classical
  have hex_kmin : ∃ k, Y ≤ r + D * k := ⟨Y, by nlinarith⟩
  set kmin := Nat.find hex_kmin with hkmin_def
  have hkmin_ge : Y ≤ r + D * kmin := Nat.find_spec hex_kmin
  have hkmin_min : ∀ k < kmin, ¬ (Y ≤ r + D * k) := fun k hk => Nat.find_min hex_kmin hk
  have hex_N : ∃ n, Z ≤ r + D * (kmin + n) := ⟨Z, by nlinarith⟩
  set N := Nat.find hex_N with hN_def
  have hN_ge : Z ≤ r + D * (kmin + N) := Nat.find_spec hex_N
  have hN_min : ∀ n < N, ¬ (Z ≤ r + D * (kmin + n)) := fun n hn => Nat.find_min hex_N hn
  have hmem : ∀ j < N, Y ≤ r + D * (kmin + j) ∧ r + D * (kmin + j) < Z := by
    intro j hjN
    have hge : Y ≤ r + D * (kmin + j) := by
      have : D * kmin ≤ D * (kmin + j) := Nat.mul_le_mul_left D (by omega)
      omega
    have hlt : r + D * (kmin + j) < Z := by
      by_contra hge'
      push_neg at hge'
      exact hN_min j hjN hge'
    exact ⟨hge, hlt⟩
  have hiff : ∀ m : ℕ, Y ≤ m → m < Z →
      (m ≡ r [MOD D] ↔ ∃ j < N, m = r + D * (kmin + j)) := by
    intro m hmY hmZ
    constructor
    · intro hmeq
      have hmr : r ≤ m := le_trans hYr hmY
      obtain ⟨k, hk⟩ : D ∣ (m - r) := (Nat.modEq_iff_dvd' hmr).mp hmeq.symm
      have hmeq2 : m = r + D * k := by omega
      have hkge : kmin ≤ k := by
        by_contra hklt
        push_neg at hklt
        have hnot := hkmin_min k hklt
        apply hnot
        omega
      refine ⟨k - kmin, ?_, ?_⟩
      · by_contra hjge
        push_neg at hjge
        have hmono2 : r + D * (kmin + N) ≤ r + D * k := by
          have hle : kmin + N ≤ k := by omega
          have : D * (kmin + N) ≤ D * k := Nat.mul_le_mul_left D hle
          omega
        omega
      · have hkeq : kmin + (k - kmin) = k := by omega
        rw [hmeq2, hkeq]
    · rintro ⟨j, hjN, hmeq⟩
      rw [hmeq]
      have hle : r ≤ r + D * (kmin + j) := Nat.le_add_right r _
      exact ((Nat.modEq_iff_dvd' hle).mpr ⟨kmin + j, by omega⟩).symm
  refine ⟨kmin, N, hmem, hiff, ?_⟩
  have hkmin_bound : r + D * kmin < Y + D := by
    rcases Nat.eq_zero_or_pos kmin with hk0 | hkpos
    · rw [hk0]; omega
    · have hkm1 : kmin - 1 < kmin := by omega
      have hlt := hkmin_min (kmin - 1) hkm1
      push_neg at hlt
      have hDeq : D * kmin = D * (kmin - 1) + D := by
        have hks : kmin = (kmin - 1) + 1 := by omega
        calc D * kmin = D * ((kmin - 1) + 1) := by rw [← hks]
          _ = D * (kmin - 1) + D := by ring
      omega
  have hZbound : Z ≤ r + D * kmin + D * N := by
    have hDeq : D * (kmin + N) = D * kmin + D * N := by ring
    omega
  have h1 : (Z : ℝ) ≤ (r : ℝ) + (D : ℝ) * (kmin : ℝ) + (D : ℝ) * (N : ℝ) := by
    exact_mod_cast hZbound
  have h2 : (r : ℝ) + (D : ℝ) * (kmin : ℝ) < (Y : ℝ) + (D : ℝ) := by
    exact_mod_cast hkmin_bound
  nlinarith [h1, h2]

/-- **Uniqueness of the index.** For fixed `r, D > 0, kmin`, the index `j` with
`m = r + D*(kmin+j)` is unique. -/
theorem reindexed_index_unique (r D kmin j1 j2 : ℕ) (hD : 0 < D)
    (heq : r + D * (kmin + j1) = r + D * (kmin + j2)) : j1 = j2 := by
  have hmul : D * (kmin + j1) = D * (kmin + j2) := by omega
  have hsum : kmin + j1 = kmin + j2 := Nat.eq_of_mul_eq_mul_left hD hmul
  omega

/-- **Exhaustive AP window parametrization, with uniqueness.** -/
theorem modEq_window_exact_unique (r D Y Z : ℕ) (hD : 0 < D) (hYr : r ≤ Y) (hYZ : Y ≤ Z) :
    ∃ kmin N : ℕ, ∀ m : ℕ, Y ≤ m → m < Z → m ≡ r [MOD D] →
      ∃! j, j < N ∧ m = r + D * (kmin + j) := by
  obtain ⟨kmin, N, hmem, hiff⟩ := modEq_window_exact r D Y Z hD hYr hYZ
  refine ⟨kmin, N, ?_⟩
  intro m hmY hmZ hmeq
  obtain ⟨j, hjN, hjeq⟩ := (hiff m hmY hmZ).mp hmeq
  refine ⟨j, ⟨hjN, hjeq⟩, ?_⟩
  rintro j' ⟨_, hj'eq⟩
  exact (reindexed_index_unique r D kmin j j' hD (hjeq.symm.trans hj'eq)).symm

/-! ## Part 2: the exhaustive window theorem at the `Realizes` level -/

/-- **Exhaustive prefix-cylinder window parametrization.** Combines `modEq_window_exact` with
`realizes_iff_modEq` (Milestone 9): every `m` in the window realizing the length-`t` word `d`
is exactly one of the `N` explicit points `r + 2^(S d t+1)*(kmin+j)`. This is the converse
Milestone 9 identified as missing. -/
theorem realizes_window_exact (d : ℕ → ℕ) (t r Y Z : ℕ) (hd_pos : ∀ i < t, 1 ≤ d i)
    (hr : Realizes d t r) (hYr : r ≤ Y) (hYZ : Y ≤ Z) :
    ∃ kmin N : ℕ, (∀ j < N, Y ≤ r + 2 ^ (S d t + 1) * (kmin + j)
        ∧ r + 2 ^ (S d t + 1) * (kmin + j) < Z) ∧
      ∀ m, Y ≤ m → m < Z →
      (Realizes d t m ↔ ∃ j < N, m = r + 2 ^ (S d t + 1) * (kmin + j)) := by
  obtain ⟨kmin, N, hmem, hiff⟩ := modEq_window_exact r (2 ^ (S d t + 1)) Y Z (by positivity) hYr hYZ
  refine ⟨kmin, N, hmem, ?_⟩
  intro m hmY hmZ
  rw [realizes_iff_modEq d t r m hd_pos hr]
  constructor
  · rintro ⟨_, hmeq⟩
    exact (hiff m hmY hmZ).mp hmeq
  · intro hex
    have hmeq := (hiff m hmY hmZ).mpr hex
    refine ⟨?_, hmeq⟩
    obtain ⟨j, _, hmeqj⟩ := hex
    rw [hmeqj]
    have hrodd := hr.1
    have h2 : Even (2 ^ (S d t + 1)) := (Nat.even_pow).mpr ⟨even_two, by omega⟩
    exact hrodd.add_even (h2.mul_right _)

/-- **Exhaustive prefix-cylinder window parametrization, with size bound.** Same as
`realizes_window_exact`, plus the extra `(Z:ℝ)-(Y:ℝ) ≤ (N+2)*2^(S d t+1)` fact from
`modEq_window_exact_with_bound`. -/
theorem realizes_window_exact_with_bound (d : ℕ → ℕ) (t r Y Z : ℕ) (hd_pos : ∀ i < t, 1 ≤ d i)
    (hr : Realizes d t r) (hYr : r ≤ Y) (hYZ : Y ≤ Z) :
    ∃ kmin N : ℕ, (∀ j < N, Y ≤ r + 2 ^ (S d t + 1) * (kmin + j)
        ∧ r + 2 ^ (S d t + 1) * (kmin + j) < Z) ∧
      (∀ m, Y ≤ m → m < Z →
        (Realizes d t m ↔ ∃ j < N, m = r + 2 ^ (S d t + 1) * (kmin + j))) ∧
      ((Z : ℝ) - (Y : ℝ) ≤ ((N : ℝ) + 2) * (2 ^ (S d t + 1) : ℝ)) := by
  obtain ⟨kmin, N, hmem, hiff, hNlb⟩ :=
    modEq_window_exact_with_bound r (2 ^ (S d t + 1)) Y Z (by positivity) hYr hYZ
  have hNlb' : (Z : ℝ) - (Y : ℝ) ≤ ((N : ℝ) + 2) * (2 ^ (S d t + 1) : ℝ) := by
    push_cast at hNlb ⊢; linarith [hNlb]
  refine ⟨kmin, N, hmem, ?_, hNlb'⟩
  intro m hmY hmZ
  rw [realizes_iff_modEq d t r m hd_pos hr]
  constructor
  · rintro ⟨_, hmeq⟩
    exact (hiff m hmY hmZ).mp hmeq
  · intro hex
    have hmeq := (hiff m hmY hmZ).mpr hex
    refine ⟨?_, hmeq⟩
    obtain ⟨j, _, hmeqj⟩ := hex
    rw [hmeqj]
    have hrodd := hr.1
    have h2 : Even (2 ^ (S d t + 1)) := (Nat.even_pow).mpr ⟨even_two, by omega⟩
    exact hrodd.add_even (h2.mul_right _)

/-! ## Part 3: the harmonic global weight and its prefix-mass normalization -/

/-- **The harmonic window weight**: `1/m` on odd `m` in `[Y,Z)`, `0` elsewhere. No reusable
harmonic-window weight definition exists in the repo (`ConditionalMixing.lean`/`ResidueTV.lean`
work directly with the raw `1/(r+Dcyl*(kmin+j))` terms inside a `Finset.sum`, never packaging
a standalone global weight function `ℕ → ℝ`), so this is a genuinely new definition, not a
duplicate. -/
noncomputable def harmonicWindowWeight (Y Z : ℕ) (m : ℕ) : ℝ :=
  if Y ≤ m ∧ m < Z ∧ Odd m then 1 / (m : ℝ) else 0

theorem harmonicWindowWeight_nonneg (Y Z m : ℕ) : 0 ≤ harmonicWindowWeight Y Z m := by
  unfold harmonicWindowWeight; split_ifs with h
  · positivity
  · exact le_refl 0

theorem harmonicWindowWeight_supp (Y Z : ℕ) :
    Function.support (harmonicWindowWeight Y Z) ⊆ ↑(range Z) := by
  intro m hm
  by_contra hmni
  apply hm
  unfold harmonicWindowWeight
  rw [if_neg]
  rintro ⟨_, hlt, _⟩
  exact hmni (Finset.mem_range.mpr hlt)

/-- **`Realizes` in terms of `valuationVector` equality.** `Realizes d t m` unfolds
(definitionally, via `valuationVector_apply`) to exactly `Odd m` plus `valuationVector m t`
agreeing pointwise with `d`. -/
theorem realizes_iff_valuationVector_eq (d : ℕ → ℕ) (t m : ℕ) :
    Realizes d t m ↔ Odd m ∧ valuationVector m t = fun i : Fin t => d i.val := by
  unfold Realizes
  constructor
  · rintro ⟨hodd, hval⟩
    exact ⟨hodd, funext (fun i => hval i.val i.isLt)⟩
  · rintro ⟨hodd, heq⟩
    refine ⟨hodd, fun j hj => ?_⟩
    have := congrFun heq ⟨j, hj⟩
    simpa using this

/-- **`Realizes d t m` vs. matching `r`'s prefix vector.** Given a fixed realizer `r`, realizing
`d` is exactly matching `r`'s own `valuationVector` (plus oddness). -/
theorem realizes_iff_valuationVector_eq_of_realizer (d : ℕ → ℕ) (t r m : ℕ) (hr : Realizes d t r) :
    Realizes d t m ↔ (valuationVector m t = valuationVector r t ∧ Odd m) := by
  have hr' := (realizes_iff_valuationVector_eq d t r).mp hr
  rw [realizes_iff_valuationVector_eq d t m, ← hr'.2]
  tauto

open Classical in
/-- **Normalization identity.** The prefix mass of the harmonic window weight, on the prefix
realized by `r`, equals exactly the restart normalizer `W` already used by
`conditional_future_valuation_mixing`/`conditional_future_event_bound` (Milestone 5/7) — via
reindexing along the exhaustive bijection `j ↦ r + 2^(S d t+1)*(kmin+j)`. -/
theorem harmonic_prefixMass_eq_W (d : ℕ → ℕ) (t r Y Z : ℕ) (hd_pos : ∀ i < t, 1 ≤ d i)
    (hr : Realizes d t r) (hYr : r ≤ Y) (hYZ : Y ≤ Z) :
    ∃ kmin N : ℕ, (∀ j < N, Y ≤ r + 2 ^ (S d t + 1) * (kmin + j)
        ∧ r + 2 ^ (S d t + 1) * (kmin + j) < Z) ∧
      (∀ m, Y ≤ m → m < Z →
        (Realizes d t m ↔ ∃ j < N, m = r + 2 ^ (S d t + 1) * (kmin + j))) ∧
      prefixMass (harmonicWindowWeight Y Z) Z t (valuationVector r t)
        = ∑ j ∈ range N, (1 : ℝ) / ((r : ℝ) + (2 ^ (S d t + 1) : ℝ) * ((kmin : ℝ) + j)) := by
  obtain ⟨kmin, N, hmem, hiff⟩ := realizes_window_exact d t r Y Z hd_pos hr hYr hYZ
  refine ⟨kmin, N, hmem, hiff, ?_⟩
  set D := 2 ^ (S d t + 1) with hD_def
  have hDpos : 0 < D := by positivity
  set F : ℕ → ℕ := fun j => r + D * (kmin + j) with hF_def
  have hFinj : Set.InjOn F ↑(range N) := fun j1 _ j2 _ heq =>
    reindexed_index_unique r D kmin j1 j2 hDpos heq
  unfold prefixMass
  have hpt : ∀ j ∈ range Z,
      (if valuationVector j t = valuationVector r t then harmonicWindowWeight Y Z j else 0)
        = (if Realizes d t j ∧ Y ≤ j then (1 : ℝ) / (j : ℝ) else 0) := by
    intro j hjZ
    have hjZ' : j < Z := Finset.mem_range.mp hjZ
    unfold harmonicWindowWeight
    by_cases hR : Realizes d t j ∧ Y ≤ j
    · obtain ⟨hRj, hYj⟩ := hR
      have hveq := (realizes_iff_valuationVector_eq_of_realizer d t r j hr).mp hRj
      rw [if_pos hveq.1, if_pos ⟨hYj, hjZ', hveq.2⟩, if_pos ⟨hRj, hYj⟩]
    · by_cases hveq : valuationVector j t = valuationVector r t
      · rw [if_pos hveq, if_neg hR]
        have hRj_iff : Realizes d t j ↔ Odd j :=
          ⟨fun h => ((realizes_iff_valuationVector_eq_of_realizer d t r j hr).mp h).2,
           fun hodd => (realizes_iff_valuationVector_eq_of_realizer d t r j hr).mpr ⟨hveq, hodd⟩⟩
        by_cases hYj : Y ≤ j
        · have hRj : ¬ Realizes d t j := fun h => hR ⟨h, hYj⟩
          rw [hRj_iff] at hRj
          exact if_neg (fun hcond : Y ≤ j ∧ j < Z ∧ Odd j => hRj hcond.2.2)
        · exact if_neg (fun hcond : Y ≤ j ∧ j < Z ∧ Odd j => hYj hcond.1)
      · rw [if_neg hveq]
        exact (if_neg (fun hcond : Realizes d t j ∧ Y ≤ j => hveq
          ((realizes_iff_valuationVector_eq_of_realizer d t r j hr).mp hcond.1).1)).symm
  rw [Finset.sum_congr rfl hpt, ← Finset.sum_filter]
  have hfilter_eq : (range Z).filter (fun j => Realizes d t j ∧ Y ≤ j) = (range N).image F := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hjZ, hRj, hYj⟩
      obtain ⟨j', hj'N, hFj'⟩ := (hiff j hYj hjZ).mp hRj
      exact ⟨j', hj'N, hFj'.symm⟩
    · rintro ⟨j', hj'N, hFj'⟩
      obtain ⟨hYj', hjZ'⟩ := hmem j' hj'N
      subst hFj'
      exact ⟨hjZ', (hiff (F j') hYj' hjZ').mpr ⟨j', hj'N, rfl⟩, hYj'⟩
  rw [hfilter_eq, Finset.sum_image hFinj]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  simp only [hF_def, hD_def]
  push_cast
  ring

open Classical in
/-- **Normalization identity, with size bound.** Same as `harmonic_prefixMass_eq_W`, plus the
extra `(Z:ℝ)-(Y:ℝ) ≤ (N+2)*2^(S d t+1)` fact from `realizes_window_exact_with_bound` — exactly
the two facts (`hmem`, `hNlb`) the `_at_window` theorems (`ConditionalMixing.lean`,
`ResidueTV.lean`, `ShiftedPersistence.lean`) require of a caller-supplied window, so Milestone
10's own `kmin, N, W` can be fed into them directly without re-deriving a second window via
`cylinder_window_reindex`. -/
theorem harmonic_prefixMass_eq_W_with_bound (d : ℕ → ℕ) (t r Y Z : ℕ) (hd_pos : ∀ i < t, 1 ≤ d i)
    (hr : Realizes d t r) (hYr : r ≤ Y) (hYZ : Y ≤ Z) :
    ∃ kmin N : ℕ, (∀ j < N, Y ≤ r + 2 ^ (S d t + 1) * (kmin + j)
        ∧ r + 2 ^ (S d t + 1) * (kmin + j) < Z) ∧
      (∀ m, Y ≤ m → m < Z →
        (Realizes d t m ↔ ∃ j < N, m = r + 2 ^ (S d t + 1) * (kmin + j))) ∧
      ((Z : ℝ) - (Y : ℝ) ≤ ((N : ℝ) + 2) * (2 ^ (S d t + 1) : ℝ)) ∧
      prefixMass (harmonicWindowWeight Y Z) Z t (valuationVector r t)
        = ∑ j ∈ range N, (1 : ℝ) / ((r : ℝ) + (2 ^ (S d t + 1) : ℝ) * ((kmin : ℝ) + j)) := by
  obtain ⟨kmin, N, hmem, hiff, hNlb⟩ := realizes_window_exact_with_bound d t r Y Z hd_pos hr hYr hYZ
  refine ⟨kmin, N, hmem, hiff, hNlb, ?_⟩
  set D := 2 ^ (S d t + 1) with hD_def
  have hDpos : 0 < D := by positivity
  set F : ℕ → ℕ := fun j => r + D * (kmin + j) with hF_def
  have hFinj : Set.InjOn F ↑(range N) := fun j1 _ j2 _ heq =>
    reindexed_index_unique r D kmin j1 j2 hDpos heq
  unfold prefixMass
  have hpt : ∀ j ∈ range Z,
      (if valuationVector j t = valuationVector r t then harmonicWindowWeight Y Z j else 0)
        = (if Realizes d t j ∧ Y ≤ j then (1 : ℝ) / (j : ℝ) else 0) := by
    intro j hjZ
    have hjZ' : j < Z := Finset.mem_range.mp hjZ
    unfold harmonicWindowWeight
    by_cases hR : Realizes d t j ∧ Y ≤ j
    · obtain ⟨hRj, hYj⟩ := hR
      have hveq := (realizes_iff_valuationVector_eq_of_realizer d t r j hr).mp hRj
      rw [if_pos hveq.1, if_pos ⟨hYj, hjZ', hveq.2⟩, if_pos ⟨hRj, hYj⟩]
    · by_cases hveq : valuationVector j t = valuationVector r t
      · rw [if_pos hveq, if_neg hR]
        have hRj_iff : Realizes d t j ↔ Odd j :=
          ⟨fun h => ((realizes_iff_valuationVector_eq_of_realizer d t r j hr).mp h).2,
           fun hodd => (realizes_iff_valuationVector_eq_of_realizer d t r j hr).mpr ⟨hveq, hodd⟩⟩
        by_cases hYj : Y ≤ j
        · have hRj : ¬ Realizes d t j := fun h => hR ⟨h, hYj⟩
          rw [hRj_iff] at hRj
          exact if_neg (fun hcond : Y ≤ j ∧ j < Z ∧ Odd j => hRj hcond.2.2)
        · exact if_neg (fun hcond : Y ≤ j ∧ j < Z ∧ Odd j => hYj hcond.1)
      · rw [if_neg hveq]
        exact (if_neg (fun hcond : Realizes d t j ∧ Y ≤ j => hveq
          ((realizes_iff_valuationVector_eq_of_realizer d t r j hr).mp hcond.1).1)).symm
  rw [Finset.sum_congr rfl hpt, ← Finset.sum_filter]
  have hfilter_eq : (range Z).filter (fun j => Realizes d t j ∧ Y ≤ j) = (range N).image F := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hjZ, hRj, hYj⟩
      obtain ⟨j', hj'N, hFj'⟩ := (hiff j hYj hjZ).mp hRj
      exact ⟨j', hj'N, hFj'.symm⟩
    · rintro ⟨j', hj'N, hFj'⟩
      obtain ⟨hYj', hjZ'⟩ := hmem j' hj'N
      subst hFj'
      exact ⟨hjZ', (hiff (F j') hYj' hjZ').mpr ⟨j', hj'N, rfl⟩, hYj'⟩
  rw [hfilter_eq, Finset.sum_image hFinj]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  simp only [hF_def, hD_def]
  push_cast
  ring

/-! ## Part 4: central law alignment -/

open Classical in
/-- **Central law alignment (pointwise).** Under the reindexing `j ↦ r + 2^(S d t+1)*(kmin+j)`,
the true harmonic prefix-conditional weight (`prefixConditionalWeight` applied to the harmonic
window weight, at the prefix realized by `r`) is *exactly* `conditionalIndexWeight` — the
weight `conditionalRestartLaw` is built from — with `W` instantiated to the prefix mass
(equal, by `harmonic_prefixMass_eq_W`, to the closed-form normalizer). **EXACT ALIGNMENT**,
not merely comparable or normalized-up-to-a-constant. -/
theorem prefixConditionalWeight_reindex_eq_conditionalIndexWeight
    (d : ℕ → ℕ) (t r Y Z : ℕ) (kmin N : ℕ)
    (hmem : ∀ j < N, Y ≤ r + 2 ^ (S d t + 1) * (kmin + j)
      ∧ r + 2 ^ (S d t + 1) * (kmin + j) < Z)
    (hiff : ∀ m, Y ≤ m → m < Z →
      (Realizes d t m ↔ ∃ j < N, m = r + 2 ^ (S d t + 1) * (kmin + j)))
    (hr : Realizes d t r) :
    ∀ j : ℕ, prefixConditionalWeight (harmonicWindowWeight Y Z) Z t (valuationVector r t)
        (r + 2 ^ (S d t + 1) * (kmin + j))
      = conditionalIndexWeight r (2 ^ (S d t + 1)) kmin N
          (prefixMass (harmonicWindowWeight Y Z) Z t (valuationVector r t)) j := by
  intro j
  set D := 2 ^ (S d t + 1) with hD_def
  have hDpos : 0 < D := by positivity
  have hrealizes_always : Realizes d t (r + D * (kmin + j)) :=
    (cylinder_restart d t r (kmin + j) hr).1
  have hveq : valuationVector (r + D * (kmin + j)) t = valuationVector r t :=
    ((realizes_iff_valuationVector_eq_of_realizer d t r (r + D * (kmin + j)) hr).mp
      hrealizes_always).1
  unfold prefixConditionalWeight conditionalIndexWeight
  rw [if_pos hveq]
  by_cases hjN : j < N
  · rw [if_pos hjN]
    congr 1
    unfold harmonicWindowWeight
    rw [if_pos (show Y ≤ r + D * (kmin + j) ∧ r + D * (kmin + j) < Z ∧ Odd (r + D * (kmin + j))
      from ⟨(hmem j hjN).1, (hmem j hjN).2, hrealizes_always.1⟩)]
    push_cast
    ring
  · rw [if_neg hjN]
    have hout : ¬ (Y ≤ r + D * (kmin + j) ∧ r + D * (kmin + j) < Z) := by
      rintro ⟨hY', hZ'⟩
      obtain ⟨j', hj'N, hj'eq⟩ := (hiff (r + D * (kmin + j)) hY' hZ').mp hrealizes_always
      have hjj' := reindexed_index_unique r D kmin j j' hDpos hj'eq
      omega
    unfold harmonicWindowWeight
    rw [if_neg (fun hcond : Y ≤ r + D * (kmin + j) ∧ r + D * (kmin + j) < Z ∧
        Odd (r + D * (kmin + j)) => hout ⟨hcond.1, hcond.2.1⟩)]
    simp

/-! ## Part 5: the event-level restart law identity -/

open Classical in
/-- **Support characterization.** The true harmonic prefix-conditional weight vanishes at every
seed that is *not* one of the `N` exhaustive AP cylinder points. -/
theorem prefixConditionalWeight_support_reindexed
    (d : ℕ → ℕ) (t r Y Z : ℕ) (kmin N : ℕ)
    (hiff : ∀ m, Y ≤ m → m < Z →
      (Realizes d t m ↔ ∃ j < N, m = r + 2 ^ (S d t + 1) * (kmin + j)))
    (hr : Realizes d t r) :
    ∀ m : ℕ, (¬ ∃ j < N, m = r + 2 ^ (S d t + 1) * (kmin + j)) →
      prefixConditionalWeight (harmonicWindowWeight Y Z) Z t (valuationVector r t) m = 0 := by
  intro m hnotex
  unfold prefixConditionalWeight
  by_cases hveq : valuationVector m t = valuationVector r t
  · rw [if_pos hveq]
    unfold harmonicWindowWeight
    by_cases hodd : Odd m
    · have hRm := (realizes_iff_valuationVector_eq_of_realizer d t r m hr).mpr ⟨hveq, hodd⟩
      have hout : ¬ (Y ≤ m ∧ m < Z) := by
        rintro ⟨hY, hZ⟩
        exact hnotex ((hiff m hY hZ).mp hRm)
      rw [if_neg (fun hcond : Y ≤ m ∧ m < Z ∧ Odd m => hout ⟨hcond.1, hcond.2.1⟩)]
      simp
    · rw [if_neg (fun hcond : Y ≤ m ∧ m < Z ∧ Odd m => hodd hcond.2.2)]
      simp
  · rw [if_neg hveq]
    simp

open Classical in
/-- **Seed-law reindexing identity, fixed-window version.** Same as
`genEventProb_prefixConditional_eq_reindexed`, but the restart-window parameters `kmin, N`
(with `hmem`, `hiff`) are supplied by the caller — e.g. Milestone 10's own
`harmonic_prefixMass_eq_W_with_bound` — instead of derived internally via
`harmonic_prefixMass_eq_W`. Needed so Milestone 11's GOOD-prefix argument can obtain
`kmin, N, hmem, hNlb` ONCE (from `harmonic_prefixMass_eq_W_with_bound`) and reuse the exact
same local constants both here and in the `_at_window` M7 chain — no second, syntactically
distinct existential witness is ever introduced for the same prefix. -/
theorem genEventProb_prefixConditional_eq_reindexed_at_window
    (d : ℕ → ℕ) (t r Y Z : ℕ) (hr : Realizes d t r)
    (kmin N : ℕ)
    (hmem : ∀ j < N, Y ≤ r + 2 ^ (S d t + 1) * (kmin + j)
      ∧ r + 2 ^ (S d t + 1) * (kmin + j) < Z)
    (hiff : ∀ m, Y ≤ m → m < Z →
      (Realizes d t m ↔ ∃ j < N, m = r + 2 ^ (S d t + 1) * (kmin + j))) :
    ∀ E : Set ℕ,
      genEventProb (prefixConditionalWeight (harmonicWindowWeight Y Z) Z t (valuationVector r t)) E
        = genEventProb (conditionalIndexWeight r (2 ^ (S d t + 1)) kmin N
            (prefixMass (harmonicWindowWeight Y Z) Z t (valuationVector r t)))
            ((fun j => r + 2 ^ (S d t + 1) * (kmin + j)) ⁻¹' E) := by
  have hpointwise :=
    prefixConditionalWeight_reindex_eq_conditionalIndexWeight d t r Y Z kmin N hmem hiff hr
  have hsupport := prefixConditionalWeight_support_reindexed d t r Y Z kmin N hiff hr
  intro E
  set D := 2 ^ (S d t + 1) with hD_def
  set W := prefixMass (harmonicWindowWeight Y Z) Z t (valuationVector r t) with hW_def
  set F : ℕ → ℕ := fun j => r + D * (kmin + j) with hF_def
  have hDpos : 0 < D := by positivity
  have hFinj : Function.Injective F := fun j1 j2 heq =>
    reindexed_index_unique r D kmin j1 j2 hDpos heq
  have hw1_supp :
      Function.support
        (prefixConditionalWeight (harmonicWindowWeight Y Z) Z t (valuationVector r t))
        ⊆ ↑((range N).image F) := by
    intro m hm
    by_contra hmni
    apply hm
    apply hsupport
    rintro ⟨j, hjN, hjeq⟩
    apply hmni
    rw [hjeq]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hjN, rfl⟩
  have hw2_supp : Function.support (conditionalIndexWeight r D kmin N W) ⊆ ↑(range N) := by
    intro j hj
    by_contra hjni
    apply hj
    unfold conditionalIndexWeight
    exact if_neg (fun h => hjni (Finset.mem_range.mpr h))
  have hind1_supp : Function.support (Set.indicator E
      (prefixConditionalWeight (harmonicWindowWeight Y Z) Z t (valuationVector r t)))
      ⊆ ↑((range N).image F) :=
    fun m hm => hw1_supp (fun h0 => hm (by simp [Set.indicator, h0]))
  have hind2_supp : Function.support (Set.indicator (F ⁻¹' E) (conditionalIndexWeight r D kmin N W))
      ⊆ ↑(range N) :=
    fun j hj => hw2_supp (fun h0 => hj (by simp [Set.indicator, h0]))
  unfold genEventProb
  rw [tsum_eq_sum' hind1_supp, tsum_eq_sum' hind2_supp,
    Finset.sum_image (fun j1 _ j2 _ heq => hFinj heq)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases hFE : F j ∈ E
  · simp only [Set.indicator, Set.mem_preimage, hFE, if_true]
    exact hpointwise j
  · simp only [Set.indicator, Set.mem_preimage, hFE, if_false]

open Classical in
/-- **Seed-law reindexing identity.** The true harmonic prefix-conditional law, as an event law
on starting seeds, equals `genEventProb (conditionalIndexWeight ...)` pulled back along the
reindexing `j ↦ r + D*(kmin+j)`. -/
theorem genEventProb_prefixConditional_eq_reindexed
    (d : ℕ → ℕ) (t r Y Z : ℕ) (hd_pos : ∀ i < t, 1 ≤ d i)
    (hr : Realizes d t r) (hYr : r ≤ Y) (hYZ : Y ≤ Z) :
    ∃ kmin N : ℕ, ∀ E : Set ℕ,
      genEventProb (prefixConditionalWeight (harmonicWindowWeight Y Z) Z t (valuationVector r t)) E
        = genEventProb (conditionalIndexWeight r (2 ^ (S d t + 1)) kmin N
            (prefixMass (harmonicWindowWeight Y Z) Z t (valuationVector r t)))
            ((fun j => r + 2 ^ (S d t + 1) * (kmin + j)) ⁻¹' E) := by
  obtain ⟨kmin, N, hmem, hiff, _⟩ := harmonic_prefixMass_eq_W d t r Y Z hd_pos hr hYr hYZ
  exact ⟨kmin, N,
    genEventProb_prefixConditional_eq_reindexed_at_window d t r Y Z hr kmin N hmem hiff⟩

/-- **Restart-state law identity, fixed-window version.** Same as
`prefixConditional_restart_eq_conditionalRestartLaw`, with `kmin, N, hmem, hiff` supplied by
the caller instead of derived internally. -/
theorem prefixConditional_restart_eq_conditionalRestartLaw_at_window
    (d : ℕ → ℕ) (t r Y Z : ℕ) (hr : Realizes d t r)
    (kmin N : ℕ)
    (hmem : ∀ j < N, Y ≤ r + 2 ^ (S d t + 1) * (kmin + j)
      ∧ r + 2 ^ (S d t + 1) * (kmin + j) < Z)
    (hiff : ∀ m, Y ≤ m → m < Z →
      (Realizes d t m ↔ ∃ j < N, m = r + 2 ^ (S d t + 1) * (kmin + j))) :
    ∀ E : Set ℕ,
      pushforward (genEventProb (prefixConditionalWeight (harmonicWindowWeight Y Z) Z t
          (valuationVector r t))) (fun m => orbit m t) E
        = conditionalRestartLaw r (2 ^ (S d t + 1)) kmin N
            (prefixMass (harmonicWindowWeight Y Z) Z t (valuationVector r t)) (orbit r t) t E := by
  have hE := genEventProb_prefixConditional_eq_reindexed_at_window d t r Y Z hr kmin N hmem hiff
  intro E
  unfold pushforward
  rw [hE ((fun m => orbit m t) ⁻¹' E)]
  unfold conditionalRestartLaw pushforward
  congr 1
  ext j
  simp only [Set.mem_preimage]
  rw [(cylinder_restart d t r (kmin + j) hr).2]

/-- **Restart-state law identity.** The true harmonic prefix-conditional law, pushed forward
along the restart map `orbit ·t`, is *exactly* `conditionalRestartLaw` — the law Milestone 7 is
built on. -/
theorem prefixConditional_restart_eq_conditionalRestartLaw
    (d : ℕ → ℕ) (t r Y Z : ℕ) (hd_pos : ∀ i < t, 1 ≤ d i)
    (hr : Realizes d t r) (hYr : r ≤ Y) (hYZ : Y ≤ Z) :
    ∃ kmin N : ℕ, ∀ E : Set ℕ,
      pushforward (genEventProb (prefixConditionalWeight (harmonicWindowWeight Y Z) Z t
          (valuationVector r t))) (fun m => orbit m t) E
        = conditionalRestartLaw r (2 ^ (S d t + 1)) kmin N
            (prefixMass (harmonicWindowWeight Y Z) Z t (valuationVector r t)) (orbit r t) t E := by
  obtain ⟨kmin, N, hmem, hiff, _⟩ := harmonic_prefixMass_eq_W d t r Y Z hd_pos hr hYr hYZ
  exact ⟨kmin, N, prefixConditional_restart_eq_conditionalRestartLaw_at_window d t r Y Z hr kmin N
    hmem hiff⟩

/-- **Future valuation corollary, fixed-window version.** Same as
`prefix_conditional_future_eq_restart_future`, with `kmin, N, hmem, hiff` supplied by the
caller instead of derived internally — the exact theorem Milestone 11's GOOD-prefix argument
consumes, fed the SAME `kmin, N, hmem` (with `hNlb`) obtained once from
`harmonic_prefixMass_eq_W_with_bound`, so no second, independently-derived window witness is
ever introduced for the same realized prefix. -/
theorem prefix_conditional_future_eq_restart_future_at_window
    (d : ℕ → ℕ) (t r Y Z n : ℕ) (hr : Realizes d t r)
    (kmin N : ℕ)
    (hmem : ∀ j < N, Y ≤ r + 2 ^ (S d t + 1) * (kmin + j)
      ∧ r + 2 ^ (S d t + 1) * (kmin + j) < Z)
    (hiff : ∀ m, Y ≤ m → m < Z →
      (Realizes d t m ↔ ∃ j < N, m = r + 2 ^ (S d t + 1) * (kmin + j))) :
    ∀ E : Set (Fin n → ℕ),
      pushforward (pushforward (genEventProb (prefixConditionalWeight (harmonicWindowWeight Y Z) Z t
          (valuationVector r t))) (fun m => orbit m t)) (fun x => valuationVector x n) E
        = pushforward (conditionalRestartLaw r (2 ^ (S d t + 1)) kmin N
            (prefixMass (harmonicWindowWeight Y Z) Z t (valuationVector r t)) (orbit r t) t)
            (fun x => valuationVector x n) E := by
  have hstate := prefixConditional_restart_eq_conditionalRestartLaw_at_window d t r Y Z hr kmin N
    hmem hiff
  intro E
  unfold pushforward
  exact hstate ((fun x => valuationVector x n) ⁻¹' E)

/-- **Future valuation corollary.** The exact theorem Milestone 11 should consume: the true
prefix-conditional law's future valuation vector law equals `conditionalRestartLaw`'s. -/
theorem prefix_conditional_future_eq_restart_future
    (d : ℕ → ℕ) (t r Y Z n : ℕ) (hd_pos : ∀ i < t, 1 ≤ d i)
    (hr : Realizes d t r) (hYr : r ≤ Y) (hYZ : Y ≤ Z) :
    ∃ kmin N : ℕ, ∀ E : Set (Fin n → ℕ),
      pushforward (pushforward (genEventProb (prefixConditionalWeight (harmonicWindowWeight Y Z) Z t
          (valuationVector r t))) (fun m => orbit m t)) (fun x => valuationVector x n) E
        = pushforward (conditionalRestartLaw r (2 ^ (S d t + 1)) kmin N
            (prefixMass (harmonicWindowWeight Y Z) Z t (valuationVector r t)) (orbit r t) t)
            (fun x => valuationVector x n) E := by
  obtain ⟨kmin, N, hmem, hiff, _⟩ := harmonic_prefixMass_eq_W d t r Y Z hd_pos hr hYr hYZ
  exact ⟨kmin, N, prefix_conditional_future_eq_restart_future_at_window d t r Y Z n hr kmin N hmem
    hiff⟩

end TaoExternal
end EOC
