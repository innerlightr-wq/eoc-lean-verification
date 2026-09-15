import EOC.WeightedChain
import EOC.FirstDivergence

/-!
# Dyadic-shell decomposition of the `WeightedFourier` sum

The analytic hypothesis `WeightedChain.WeightedFourier` is a double sum over the fibres
`λ = g + 2^t k` (`1 ≤ g < 2^t`, `k < 2^r`, `r = σ+1`).  This file rewrites it as a sum over
frequency shells and gives a sufficient condition in terms of per-shell averages.

* `sum_fibre_eq_sum_nondvd` — the fibre double sum is the sum over all
  `λ ∈ [1, 2^(r+t))` with `2^t ∤ λ`.
* `sum_Ico_one_two_pow` — `[1, 2^n)` splits into the dyadic bit-length shells `[2^u, 2^(u+1))`.
* `sum_fibre_eq_sum_shells` — the fibre double sum in bit-length shell form;
  `weightedFourier_lhs_shells` — the `WeightedFourier` left-hand side in that form.
* Centered shells: `cdist M λ = min λ (M − λ)`, `cshell r t u` = the `λ` with `2^t ∤ λ` whose
  centered distance has bit length `u`; `sum_nondvd_eq_sum_cshell` (decomposition),
  `mem_cshell_bounds` (`2^u ≤ cdist < 2^(u+1)`), `card_cshell_le` (`#cshell ≤ 2^(u+1)`).
* `norm_coef_le_cshell` — on the centered shell `u`: `‖coef r t λ‖ ≤ 2^t / (2 · 2^u)`.
* `weighted_sum_le_of_shell_averages` — if every centered shell has
  `∑_{λ ∈ shell} F λ ≤ #shell · a_u`, then `∑_g ∑_k ‖coef‖ F ≤ 2^t ∑_u a_u`
  (each shell contributes at most `2^t a_u`).
* **`weightedFourier_of_shell_averages`** — `WeightedFourier b N j0 s σ ε` follows from
  per-shell averages `∑_{λ ∈ shell_u} ‖Ψ λ‖^2 ≤ #shell_u · a_u · |P_σ|^2` together with
  `(1 + (σ+1)/2) · 2^t · ∑_u a_u ≤ ε^2 |V_{σ,s}| / 2^t`.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace ShellDecomposition

open Finset TwistExpansion PrefixCollision WeightedChain

/-! ## Fibre sum = sum over non-multiples of `2^t` -/

theorem sum_fibre_eq_sum_nondvd {M : Type*} [AddCommMonoid M] (r t : ℕ) (F : ℕ → M) :
    ∑ g ∈ Ico 1 (2 ^ t), ∑ k ∈ range (2 ^ r), F (g + 2 ^ t * k) =
      ∑ lam ∈ (Ico 1 (2 ^ (r + t))).filter (fun lam => ¬ 2 ^ t ∣ lam), F lam := by
  have ht : 0 < 2 ^ t := by positivity
  rw [← sum_product']
  refine sum_nbij' (fun p => p.1 + 2 ^ t * p.2) (fun lam => (lam % 2 ^ t, lam / 2 ^ t))
    ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · rintro ⟨g, k⟩ hp
    simp only [mem_product, mem_Ico, mem_range] at hp
    simp only [mem_filter, mem_Ico]
    refine ⟨⟨by omega, ?_⟩, ?_⟩
    · have h1 : k + 1 ≤ 2 ^ r := hp.2
      have h2 : 2 ^ t * (k + 1) ≤ 2 ^ t * 2 ^ r := Nat.mul_le_mul_left _ h1
      rw [pow_add]; nlinarith [hp.1.2]
    · intro hd
      have : 2 ^ t ∣ g := (Nat.dvd_add_right (dvd_mul_right _ _)).mp (by
        rwa [add_comm] at hd)
      have := Nat.eq_zero_of_dvd_of_lt this hp.1.2
      omega
  · intro lam hl
    simp only [mem_filter, mem_Ico] at hl
    simp only [mem_product, mem_Ico, mem_range]
    refine ⟨⟨?_, Nat.mod_lt _ ht⟩, ?_⟩
    · by_contra h0
      exact hl.2 (Nat.dvd_of_mod_eq_zero (by omega))
    · rw [Nat.div_lt_iff_lt_mul ht, ← pow_add]; exact hl.1.2
  · rintro ⟨g, k⟩ hp
    simp only [mem_product, mem_Ico, mem_range] at hp
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp.1.2]
    · rw [Nat.add_mul_div_left _ _ ht, Nat.div_eq_of_lt hp.1.2, zero_add]
  · intro lam _
    exact Nat.mod_add_div lam (2 ^ t)

/-! ## Bit-length shells -/

theorem sum_Ico_one_two_pow {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ∑ lam ∈ Ico 1 (2 ^ n), f lam = ∑ u ∈ range n, ∑ lam ∈ Ico (2 ^ u) (2 ^ (u + 1)), f lam := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [sum_range_succ, ← ih, sum_Ico_consecutive f Nat.one_le_two_pow
        (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ n))]

/-- **Bit-length shell form** of the fibre double sum. -/
theorem sum_fibre_eq_sum_shells {M : Type*} [AddCommMonoid M] (r t : ℕ) (F : ℕ → M) :
    ∑ g ∈ Ico 1 (2 ^ t), ∑ k ∈ range (2 ^ r), F (g + 2 ^ t * k) =
      ∑ u ∈ range (r + t),
        ∑ lam ∈ (Ico (2 ^ u) (2 ^ (u + 1))).filter (fun lam => ¬ 2 ^ t ∣ lam), F lam := by
  classical
  rw [sum_fibre_eq_sum_nondvd, sum_filter, sum_Ico_one_two_pow]
  exact sum_congr rfl fun u _ => (sum_filter _ _).symm

/-- The `WeightedFourier` left-hand side (without the prefactor `1 + (σ+1)/2`) in bit-length
shell form. -/
theorem weightedFourier_lhs_shells (b : ℕ → ℕ) (j0 s σ : ℕ) :
    ∑ g ∈ Ico 1 (2 ^ (s - σ)), ∑ k ∈ range (2 ^ (σ + 1)),
      ‖coef (σ + 1) (s - σ) (g + 2 ^ (s - σ) * k)‖ *
        ‖Psi (shellP b j0 σ) (σ + 1) (s - σ) (yPrime j0 σ (s - σ)) (g + 2 ^ (s - σ) * k)‖ ^ 2 =
    ∑ u ∈ range (σ + 1 + (s - σ)),
      ∑ lam ∈ (Ico (2 ^ u) (2 ^ (u + 1))).filter (fun lam => ¬ 2 ^ (s - σ) ∣ lam),
        ‖coef (σ + 1) (s - σ) lam‖ *
          ‖Psi (shellP b j0 σ) (σ + 1) (s - σ) (yPrime j0 σ (s - σ)) lam‖ ^ 2 :=
  sum_fibre_eq_sum_shells (σ + 1) (s - σ)
    (fun lam => ‖coef (σ + 1) (s - σ) lam‖ *
      ‖Psi (shellP b j0 σ) (σ + 1) (s - σ) (yPrime j0 σ (s - σ)) lam‖ ^ 2)

/-! ## Centered shells -/

/-- Centered distance of `λ` from `0` in `ℤ/M`: `min λ (M − λ)`. -/
def cdist (M lam : ℕ) : ℕ := min lam (M - lam)

/-- The non-multiples of `2^t` in `[1, 2^(r+t))`. -/
def nondvd (r t : ℕ) : Finset ℕ := (Ico 1 (2 ^ (r + t))).filter (fun lam => ¬ 2 ^ t ∣ lam)

/-- Centered shell `u`: the `λ ∈ nondvd r t` whose centered distance has bit length `u`. -/
def cshell (r t u : ℕ) : Finset ℕ :=
  (nondvd r t).filter (fun lam => Nat.log 2 (cdist (2 ^ (r + t)) lam) = u)

theorem cdist_pos {r t lam : ℕ} (h : lam ∈ nondvd r t) : 0 < cdist (2 ^ (r + t)) lam := by
  simp only [nondvd, mem_filter, mem_Ico] at h
  unfold cdist; omega

theorem cdist_lt {r t lam : ℕ} (h : lam ∈ nondvd r t) : cdist (2 ^ (r + t)) lam < 2 ^ (r + t) := by
  simp only [nondvd, mem_filter, mem_Ico] at h
  unfold cdist; omega

/-- **Centered-shell decomposition.** -/
theorem sum_nondvd_eq_sum_cshell {M : Type*} [AddCommMonoid M] (r t : ℕ) (F : ℕ → M) :
    ∑ lam ∈ nondvd r t, F lam = ∑ u ∈ range (r + t), ∑ lam ∈ cshell r t u, F lam := by
  have hmap : ∀ lam ∈ nondvd r t, Nat.log 2 (cdist (2 ^ (r + t)) lam) ∈ range (r + t) := by
    intro lam h
    exact mem_range.mpr (Nat.log_lt_of_lt_pow (cdist_pos h).ne' (cdist_lt h))
  exact (sum_fiberwise_of_maps_to hmap F).symm

theorem mem_cshell_bounds {r t u lam : ℕ} (h : lam ∈ cshell r t u) :
    2 ^ u ≤ cdist (2 ^ (r + t)) lam ∧ cdist (2 ^ (r + t)) lam < 2 ^ (u + 1) := by
  simp only [cshell, mem_filter] at h
  obtain ⟨hn, hlog⟩ := h
  have hpos := cdist_pos hn
  refine ⟨?_, ?_⟩
  · have := Nat.pow_log_le_self 2 hpos.ne'
    rwa [hlog] at this
  · have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (cdist (2 ^ (r + t)) lam)
    rwa [hlog] at this

theorem card_cshell_le (r t u : ℕ) : (cshell r t u).card ≤ 2 ^ (u + 1) := by
  set M := 2 ^ (r + t)
  have hsub : cshell r t u ⊆
      Ico (2 ^ u) (2 ^ (u + 1)) ∪ (Ico (2 ^ u) (2 ^ (u + 1))).image (fun x => M - x) := by
    intro lam h
    have hb := mem_cshell_bounds h
    have hlt : lam < M := by
      simp only [cshell, nondvd, mem_filter, mem_Ico] at h; exact h.1.1.2
    simp only [mem_union, mem_Ico, mem_image]
    unfold cdist at hb
    by_cases hc : lam ≤ M - lam
    · left; rw [min_eq_left hc] at hb; exact hb
    · right
      rw [min_eq_right (by omega)] at hb
      exact ⟨M - lam, hb, by omega⟩
  calc (cshell r t u).card
      ≤ (Ico (2 ^ u) (2 ^ (u + 1)) ∪ (Ico (2 ^ u) (2 ^ (u + 1))).image (fun x => M - x)).card :=
        card_le_card hsub
    _ ≤ (Ico (2 ^ u) (2 ^ (u + 1))).card +
          ((Ico (2 ^ u) (2 ^ (u + 1))).image (fun x => M - x)).card := card_union_le _ _
    _ ≤ (Ico (2 ^ u) (2 ^ (u + 1))).card + (Ico (2 ^ u) (2 ^ (u + 1))).card :=
        Nat.add_le_add_left card_image_le _
    _ = 2 ^ (u + 1) := by rw [Nat.card_Ico, pow_succ]; omega

/-- **Weight bound on a centered shell.** For `λ ∈ cshell r t u`:
`‖coef r t λ‖ ≤ 2^t / (2 · 2^u)`. -/
theorem norm_coef_le_cshell {r t u lam : ℕ} (h : lam ∈ cshell r t u) :
    ‖coef r t lam‖ ≤ 2 ^ t / (2 * 2 ^ u) := by
  have hn : lam ∈ nondvd r t := (mem_filter.mp h).1
  have hI : 1 ≤ lam ∧ lam < 2 ^ (r + t) := by
    simp only [nondvd, mem_filter, mem_Ico] at hn; exact hn.1
  have hb := (mem_cshell_bounds h).1
  have hcast : ((cdist (2 ^ (r + t)) lam : ℕ) : ℝ) = min (lam : ℝ) (2 ^ (r + t) - lam) := by
    unfold cdist
    rw [Nat.cast_min, Nat.cast_sub hI.2.le]
    push_cast; rfl
  have hbR : (2 : ℝ) ^ u ≤ min (lam : ℝ) (2 ^ (r + t) - lam) := by
    rw [← hcast]; exact_mod_cast hb
  calc ‖coef r t lam‖ ≤ 2 ^ t / (2 * min (lam : ℝ) (2 ^ (r + t) - lam)) :=
        norm_coef_le r t lam (by omega) hI.2
    _ ≤ 2 ^ t / (2 * 2 ^ u) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        linarith

/-! ## Sufficient condition from shell averages -/

/-- **Shell-average bound.** If `F ≥ 0` and every centered shell satisfies
`∑_{λ ∈ shell_u} F λ ≤ #shell_u · a_u` (with `a_u ≥ 0`), then
`∑_{1≤g<2^t} ∑_{k<2^r} ‖coef(g + 2^t k)‖ F(g + 2^t k) ≤ 2^t ∑_{u < r+t} a_u`. -/
theorem weighted_sum_le_of_shell_averages (r t : ℕ) (F : ℕ → ℝ) (a : ℕ → ℝ)
    (hF : ∀ lam, 0 ≤ F lam) (ha : ∀ u, 0 ≤ a u)
    (hshell : ∀ u ∈ range (r + t), ∑ lam ∈ cshell r t u, F lam ≤ (cshell r t u).card * a u) :
    ∑ g ∈ Ico 1 (2 ^ t), ∑ k ∈ range (2 ^ r), ‖coef r t (g + 2 ^ t * k)‖ * F (g + 2 ^ t * k) ≤
      2 ^ t * ∑ u ∈ range (r + t), a u := by
  rw [sum_fibre_eq_sum_nondvd r t (fun lam => ‖coef r t lam‖ * F lam)]
  change ∑ lam ∈ nondvd r t, ‖coef r t lam‖ * F lam ≤ _
  rw [sum_nondvd_eq_sum_cshell, mul_sum]
  refine sum_le_sum fun u hu => ?_
  have hw : ∀ lam ∈ cshell r t u, ‖coef r t lam‖ * F lam ≤ 2 ^ t / (2 * 2 ^ u) * F lam :=
    fun lam hl => mul_le_mul_of_nonneg_right (norm_coef_le_cshell hl) (hF lam)
  have hcard : ((cshell r t u).card : ℝ) ≤ 2 ^ (u + 1) := by exact_mod_cast card_cshell_le r t u
  have hc0 : (0 : ℝ) ≤ 2 ^ t / (2 * 2 ^ u) := by positivity
  calc ∑ lam ∈ cshell r t u, ‖coef r t lam‖ * F lam
      ≤ ∑ lam ∈ cshell r t u, 2 ^ t / (2 * 2 ^ u) * F lam := sum_le_sum hw
    _ = 2 ^ t / (2 * 2 ^ u) * ∑ lam ∈ cshell r t u, F lam := by rw [mul_sum]
    _ ≤ 2 ^ t / (2 * 2 ^ u) * ((cshell r t u).card * a u) :=
        mul_le_mul_of_nonneg_left (hshell u hu) hc0
    _ ≤ 2 ^ t / (2 * 2 ^ u) * (2 ^ (u + 1) * a u) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard (ha u)) hc0
    _ = 2 ^ t * a u := by rw [pow_succ]; field_simp

/-- **`WeightedFourier` from per-shell averages.** With `t = s − σ`, `r = σ + 1`: if every
centered shell satisfies `∑_{λ ∈ shell_u} ‖Ψ λ‖^2 ≤ #shell_u · a_u · |P_σ|^2` (normalized shell
averages `a_u ≥ 0`) and `(1 + (σ+1)/2) · 2^t · ∑_u a_u ≤ ε^2 |V_{σ,s}| / 2^t`, then
`WeightedFourier b N j0 s σ ε`. -/
theorem weightedFourier_of_shell_averages (b : ℕ → ℕ) (N j0 s σ : ℕ) (ε : ℝ) (a : ℕ → ℝ)
    (ha : ∀ u, 0 ≤ a u)
    (hshell : ∀ u ∈ range (σ + 1 + (s - σ)),
      ∑ lam ∈ cshell (σ + 1) (s - σ) u,
        ‖Psi (shellP b j0 σ) (σ + 1) (s - σ) (yPrime j0 σ (s - σ)) lam‖ ^ 2 ≤
      (cshell (σ + 1) (s - σ) u).card * (a u * ((shellP b j0 σ).card : ℝ) ^ 2))
    (hfin : (1 + ((σ + 1 : ℕ) : ℝ) / 2) * 2 ^ (s - σ) * ∑ u ∈ range (σ + 1 + (s - σ)), a u ≤
      ε ^ 2 * (shellV b N j0 σ (s - σ)).card / 2 ^ (s - σ)) :
    WeightedFourier b N j0 s σ ε := by
  unfold WeightedFourier
  set P2 : ℝ := ((shellP b j0 σ).card : ℝ) ^ 2
  have hP2 : 0 ≤ P2 := by positivity
  have hbase := weighted_sum_le_of_shell_averages (σ + 1) (s - σ)
    (fun lam => ‖Psi (shellP b j0 σ) (σ + 1) (s - σ) (yPrime j0 σ (s - σ)) lam‖ ^ 2)
    (fun u => a u * P2) (fun _ => by positivity) (fun u => mul_nonneg (ha u) hP2) hshell
  have hpre : (0 : ℝ) ≤ 1 + ((σ + 1 : ℕ) : ℝ) / 2 := by positivity
  calc (1 + ((σ + 1 : ℕ) : ℝ) / 2) * ∑ g ∈ Ico 1 (2 ^ (s - σ)), ∑ k ∈ range (2 ^ (σ + 1)),
        ‖coef (σ + 1) (s - σ) (g + 2 ^ (s - σ) * k)‖ *
          ‖Psi (shellP b j0 σ) (σ + 1) (s - σ) (yPrime j0 σ (s - σ))
            (g + 2 ^ (s - σ) * k)‖ ^ 2
      ≤ (1 + ((σ + 1 : ℕ) : ℝ) / 2) *
          (2 ^ (s - σ) * ∑ u ∈ range (σ + 1 + (s - σ)), a u * P2) :=
        mul_le_mul_of_nonneg_left hbase hpre
    _ = ((1 + ((σ + 1 : ℕ) : ℝ) / 2) * 2 ^ (s - σ) *
          ∑ u ∈ range (σ + 1 + (s - σ)), a u) * P2 := by rw [← sum_mul]; ring
    _ ≤ (ε ^ 2 * (shellV b N j0 σ (s - σ)).card / 2 ^ (s - σ)) * P2 :=
        mul_le_mul_of_nonneg_right hfin hP2
    _ = ε ^ 2 * P2 * (shellV b N j0 σ (s - σ)).card / 2 ^ (s - σ) := by ring

end ShellDecomposition
end EOC
