import EOC.ShapeTail
import EOC.LocalWindow

/-!
# The class-sum ↔ layered-kernel bridge

`EOC.ShapeTailRed.tightTail_of_tilted` reduces `ShapeTail` to a bound on the tilted class sum

  `∑_c (∏_r |B_r(c)|) · u^{#tight(c)}`,

where `c` ranges over the coarse classes (even prefix sums) of the confined prefix shell.  This file
connects that sum to the layered transfer kernel `EOC.LocalWindow.ker`, so that the finite
super-eigenvector certificates (`ker_le_of_superEigen`) apply.

The bridge does **not** require characterizing which sequences of even prefix sums actually arise as
classes: since all weights are nonnegative, it suffices that the classes *inject* into the paths of
the kernel.  The general statement is

* `sum_prod_le_ker` — for any finite family of paths with fixed endpoints, the sum of the path
  products is at most the pinned kernel `ker w l n x z`.

and the application is

* `class_sum_le_ker` — the tilted class sum is at most `ker (blockW b u) 0 (j₀/2) 0 σ`,
* `tightTail_of_superEigen` — hence `TightTail` follows from a super-eigenvector certificate.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace ShapeBridge

open Finset BlockCubeInstance PrefixCollision OddBlack WhiteContraction ShapeTailRed LocalWindow

/-! ## 1. Paths of a layered kernel -/

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- **Path sum ≤ pinned kernel.**  Any finite family `C` of paths `Fin (n+1) → S` with `c 0 = x` and
`c (last n) = z` satisfies `∑_{c ∈ C} ∏_r w (l+r) (c r) (c (r+1)) ≤ ker w l n x z`.  Distinct paths
contribute distinct terms and the kernel sums over *all* paths, so no characterization of `C` is
needed — only nonnegativity of the weights. -/
theorem sum_prod_le_ker {w : ℕ → S → S → ℝ} (hw : ∀ l x y, 0 ≤ w l x y) :
    ∀ (n l : ℕ) (x z : S) (C : Finset (Fin (n + 1) → S)),
      (∀ c ∈ C, c 0 = x) → (∀ c ∈ C, c (Fin.last n) = z) →
      ∑ c ∈ C, ∏ r : Fin n, w (l + (r : ℕ)) (c r.castSucc) (c r.succ) ≤ ker w l n x z := by
  intro n
  induction n with
  | zero =>
    intro l x z C h0 hz
    have hker : ker w l 0 x z = if x = z then 1 else 0 := ker_zero w l x z
    rcases C.eq_empty_or_nonempty with rfl | ⟨c, hc⟩
    · simp [hker]
      split_ifs <;> norm_num
    · -- a single path, and `x = z`
      have hxz : x = z := by
        have h1 := h0 c hc
        have h2 := hz c hc
        rw [show (Fin.last 0) = (0 : Fin 1) from rfl] at h2
        rw [← h1, h2]
      have hsub : C ⊆ {c} := by
        intro d hd
        simp only [mem_singleton]
        funext i
        have : i = 0 := Fin.ext (by omega)
        rw [this, h0 d hd, h0 c hc]
      have hcard : C.card ≤ 1 := by
        have := card_le_card hsub
        simpa using this
      calc ∑ _c ∈ C, ∏ _r : Fin 0, w l x z = (C.card : ℝ) := by simp
        _ ≤ 1 := by exact_mod_cast hcard
        _ = ker w l 0 x z := by rw [hker, if_pos hxz]
  | succ n ih =>
    intro l x z C h0 hz
    classical
    -- split the product at the first step and group the paths by their value at index 1
    have hsplit : ∀ c ∈ C, ∏ r : Fin (n + 1), w (l + (r : ℕ)) (c r.castSucc) (c r.succ)
        = w l x (c 1) * ∏ r : Fin n, w (l + 1 + (r : ℕ))
            ((fun i : Fin (n + 1) => c i.succ) r.castSucc)
            ((fun i : Fin (n + 1) => c i.succ) r.succ) := by
      intro c hc
      rw [Fin.prod_univ_succ]
      congr 1
      · simp only [Fin.val_zero, Nat.add_zero, Fin.castSucc_zero, Fin.succ_zero_eq_one]
        rw [h0 c hc]
      · refine prod_congr rfl fun r _ => ?_
        congr 1 <;> first
          | rfl
          | (simp only [Fin.val_succ]; omega)
          | simp [Fin.succ_castSucc]
    rw [sum_congr rfl hsplit]
    -- group by `c 1`
    rw [← sum_fiberwise_of_maps_to (g := fun c : Fin (n + 2) → S => c 1)
      (fun c _ => mem_univ (c 1))]
    rw [ker_succ]
    refine sum_le_sum fun y _ => ?_
    set F := C.filter (fun c : Fin (n + 2) → S => c 1 = y) with hF
    have hval : ∀ c ∈ F, c 1 = y := fun c hc => (mem_filter.mp hc).2
    -- the tail map is injective on the fibre (the head is pinned to `x`)
    set tail : (Fin (n + 2) → S) → (Fin (n + 1) → S) := fun c i => c i.succ with htail
    have hinj : Set.InjOn tail ↑F := by
      intro c hc d hd hcd
      have hc' : c ∈ F := hc
      have hd' : d ∈ F := hd
      funext i
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · rw [h0 c (mem_filter.mp hc').1, h0 d (mem_filter.mp hd').1]
      · exact congrFun hcd j
    have hsum : ∑ c ∈ F, w l x y * ∏ r : Fin n, w (l + 1 + (r : ℕ))
          (tail c r.castSucc) (tail c r.succ)
        = w l x y * ∑ c' ∈ F.image tail, ∏ r : Fin n, w (l + 1 + (r : ℕ))
          (c' r.castSucc) (c' r.succ) := by
      rw [sum_image (fun a ha b hb h => hinj ha hb h), mul_sum]
    have hrw : ∑ c ∈ F, w l x (c 1) * ∏ r : Fin n, w (l + 1 + (r : ℕ))
          (tail c r.castSucc) (tail c r.succ)
        = ∑ c ∈ F, w l x y * ∏ r : Fin n, w (l + 1 + (r : ℕ))
          (tail c r.castSucc) (tail c r.succ) := by
      refine sum_congr rfl fun c hc => ?_
      rw [hval c hc]
    rw [hrw, hsum]
    refine mul_le_mul_of_nonneg_left ?_ (hw l x y)
    refine ih (l + 1) y z (F.image tail) ?_ ?_
    · intro c' hc'
      obtain ⟨c, hc, rfl⟩ := mem_image.mp hc'
      simpa [htail] using hval c hc
    · intro c' hc'
      obtain ⟨c, hc, rfl⟩ := mem_image.mp hc'
      have := hz c (mem_filter.mp hc).1
      simpa [htail, Fin.succ_last] using this

/-! ## 2. The block kernel of the confined prefix shell -/

variable (b : ℕ → ℕ)

/-- The choice set of pair block `r` as a function of the two even prefix sums. -/
def Bset (r x y : ℕ) : Finset ℕ := (Ioo x y).filter (fun z => z ≤ b (2 * r + 1))

theorem pairB_eq_Bset {j0 : ℕ} (c : Fin (j0 + 1) → ℕ) (r : ℕ) :
    pairB b c r = Bset b r (cget c (2 * r)) (cget c (2 * r + 2)) := rfl

/-- The tilted block weight `|B_r| · u^{[|B_r| ≤ 1]}` as a layered kernel on `Fin (σ+1)`. -/
noncomputable def blockW (u : ℝ) (σ : ℕ) : ℕ → Fin (σ + 1) → Fin (σ + 1) → ℝ :=
  fun r x y => ((Bset b r x y).card : ℝ) * (if (Bset b r x y).card ≤ 1 then u else 1)

theorem blockW_nonneg {u : ℝ} (hu : 0 ≤ u) (σ r : ℕ) (x y : Fin (σ + 1)) :
    0 ≤ blockW b u σ r x y := by
  unfold blockW
  have hc : (0 : ℝ) ≤ ((Bset b r x y).card : ℝ) := Nat.cast_nonneg _
  split_ifs
  · exact mul_nonneg hc hu
  · simpa using hc

/-- The path of even prefix sums attached to a coarse class. -/
def classPath (σ : ℕ) {j0 : ℕ} (c : Fin (j0 + 1) → ℕ) : Fin (j0 / 2 + 1) → Fin (σ + 1) :=
  fun r => ⟨min (cget c (2 * (r : ℕ))) σ, by omega⟩

/-- On classes of the prefix shell, the even prefix sums are at most `σ`. -/
theorem cget_pairκ_le {j0 σ : ℕ} (hj : 1 ≤ j0) {P : FiniteValuationWord j0}
    (hP : P ∈ shellP b j0 σ) {r : ℕ} (hr : 2 * r ≤ j0) :
    cget (pairκ j0 P) (2 * r) = P.prefixSum (2 * r) ∧ P.prefixSum (2 * r) ≤ σ := by
  obtain ⟨hpos, hconf, htot⟩ := (mem_shellP_iff b hj).mp hP
  refine ⟨cget_pairκ P hr (by omega), ?_⟩
  have := prefixSum_le_prefixSum P j0 hr le_rfl
  rw [← htot]
  exact this

/-- **The bridge.**  The tilted class sum is at most the pinned layered kernel of the block
weight.  Nonnegativity of the weights is all that is needed: the classes inject into the kernel's
paths, and the kernel sums over *all* paths. -/
theorem class_sum_le_ker {j0 σ : ℕ} {u : ℝ} (hj : 1 ≤ j0) (hu : 0 ≤ u)
    (hj2 : 2 * (j0 / 2) = j0) :
    ∑ c ∈ (shellP b j0 σ).image (pairκ j0),
        (∏ r : Fin (j0 / 2), ((pairB b c (r : ℕ)).card : ℝ)) *
          u ^ ((range (j0 / 2)).filter (Tight b c)).card
      ≤ ker (blockW b u σ) 0 (j0 / 2) ⟨0, by omega⟩ ⟨σ, by omega⟩ := by
  classical
  set R := j0 / 2 with hR
  set 𝒞 := (shellP b j0 σ).image (pairκ j0) with h𝒞
  -- the even prefix sums of a class never exceed the total
  have hle : ∀ c ∈ 𝒞, ∀ r, r ≤ R → cget c (2 * r) ≤ σ := by
    intro c hc r hr
    obtain ⟨P, hP, rfl⟩ := mem_image.mp hc
    obtain ⟨heq, hlee⟩ := cget_pairκ_le b hj hP (r := r) (by omega)
    rw [heq]; exact hlee
  -- the weight of a class equals the product of the kernel along its path
  have hkey : ∀ c ∈ 𝒞,
      (∏ r : Fin R, blockW b u σ (0 + (r : ℕ)) (classPath σ c r.castSucc) (classPath σ c r.succ))
        = (∏ r : Fin R, ((pairB b c (r : ℕ)).card : ℝ)) *
          u ^ ((range R).filter (Tight b c)).card := by
    intro c hc
    have hB : ∀ r : Fin R, Bset b (0 + (r : ℕ))
        (classPath σ c r.castSucc) (classPath σ c r.succ) = pairB b c (r : ℕ) := by
      intro r
      have hrR : (r : ℕ) < R := r.isLt
      rw [pairB_eq_Bset, Nat.zero_add]
      simp only [classPath, Fin.coe_castSucc, Fin.val_succ]
      rw [Nat.min_eq_left (hle c hc (r : ℕ) (by omega)),
        Nat.min_eq_left (hle c hc ((r : ℕ) + 1) (by omega)),
        show 2 * ((r : ℕ) + 1) = 2 * (r : ℕ) + 2 from by ring]
    have hprod : (∏ r : Fin R, blockW b u σ (0 + (r : ℕ))
          (classPath σ c r.castSucc) (classPath σ c r.succ))
        = ∏ r : Fin R, (((pairB b c (r : ℕ)).card : ℝ) *
            (if (pairB b c (r : ℕ)).card ≤ 1 then u else 1)) := by
      refine prod_congr rfl fun r _ => ?_
      unfold blockW
      rw [hB r]
    have hcount : (∏ r : Fin R, (if (pairB b c (r : ℕ)).card ≤ 1 then u else 1))
        = u ^ ((range R).filter (Tight b c)).card := by
      rw [Fin.prod_univ_eq_prod_range (fun r => if (pairB b c r).card ≤ 1 then u else 1) R,
        prod_ite, prod_const_one, mul_one, prod_const]
      congr 2
    rw [hprod, prod_mul_distrib, hcount]
  -- the path map is injective on classes
  have hinj : Set.InjOn (classPath σ (j0 := j0)) ↑𝒞 := by
    intro c hc d hd hcd
    have hc' : c ∈ 𝒞 := hc
    have hd' : d ∈ 𝒞 := hd
    obtain ⟨P, hP, rfl⟩ := mem_image.mp hc'
    obtain ⟨Q, hQ, rfl⟩ := mem_image.mp hd'
    funext i
    rcases Nat.even_or_odd (i : ℕ) with ⟨k, hk⟩ | hodd
    · have hk2 : (i : ℕ) = 2 * k := by omega
      have hiL : (i : ℕ) ≤ j0 := by have := i.isLt; omega
      have hkR : k ≤ R := by omega
      have h2kj : 2 * k ≤ j0 := by omega
      have hpath := congrFun hcd ⟨k, by omega⟩
      have hv : min (cget (pairκ j0 P) (2 * k)) σ = min (cget (pairκ j0 Q) (2 * k)) σ := by
        have := congrArg (fun z : Fin (σ + 1) => (z : ℕ)) hpath
        simpa [classPath] using this
      have hcc : cget (pairκ j0 P) (2 * k) = cget (pairκ j0 Q) (2 * k) := by
        have h1 := hle _ hc' k hkR
        have h2 := hle _ hd' k hkR
        omega
      rw [cget_pairκ P h2kj (by omega), cget_pairκ Q h2kj (by omega)] at hcc
      have hmod : (i : ℕ) % 2 = 0 := by omega
      simp only [pairκ, hmod, ite_true]
      rw [hk2]
      exact hcc
    · have hmod : (i : ℕ) % 2 = 1 := Nat.odd_iff.mp hodd
      simp [pairκ, hmod]
  -- sum over the image of the path map, then compare with the kernel
  have hmain : ∑ p ∈ 𝒞.image (classPath σ), ∏ r : Fin R, blockW b u σ (0 + (r : ℕ))
      (p r.castSucc) (p r.succ) ≤ ker (blockW b u σ) 0 R ⟨0, by omega⟩ ⟨σ, by omega⟩ := by
    refine sum_prod_le_ker (blockW_nonneg b hu σ) R 0 _ _ _ ?_ ?_
    · intro p hp
      obtain ⟨c, hc, rfl⟩ := mem_image.mp hp
      obtain ⟨P, hP, rfl⟩ := mem_image.mp hc
      have hz : cget (pairκ j0 P) 0 = 0 := by
        rw [cget_pairκ P (by omega) (by omega)]
        simp [FiniteValuationWord.prefixSum]
      refine Fin.ext ?_
      simp only [classPath, Fin.val_zero, Nat.mul_zero]
      omega
    · intro p hp
      obtain ⟨c, hc, rfl⟩ := mem_image.mp hp
      obtain ⟨P, hP, rfl⟩ := mem_image.mp hc
      obtain ⟨hpos, hconf, htot⟩ := (mem_shellP_iff b hj).mp hP
      have hlast : cget (pairκ j0 P) (2 * R) = σ := by
        rw [cget_pairκ P (by omega) (by omega), hj2, ← htot]
        rfl
      refine Fin.ext ?_
      simp only [classPath, Fin.val_last]
      omega
  rw [sum_image (fun a ha c hc h => hinj ha hc h)] at hmain
  calc ∑ c ∈ 𝒞, (∏ r : Fin R, ((pairB b c (r : ℕ)).card : ℝ)) *
        u ^ ((range R).filter (Tight b c)).card
      = ∑ c ∈ 𝒞, ∏ r : Fin R, blockW b u σ (0 + (r : ℕ))
          (classPath σ c r.castSucc) (classPath σ c r.succ) := (sum_congr rfl hkey).symm
    _ ≤ ker (blockW b u σ) 0 R ⟨0, by omega⟩ ⟨σ, by omega⟩ := hmain

/-! ## 3. From a super-eigenvector certificate to `ShapeTail` -/

/-- **Certificate ⇒ `TightTail`.**  A positive layer-dependent weight `h` with
`∑_y blockW(l,x,y) h(l+1,y) ≤ M h(l,x)` bounds the tilted class sum by `M^R h(0,0)/h(R,σ)`; if that
is small against `ρ₁ u^T C(σ−1, j₀−1)/j₀`, then `TightTail` holds. -/
theorem tightTail_of_superEigen {j0 σ t T : ℕ} {u ρ₁ M : ℝ} {h : ℕ → Fin (σ + 1) → ℝ}
    (hj : 1 ≤ j0) (hu : 1 ≤ u) (hρ : 0 ≤ ρ₁) (hj2 : 2 * (j0 / 2) = j0)
    (hchord : ∀ j ≤ j0, ∀ p : ℕ, j0 * p ≤ j * b j0 → p ≤ b j)
    (hjσ : j0 ≤ σ) (hσ : σ ≤ b j0)
    (hh : ∀ l y, 0 < h l y) (hM : 0 ≤ M)
    (hsuper : ∀ l x, ∑ y : Fin (σ + 1), blockW b u σ l x y * h (l + 1) y ≤ M * h l x)
    (hbound : (j0 : ℝ) * (M ^ (j0 / 2) * h 0 ⟨0, by omega⟩ / h (0 + j0 / 2) ⟨σ, by omega⟩)
      ≤ ρ₁ * u ^ T * (Nat.choose (σ - 1) (j0 - 1) : ℝ)) :
    TightTail b j0 σ T ρ₁ := by
  have hu0 : (0 : ℝ) ≤ u := le_trans zero_le_one hu
  have hcert := ker_le_of_superEigen (blockW_nonneg b hu0 σ) hh hM hsuper 0 (j0 / 2)
    (⟨0, by omega⟩ : Fin (σ + 1)) (⟨σ, by omega⟩ : Fin (σ + 1))
  have hclass := class_sum_le_ker b hj hu0 hj2 (σ := σ) (u := u)
  have hj0 : (0 : ℝ) ≤ (j0 : ℝ) := Nat.cast_nonneg j0
  refine tightTail_of_tilted_choose b (t := t) hj hu hρ hchord hjσ hσ ?_
  calc (j0 : ℝ) * ∑ c ∈ (shellP b j0 σ).image (pairκ j0),
        (∏ r : Fin (j0 / 2), ((pairB b c (r : ℕ)).card : ℝ)) *
          u ^ ((range (j0 / 2)).filter (Tight b c)).card
      ≤ (j0 : ℝ) * (M ^ (j0 / 2) * h 0 ⟨0, by omega⟩ / h (0 + j0 / 2) ⟨σ, by omega⟩) :=
        mul_le_mul_of_nonneg_left (le_trans hclass hcert) hj0
    _ ≤ ρ₁ * u ^ T * (Nat.choose (σ - 1) (j0 - 1) : ℝ) := hbound

/-- **Certificate ⇒ `ShapeTail`.**  The whole shape hypothesis now follows from one finite
super-eigenvector certificate for the block kernel, together with the arithmetic side condition
`K + T + σ/(N₀+2) ≤ j₀/2`. -/
theorem shapeTail_of_superEigen {j0 σ t N0 K T : ℕ} {u ρ₁ M : ℝ} {h : ℕ → Fin (σ + 1) → ℝ}
    (hj : 1 ≤ j0) (hu : 1 ≤ u) (hρ : 0 ≤ ρ₁) (hj2 : 2 * (j0 / 2) = j0)
    (hchord : ∀ j ≤ j0, ∀ p : ℕ, j0 * p ≤ j * b j0 → p ≤ b j)
    (hjσ : j0 ≤ σ) (hσ : σ ≤ b j0)
    (hK : K + T + σ / (N0 + 2) ≤ j0 / 2)
    (hh : ∀ l y, 0 < h l y) (hM : 0 ≤ M)
    (hsuper : ∀ l x, ∑ y : Fin (σ + 1), blockW b u σ l x y * h (l + 1) y ≤ M * h l x)
    (hbound : (j0 : ℝ) * (M ^ (j0 / 2) * h 0 ⟨0, by omega⟩ / h (0 + j0 / 2) ⟨σ, by omega⟩)
      ≤ ρ₁ * u ^ T * (Nat.choose (σ - 1) (j0 - 1) : ℝ)) :
    ShapeTail b j0 σ N0 K ρ₁ :=
  shapeTail_of_tightTail b (N0 := N0) hj hK
    (tightTail_of_superEigen b (t := t) hj hu hρ hj2 hchord hjσ hσ hh hM hsuper hbound)

end ShapeBridge
end EOC
