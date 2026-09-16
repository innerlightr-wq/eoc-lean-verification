import EOC.AverageOddDark
import EOC.BinomialEntropy

/-!
# The pressure class-to-kernel bridge

The odd-dark exponential moment is a layered kernel, exactly as the tilted class sum of `ShapeTail`
is (`ShapeBridge.class_sum_le_ker`):

* `oddW b m d s lam r x y = ∑_{z ∈ B_r(x,y)} s^{[z+1 ∈ B_r(x,y) ∧ Dark m d lam r z]}` — block
  weight;
* `sum_pow_nodd_eq_class` — `∑_P s^{N_odd(P)} = ∑_c ∏_r oddW r (c_{2r}) (c_{2r+2})` (class product);
* `class_prod_le_ker` — any nonnegative class product is at most the pinned kernel (paths inject);
* `geoW p q oddW` — the geometric (killed `P*`) weight `p² q^{y−x−2} · oddW`;
* `ker_geo_eq` — **exact identity** `ker geoW l n x z = p^{2n} q^{z−x−2n} · ker W l n x z`;
* `sum_pow_nodd_le_geo` — **the bridge**: with `p = (j−1)/(σ−1)`, `q = 1 − p`,
  `∑_P s^{N_odd} ≤ (σ j / p) · ker geoW 0 (j/2) 0 σ · |P_σ|`.
  The loss `σ j / p` is polynomial in `j` (binomial entropy + chord rotation).
* `sum_pow_nodd_le_windows` — combined with `LocalWindow.val_le_of_window_rem`: if every `K`-block
  window of the geometric kernel has mass `≤ M` from every state and the remainder `≤ Mrem`, then
  `∑_P s^{N_odd} ≤ (σ j / p) · M^W · Mrem · |P_σ|` for `j/2 = W K + ρ`.

The untilted geometric weight is substochastic (row sums `≤ 1`); nothing here needs that.

No `sorry`, `admit`, `axiom`, `opaque`, or `native_decide`.
-/

namespace EOC
namespace PressureBridge

open Finset BlockCubeInstance PrefixCollision OddBlack WhiteContraction LocalWindow ShapeBridge

variable (b : ℕ → ℕ)

open Classical in
/-- The odd-dark block weight as a function of the two even prefix sums. -/
noncomputable def oddW (m : ℕ) (d s : ℝ) (lam : ℕ) (r x y : ℕ) : ℝ :=
  ∑ z ∈ Bset b r x y, (if z + 1 ∈ Bset b r x y ∧ Dark m d lam r z then s else 1)

theorem oddW_nonneg {m : ℕ} {d s : ℝ} {lam : ℕ} (hs : 0 ≤ s) (r x y : ℕ) :
    0 ≤ oddW b m d s lam r x y := by
  classical
  unfold oddW
  exact sum_nonneg fun z _ => by split_ifs <;> linarith

open Classical in
/-- **Class product form of the moment.** -/
theorem sum_pow_nodd_eq_class {j σ t m : ℕ} {d s : ℝ} {lam : ℕ} (hj : 1 ≤ j) :
    ∑ P ∈ shellP b j σ, s ^ Nodd b m d lam P =
      ∑ c ∈ (shellP b j σ).image (pairκ j),
        ∏ r : Fin (j / 2),
          oddW b m d s lam (r : ℕ) (cget c (2 * (r : ℕ))) (cget c (2 * (r : ℕ) + 2)) := by
  set D := pairDecomposition b j σ t hj
  rw [← sum_fiberwise_of_maps_to (fun P hP => mem_image_of_mem (pairκ j) hP)]
  refine sum_congr rfl fun c hc => ?_
  let g : Fin (j / 2) → ℕ → ℝ := fun r x =>
    if x ∈ Elig b c r ∧ Dark m d lam r x then s else 1
  have hword : ∀ P ∈ (shellP b j σ).filter (fun P => pairκ j P = c),
      s ^ Nodd b m d lam P = ∏ r : Fin (j / 2), g r (pairπ j P r) := by
    intro P hP
    have hκ : pairκ j P = c := (mem_filter.mp hP).2
    unfold Nodd
    rw [pow_card_filter_eq_prod]
    refine prod_congr rfl fun r _ => ?_
    simp only [g, OwnDark, hκ, pairπ]
  rw [sum_congr rfl hword, sum_class_prod (shellP b j σ) (pairκ j) (pairB b) (pairπ j)
    (D.inj c hc) (D.image_eq c hc) g]
  refine prod_congr rfl fun r _ => ?_
  unfold oddW
  rw [← pairB_eq_Bset]
  refine sum_congr rfl fun z hz => ?_
  simp only [g, Elig, mem_filter]
  by_cases h1 : z + 1 ∈ pairB b c (r : ℕ)
  · simp [hz, h1]
  · simp [h1]

/-! ## Classes inject into kernel paths (generic weight) -/

open Classical in
/-- **Any nonnegative class product is at most the pinned kernel.** -/
theorem class_prod_le_ker {j σ : ℕ} (F : ℕ → ℕ → ℕ → ℝ) (hF : ∀ r x y, 0 ≤ F r x y)
    (hj : 1 ≤ j) (hj2 : 2 * (j / 2) = j) :
    ∑ c ∈ (shellP b j σ).image (pairκ j),
        ∏ r : Fin (j / 2), F (r : ℕ) (cget c (2 * (r : ℕ))) (cget c (2 * (r : ℕ) + 2))
      ≤ ker (fun r (x y : Fin (σ + 1)) => F r x y) 0 (j / 2) ⟨0, by omega⟩ ⟨σ, by omega⟩ := by
  set R := j / 2 with hR
  set 𝒞 := (shellP b j σ).image (pairκ j) with h𝒞
  set w : ℕ → Fin (σ + 1) → Fin (σ + 1) → ℝ := fun r x y => F r x y
  have hle : ∀ c ∈ 𝒞, ∀ r, r ≤ R → cget c (2 * r) ≤ σ := by
    intro c hc r hr
    obtain ⟨P, hP, rfl⟩ := mem_image.mp hc
    obtain ⟨heq, hlee⟩ := cget_pairκ_le b hj hP (r := r) (by omega)
    rw [heq]; exact hlee
  have hkey : ∀ c ∈ 𝒞,
      (∏ r : Fin R, w (0 + (r : ℕ)) (classPath σ c r.castSucc) (classPath σ c r.succ))
        = ∏ r : Fin R, F (r : ℕ) (cget c (2 * (r : ℕ))) (cget c (2 * (r : ℕ) + 2)) := by
    intro c hc
    refine prod_congr rfl fun r _ => ?_
    have hrR : (r : ℕ) < R := r.isLt
    simp only [w, classPath, Fin.val_castSucc, Fin.val_succ, Nat.zero_add]
    rw [Nat.min_eq_left (hle c hc (r : ℕ) (by omega)),
      Nat.min_eq_left (hle c hc ((r : ℕ) + 1) (by omega)),
      show 2 * ((r : ℕ) + 1) = 2 * (r : ℕ) + 2 from by ring]
  have hinj : Set.InjOn (classPath σ (j0 := j)) ↑𝒞 := by
    intro c hc d hd hcd
    have hc' : c ∈ 𝒞 := hc
    have hd' : d ∈ 𝒞 := hd
    obtain ⟨P, hP, rfl⟩ := mem_image.mp hc'
    obtain ⟨Q, hQ, rfl⟩ := mem_image.mp hd'
    funext i
    rcases Nat.even_or_odd (i : ℕ) with ⟨k, hk⟩ | hodd
    · have hk2 : (i : ℕ) = 2 * k := by omega
      have hiL : (i : ℕ) ≤ j := by have := i.isLt; omega
      have hkR : k ≤ R := by omega
      have h2kj : 2 * k ≤ j := by omega
      have hpath := congrFun hcd ⟨k, by omega⟩
      have hv : min (cget (pairκ j P) (2 * k)) σ = min (cget (pairκ j Q) (2 * k)) σ := by
        have := congrArg (fun z : Fin (σ + 1) => (z : ℕ)) hpath
        simpa [classPath] using this
      have hcc : cget (pairκ j P) (2 * k) = cget (pairκ j Q) (2 * k) := by
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
  have hmain : ∑ p ∈ 𝒞.image (classPath σ), ∏ r : Fin R, w (0 + (r : ℕ))
      (p r.castSucc) (p r.succ) ≤ ker w 0 R ⟨0, by omega⟩ ⟨σ, by omega⟩ := by
    refine sum_prod_le_ker (fun l (x y : Fin (σ + 1)) => hF l x y) R 0 _ _ _ ?_ ?_
    · intro p hp
      obtain ⟨c, hc, rfl⟩ := mem_image.mp hp
      obtain ⟨P, hP, rfl⟩ := mem_image.mp hc
      have hz : cget (pairκ j P) 0 = 0 := by
        rw [cget_pairκ P (by omega) (by omega)]
        simp [FiniteValuationWord.prefixSum]
      refine Fin.ext ?_
      simp only [classPath, Fin.val_zero, Nat.mul_zero]
      omega
    · intro p hp
      obtain ⟨c, hc, rfl⟩ := mem_image.mp hp
      obtain ⟨P, hP, rfl⟩ := mem_image.mp hc
      obtain ⟨hpos, hconf, htot⟩ := (mem_shellP_iff b hj).mp hP
      have hlast : cget (pairκ j P) (2 * R) = σ := by
        rw [cget_pairκ P (by omega) (by omega), hj2, ← htot]
        rfl
      refine Fin.ext ?_
      simp only [classPath, Fin.val_last]
      omega
  rw [sum_image (fun a ha c hc h => hinj ha hc h)] at hmain
  calc _ = ∑ c ∈ 𝒞, ∏ r : Fin R, w (0 + (r : ℕ))
          (classPath σ c r.castSucc) (classPath σ c r.succ) := (sum_congr rfl hkey).symm
    _ ≤ _ := hmain

/-! ## Geometric normalisation: an exact kernel identity -/

/-- The geometric (killed `P*`) block weight `p² q^{y−x−2} · W`. -/
noncomputable def geoW (p q : ℝ) (W : ℕ → ℕ → ℕ → ℝ) (σ : ℕ) : ℕ → Fin (σ + 1) → Fin (σ + 1) → ℝ :=
  fun r x y => p ^ 2 * q ^ ((y : ℤ) - x - 2) * W r x y

/-- **Exact identity.**  `ker geoW l n x z = p^{2n} q^{z−x−2n} · ker W l n x z`. -/
theorem ker_geo_eq {p q : ℝ} (hq : q ≠ 0) (W : ℕ → ℕ → ℕ → ℝ) (σ : ℕ) :
    ∀ (n l : ℕ) (x z : Fin (σ + 1)),
      ker (geoW p q W σ) l n x z =
        p ^ (2 * n) * q ^ ((z : ℤ) - x - 2 * n) *
          ker (fun r (x y : Fin (σ + 1)) => W r x y) l n x z := by
  intro n
  induction n with
  | zero =>
    intro l x z
    rw [ker_zero, ker_zero]
    split_ifs with h
    · subst h; simp
    · simp
  | succ n ih =>
    intro l x z
    rw [ker_succ, ker_succ, mul_sum]
    refine sum_congr rfl fun y _ => ?_
    rw [ih (l + 1) y z]
    unfold geoW
    have e : q ^ ((y : ℤ) - x - 2) * q ^ ((z : ℤ) - y - 2 * n) =
        q ^ ((z : ℤ) - x - 2 * ((n + 1 : ℕ) : ℤ)) := by
      rw [← zpow_add₀ hq]; congr 1; push_cast; ring
    calc p ^ 2 * q ^ ((y : ℤ) - x - 2) * W l x y *
          (p ^ (2 * n) * q ^ ((z : ℤ) - y - 2 * n) *
            ker (fun r (x y : Fin (σ + 1)) => W r x y) (l + 1) n y z)
        = p ^ (2 * (n + 1)) * (q ^ ((y : ℤ) - x - 2) * q ^ ((z : ℤ) - y - 2 * n)) *
            (W l x y * ker (fun r (x y : Fin (σ + 1)) => W r x y) (l + 1) n y z) := by ring
      _ = _ := by rw [e]

/-! ## The bridge -/

/-- **The pressure bridge.**  With `p = (j−1)/(σ−1)` and `q = (σ−j)/(σ−1)`:
`∑_P s^{N_odd(P)} ≤ (σ j / p) · ker (geoW p q oddW) 0 (j/2) 0 σ · |P_σ|`. -/
theorem sum_pow_nodd_le_geo {j σ m : ℕ} {d s : ℝ} {lam : ℕ} (hj : 2 ≤ j) (hj2 : 2 * (j / 2) = j)
    (hchord : ∀ i ≤ j, ∀ p : ℕ, j * p ≤ i * b j → p ≤ b i) (hjσ : j < σ) (hσ : σ ≤ b j)
    (hs : 0 ≤ s) :
    ∑ P ∈ shellP b j σ, s ^ Nodd b m d lam P ≤
      ((σ : ℝ) * j / (((j : ℝ) - 1) / ((σ : ℝ) - 1))) *
        ker (geoW (((j : ℝ) - 1) / ((σ : ℝ) - 1)) (((σ : ℝ) - j) / ((σ : ℝ) - 1))
          (oddW b m d s lam) σ)
          0 (j / 2) ⟨0, by omega⟩ ⟨σ, by omega⟩ *
        ((shellP b j σ).card : ℝ) := by
  set p : ℝ := ((j : ℝ) - 1) / ((σ : ℝ) - 1) with hp
  set q : ℝ := ((σ : ℝ) - j) / ((σ : ℝ) - 1) with hq
  have hσ1 : (1 : ℝ) < σ := by exact_mod_cast (by omega : 1 < σ)
  have hj1 : (1 : ℝ) < j := by exact_mod_cast (by omega : 1 < j)
  have hjσr : (j : ℝ) < σ := by exact_mod_cast hjσ
  have hp0 : 0 < p := div_pos (by linarith) (by linarith)
  have hq0 : 0 < q := div_pos (by linarith) (by linarith)
  -- (1) moment ≤ counting kernel
  have h1 := sum_pow_nodd_eq_class b (j := j) (σ := σ) (t := 0) (m := m) (d := d) (s := s)
    (lam := lam)
    (by omega)
  have h2 := class_prod_le_ker b (j := j) (σ := σ) (oddW b m d s lam) (oddW_nonneg b hs)
    (by omega) hj2
  -- (2) counting kernel = geometric kernel / (p^j q^(σ−j))
  have h3 := ker_geo_eq (p := p) hq0.ne' (oddW b m d s lam) σ (j / 2) 0 ⟨0, by omega⟩ ⟨σ, by omega⟩
  have hexp : (((⟨σ, by omega⟩ : Fin (σ + 1)) : ℕ) : ℤ) - ((⟨0, by omega⟩ : Fin (σ + 1)) : ℕ) -
      2 * ((j / 2 : ℕ) : ℤ) = ((σ - j : ℕ) : ℤ) := by
    push_cast; omega
  rw [hexp, zpow_natCast, show 2 * (j / 2) = j by omega] at h3
  -- (3) binomial entropy and the chord shell bound
  have hent := BinomialEntropy.one_le_succ_mul_choose_mul (σ - 1) (j - 1) (by omega) (by omega)
  have hcast1 : (((j - 1 : ℕ) : ℝ) / ((σ - 1 : ℕ) : ℝ)) = p := by
    rw [hp]; push_cast [show 1 ≤ j by omega, show 1 ≤ σ by omega]; ring
  have hcast2 : ((((σ - 1 : ℕ) : ℝ) - ((j - 1 : ℕ) : ℝ)) / ((σ - 1 : ℕ) : ℝ)) = q := by
    rw [hq]; push_cast [show 1 ≤ j by omega, show 1 ≤ σ by omega]; ring
  rw [hcast1, hcast2, show σ - 1 - (j - 1) = σ - j by omega] at hent
  have hsh : ((σ - 1).choose (j - 1) : ℝ) ≤ j * ((shellP b j σ).card : ℝ) := by
    exact_mod_cast CapacityBounds.shell_choose_le_mul_card (by omega) b hchord hjσ.le hσ
  have hσcast : (((σ - 1 : ℕ) : ℝ) + 1) = σ := by push_cast [show 1 ≤ σ by omega]; ring
  rw [hσcast] at hent
  -- 1 ≤ σ · j |P| p^{j−1} q^{σ−j}
  have hpq0 : 0 ≤ p ^ (j - 1) * q ^ (σ - j) := by positivity
  have hkey : 1 ≤ (σ : ℝ) * j * ((shellP b j σ).card : ℝ) * (p ^ (j - 1) * q ^ (σ - j)) := by
    calc (1 : ℝ) ≤ σ * ((σ - 1).choose (j - 1) : ℝ) * p ^ (j - 1) * q ^ (σ - j) := hent
      _ = σ * ((σ - 1).choose (j - 1) : ℝ) * (p ^ (j - 1) * q ^ (σ - j)) := by ring
      _ ≤ σ * (j * ((shellP b j σ).card : ℝ)) * (p ^ (j - 1) * q ^ (σ - j)) := by gcongr
      _ = _ := by ring
  have hker0 : 0 ≤ ker (fun r (x y : Fin (σ + 1)) => oddW b m d s lam r x y) 0 (j / 2)
      ⟨0, by omega⟩ ⟨σ, by omega⟩ :=
    ker_nonneg (fun l (x y : Fin (σ + 1)) => oddW_nonneg b hs l x y) _ _ _ _
  have hpj : p ^ j = p * p ^ (j - 1) := by
    rw [← pow_succ']; congr 1; omega
  calc ∑ P ∈ shellP b j σ, s ^ Nodd b m d lam P
      ≤ ker (fun r (x y : Fin (σ + 1)) => oddW b m d s lam r x y) 0 (j / 2)
          ⟨0, by omega⟩ ⟨σ, by omega⟩ := by
        rw [h1]; exact h2
    _ ≤ ker (fun r (x y : Fin (σ + 1)) => oddW b m d s lam r x y) 0 (j / 2)
          ⟨0, by omega⟩ ⟨σ, by omega⟩ *
          ((σ : ℝ) * j * ((shellP b j σ).card : ℝ) * (p ^ (j - 1) * q ^ (σ - j))) :=
        le_mul_of_one_le_right hker0 hkey
    _ = ((σ : ℝ) * j / p) * (p ^ j * q ^ (σ - j) *
          ker (fun r (x y : Fin (σ + 1)) => oddW b m d s lam r x y) 0 (j / 2)
            ⟨0, by omega⟩ ⟨σ, by omega⟩) *
          ((shellP b j σ).card : ℝ) := by
        rw [hpj]; field_simp
    _ = _ := by rw [h3]

/-- **Window form of the bridge.**  If every `K`-block window of the geometric kernel has mass at
most `M` from every state, and the final `ρ` blocks have mass at most `Mrem`, then
`∑_P s^{N_odd} ≤ (σ j / p) · M^W · Mrem · |P_σ|` where `j/2 = W K + ρ`. -/
theorem sum_pow_nodd_le_windows {j σ m K W ρ : ℕ} {d s M Mrem : ℝ} {lam : ℕ} (hj : 2 ≤ j)
    (hj2 : 2 * (j / 2) = j) (hchord : ∀ i ≤ j, ∀ p : ℕ, j * p ≤ i * b j → p ≤ b i)
    (hjσ : j < σ) (hσ : σ ≤ b j) (hs : 0 ≤ s) (hR : j / 2 = W * K + ρ)
    (hwin : ∀ (l : ℕ) (y : Fin (σ + 1)),
      LocalWindow.val (geoW (((j : ℝ) - 1) / ((σ : ℝ) - 1)) (((σ : ℝ) - j) / ((σ : ℝ) - 1))
        (oddW b m d s lam) σ) l K y ≤ M)
    (hrem : ∀ y : Fin (σ + 1),
      LocalWindow.val (geoW (((j : ℝ) - 1) / ((σ : ℝ) - 1)) (((σ : ℝ) - j) / ((σ : ℝ) - 1))
        (oddW b m d s lam) σ) (W * K) ρ y ≤ Mrem) (hMrem : 0 ≤ Mrem) :
    ∑ P ∈ shellP b j σ, s ^ Nodd b m d lam P ≤
      ((σ : ℝ) * j / (((j : ℝ) - 1) / ((σ : ℝ) - 1))) * (M ^ W * Mrem) *
        ((shellP b j σ).card : ℝ) := by
  set p : ℝ := ((j : ℝ) - 1) / ((σ : ℝ) - 1)
  set q : ℝ := ((σ : ℝ) - j) / ((σ : ℝ) - 1)
  have hσ1 : (1 : ℝ) < σ := by exact_mod_cast (by omega : 1 < σ)
  have hj1 : (1 : ℝ) < j := by exact_mod_cast (by omega : 1 < j)
  have hjσr : (j : ℝ) < σ := by exact_mod_cast hjσ
  have hp0 : 0 < p := div_pos (by linarith) (by linarith)
  have hq0 : 0 < q := div_pos (by linarith) (by linarith)
  have hw : ∀ l (x y : Fin (σ + 1)), 0 ≤ geoW p q (oddW b m d s lam) σ l x y := fun l x y => by
    unfold geoW; have := oddW_nonneg b (m := m) (d := d) (lam := lam) hs l x y; positivity
  have hbr := sum_pow_nodd_le_geo b (m := m) (d := d) (lam := lam) hj hj2 hchord hjσ hσ hs
  have hkv : ker (geoW p q (oddW b m d s lam) σ) 0 (j / 2) ⟨0, by omega⟩ ⟨σ, by omega⟩ ≤
      LocalWindow.val (geoW p q (oddW b m d s lam) σ) 0 (j / 2) ⟨0, by omega⟩ := by
    unfold LocalWindow.val
    exact single_le_sum (fun y _ => ker_nonneg hw _ _ _ y) (mem_univ _)
  have hval := val_le_of_window_rem hw hwin hrem hMrem ⟨0, by omega⟩
  rw [← hR] at hval
  have hc : (0 : ℝ) ≤ (σ : ℝ) * j / p := by positivity
  have hP : (0 : ℝ) ≤ ((shellP b j σ).card : ℝ) := Nat.cast_nonneg _
  calc _ ≤ _ := hbr
    _ ≤ _ := by gcongr; exact hkv.trans hval

end PressureBridge
end EOC
