import EOC.GoodAngles
import EOC.BlockCube

/-!
# Instantiating the block-cube hypothesis `GoodAngles.BlockCubeHyp`

* `norm_sq_le_classAvg` — abstract **block-cube bound**: if a finite exponential sum over `T` is
  split into classes, and every class sum factors as `(class size) · ∏_{r<R} W c r`, then
  `‖∑_T e(θ)‖² ≤ |T|² · (∑_c n_c ∏_r W c r²) / ∑_c n_c`.  (Class Cauchy–Schwarz.)
* `ClassProduct` — a class decomposition in which every class is in bijection (through a choice
  map `π : ι → (Fin R → ℕ)`) with a product set `∏_r B c r`, and the phase is additive over the
  blocks (up to integers and a class constant).  `norm_class_sum_eq` — then each class sum factors
  with `W c r = ‖∑_{x ∈ B c r} e(φ c r x)‖ / |B c r|`, and `norm_sq_le_of_classProduct` gives the
  block-cube bound.
* `BlockDecomposition` — the same data for the prefix shell `P_σ` with λ-independent classes and
  choice sets and a λ-dependent additive phase decomposition; `blockCubeHyp_of_decomposition`
  proves `GoodAngles.BlockCubeHyp` from it.
* `trivialDecomposition` / `blockCubeHyp_trivial` — an unconditional (but vacuous) instance: every
  word its own class, zero blocks.
* `pairDecomposition` / `blockCubeHyp_pair` — an unconditional, nontrivial instance (block length
  L = 2): coarse class = the even prefix sums `S_0, S_2, …`; block `r` = digits `2r, 2r+1` with
  internal configuration the odd prefix sum `S_{2r+1} ∈ (S_{2r}, S_{2r+2})`, `S_{2r+1} ≤ b(2r+1)`;
  block phase = the Collatz step phase at index `2r+1` (via `ee_yPrime_eq`, the per-word form of
  `Psi_eq_pathProduct`, and `prod_range_even_odd`).  The word ↔ (class, choices) bijection is
  proved (`recW`, `pair_inj`, `pairπ_mem`, `recW_mem`).  L = 3 blocks are not instantiated.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace BlockCubeInstance

open Finset SwapBound TwistExpansion PrefixCollision WeightedChain ShellDecomposition CapacityBounds

/-! ## 1. Abstract block-cube bound from a class factorization -/

section Abstract

variable {ι β : Type*} [DecidableEq β]

/-- Class sizes. -/
def nCls (T : Finset ι) (κ : ι → β) (c : β) : ℝ := ((T.filter (fun i => κ i = c)).card : ℝ)

theorem sum_nCls (T : Finset ι) (κ : ι → β) : ∑ c ∈ T.image κ, nCls T κ c = T.card := by
  unfold nCls
  rw [← Nat.cast_sum, ← card_eq_sum_card_fiberwise (fun i hi => mem_image_of_mem κ hi)]

theorem nCls_pos {T : Finset ι} {κ : ι → β} {c : β} (hc : c ∈ T.image κ) : 0 < nCls T κ c := by
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hc
  exact Nat.cast_pos.mpr (card_pos.mpr ⟨i, mem_filter.mpr ⟨hi, rfl⟩⟩)

/-- **Abstract block-cube bound.** -/
theorem norm_sq_le_classAvg (T : Finset ι) (κ : ι → β) (θ : ι → ℝ) (R : ℕ) (W : β → ℕ → ℝ)
    (hfac : ∀ c ∈ T.image κ,
      ‖∑ i ∈ T.filter (fun i => κ i = c), ee (θ i)‖ = nCls T κ c * ∏ r ∈ range R, W c r) :
    ‖∑ i ∈ T, ee (θ i)‖ ^ 2 ≤
      (T.card : ℝ) ^ 2 *
        ((∑ c ∈ T.image κ, nCls T κ c * ∏ r ∈ range R, W c r ^ 2) /
          ∑ c ∈ T.image κ, nCls T κ c) := by
  have hcs := BlockCube.norm_sq_sum_le_classes T κ θ
  have hterm : ∀ c ∈ T.image κ,
      ‖∑ i ∈ T.filter (fun i => κ i = c), ee (θ i)‖ ^ 2 /
          ((T.filter (fun i => κ i = c)).card : ℝ) =
        nCls T κ c * ∏ r ∈ range R, W c r ^ 2 := by
    intro c hc
    have hn := nCls_pos hc
    rw [hfac c hc, mul_pow, ← prod_pow]
    change nCls T κ c ^ 2 * _ / nCls T κ c = _
    field_simp
  rw [sum_congr rfl hterm] at hcs
  rw [sum_nCls]
  rcases (Nat.cast_nonneg T.card : (0 : ℝ) ≤ T.card).eq_or_lt with h0 | hpos
  · have hTe : T = ∅ := card_eq_zero.mp (by exact_mod_cast h0.symm)
    subst hTe; simp
  · calc ‖∑ i ∈ T, ee (θ i)‖ ^ 2
        ≤ (T.card : ℝ) * ∑ c ∈ T.image κ, nCls T κ c * ∏ r ∈ range R, W c r ^ 2 := hcs
      _ = (T.card : ℝ) ^ 2 *
            ((∑ c ∈ T.image κ, nCls T κ c * ∏ r ∈ range R, W c r ^ 2) / (T.card : ℝ)) := by
          field_simp

/-! ## 2. Product classes -/

/-- A class decomposition in which every class is (via `π`) a product set `∏_{r<R} B c r`, and
the phase is additive over the blocks, up to a class constant and integers. -/
structure ClassProduct (T : Finset ι) (θ : ι → ℝ) (R : ℕ) where
  κ : ι → β
  B : β → ℕ → Finset ℕ
  φ : β → ℕ → ℕ → ℝ
  θ0 : β → ℝ
  π : ι → Fin R → ℕ
  inj : ∀ c ∈ T.image κ, Set.InjOn π ↑(T.filter (fun i => κ i = c))
  image_eq : ∀ c ∈ T.image κ,
    (T.filter (fun i => κ i = c)).image π = Fintype.piFinset (fun r : Fin R => B c r)
  phase : ∀ i ∈ T, ee (θ i) = ee (θ0 (κ i)) * ∏ r : Fin R, ee (φ (κ i) r (π i r))

/-- The normalized block factor. -/
noncomputable def Wfac (B : β → ℕ → Finset ℕ) (φ : β → ℕ → ℕ → ℝ) (c : β) (r : ℕ) : ℝ :=
  ‖∑ x ∈ B c r, ee (φ c r x)‖ / ((B c r).card : ℝ)

theorem ee_add_int (x : ℝ) (z : ℤ) : ee (x + z) = ee x := by
  rw [ee_add, ee_int, mul_one]

/-- **Class factorization.** Each product class sum factors. -/
theorem norm_class_sum_eq {T : Finset ι} {θ : ι → ℝ} {R : ℕ}
    (D : ClassProduct (β := β) T θ R) {c : β} (hc : c ∈ T.image D.κ) :
    ‖∑ i ∈ T.filter (fun i => D.κ i = c), ee (θ i)‖ =
      nCls T D.κ c * ∏ r ∈ range R, Wfac D.B D.φ c r := by
  set S := T.filter (fun i => D.κ i = c)
  -- rewrite phases
  have hph : ∀ i ∈ S, ee (θ i) = ee (D.θ0 c) * ee (∑ r : Fin R, D.φ c r (D.π i r)) := by
    intro i hi
    have hiT : i ∈ T := (mem_filter.mp hi).1
    have hκ : D.κ i = c := (mem_filter.mp hi).2
    rw [D.phase i hiT, hκ, BlockCube.ee_sum]
  have hsum : ∑ i ∈ S, ee (θ i) =
      ee (D.θ0 c) * ∑ f ∈ Fintype.piFinset (fun r : Fin R => D.B c r),
        ee (∑ r : Fin R, D.φ c r (f r)) := by
    rw [sum_congr rfl hph, ← mul_sum, ← D.image_eq c hc,
      sum_image (fun x hx y hy h => D.inj c hc hx hy h)]
  have hcard : (S.card : ℝ) = ∏ r : Fin R, ((D.B c r).card : ℝ) := by
    have h1 : S.card = (Fintype.piFinset (fun r : Fin R => D.B c r)).card := by
      rw [← D.image_eq c hc, card_image_of_injOn (D.inj c hc)]
    rw [h1, Fintype.card_piFinset]; push_cast; rfl
  have hne : ∀ r : Fin R, (D.B c r).Nonempty := by
    intro r
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hc
    have hiS : i ∈ S := mem_filter.mpr ⟨hi, rfl⟩
    have hmem : D.π i ∈ Fintype.piFinset (fun r : Fin R => D.B (D.κ i) r) := by
      rw [← D.image_eq _ hc]; exact mem_image_of_mem _ hiS
    exact ⟨D.π i r, Fintype.mem_piFinset.mp hmem r⟩
  rw [hsum, norm_mul, SwapBound.norm_ee, one_mul,
    BlockCube.norm_sum_piFinset_eq_prod (fun r : Fin R => D.B c r) (fun r x => D.φ c r x)]
  unfold nCls; change _ = (S.card : ℝ) * _
  rw [hcard, ← Fin.prod_univ_eq_prod_range (fun r => Wfac D.B D.φ c r), ← prod_mul_distrib]
  refine prod_congr rfl fun r _ => ?_
  have hpos : (0 : ℝ) < ((D.B c r).card : ℝ) := Nat.cast_pos.mpr (card_pos.mpr (hne r))
  unfold Wfac
  field_simp

/-- **Block-cube bound for a product class decomposition.** -/
theorem norm_sq_le_of_classProduct {T : Finset ι} {θ : ι → ℝ} {R : ℕ}
    (D : ClassProduct (β := β) T θ R) :
    ‖∑ i ∈ T, ee (θ i)‖ ^ 2 ≤
      (T.card : ℝ) ^ 2 *
        ((∑ c ∈ T.image D.κ, nCls T D.κ c * ∏ r ∈ range R, Wfac D.B D.φ c r ^ 2) /
          ∑ c ∈ T.image D.κ, nCls T D.κ c) :=
  norm_sq_le_classAvg T D.κ θ R (Wfac D.B D.φ) fun c hc => norm_class_sum_eq D hc

end Abstract

/-! ## 3. The prefix shell: `BlockDecomposition ⇒ BlockCubeHyp` -/

section Shell

variable (b : ℕ → ℕ)

/-- A block decomposition of the prefix shell `P_σ` with λ-independent classes `κ`, choice sets `B`
and choice map `π`, together with, for every frequency, an additive decomposition of the phase
`λ y'_P / 2^m` over the blocks (up to a class constant and integers). -/
structure BlockDecomposition {β : Type*} [DecidableEq β] (j0 σ t R : ℕ) where
  κ : FiniteValuationWord j0 → β
  B : β → ℕ → Finset ℕ
  π : FiniteValuationWord j0 → Fin R → ℕ
  φ : ℕ → β → ℕ → ℕ → ℝ
  θ0 : ℕ → β → ℝ
  inj : ∀ c ∈ (shellP b j0 σ).image κ,
    Set.InjOn π ↑((shellP b j0 σ).filter (fun P => κ P = c))
  image_eq : ∀ c ∈ (shellP b j0 σ).image κ,
    ((shellP b j0 σ).filter (fun P => κ P = c)).image π =
      Fintype.piFinset (fun r : Fin R => B c r)
  phase : ∀ lam : ℕ, ∀ P ∈ shellP b j0 σ,
    ee ((lam : ℝ) * (yPrime j0 σ t P : ℕ) / 2 ^ (σ + 1 + t)) =
      ee (θ0 lam (κ P)) * ∏ r : Fin R, ee (φ lam (κ P) r (π P r))

/-- The `ClassProduct` at a fixed frequency. -/
def BlockDecomposition.at {β : Type*} [DecidableEq β] {j0 σ t R : ℕ}
    (D : BlockDecomposition (β := β) b j0 σ t R) (lam : ℕ) :
    ClassProduct (β := β) (shellP b j0 σ)
      (fun P => (lam : ℝ) * (yPrime j0 σ t P : ℕ) / 2 ^ (σ + 1 + t)) R where
  κ := D.κ
  B := D.B
  φ := D.φ lam
  θ0 := D.θ0 lam
  π := D.π
  inj := D.inj
  image_eq := D.image_eq
  phase := D.phase lam

/-- **`BlockCubeHyp` from a block decomposition.** Classes `T = P_σ.image κ`, weights = class
sizes, block factors `W λ c r = ‖∑_{x ∈ B c r} e(φ λ c r x)‖ / |B c r|`. -/
theorem blockCubeHyp_of_decomposition {β : Type*} [DecidableEq β] {j0 σ t R : ℕ}
    (D : BlockDecomposition (β := β) b j0 σ t R) (U : ℕ) (hne : (shellP b j0 σ).Nonempty) :
    GoodAngles.BlockCubeHyp b j0 σ t U ((shellP b j0 σ).image D.κ)
      (nCls (shellP b j0 σ) D.κ) (fun lam => Wfac D.B (D.φ lam)) R := by
  refine ⟨?_, ?_⟩
  · rw [sum_nCls]; exact_mod_cast card_pos.mpr hne
  · intro u _ lam _
    have h := norm_sq_le_of_classProduct (D.at b lam)
    unfold Psi
    exact h

/-! ## 4. The trivial (vacuous) decomposition -/

/-- Every word its own class, zero blocks: always a valid decomposition (it only yields the trivial
bound `‖Ψ‖² ≤ |P_σ|²`). -/
noncomputable def trivialDecomposition (j0 σ t : ℕ) :
    BlockDecomposition (β := FiniteValuationWord j0) b j0 σ t 0 where
  κ := id
  B := fun _ _ => ∅
  π := fun _ => Fin.elim0
  φ := fun _ _ _ _ => 0
  θ0 := fun lam P => (lam : ℝ) * (yPrime j0 σ t P : ℕ) / 2 ^ (σ + 1 + t)
  inj := by
    intro c _ x hx y hy _
    simp only [coe_filter, Set.mem_setOf_eq, id] at hx hy
    rw [hx.2, hy.2]
  image_eq := by
    intro c hc
    obtain ⟨P, hP, rfl⟩ := mem_image.mp hc
    ext f
    simp only [mem_image, mem_filter, id, Fintype.mem_piFinset, IsEmpty.forall_iff, iff_true]
    exact ⟨P, ⟨hP, rfl⟩, funext fun r => r.elim0⟩
  phase := by
    intro lam P _
    simp

theorem blockCubeHyp_trivial (j0 σ t U : ℕ) (hne : (shellP b j0 σ).Nonempty) :
    GoodAngles.BlockCubeHyp b j0 σ t U ((shellP b j0 σ).image id)
      (nCls (shellP b j0 σ) id) (fun lam => Wfac (trivialDecomposition b j0 σ t).B
        ((trivialDecomposition b j0 σ t).φ lam)) 0 :=
  blockCubeHyp_of_decomposition b (trivialDecomposition b j0 σ t) U hne

/-! ## 5. Word-level lemmas -/

theorem prefixSum_zero' {N : ℕ} (w : FiniteValuationWord N) : w.prefixSum 0 = 0 := by
  simp [FiniteValuationWord.prefixSum]

theorem prefixSum_succ' {N : ℕ} (w : FiniteValuationWord N) {k : ℕ} (hk : k < N) :
    w.prefixSum (k + 1) = w.prefixSum k + w ⟨k, hk⟩ := by
  rw [FiniteValuationWord.prefixSum, List.sum_take_succ _ _ (by simpa using hk)]
  simp [FiniteValuationWord.prefixSum]

/-- Two words with the same prefix sums at every `j ≤ N` are equal. -/
theorem eq_of_prefixSum_eq {N : ℕ} {w v : FiniteValuationWord N}
    (h : ∀ j ≤ N, w.prefixSum j = v.prefixSum j) : w = v := by
  funext k
  have h1 := prefixSum_succ' w k.2
  have h2 := prefixSum_succ' v k.2
  have e1 := h (k + 1) k.2
  have e0 := h k (le_of_lt k.2)
  simp only [Fin.eta] at h1 h2
  omega

/-- Per-word form of `Psi_eq_pathProduct`. -/
theorem ee_yPrime_eq (j0 σ t lam : ℕ) (P : FiniteValuationWord j0) :
    SwapBound.ee ((lam : ℝ) * (yPrime j0 σ t P : ℕ) / 2 ^ (σ + 1 + t)) =
      SwapBound.ee ((lam : ℝ) * cSig (σ + 1 + t) j0 σ / 2 ^ (σ + 1 + t)) *
        ∏ i ∈ range j0,
          SwapBound.ee (SwapCollatz.collatzPhase lam (σ + 1 + t) (uInv (σ + 1 + t)) i
            (P.prefixSum i)) := by
  simp only [SwapCollatz.collatzPhase, ee_neg_fract]
  rw [prod_ee]
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

/-- Splitting a product over `range n` into even and odd indices. -/
theorem prod_range_even_odd {M : Type*} [CommMonoid M] (g : ℕ → M) (n : ℕ) :
    ∏ i ∈ range n, g i =
      (∏ k ∈ range ((n + 1) / 2), g (2 * k)) * ∏ r ∈ range (n / 2), g (2 * r + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, ih]
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- n = k + k: new index n is even
      have h1 : (n + 1 + 1) / 2 = (n + 1) / 2 + 1 := by omega
      have h2 : (n + 1) / 2 = n / 2 := by omega
      have h3 : 2 * ((n + 1) / 2) = n := by omega
      rw [h1, prod_range_succ, h3, show (n + 1) / 2 = n / 2 from h2]
      exact mul_right_comm _ _ _
    · -- n = 2k+1: new index n is odd
      have h1 : (n + 1 + 1) / 2 = (n + 1) / 2 := by omega
      have h2 : (n + 1) / 2 = n / 2 + 1 := by omega
      have h3 : 2 * (n / 2) + 1 = n := by omega
      rw [h1, h2, prod_range_succ (fun r => g (2 * r + 1)), h3]
      exact mul_assoc _ _ _

/-! ## 6. A nontrivial instance: coarse classes = even prefix sums, blocks = digit pairs -/

/-- Coarse class: all even-indexed prefix sums `S_0, S_2, S_4, …` (odd slots recorded as `0`). -/
def pairκ (j0 : ℕ) (P : FiniteValuationWord j0) : Fin (j0 + 1) → ℕ :=
  fun j => if (j : ℕ) % 2 = 0 then P.prefixSum j else 0

/-- Internal configuration of pair-block `r`: the odd prefix sum `S_{2r+1}`. -/
def pairπ (j0 : ℕ) (P : FiniteValuationWord j0) : Fin (j0 / 2) → ℕ :=
  fun r => P.prefixSum (2 * (r : ℕ) + 1)

/-- Reading a coarse class at index `j`. -/
def cget {j0 : ℕ} (c : Fin (j0 + 1) → ℕ) (j : ℕ) : ℕ := if h : j < j0 + 1 then c ⟨j, h⟩ else 0

/-- Admissible internal prefix sums of pair-block `r`: `S_{2r} < x < S_{2r+2}`, `x ≤ b(2r+1)`. -/
def pairB {j0 : ℕ} (c : Fin (j0 + 1) → ℕ) (r : ℕ) : Finset ℕ :=
  (Ioo (cget c (2 * r)) (cget c (2 * r + 2))).filter (fun x => x ≤ b (2 * r + 1))

theorem cget_pairκ {j0 : ℕ} (P : FiniteValuationWord j0) {j : ℕ} (hj : j ≤ j0) (he : j % 2 = 0) :
    cget (pairκ j0 P) j = P.prefixSum j := by
  simp [cget, pairκ, Nat.lt_succ_of_le hj, he]

theorem prefixSum_lt_succ {N : ℕ} {w : FiniteValuationWord N} (hw : w.Positive) {k : ℕ}
    (hk : k < N) : w.prefixSum k < w.prefixSum (k + 1) := by
  rw [prefixSum_succ' w hk]; have := hw ⟨k, hk⟩; omega

theorem mem_shellP_iff {j0 σ : ℕ} (hj : 1 ≤ j0) {P : FiniteValuationWord j0} :
    P ∈ shellP b j0 σ ↔ P.Positive ∧ BarrierConfined b P ∧ P.total = σ := by
  rw [shellP, mem_filter, mem_confinedWords hj, and_assoc]

section Pair

variable {j0 σ : ℕ}

/-- Reconstructed prefix sums from a class representative `P0` and a choice `f`. -/
def recT (P0 : FiniteValuationWord j0) (f : Fin (j0 / 2) → ℕ) (j : ℕ) : ℕ :=
  if h : j % 2 = 1 ∧ j < j0 then f ⟨(j - 1) / 2, by omega⟩ else P0.prefixSum j

/-- The reconstructed word. -/
def recW (P0 : FiniteValuationWord j0) (f : Fin (j0 / 2) → ℕ) : FiniteValuationWord j0 :=
  fun i => recT P0 f ((i : ℕ) + 1) - recT P0 f i

theorem recT_lt (hj : 1 ≤ j0) {P0 : FiniteValuationWord j0} (hP0 : P0 ∈ shellP b j0 σ)
    {f : Fin (j0 / 2) → ℕ} (hf : f ∈ Fintype.piFinset (fun r : Fin (j0 / 2) => pairB b (pairκ j0 P0) r))
    {j : ℕ} (hjl : j < j0) : recT P0 f j < recT P0 f (j + 1) := by
  have hpos := ((mem_shellP_iff b hj).mp hP0).1
  have hmem := fun r => Fintype.mem_piFinset.mp hf r
  rcases Nat.mod_two_eq_zero_or_one j with he | ho
  · by_cases hj1 : j + 1 < j0
    · -- j even, j+1 odd < j0
      have hr : j / 2 < j0 / 2 := by omega
      have hB := hmem ⟨j / 2, hr⟩
      simp only [pairB, mem_filter, mem_Ioo] at hB
      have e1 : recT P0 f j = P0.prefixSum j := by
        unfold recT; rw [dif_neg (by omega)]
      have e2 : recT P0 f (j + 1) = f ⟨j / 2, hr⟩ := by
        unfold recT; rw [dif_pos (by omega)]; congr 2 <;> omega
      rw [e1, e2]
      have := hB.1.1
      rw [show 2 * (j / 2) = j by omega, cget_pairκ P0 (by omega) he] at this
      exact this
    · -- j even, j+1 = j0
      have e1 : recT P0 f j = P0.prefixSum j := by
        unfold recT; rw [dif_neg (by omega)]
      have e2 : recT P0 f (j + 1) = P0.prefixSum (j + 1) := by
        unfold recT; rw [dif_neg (by omega)]
      rw [e1, e2]; exact prefixSum_lt_succ hpos hjl
  · -- j odd < j0, j+1 even
    have hr : (j - 1) / 2 < j0 / 2 := by omega
    have hB := hmem ⟨(j - 1) / 2, hr⟩
    simp only [pairB, mem_filter, mem_Ioo] at hB
    have e1 : recT P0 f j = f ⟨(j - 1) / 2, hr⟩ := by
      unfold recT; rw [dif_pos ⟨ho, hjl⟩]
    have e2 : recT P0 f (j + 1) = P0.prefixSum (j + 1) := by
      unfold recT; rw [dif_neg (by omega)]
    rw [e1, e2]
    have := hB.1.2
    rw [show 2 * ((j - 1) / 2) + 2 = j + 1 by omega,
      cget_pairκ P0 (by omega) (by omega)] at this
    exact this

theorem prefixSum_recW (hj : 1 ≤ j0) {P0 : FiniteValuationWord j0} (hP0 : P0 ∈ shellP b j0 σ)
    {f : Fin (j0 / 2) → ℕ} (hf : f ∈ Fintype.piFinset (fun r : Fin (j0 / 2) => pairB b (pairκ j0 P0) r))
    {j : ℕ} (hjl : j ≤ j0) : (recW P0 f).prefixSum j = recT P0 f j := by
  induction j with
  | zero =>
    rw [prefixSum_zero']
    unfold recT; rw [dif_neg (by omega), prefixSum_zero']
  | succ k ih =>
    rw [prefixSum_succ' _ (by omega), ih (by omega)]
    have hlt := recT_lt b hj hP0 hf (j := k) (by omega)
    simp only [recW]
    omega

theorem recW_mem (hj : 1 ≤ j0) {P0 : FiniteValuationWord j0} (hP0 : P0 ∈ shellP b j0 σ)
    {f : Fin (j0 / 2) → ℕ} (hf : f ∈ Fintype.piFinset (fun r : Fin (j0 / 2) => pairB b (pairκ j0 P0) r)) :
    recW P0 f ∈ shellP b j0 σ := by
  obtain ⟨_, hbar, htot⟩ := (mem_shellP_iff b hj).mp hP0
  have hmem := fun r => Fintype.mem_piFinset.mp hf r
  refine (mem_shellP_iff b hj).mpr ⟨?_, ?_, ?_⟩
  · intro i
    have := recT_lt b hj hP0 hf (j := i) i.2
    simp only [recW]; omega
  · intro j hjI
    have hjI' := mem_Icc.mp hjI
    rw [prefixSum_recW b hj hP0 hf hjI'.2]
    unfold recT
    split_ifs with h
    · have hr : (j - 1) / 2 < j0 / 2 := by omega
      have hB := hmem ⟨(j - 1) / 2, hr⟩
      simp only [pairB, mem_filter] at hB
      rw [show 2 * ((j - 1) / 2) + 1 = j by omega] at hB
      exact hB.2
    · exact hbar j hjI
  · rw [FiniteValuationWord.total, prefixSum_recW b hj hP0 hf le_rfl]
    unfold recT; rw [dif_neg (by omega)]; exact htot

theorem pairκ_recW (hj : 1 ≤ j0) {P0 : FiniteValuationWord j0} (hP0 : P0 ∈ shellP b j0 σ)
    {f : Fin (j0 / 2) → ℕ} (hf : f ∈ Fintype.piFinset (fun r : Fin (j0 / 2) => pairB b (pairκ j0 P0) r)) :
    pairκ j0 (recW P0 f) = pairκ j0 P0 := by
  funext j
  simp only [pairκ]
  split_ifs with he
  · rw [prefixSum_recW b hj hP0 hf (by omega)]
    unfold recT; rw [dif_neg (by omega)]
  · rfl

theorem pairπ_recW (hj : 1 ≤ j0) {P0 : FiniteValuationWord j0} (hP0 : P0 ∈ shellP b j0 σ)
    {f : Fin (j0 / 2) → ℕ} (hf : f ∈ Fintype.piFinset (fun r : Fin (j0 / 2) => pairB b (pairκ j0 P0) r)) :
    pairπ j0 (recW P0 f) = f := by
  funext r
  have hr := r.2
  simp only [pairπ]
  rw [prefixSum_recW b hj hP0 hf (by omega)]
  unfold recT; rw [dif_pos (by omega)]
  first | (congr 1; ext; simp; done) | (congr 1; ext; simp; omega)

/-- Membership of the choice in the product set. -/
theorem pairπ_mem (hj : 1 ≤ j0) {P : FiniteValuationWord j0} (hP : P ∈ shellP b j0 σ) :
    pairπ j0 P ∈ Fintype.piFinset (fun r : Fin (j0 / 2) => pairB b (pairκ j0 P) r) := by
  obtain ⟨hpos, hbar, _⟩ := (mem_shellP_iff b hj).mp hP
  refine Fintype.mem_piFinset.mpr fun r => ?_
  have hr := r.2
  simp only [pairB, pairπ, mem_filter, mem_Ioo]
  rw [cget_pairκ P (by omega) (by omega), cget_pairκ P (by omega) (by omega)]
  refine ⟨⟨prefixSum_lt_succ hpos (by omega), ?_⟩, hbar _ (mem_Icc.mpr ⟨by omega, by omega⟩)⟩
  exact prefixSum_lt_succ hpos (by omega)

/-- Words with the same coarse class and the same internal choices coincide. -/
theorem pair_inj (hj : 1 ≤ j0) {P Q : FiniteValuationWord j0} (hP : P ∈ shellP b j0 σ)
    (hQ : Q ∈ shellP b j0 σ) (hκ : pairκ j0 P = pairκ j0 Q) (hπ : pairπ j0 P = pairπ j0 Q) :
    P = Q := by
  have htP := ((mem_shellP_iff b hj).mp hP).2.2
  have htQ := ((mem_shellP_iff b hj).mp hQ).2.2
  refine eq_of_prefixSum_eq fun j hjl => ?_
  rcases Nat.mod_two_eq_zero_or_one j with he | ho
  · have := congrFun hκ ⟨j, by omega⟩
    simpa [pairκ, he] using this
  · by_cases hlt : j < j0
    · have := congrFun hπ ⟨(j - 1) / 2, by omega⟩
      simp only [pairπ] at this
      rwa [show 2 * ((j - 1) / 2) + 1 = j by omega] at this
    · have hjj : j = j0 := by omega
      subst hjj
      rw [← FiniteValuationWord.total, ← FiniteValuationWord.total, htP, htQ]

end Pair

/-- **The pair decomposition** of the prefix shell (`j0 ≥ 1`): coarse class = even prefix sums,
blocks = consecutive digit pairs with internal odd prefix sum, phase = Collatz path phases. -/
noncomputable def pairDecomposition (j0 σ t : ℕ) (hj : 1 ≤ j0) :
    BlockDecomposition (β := Fin (j0 + 1) → ℕ) b j0 σ t (j0 / 2) where
  κ := pairκ j0
  B := pairB b
  π := pairπ j0
  φ := fun lam _ r x => SwapCollatz.collatzPhase lam (σ + 1 + t) (uInv (σ + 1 + t)) (2 * r + 1) x
  θ0 := fun lam c => (lam : ℝ) * cSig (σ + 1 + t) j0 σ / 2 ^ (σ + 1 + t) +
    ∑ k ∈ range ((j0 + 1) / 2),
      SwapCollatz.collatzPhase lam (σ + 1 + t) (uInv (σ + 1 + t)) (2 * k) (cget c (2 * k))
  inj := by
    intro c _ P hP Q hQ h
    simp only [coe_filter, Set.mem_setOf_eq] at hP hQ
    exact pair_inj b hj hP.1 hQ.1 (hP.2.trans hQ.2.symm) h
  image_eq := by
    intro c hc
    obtain ⟨P0, hP0, rfl⟩ := mem_image.mp hc
    ext f
    simp only [mem_image, mem_filter]
    constructor
    · rintro ⟨P, ⟨hP, hκ⟩, rfl⟩
      rw [← hκ]; exact pairπ_mem b hj hP
    · intro hf
      exact ⟨recW P0 f, ⟨recW_mem b hj hP0 hf, pairκ_recW b hj hP0 hf⟩, pairπ_recW b hj hP0 hf⟩
  phase := by
    intro lam P _
    rw [ee_yPrime_eq, prod_range_even_odd, ← mul_assoc, ee_add, ← prod_ee]
    congr 1
    · congr 1
      refine prod_congr rfl fun k hk => ?_
      rw [cget_pairκ P (by have := mem_range.mp hk; omega) (by omega)]
    · rw [← Fin.prod_univ_eq_prod_range
        (fun r => SwapBound.ee (SwapCollatz.collatzPhase lam (σ + 1 + t) (uInv (σ + 1 + t))
          (2 * r + 1) (P.prefixSum (2 * r + 1))))]
      rfl

/-- **`BlockCubeHyp` for `Ψ` along coarse pair classes (unconditional).** For `j0 ≥ 1` and a
nonempty prefix shell: `‖Ψ λ‖² ≤ |P_σ|² · (∑_c |c| ∏_{r < j0/2} W λ c r²) / ∑_c |c|`, where `c`
ranges over the coarse classes (even prefix sums) and
`W λ c r = ‖∑_{x ∈ B c r} e(φ_{2r+1}(x))‖ / |B c r|` is the normalized internal sum of pair-block
`r` (internal odd prefix sum `x`). -/
theorem blockCubeHyp_pair (j0 σ t U : ℕ) (hj : 1 ≤ j0) (hne : (shellP b j0 σ).Nonempty) :
    GoodAngles.BlockCubeHyp b j0 σ t U ((shellP b j0 σ).image (pairκ j0))
      (nCls (shellP b j0 σ) (pairκ j0))
      (fun lam => Wfac (pairB b) (fun _ r x =>
        SwapCollatz.collatzPhase lam (σ + 1 + t) (uInv (σ + 1 + t)) (2 * r + 1) x)) (j0 / 2) :=
  blockCubeHyp_of_decomposition b (pairDecomposition b j0 σ t hj) U hne

end Shell

end BlockCubeInstance
end EOC
