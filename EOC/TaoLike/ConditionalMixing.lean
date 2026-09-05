import EOC.TaoLike.ResidueTV
import EOC.TaoLike.TaoInterface
import EOC.TaoLike.Cylinder

/-!
# Conditional future valuation mixing (Milestone 5)

Composes the verified deterministic Collatz cylinder arithmetic (Milestones 1–3B) with the
external Tao mixing interface (Milestones 4–4B): conditioned on a realized valuation prefix
and a thick harmonic restart window, the conditional law of the *future* valuation vector
(the next `n` digits after the restarted state) is within an explicit `TaoMixingHypothesis`
error of the concrete iid `Geom(2)^n` law.

**EPISTEMIC STATUS.** This is FORMALLY VERIFIED *conditional on* the external
`TaoMixingHypothesis` interface (Milestones 4/4B) — Tao's Proposition 1.9 itself is **not**
proved here or anywhere in this repository. Every theorem in this file that consumes
`(tao : TaoMixingHypothesis)` inherits that external dependency explicitly through its
hypotheses; no custom `axiom` is introduced.
-/

namespace EOC
namespace TaoExternal

open Finset

/-! ### Conditional index weight over the harmonic restart window -/

/-- The normalized harmonic weight on the restart index `j`, for a window of length `Nwin`
starting at `kmin` inside a cylinder with base seed `r` and spacing `Dcyl`, normalized by the
total harmonic mass `W`. -/
noncomputable def conditionalIndexWeight (r Dcyl kmin Nwin : ℕ) (W : ℝ) (j : ℕ) : ℝ :=
  if j < Nwin then (1 / ((r : ℝ) + (Dcyl : ℝ) * ((kmin : ℝ) + j))) / W else 0

theorem conditionalIndexWeight_nonneg (r Dcyl kmin Nwin : ℕ) (W : ℝ) (hW : 0 < W)
    (hr : 0 < r) (j : ℕ) : 0 ≤ conditionalIndexWeight r Dcyl kmin Nwin W j := by
  unfold conditionalIndexWeight
  split_ifs
  · positivity
  · exact le_refl 0

theorem conditionalIndexWeight_support (r Dcyl kmin Nwin : ℕ) (W : ℝ) :
    Function.support (conditionalIndexWeight r Dcyl kmin Nwin W) ⊆ ↑(range Nwin) := by
  intro j hj
  by_contra hjr
  apply hj
  unfold conditionalIndexWeight
  rw [if_neg (by simpa using hjr)]

theorem conditionalIndexWeight_summable (r Dcyl kmin Nwin : ℕ) (W : ℝ) :
    Summable (conditionalIndexWeight r Dcyl kmin Nwin W) :=
  summable_of_hasFiniteSupport (Set.Finite.subset (Finset.finite_toSet (range Nwin))
    (conditionalIndexWeight_support r Dcyl kmin Nwin W))

/-- Given `W` is exactly the total harmonic mass of the window (as `conditional_residue_tv_eta_bound`
supplies), the index weight normalizes to `1`. -/
theorem conditionalIndexWeight_tsum_eq_one (r Dcyl kmin Nwin : ℕ) (W : ℝ) (hW : 0 < W)
    (hWdef : W = ∑ j ∈ range Nwin, (1 : ℝ) / ((r : ℝ) + (Dcyl : ℝ) * ((kmin : ℝ) + j))) :
    ∑' j, conditionalIndexWeight r Dcyl kmin Nwin W j = 1 := by
  rw [tsum_eq_sum' (conditionalIndexWeight_support r Dcyl kmin Nwin W)]
  have heq : ∀ j ∈ range Nwin, conditionalIndexWeight r Dcyl kmin Nwin W j
      = (1 / ((r : ℝ) + (Dcyl : ℝ) * ((kmin : ℝ) + j))) / W := by
    intro j hj
    unfold conditionalIndexWeight
    rw [if_pos (Finset.mem_range.mp hj)]
  rw [Finset.sum_congr rfl heq]
  have hdiv : ∀ j : ℕ, (1 : ℝ) / ((r : ℝ) + (Dcyl : ℝ) * ((kmin : ℝ) + j)) / W
      = (1 / ((r : ℝ) + (Dcyl : ℝ) * ((kmin : ℝ) + j))) * (1 / W) := by
    intro j; ring
  simp_rw [hdiv]
  rw [← Finset.sum_mul, ← hWdef]
  field_simp

/-! ### The conditional restart-state law -/

/-- The law of the restarted state `orbit m_j t` (via `cylinder_restart`'s formula
`C + 2*3^t*(kmin+j)`), induced by the normalized harmonic weight on the restart index `j`. -/
noncomputable def conditionalRestartLaw (r Dcyl kmin Nwin : ℕ) (W : ℝ) (C t : ℕ) : EventProb ℕ :=
  pushforward (genEventProb (conditionalIndexWeight r Dcyl kmin Nwin W))
    (fun j => C + 2 * 3 ^ t * (kmin + j))

theorem conditionalRestartLaw_univ (r Dcyl kmin Nwin : ℕ) (W : ℝ) (hW : 0 < W)
    (hWdef : W = ∑ j ∈ range Nwin, (1 : ℝ) / ((r : ℝ) + (Dcyl : ℝ) * ((kmin : ℝ) + j)))
    (C t : ℕ) :
    conditionalRestartLaw r Dcyl kmin Nwin W C t Set.univ = 1 := by
  unfold conditionalRestartLaw pushforward
  rw [Set.preimage_univ]
  exact genEventProb_univ _ (conditionalIndexWeight_tsum_eq_one r Dcyl kmin Nwin W hW hWdef)

/-- The restarted state `C + 2*3^t*(kmin+j)` is always odd when `C` is odd (as it is for
`C = orbit r t`, `t ≥ 1`), so the conditional restart law is supported entirely on odd
naturals — exactly `TaoMixingHypothesis`'s required hypothesis on `N`. -/
theorem conditionalRestartLaw_odd_support (r Dcyl kmin Nwin : ℕ) (W : ℝ) (C t : ℕ)
    (hCodd : Odd C) :
    conditionalRestartLaw r Dcyl kmin Nwin W C t {m : ℕ | ¬ Odd m} = 0 := by
  unfold conditionalRestartLaw pushforward
  have hpre : (fun j => C + 2 * 3 ^ t * (kmin + j)) ⁻¹' {m : ℕ | ¬ Odd m} = ∅ := by
    ext j
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
      not_not]
    have heven : Even (2 * 3 ^ t * (kmin + j)) := ⟨3 ^ t * (kmin + j), by ring⟩
    exact hCodd.add_even heven
  rw [hpre]
  exact genEventProb_empty _

/-! ### The conditional restart law's residue pushforward, made concrete -/

/-- The fiber-sum residue weight: the harmonic mass of restart indices `j < Nwin` whose
restarted state lands in residue class `v` modulo `2^Qres`. -/
noncomputable def conditionalResidueWeight (r Dcyl kmin Nwin : ℕ) (W : ℝ) (C t Qres : ℕ)
    (v : ZMod (2 ^ Qres)) : ℝ :=
  ∑ j ∈ range Nwin,
    if ((C + 2 * 3 ^ t * (kmin + j) : ℕ) : ZMod (2 ^ Qres)) = v
      then conditionalIndexWeight r Dcyl kmin Nwin W j else 0

/-- **Generic fiber-sum reindexing** for a finitely-supported weight generating an
`EventProb` on `ℕ`, pushed forward along a map into a finite type: the pushforward is again
`genEventProb`-shaped, generated by the fiber sums. This is the reusable engine behind
`conditionalRestartLaw_mod_eq` below. -/
theorem genEventProb_pushforward_fiber {β : Type*} [Fintype β] [DecidableEq β]
    (Nwin : ℕ) (w : ℕ → ℝ) (hsupp : Function.support w ⊆ ↑(range Nwin)) (F : ℕ → β) :
    pushforward (genEventProb w) F
      = genEventProb (fun v : β => ∑ j ∈ range Nwin, if F j = v then w j else 0) := by
  classical
  funext E
  show genEventProb w (F ⁻¹' E) = _
  unfold genEventProb
  have hstep1 : (∑' j, Set.indicator (F ⁻¹' E) w j)
      = ∑ j ∈ range Nwin, Set.indicator (F ⁻¹' E) w j := by
    apply tsum_eq_sum'
    intro j hj
    have hwne : w j ≠ 0 := by
      intro h0
      apply hj
      simp [Set.indicator, h0]
    exact hsupp hwne
  rw [hstep1]
  have hLHSeq : ∀ j ∈ range Nwin,
      Set.indicator (F ⁻¹' E) w j = if F j ∈ E then w j else 0 := by
    intro j _
    by_cases hj : F j ∈ E
    · simp [Set.indicator, hj]
    · simp [Set.indicator, hj]
  rw [Finset.sum_congr rfl hLHSeq]
  have hRHSeq : ∀ v : β, Set.indicator E
      (fun v => ∑ j ∈ range Nwin, if F j = v then w j else 0) v
      = if v ∈ E then (∑ j ∈ range Nwin, if F j = v then w j else 0) else 0 := by
    intro v
    by_cases hv : v ∈ E
    · simp [Set.indicator, hv]
    · simp [Set.indicator, hv]
  rw [tsum_fintype, Finset.sum_congr rfl (fun v _ => hRHSeq v)]
  have hswap : ∀ v : β,
      (if v ∈ E then (∑ j ∈ range Nwin, if F j = v then w j else 0) else 0)
      = ∑ j ∈ range Nwin, (if F j = v then (if v ∈ E then w j else 0) else 0) := by
    intro v
    by_cases hv : v ∈ E
    · simp [hv]
    · simp [hv]
  rw [Finset.sum_congr rfl (fun v _ => hswap v), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_ite_eq univ (F j) (fun v => if v ∈ E then w j else 0)]
  simp

/-- Pushforward composes along function composition. -/
theorem pushforward_comp {α β γ : Type*} (P : EventProb α) (f : α → β) (g : β → γ) :
    pushforward (pushforward P f) g = pushforward P (g ∘ f) := by
  funext E
  unfold pushforward
  rw [Set.preimage_comp]

/-- The mod-`2^Qres` pushforward of the conditional restart law is exactly the `genEventProb`
law generated by `conditionalResidueWeight` — this is what lets us apply the metric bridge
`event_discrepancy_le_taoL1TV` / compute `taoL1TV` explicitly, rather than reasoning about an
abstract pushforward. -/
theorem conditionalRestartLaw_mod_eq (r Dcyl kmin Nwin : ℕ) (W : ℝ) (C t Qres : ℕ) :
    pushforward (conditionalRestartLaw r Dcyl kmin Nwin W C t)
        (fun m : ℕ => (m : ZMod (2 ^ Qres)))
      = genEventProb (conditionalResidueWeight r Dcyl kmin Nwin W C t Qres) := by
  have hNZ : NeZero (2 ^ Qres) := ⟨by positivity⟩
  unfold conditionalRestartLaw
  rw [pushforward_comp]
  exact genEventProb_pushforward_fiber Nwin (conditionalIndexWeight r Dcyl kmin Nwin W)
    (conditionalIndexWeight_support r Dcyl kmin Nwin W) _

/-! ### Half-L1 (Milestone 3B) → full-L1 (Tao) conversion -/

/-- **The explicit factor-2 conversion.** For two `genEventProb` laws on `ZMod (2^Qres)`
supported only on the (image of the) odd residues, Tao's full-`Σ` metric `taoL1TV` equals
the sum over `oddResidues Qres` of the pointwise differences — with **no** leading `1/2`.
Since Milestone 3B's `dTV`-shaped quantities *do* carry a leading `1/2`, this is exactly
`taoL1TV = 2 * (Milestone-3B half-sum)`: the explicit factor of 2 the brief requires, not
hidden in a generic constant. -/
theorem taoL1TV_genEventProb_eq_odd_finsum (Qres : ℕ) (hQres : 1 ≤ Qres)
    (w1 w2 : ZMod (2 ^ Qres) → ℝ)
    (hw1_supp : ∀ v : ZMod (2 ^ Qres), w1 v ≠ 0 →
      v ∈ (oddResidues Qres).image (fun n : ℕ => (n : ZMod (2 ^ Qres))))
    (hw2_supp : ∀ v : ZMod (2 ^ Qres), w2 v ≠ 0 →
      v ∈ (oddResidues Qres).image (fun n : ℕ => (n : ZMod (2 ^ Qres)))) :
    taoL1TV (genEventProb w1) (genEventProb w2)
      = ∑ u ∈ oddResidues Qres, |w1 (u : ZMod (2 ^ Qres)) - w2 (u : ZMod (2 ^ Qres))| := by
  have hNZ : NeZero (2 ^ Qres) := ⟨by positivity⟩
  rw [taoL1TV_genEventProb, tsum_fintype]
  have hinj : Set.InjOn (fun n : ℕ => (n : ZMod (2 ^ Qres))) (oddResidues Qres) := by
    intro x hx y hy hxy
    have hxlt : x < 2 ^ Qres := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
    have hylt : y < 2 ^ Qres := Finset.mem_range.mp (Finset.mem_filter.mp hy).1
    have := congrArg ZMod.val hxy
    rwa [ZMod.val_cast_of_lt hxlt, ZMod.val_cast_of_lt hylt] at this
  have himg : ∑ u ∈ oddResidues Qres, |w1 (u : ZMod (2 ^ Qres)) - w2 (u : ZMod (2 ^ Qres))|
      = ∑ v ∈ (oddResidues Qres).image (fun n : ℕ => (n : ZMod (2 ^ Qres))), |w1 v - w2 v| :=
    (Finset.sum_image (f := fun v : ZMod (2 ^ Qres) => |w1 v - w2 v|) hinj).symm
  rw [himg]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  · intro v _ hv
    have hw1z : w1 v = 0 := by
      by_contra hne; exact hv (hw1_supp v hne)
    have hw2z : w2 v = 0 := by
      by_contra hne; exact hv (hw2_supp v hne)
    rw [hw1z, hw2z]
    simp

/-- Every odd natural has an odd-residue representative below `2^Qres` (`Qres ≥ 1`) with the
same class modulo `2^Qres`. -/
theorem exists_oddResidues_cast_eq (X Qres : ℕ) (hXodd : Odd X) (hQres : 1 ≤ Qres) :
    ∃ u ∈ oddResidues Qres, (u : ZMod (2 ^ Qres)) = (X : ZMod (2 ^ Qres)) := by
  have hNZ : NeZero (2 ^ Qres) := ⟨by positivity⟩
  set u := X % 2 ^ Qres with hu_def
  have hult : u < 2 ^ Qres := Nat.mod_lt _ (by positivity)
  have h2dvd : (2 : ℕ) ∣ 2 ^ Qres := dvd_pow_self 2 (by omega : Qres ≠ 0)
  have humod2 : u % 2 = X % 2 := by rw [hu_def, Nat.mod_mod_of_dvd X h2dvd]
  have huodd : Odd u := by
    rw [Nat.odd_iff] at hXodd ⊢
    rw [humod2, hXodd]
  have humem : u ∈ oddResidues Qres := by
    unfold oddResidues
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨hult, Nat.odd_iff.mp huodd⟩
  refine ⟨u, humem, ?_⟩
  have hmodeq : X ≡ u [MOD 2 ^ Qres] := by
    show X % 2 ^ Qres = u % 2 ^ Qres
    rw [Nat.mod_eq_of_lt hult, hu_def]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmodeq.symm

/-- The residue weight of the restarted cylinder points is supported on the odd-residue
image: every restarted state `C + 2*3^t*(kmin+j)` is odd (given `C` odd), and every odd
natural's residue class mod `2^Qres` lies in the odd-residue image. -/
theorem conditionalResidueWeight_support (r Dcyl kmin Nwin : ℕ) (W : ℝ) (C t Qres : ℕ)
    (hCodd : Odd C) (hQres : 1 ≤ Qres) (v : ZMod (2 ^ Qres))
    (hv : v ∉ (oddResidues Qres).image (fun n : ℕ => (n : ZMod (2 ^ Qres)))) :
    conditionalResidueWeight r Dcyl kmin Nwin W C t Qres v = 0 := by
  unfold conditionalResidueWeight
  apply Finset.sum_eq_zero
  intro j _
  by_cases hFj : ((C + 2 * 3 ^ t * (kmin + j) : ℕ) : ZMod (2 ^ Qres)) = v
  · exfalso
    apply hv
    have hXodd : Odd (C + 2 * 3 ^ t * (kmin + j)) :=
      hCodd.add_even ⟨3 ^ t * (kmin + j), by ring⟩
    obtain ⟨u, humem, hueq⟩ := exists_oddResidues_cast_eq _ Qres hXodd hQres
    exact Finset.mem_image.mpr ⟨u, humem, hueq.trans hFj⟩
  · rw [if_neg hFj]

/-! ### Connecting Milestone 3B to Tao's literal metric -/

/-- **Fixed-window version of the central residue theorem** (Part 6 of the Milestone 5
brief): the conditional restart-state law's residue distribution, measured in Tao's own
`taoL1TV`, is within an explicit `2×` multiple of Milestone 3B's half-L1 bound — the factor
of 2 made fully explicit, not hidden in a generic constant. `kmin, N` (with `hmem`, `hNlb`)
are supplied by the caller instead of derived via `cylinder_window_reindex`. -/
theorem conditional_residue_taoL1TV_eta_bound_at_window
    (d : ℕ → ℕ) (t r : ℕ) (h : Realizes d t r) (ht : 1 ≤ t)
    (Q : ℕ) (hQ : 1 ≤ Q) (Y H : ℕ) (hYr : r ≤ Y) (hYpos : 0 < Y) (η : ℝ) (hη : 0 < η)
    (hH : η * (Y : ℝ) ≤ (H : ℝ))
    (hthick : 4 * (2 ^ (S d t + 1) : ℝ) ≤ η * (Y : ℝ))
    (kmin N : ℕ)
    (hmem : ∀ j < N, Y ≤ r + 2 ^ (S d t + 1) * (kmin + j)
      ∧ r + 2 ^ (S d t + 1) * (kmin + j) < Y + H)
    (hNlb : ((Y : ℝ) + (H : ℝ)) - (Y : ℝ) ≤ ((N : ℝ) + 2) * (2 ^ (S d t + 1) : ℝ)) :
    ∃ W : ℝ, 0 < W ∧
      W = ∑ j ∈ range N, (1 : ℝ) / ((r : ℝ) + (2 ^ (S d t + 1) : ℝ) * ((kmin : ℝ) + j)) ∧
      taoL1TV (pushforward (conditionalRestartLaw r (2 ^ (S d t + 1)) kmin N W (orbit r t) t)
          (fun m : ℕ => (m : ZMod (2 ^ Q))))
        (unifOddResidues Q)
      ≤ 2 * (1 + 1 / η) * (2 : ℝ) ^ (Q + S d t) / (Y : ℝ) := by
  obtain ⟨W, hWpos, hWdef, hbound⟩ :=
    conditional_residue_tv_eta_bound_at_window d t r h ht Q hQ Y H hYr hYpos η hη hH hthick kmin
      N hmem hNlb
  refine ⟨W, hWpos, hWdef, ?_⟩
  have hCodd : Odd (orbit r t) := orbit_odd_of_pos r t ht
  rw [conditionalRestartLaw_mod_eq]
  have hres_supp : ∀ v : ZMod (2 ^ Q),
      conditionalResidueWeight r (2 ^ (S d t + 1)) kmin N W (orbit r t) t Q v ≠ 0 →
      v ∈ (oddResidues Q).image (fun n : ℕ => (n : ZMod (2 ^ Q))) := by
    intro v hv
    by_contra hcon
    exact hv (conditionalResidueWeight_support r (2 ^ (S d t + 1)) kmin N W (orbit r t) t Q
      hCodd hQ v hcon)
  have hunif_supp : ∀ v : ZMod (2 ^ Q), unifOddResiduesWeight Q v ≠ 0 →
      v ∈ (oddResidues Q).image (fun n : ℕ => (n : ZMod (2 ^ Q))) := by
    intro v hv
    unfold unifOddResiduesWeight at hv
    by_contra hcon
    apply hv
    rw [if_neg hcon]
    simp
  show taoL1TV (genEventProb (conditionalResidueWeight r (2 ^ (S d t + 1)) kmin N W
      (orbit r t) t Q)) (unifOddResidues Q) ≤ _
  unfold unifOddResidues
  rw [taoL1TV_genEventProb_eq_odd_finsum Q hQ _ _ hres_supp hunif_supp]
  have hterm_eq : ∀ u ∈ oddResidues Q,
      |conditionalResidueWeight r (2 ^ (S d t + 1)) kmin N W (orbit r t) t Q
          (u : ZMod (2 ^ Q))
        - unifOddResiduesWeight Q (u : ZMod (2 ^ Q))|
      = |(∑ j ∈ range N,
            (if orbit (r + 2 ^ (S d t + 1) * (kmin + j)) t % 2 ^ Q = u % 2 ^ Q
              then (1 : ℝ) / ((r : ℝ) + (2 ^ (S d t + 1) : ℝ) * ((kmin : ℝ) + j)) else 0)) / W
          - 1 / (2 ^ (Q - 1) : ℝ)| := by
    intro u hu
    have hQZ : NeZero (2 ^ Q) := ⟨by positivity⟩
    congr 2
    · unfold conditionalResidueWeight conditionalIndexWeight
      have hcast_eq : ((2 ^ (S d t + 1) : ℕ) : ℝ) = (2 ^ (S d t + 1) : ℝ) := by push_cast; ring
      simp only [hcast_eq]
      have hstep : ∀ j : ℕ, j ∈ range N →
          (if ((orbit r t + 2 * 3 ^ t * (kmin + j) : ℕ) : ZMod (2 ^ Q)) = (u : ZMod (2 ^ Q))
            then (if j < N then (1 : ℝ) / ((r : ℝ) + (2 ^ (S d t + 1) : ℝ) * ((kmin : ℝ) + j)) / W
              else 0)
            else 0)
          = (if orbit (r + 2 ^ (S d t + 1) * (kmin + j)) t % 2 ^ Q = u % 2 ^ Q
              then (1 : ℝ) / ((r : ℝ) + (2 ^ (S d t + 1) : ℝ) * ((kmin : ℝ) + j)) else 0) / W := by
        intro j hj
        have horb : orbit (r + 2 ^ (S d t + 1) * (kmin + j)) t
            = orbit r t + 2 * 3 ^ t * (kmin + j) := (cylinder_restart d t r (kmin + j) h).2
        have hcond_iff : ((orbit r t + 2 * 3 ^ t * (kmin + j) : ℕ) : ZMod (2 ^ Q))
              = (u : ZMod (2 ^ Q))
            ↔ orbit (r + 2 ^ (S d t + 1) * (kmin + j)) t % 2 ^ Q = u % 2 ^ Q := by
          rw [horb]
          constructor
          · intro hc
            exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hc
          · intro hc
            exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hc
        rw [if_pos (Finset.mem_range.mp hj)]
        by_cases hcond : orbit (r + 2 ^ (S d t + 1) * (kmin + j)) t % 2 ^ Q = u % 2 ^ Q
        · rw [if_pos (hcond_iff.mpr hcond), if_pos hcond]
        · rw [if_neg (fun hc => hcond (hcond_iff.mp hc)), if_neg hcond]; simp
      rw [Finset.sum_congr rfl hstep]
      rw [eq_div_iff hWpos.ne', Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> field_simp
    · unfold unifOddResiduesWeight
      rw [if_pos (Finset.mem_image_of_mem _ hu)]
  rw [Finset.sum_congr rfl hterm_eq]
  have h2 := mul_le_mul_of_nonneg_left hbound (by norm_num : (0:ℝ) ≤ 2)
  rw [show (2:ℝ) * ((1/2:ℝ) * ∑ v ∈ oddResidues Q,
        |(∑ j ∈ range N,
            (if orbit (r + 2 ^ (S d t + 1) * (kmin + j)) t % 2 ^ Q = v % 2 ^ Q
              then (1 : ℝ) / ((r : ℝ) + (2 ^ (S d t + 1) : ℝ) * ((kmin : ℝ) + j)) else 0)) / W
          - 1 / (2 ^ (Q - 1) : ℝ)|)
      = ∑ v ∈ oddResidues Q,
          |(∑ j ∈ range N,
              (if orbit (r + 2 ^ (S d t + 1) * (kmin + j)) t % 2 ^ Q = v % 2 ^ Q
                then (1 : ℝ) / ((r : ℝ) + (2 ^ (S d t + 1) : ℝ) * ((kmin : ℝ) + j)) else 0)) / W
            - 1 / (2 ^ (Q - 1) : ℝ)| from by ring] at h2
  have hRHS : (2:ℝ) * ((1 + 1/η) * (2:ℝ)^(Q + S d t) / (Y:ℝ))
      = 2 * (1 + 1/η) * (2:ℝ)^(Q + S d t) / (Y:ℝ) := by ring
  rw [hRHS] at h2
  linarith [h2]

/-- **Convenience wrapper** (unchanged public API): derives `kmin, N` (with `hmem`, `hNlb`) via
`cylinder_window_reindex`, then invokes the fixed-window version. -/
theorem conditional_residue_taoL1TV_eta_bound
    (d : ℕ → ℕ) (t r : ℕ) (h : Realizes d t r) (ht : 1 ≤ t)
    (Q : ℕ) (hQ : 1 ≤ Q) (Y H : ℕ) (hYr : r ≤ Y) (hYpos : 0 < Y) (η : ℝ) (hη : 0 < η)
    (hH : η * (Y : ℝ) ≤ (H : ℝ))
    (hthick : 4 * (2 ^ (S d t + 1) : ℝ) ≤ η * (Y : ℝ)) :
    ∃ kmin N : ℕ, ∃ W : ℝ, 0 < W ∧
      W = ∑ j ∈ range N, (1 : ℝ) / ((r : ℝ) + (2 ^ (S d t + 1) : ℝ) * ((kmin : ℝ) + j)) ∧
      taoL1TV (pushforward (conditionalRestartLaw r (2 ^ (S d t + 1)) kmin N W (orbit r t) t)
          (fun m : ℕ => (m : ZMod (2 ^ Q))))
        (unifOddResidues Q)
      ≤ 2 * (1 + 1 / η) * (2 : ℝ) ^ (Q + S d t) / (Y : ℝ) := by
  have hDcylpos : (0:ℕ) < 2 ^ (S d t + 1) := by positivity
  obtain ⟨kmin, N, hmem, hNlb⟩ :=
    cylinder_window_reindex r (2 ^ (S d t + 1)) Y (Y + H) hDcylpos hYr (Nat.le_add_right Y H)
  have hNlbR : ((Y : ℝ) + (H : ℝ)) - (Y : ℝ) ≤ ((N : ℝ) + 2) * (2 ^ (S d t + 1) : ℝ) := by
    push_cast at hNlb; linarith [hNlb]
  obtain ⟨W, hWpos, hWdef, hbound⟩ :=
    conditional_residue_taoL1TV_eta_bound_at_window d t r h ht Q hQ Y H hYr hYpos η hη hH hthick
      kmin N hmem hNlbR
  exact ⟨kmin, N, W, hWpos, hWdef, hbound⟩

/-! ### Information budget: turning our residue bound into Tao's literal hypothesis -/

/-- **Multiplicative information budget** (Part 7 of the Milestone 5 brief): the explicit
finite arithmetic condition `2(1+1/η)·2^(S+2Q) ≤ Cres·Y` is exactly sufficient to force our
residue bound `2(1+1/η)·2^(Q+S)/Y` under Tao's own threshold `Cres·2^(-Q)`. No logarithms
are introduced — this is the natural-number-power form, as instructed. -/
theorem tao_residue_input_of_information_budget
    (Q S : ℕ) (Y : ℕ) (hYpos : 0 < Y) (η Cres : ℝ) (hη : 0 < η) (hCres : 0 < Cres)
    (hbudget : 2 * (1 + 1 / η) * (2 : ℝ) ^ (S + 2 * Q) ≤ Cres * (Y : ℝ)) :
    2 * (1 + 1 / η) * (2 : ℝ) ^ (Q + S) / (Y : ℝ) ≤ Cres * (2 : ℝ) ^ (-(Q : ℝ)) := by
  have hYposR : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast hYpos
  have h2Qpos : (0 : ℝ) < (2 : ℝ) ^ Q := by positivity
  have hrpow : (2 : ℝ) ^ (-(Q : ℝ)) = 1 / (2 : ℝ) ^ Q := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
    rw [one_div]
  rw [hrpow, mul_one_div, div_le_div_iff₀ hYposR h2Qpos]
  have hpow_eq : (2 : ℝ) ^ (Q + S) * (2 : ℝ) ^ Q = (2 : ℝ) ^ (S + 2 * Q) := by
    rw [← pow_add]; congr 1; omega
  calc 2 * (1 + 1 / η) * (2 : ℝ) ^ (Q + S) * (2 : ℝ) ^ Q
      = 2 * (1 + 1 / η) * ((2 : ℝ) ^ (Q + S) * (2 : ℝ) ^ Q) := by ring
    _ = 2 * (1 + 1 / η) * (2 : ℝ) ^ (S + 2 * Q) := by rw [hpow_eq]
    _ ≤ Cres * (Y : ℝ) := hbudget

/-! ### Applying `TaoMixingHypothesis`: the central theorem -/

/-- **Fixed-witness AND fixed-window version.** Same as
`conditional_future_valuation_mixing_of_constants`, but the restart-window parameters
`kmin, N` (with `hmem`, `hNlb`) are ALSO supplied by the caller — e.g. Milestone 10's
exhaustive window construction — instead of derived via `cylinder_window_reindex`. Both `K`
and `kmin, N, W` appear verbatim in the conclusion; neither is re-selected internally. -/
theorem conditional_future_valuation_mixing_of_constants_at_window
    (c0 : ℝ) (K : TaoMixingConstants c0) (hK : TaoMixingProperty c0 K)
    (d : ℕ → ℕ) (t r : ℕ) (h : Realizes d t r) (ht : 1 ≤ t)
    (n : ℕ) (hn : 1 ≤ n)
    (Y H : ℕ) (hYr : r ≤ Y) (hYpos : 0 < Y) (η : ℝ) (hη : 0 < η)
    (hH : η * (Y : ℝ) ≤ (H : ℝ))
    (Q : ℕ) (hQrel : (Q : ℝ) ≥ (2 + c0) * (n : ℝ)) (hQ1 : 1 ≤ Q)
    (hthick : 4 * (2 ^ (S d t + 1) : ℝ) ≤ η * (Y : ℝ))
    (kmin N : ℕ)
    (hmem : ∀ j < N, Y ≤ r + 2 ^ (S d t + 1) * (kmin + j)
      ∧ r + 2 ^ (S d t + 1) * (kmin + j) < Y + H)
    (hNlb : ((Y : ℝ) + (H : ℝ)) - (Y : ℝ) ≤ ((N : ℝ) + 2) * (2 ^ (S d t + 1) : ℝ)) :
    ∃ W : ℝ, 0 < W ∧
      W = ∑ j ∈ range N, (1 : ℝ) / ((r : ℝ) + (2 ^ (S d t + 1) : ℝ) * ((kmin : ℝ) + j)) ∧
      (2 * (1 + 1 / η) * (2 : ℝ) ^ (S d t + 2 * Q) ≤ K.Cres * (Y : ℝ) →
        taoL1TV (pushforward (conditionalRestartLaw r (2 ^ (S d t + 1)) kmin N W (orbit r t) t)
            (fun m : ℕ => valuationVector m n))
          (iidGeom2VectorProb n)
        ≤ K.A * (2 : ℝ) ^ (-(K.c1 * (n : ℝ)))) := by
  obtain ⟨W, hWpos, hWdef, hresbound⟩ :=
    conditional_residue_taoL1TV_eta_bound_at_window d t r h ht Q hQ1 Y H hYr hYpos η hη hH
      hthick kmin N hmem hNlb
  refine ⟨W, hWpos, hWdef, ?_⟩
  intro hbudget
  have hres_final : taoL1TV (pushforward
        (conditionalRestartLaw r (2 ^ (S d t + 1)) kmin N W (orbit r t) t)
        (fun m : ℕ => (m : ZMod (2 ^ Q)))) (unifOddResidues Q)
      ≤ K.Cres * (2 : ℝ) ^ (-(Q : ℝ)) :=
    le_trans hresbound
      (tao_residue_input_of_information_budget Q (S d t) Y hYpos η K.Cres hη K.hCres hbudget)
  have hoddsupp : (conditionalRestartLaw r (2 ^ (S d t + 1)) kmin N W (orbit r t) t)
      {m : ℕ | ¬ Odd m} = 0 :=
    conditionalRestartLaw_odd_support r (2 ^ (S d t + 1)) kmin N W (orbit r t) t
      (orbit_odd_of_pos r t ht)
  exact hK n Q (conditionalRestartLaw r (2 ^ (S d t + 1)) kmin N W (orbit r t) t)
    hn hQrel hoddsupp hres_final

/-- **Fixed-witness version of `conditional_future_valuation_mixing`.** FORMALLY VERIFIED
*conditional on* the external `TaoMixingHypothesis` interface — composes: (1) the exact
deterministic Collatz cylinder restart (Milestones 1–2), (2) the explicit harmonic
residue-TV bound and its Tao-metric conversion (Milestones 3B, 5), (3) the multiplicative
information budget (Part 7), and (4) Tao's Proposition 1.9 itself, here supplied directly as
a `TaoMixingConstants` witness `K` together with its defining `TaoMixingProperty hK`, rather
than derived internally from a `tao : TaoMixingHypothesis` — so the *same* `K` can be
threaded uniformly through many calls (e.g. one per realized prefix), with `K` appearing in
the conclusion exactly as given, no re-selection. Conclusion: conditioned on a realized
prefix `d` of length `t` and a thick harmonic restart window, *if* the budget
`2(1+1/η)·2^(S d t + 2Q) ≤ K.Cres·Y` holds, then the future valuation vector (the next `n`
digits after the restarted state) is within `K.A·2^(-K.c1·n)` of the concrete iid
`Geom(2)^n` law, in Tao's own `taoL1TV` metric. -/
theorem conditional_future_valuation_mixing_of_constants
    (c0 : ℝ) (K : TaoMixingConstants c0) (hK : TaoMixingProperty c0 K)
    (d : ℕ → ℕ) (t r : ℕ) (h : Realizes d t r) (ht : 1 ≤ t)
    (n : ℕ) (hn : 1 ≤ n)
    (Y H : ℕ) (hYr : r ≤ Y) (hYpos : 0 < Y) (η : ℝ) (hη : 0 < η)
    (hH : η * (Y : ℝ) ≤ (H : ℝ))
    (Q : ℕ) (hQrel : (Q : ℝ) ≥ (2 + c0) * (n : ℝ)) (hQ1 : 1 ≤ Q)
    (hthick : 4 * (2 ^ (S d t + 1) : ℝ) ≤ η * (Y : ℝ)) :
    ∃ (kmin N : ℕ) (W : ℝ), 0 < W ∧
      W = ∑ j ∈ range N, (1 : ℝ) / ((r : ℝ) + (2 ^ (S d t + 1) : ℝ) * ((kmin : ℝ) + j)) ∧
      (2 * (1 + 1 / η) * (2 : ℝ) ^ (S d t + 2 * Q) ≤ K.Cres * (Y : ℝ) →
        taoL1TV (pushforward (conditionalRestartLaw r (2 ^ (S d t + 1)) kmin N W (orbit r t) t)
            (fun m : ℕ => valuationVector m n))
          (iidGeom2VectorProb n)
        ≤ K.A * (2 : ℝ) ^ (-(K.c1 * (n : ℝ)))) := by
  have hDcylpos : (0:ℕ) < 2 ^ (S d t + 1) := by positivity
  obtain ⟨kmin, N, hmem, hNlb⟩ :=
    cylinder_window_reindex r (2 ^ (S d t + 1)) Y (Y + H) hDcylpos hYr (Nat.le_add_right Y H)
  have hNlbR : ((Y : ℝ) + (H : ℝ)) - (Y : ℝ) ≤ ((N : ℝ) + 2) * (2 ^ (S d t + 1) : ℝ) := by
    push_cast at hNlb; linarith [hNlb]
  obtain ⟨W, hWpos, hWdef, hbound⟩ :=
    conditional_future_valuation_mixing_of_constants_at_window c0 K hK d t r h ht n hn Y H hYr
      hYpos η hη hH Q hQrel hQ1 hthick kmin N hmem hNlbR
  exact ⟨kmin, N, W, hWpos, hWdef, hbound⟩

/-- **Convenience wrapper** (unchanged public API): chooses `K` once from `tao`, then invokes
the fixed-witness version. -/
theorem conditional_future_valuation_mixing
    (tao : TaoMixingHypothesis)
    (d : ℕ → ℕ) (t r : ℕ) (h : Realizes d t r) (ht : 1 ≤ t)
    (n : ℕ) (hn : 1 ≤ n)
    (Y H : ℕ) (hYr : r ≤ Y) (hYpos : 0 < Y) (η : ℝ) (hη : 0 < η)
    (hH : η * (Y : ℝ) ≤ (H : ℝ))
    (c0 : ℝ) (hc0 : 0 < c0) (Q : ℕ) (hQrel : (Q : ℝ) ≥ (2 + c0) * (n : ℝ)) (hQ1 : 1 ≤ Q)
    (hthick : 4 * (2 ^ (S d t + 1) : ℝ) ≤ η * (Y : ℝ)) :
    ∃ (K : TaoMixingConstants c0) (kmin N : ℕ) (W : ℝ), 0 < W ∧
      W = ∑ j ∈ range N, (1 : ℝ) / ((r : ℝ) + (2 ^ (S d t + 1) : ℝ) * ((kmin : ℝ) + j)) ∧
      (2 * (1 + 1 / η) * (2 : ℝ) ^ (S d t + 2 * Q) ≤ K.Cres * (Y : ℝ) →
        taoL1TV (pushforward (conditionalRestartLaw r (2 ^ (S d t + 1)) kmin N W (orbit r t) t)
            (fun m : ℕ => valuationVector m n))
          (iidGeom2VectorProb n)
        ≤ K.A * (2 : ℝ) ^ (-(K.c1 * (n : ℝ)))) := by
  obtain ⟨K, hK⟩ := tao.finite_valuation_mixing c0 hc0
  obtain ⟨kmin, N, W, hWpos, hWdef, hbound⟩ :=
    conditional_future_valuation_mixing_of_constants c0 K hK d t r h ht n hn Y H hYr hYpos η hη
      hH Q hQrel hQ1 hthick
  exact ⟨K, kmin, N, W, hWpos, hWdef, hbound⟩

/-! ### Event-transfer corollary -/

/-- **Generalized fiber-sum reindexing**, dropping `genEventProb_pushforward_fiber`'s
`Fintype` requirement on the codomain: a finitely-supported `genEventProb` law, pushed
forward along *any* map (into a possibly infinite type, e.g. `Fin n → ℕ`), is still
`genEventProb`-shaped, generated by the (now finitely-supported) fiber sums. -/
theorem genEventProb_pushforward_fiber_general {β : Type*} [DecidableEq β]
    (Nwin : ℕ) (w : ℕ → ℝ) (hsupp : Function.support w ⊆ ↑(range Nwin)) (F : ℕ → β) :
    pushforward (genEventProb w) F
      = genEventProb (fun v : β => ∑ j ∈ range Nwin, if F j = v then w j else 0) := by
  classical
  funext E
  show genEventProb w (F ⁻¹' E) = _
  unfold genEventProb
  have hstep1 : (∑' j, Set.indicator (F ⁻¹' E) w j)
      = ∑ j ∈ range Nwin, Set.indicator (F ⁻¹' E) w j := by
    apply tsum_eq_sum'
    intro j hj
    have hwne : w j ≠ 0 := by
      intro h0; apply hj; simp [Set.indicator, h0]
    exact hsupp hwne
  rw [hstep1]
  set t := (range Nwin).image F with ht_def
  have hfiber_supp : Function.support (fun v : β => Set.indicator E
      (fun v => ∑ j ∈ range Nwin, if F j = v then w j else 0) v) ⊆ ↑t := by
    intro v hv
    by_contra hvni
    apply hv
    by_cases hvE : v ∈ E
    · simp only [Set.indicator, if_pos hvE]
      apply Finset.sum_eq_zero
      intro j hj
      rw [if_neg]
      intro hFjv
      apply hvni
      rw [ht_def]
      exact Finset.mem_image.mpr ⟨j, hj, hFjv⟩
    · simp [Set.indicator, hvE]
  rw [tsum_eq_sum' hfiber_supp]
  have key := Finset.sum_fiberwise_of_maps_to (s := range Nwin) (t := t) (g := F)
    (fun j hj => Finset.mem_image_of_mem F hj) (fun j => Set.indicator (F ⁻¹' E) w j)
  rw [← key]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hvE : v ∈ E
  · simp only [Set.indicator, if_pos hvE]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hFjv : F j = v
    · simp [hFjv, hvE]
    · simp [hFjv]
  · simp only [Set.indicator, if_neg hvE]
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_filter] at hj
    simp [hj.2, hvE]

/-- The pushforward of the conditional restart law under the future valuation vector map is
`genEventProb`-shaped, with an explicit (finitely-supported, hence summable) nonnegative
fiber-sum weight — the semantic fact that makes the event-transfer corollary provable rather
than a leap of faith. -/
theorem conditionalRestartLaw_future_genEventProb
    (r Dcyl kmin Nwin : ℕ) (W : ℝ) (C t n : ℕ) :
    pushforward (conditionalRestartLaw r Dcyl kmin Nwin W C t) (fun m : ℕ => valuationVector m n)
      = genEventProb (fun v : Fin n → ℕ =>
          ∑ j ∈ range Nwin,
            if valuationVector (C + 2 * 3 ^ t * (kmin + j)) n = v
              then conditionalIndexWeight r Dcyl kmin Nwin W j else 0) := by
  classical
  unfold conditionalRestartLaw
  rw [pushforward_comp]
  exact genEventProb_pushforward_fiber_general Nwin (conditionalIndexWeight r Dcyl kmin Nwin W)
    (conditionalIndexWeight_support r Dcyl kmin Nwin W) _

/-- **Fixed-witness AND fixed-window version.** Same as
`conditional_future_event_bound_of_constants`, but the restart-window parameters `kmin, N`
(with `hmem`, `hNlb`) are ALSO supplied by the caller — e.g. Milestone 10's exhaustive window
construction — instead of derived via `cylinder_window_reindex`. -/
theorem conditional_future_event_bound_of_constants_at_window
    (c0 : ℝ) (K : TaoMixingConstants c0) (hK : TaoMixingProperty c0 K)
    (d : ℕ → ℕ) (t r : ℕ) (h : Realizes d t r) (ht : 1 ≤ t)
    (n : ℕ) (hn : 1 ≤ n)
    (Y H : ℕ) (hYr : r ≤ Y) (hYpos : 0 < Y) (η : ℝ) (hη : 0 < η)
    (hH : η * (Y : ℝ) ≤ (H : ℝ))
    (Q : ℕ) (hQrel : (Q : ℝ) ≥ (2 + c0) * (n : ℝ)) (hQ1 : 1 ≤ Q)
    (hthick : 4 * (2 ^ (S d t + 1) : ℝ) ≤ η * (Y : ℝ)) (E : Set (Fin n → ℕ))
    (kmin N : ℕ)
    (hmem : ∀ j < N, Y ≤ r + 2 ^ (S d t + 1) * (kmin + j)
      ∧ r + 2 ^ (S d t + 1) * (kmin + j) < Y + H)
    (hNlb : ((Y : ℝ) + (H : ℝ)) - (Y : ℝ) ≤ ((N : ℝ) + 2) * (2 ^ (S d t + 1) : ℝ)) :
    ∃ W : ℝ, 0 < W ∧
      W = ∑ j ∈ range N, (1 : ℝ) / ((r : ℝ) + (2 ^ (S d t + 1) : ℝ) * ((kmin : ℝ) + j)) ∧
      (2 * (1 + 1 / η) * (2 : ℝ) ^ (S d t + 2 * Q) ≤ K.Cres * (Y : ℝ) →
        pushforward (conditionalRestartLaw r (2 ^ (S d t + 1)) kmin N W (orbit r t) t)
            (fun m : ℕ => valuationVector m n) E
          ≤ iidGeom2VectorProb n E + K.A * (2 : ℝ) ^ (-(K.c1 * (n : ℝ)))) := by
  obtain ⟨W, hWpos, hWdef, hmix⟩ :=
    conditional_future_valuation_mixing_of_constants_at_window c0 K hK d t r h ht n hn Y H hYr
      hYpos η hη hH Q hQrel hQ1 hthick kmin N hmem hNlb
  refine ⟨W, hWpos, hWdef, ?_⟩
  intro hbudget
  have htv := hmix hbudget
  have hw_nonneg : ∀ v : Fin n → ℕ, 0 ≤ ∑ j ∈ range N,
      if valuationVector (orbit r t + 2 * 3 ^ t * (kmin + j)) n = v
        then conditionalIndexWeight r (2 ^ (S d t + 1)) kmin N W j else 0 := by
    intro v
    apply Finset.sum_nonneg
    intro j _
    split_ifs
    · have hrpos : 0 < r := by obtain ⟨c, hc⟩ := h.1; omega
      unfold conditionalIndexWeight
      split_ifs
      · positivity
      · exact le_refl 0
    · exact le_refl 0
  have hw_summable : Summable (fun v : Fin n → ℕ => ∑ j ∈ range N,
      if valuationVector (orbit r t + 2 * 3 ^ t * (kmin + j)) n = v
        then conditionalIndexWeight r (2 ^ (S d t + 1)) kmin N W j else 0) := by
    apply summable_of_hasFiniteSupport
    apply Set.Finite.subset (Finset.finite_toSet
      ((range N).image (fun j => valuationVector (orbit r t + 2 * 3 ^ t * (kmin + j)) n)))
    intro v hv
    by_contra hvni
    apply hv
    apply Finset.sum_eq_zero
    intro j hj
    rw [if_neg]
    intro hveq
    apply hvni
    exact Finset.mem_image.mpr ⟨j, hj, hveq⟩
  have hbridge := event_discrepancy_le_taoL1TV hw_nonneg (atomWeight_nonneg n)
    hw_summable (atomWeight_summable n)
  have hle := event_prob_le_of_discrepancy hbridge E
  calc pushforward (conditionalRestartLaw r (2 ^ (S d t + 1)) kmin N W (orbit r t) t)
        (fun m : ℕ => valuationVector m n) E
      = genEventProb (fun v : Fin n → ℕ => ∑ j ∈ range N,
          if valuationVector (orbit r t + 2 * 3 ^ t * (kmin + j)) n = v
            then conditionalIndexWeight r (2 ^ (S d t + 1)) kmin N W j else 0) E := by
        rw [conditionalRestartLaw_future_genEventProb]
    _ ≤ iidGeom2VectorProb n E + K.A * (2 : ℝ) ^ (-(K.c1 * (n : ℝ))) := by
        unfold iidGeom2VectorProb
        unfold iidGeom2VectorProb at htv
        rw [conditionalRestartLaw_future_genEventProb] at htv
        linarith [hle, htv]

/-- **Fixed-witness version of `conditional_future_event_bound`** (Part 12/14 of the
Milestone 5 brief): under the same hypotheses as
`conditional_future_valuation_mixing_of_constants`, the conclusion transfers to a bound on
any single event's probability — exactly what persistence arguments consume, avoiding the
need to reconstruct total-variation machinery downstream. Both laws being genuinely
`genEventProb`-generated (`conditionalRestartLaw_future_genEventProb`, `iidGeom2VectorProb`)
is what makes this provable rather than an unjustified assumption for an abstract
`EventProb`. `K` is supplied by the caller (with its defining `TaoMixingProperty hK`) rather
than derived internally, so the same `K` can be reused uniformly across many prefixes. -/
theorem conditional_future_event_bound_of_constants
    (c0 : ℝ) (K : TaoMixingConstants c0) (hK : TaoMixingProperty c0 K)
    (d : ℕ → ℕ) (t r : ℕ) (h : Realizes d t r) (ht : 1 ≤ t)
    (n : ℕ) (hn : 1 ≤ n)
    (Y H : ℕ) (hYr : r ≤ Y) (hYpos : 0 < Y) (η : ℝ) (hη : 0 < η)
    (hH : η * (Y : ℝ) ≤ (H : ℝ))
    (Q : ℕ) (hQrel : (Q : ℝ) ≥ (2 + c0) * (n : ℝ)) (hQ1 : 1 ≤ Q)
    (hthick : 4 * (2 ^ (S d t + 1) : ℝ) ≤ η * (Y : ℝ)) (E : Set (Fin n → ℕ)) :
    ∃ (kmin N : ℕ) (W : ℝ), 0 < W ∧
      W = ∑ j ∈ range N, (1 : ℝ) / ((r : ℝ) + (2 ^ (S d t + 1) : ℝ) * ((kmin : ℝ) + j)) ∧
      (2 * (1 + 1 / η) * (2 : ℝ) ^ (S d t + 2 * Q) ≤ K.Cres * (Y : ℝ) →
        pushforward (conditionalRestartLaw r (2 ^ (S d t + 1)) kmin N W (orbit r t) t)
            (fun m : ℕ => valuationVector m n) E
          ≤ iidGeom2VectorProb n E + K.A * (2 : ℝ) ^ (-(K.c1 * (n : ℝ)))) := by
  have hDcylpos : (0:ℕ) < 2 ^ (S d t + 1) := by positivity
  obtain ⟨kmin, N, hmem, hNlb⟩ :=
    cylinder_window_reindex r (2 ^ (S d t + 1)) Y (Y + H) hDcylpos hYr (Nat.le_add_right Y H)
  have hNlbR : ((Y : ℝ) + (H : ℝ)) - (Y : ℝ) ≤ ((N : ℝ) + 2) * (2 ^ (S d t + 1) : ℝ) := by
    push_cast at hNlb; linarith [hNlb]
  obtain ⟨W, hWpos, hWdef, hbound⟩ :=
    conditional_future_event_bound_of_constants_at_window c0 K hK d t r h ht n hn Y H hYr hYpos η
      hη hH Q hQrel hQ1 hthick E kmin N hmem hNlbR
  exact ⟨kmin, N, W, hWpos, hWdef, hbound⟩

/-- **Convenience wrapper** (unchanged public API): chooses `K` once from `tao`, then invokes
the fixed-witness version. -/
theorem conditional_future_event_bound
    (tao : TaoMixingHypothesis)
    (d : ℕ → ℕ) (t r : ℕ) (h : Realizes d t r) (ht : 1 ≤ t)
    (n : ℕ) (hn : 1 ≤ n)
    (Y H : ℕ) (hYr : r ≤ Y) (hYpos : 0 < Y) (η : ℝ) (hη : 0 < η)
    (hH : η * (Y : ℝ) ≤ (H : ℝ))
    (c0 : ℝ) (hc0 : 0 < c0) (Q : ℕ) (hQrel : (Q : ℝ) ≥ (2 + c0) * (n : ℝ)) (hQ1 : 1 ≤ Q)
    (hthick : 4 * (2 ^ (S d t + 1) : ℝ) ≤ η * (Y : ℝ)) (E : Set (Fin n → ℕ)) :
    ∃ (K : TaoMixingConstants c0) (kmin N : ℕ) (W : ℝ), 0 < W ∧
      W = ∑ j ∈ range N, (1 : ℝ) / ((r : ℝ) + (2 ^ (S d t + 1) : ℝ) * ((kmin : ℝ) + j)) ∧
      (2 * (1 + 1 / η) * (2 : ℝ) ^ (S d t + 2 * Q) ≤ K.Cres * (Y : ℝ) →
        pushforward (conditionalRestartLaw r (2 ^ (S d t + 1)) kmin N W (orbit r t) t)
            (fun m : ℕ => valuationVector m n) E
          ≤ iidGeom2VectorProb n E + K.A * (2 : ℝ) ^ (-(K.c1 * (n : ℝ)))) := by
  obtain ⟨K, hK⟩ := tao.finite_valuation_mixing c0 hc0
  obtain ⟨kmin, N, W, hWpos, hWdef, hbound⟩ :=
    conditional_future_event_bound_of_constants c0 K hK d t r h ht n hn Y H hYr hYpos η hη hH Q
      hQrel hQ1 hthick E
  exact ⟨K, kmin, N, W, hWpos, hWdef, hbound⟩

end TaoExternal
end EOC
