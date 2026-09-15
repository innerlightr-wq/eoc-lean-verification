import EOC.ChordRotation

/-!
# The capacity sandwich for barrier-confined positive words

For a natural-number barrier `K : ℕ → ℕ`, a finite word `w` of length `N` is
`BarrierConfined K` if `S_j ≤ K j` for every `1 ≤ j ≤ N` (`S_j = w.prefixSum j`).
`confinedWords N K` is the finite set of positive `K`-confined words.

The Collatz barrier is `collatzBarrier c j = ⌊jα + c⌋₊`, and for `c : ℕ` the membership
`w ∈ confinedWords N (collatzBarrier c)` is exactly "`w` positive and `PaperConfined α c w`"
(`mem_collatzConfinedWords`).

Main results (paper: *Three Scales of Confinement*, Thm 5.2, Cor 6.1, Prop 6.3):

* `card_feasibleWords` — the positive words with `S_N ≤ B` number exactly `C(B, N)`
  (terminal-only count; uses `terminalCount_eq_choose`).
* `card_filter_le_mul_card` — **rotation counting.** If the barrier dominates every chord
  (`hchord`), then for any property `P` of the total, the feasible words with total satisfying
  `P` number at most `N` times the confined words with total satisfying `P`. Each feasible word
  is sent to its chord rotation (`ChordRotation.chord_rotation_nat`), which is confined; every
  fibre lies in one rotation class, which has at most `N` elements.
* `choose_le_mul_card_confinedWords`, `card_confinedWords_le_choose` — the summed sandwich
  `C(K N, N) ≤ N · #confined ≤ N · C(K N, N)`.
* `shell_choose_le_mul_card` — the per-shell lower bound `C(s-1, N-1) ≤ N · #confined shell s`.
* `collatz_capacity_sandwich` — the Collatz case: with `s_N = ⌊Nα + c⌋₊`,
  `C(s_N - 1, N - 1) ≤ C(s_N, N) ≤ N · W_c(N) ≤ N · C(s_N, N)`.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace CapacityBounds

open Finset FiniteValuationWord

variable {N : ℕ}

/-! ## 1. The digit box and the confined set -/

/-- Words with every digit in `[1, B]`. -/
def box (N B : ℕ) : Finset (FiniteValuationWord N) :=
  Fintype.piFinset fun _ => Finset.Icc 1 B

theorem mem_box {B : ℕ} {w : FiniteValuationWord N} :
    w ∈ box N B ↔ ∀ i, 1 ≤ w i ∧ w i ≤ B := by
  simp [box, Fintype.mem_piFinset]

theorem digit_le_total (w : FiniteValuationWord N) (i : Fin N) : w i ≤ w.total := by
  rw [total_eq_sum_univ]
  exact Finset.single_le_sum (fun j _ => Nat.zero_le (w j)) (Finset.mem_univ i)

theorem mem_box_of_positive {B : ℕ} {w : FiniteValuationWord N} (hw : w.Positive)
    (hB : w.total ≤ B) : w ∈ box N B :=
  mem_box.mpr fun i => ⟨hw i, (digit_le_total w i).trans hB⟩

theorem positive_of_mem_box {B : ℕ} {w : FiniteValuationWord N} (h : w ∈ box N B) :
    w.Positive :=
  fun i => (mem_box.mp h i).1

theorem le_total_of_positive {w : FiniteValuationWord N} (hw : w.Positive) : N ≤ w.total := by
  rw [total_eq_sum_univ]
  calc N = ∑ _i : Fin N, 1 := by simp
    _ ≤ ∑ i, w i := Finset.sum_le_sum fun i _ => hw i

/-- Confinement under a natural-number barrier: `S_j ≤ K j` for `1 ≤ j ≤ N`. -/
def BarrierConfined (K : ℕ → ℕ) (w : FiniteValuationWord N) : Prop :=
  ∀ j ∈ Finset.Icc 1 N, w.prefixSum j ≤ K j

instance (K : ℕ → ℕ) : DecidablePred (BarrierConfined (N := N) K) := fun w => by
  unfold BarrierConfined
  infer_instance

/-- The positive `K`-confined words of length `N`. -/
def confinedWords (N : ℕ) (K : ℕ → ℕ) : Finset (FiniteValuationWord N) :=
  (box N (K N)).filter (BarrierConfined K)

theorem total_le_of_barrierConfined (hN : 1 ≤ N) {K : ℕ → ℕ} {w : FiniteValuationWord N}
    (h : BarrierConfined K w) : w.total ≤ K N :=
  h N (mem_Icc.mpr ⟨hN, le_rfl⟩)

theorem mem_confinedWords (hN : 1 ≤ N) {K : ℕ → ℕ} {w : FiniteValuationWord N} :
    w ∈ confinedWords N K ↔ w.Positive ∧ BarrierConfined K w := by
  constructor
  · intro h
    rw [confinedWords, mem_filter] at h
    exact ⟨positive_of_mem_box h.1, h.2⟩
  · rintro ⟨hp, hc⟩
    exact mem_filter.mpr ⟨mem_box_of_positive hp (total_le_of_barrierConfined hN hc), hc⟩

/-! ## 2. Shells and the terminal-only count -/

/-- Positive words of length `N` and total exactly `s`. -/
def shellWords (N s : ℕ) : Finset (FiniteValuationWord N) :=
  (box N s).filter fun w => w.total = s

/-- Positive words of length `N` and total at most `B`. -/
def feasibleWords (N B : ℕ) : Finset (FiniteValuationWord N) :=
  (box N B).filter fun w => w.total ≤ B

theorem mem_shellWords {s : ℕ} {w : FiniteValuationWord N} :
    w ∈ shellWords N s ↔ w.Positive ∧ w.total = s := by
  constructor
  · intro h
    rw [shellWords, mem_filter] at h
    exact ⟨positive_of_mem_box h.1, h.2⟩
  · rintro ⟨hp, ht⟩
    exact mem_filter.mpr ⟨mem_box_of_positive hp ht.le, ht⟩

theorem mem_feasibleWords {B : ℕ} {w : FiniteValuationWord N} :
    w ∈ feasibleWords N B ↔ w.Positive ∧ w.total ≤ B := by
  constructor
  · intro h
    rw [feasibleWords, mem_filter] at h
    exact ⟨positive_of_mem_box h.1, h.2⟩
  · rintro ⟨hp, ht⟩
    exact mem_filter.mpr ⟨mem_box_of_positive hp ht, ht⟩

/-- A shell of positive words is the image of the composition shell `ValuationShell N s`. -/
theorem card_shellWords (hN : 1 ≤ N) {s : ℕ} (hNs : N ≤ s) :
    (shellWords N s).card = Nat.choose (s - 1) (N - 1) := by
  rw [← valuationShell_card hN hNs, ← Finset.card_univ]
  have himage : shellWords N s =
      (Finset.univ : Finset (ValuationShell N s)).image ValuationShell.toWord := by
    ext w
    rw [mem_shellWords, mem_image]
    constructor
    · rintro ⟨hpos, htot⟩
      refine ⟨⟨⟨List.ofFn w, ?_, ?_⟩, by simp [Composition.length]⟩, mem_univ _, ?_⟩
      · intro i hi
        rw [List.mem_ofFn] at hi
        obtain ⟨k, rfl⟩ := hi
        exact hpos k
      · rw [List.sum_ofFn, ← total_eq_sum_univ, htot]
      · apply List.ofFn_injective
        rw [ValuationShell.ofFn_toWord]
    · rintro ⟨q, -, rfl⟩
      exact ⟨q.toWord_positive, q.toWord_total⟩
  rw [himage, card_image_of_injective _ ValuationShell.toWord_injective]

theorem feasibleWords_eq_biUnion (N B : ℕ) :
    feasibleWords N B = (Icc N B).biUnion (shellWords N) := by
  ext w
  rw [mem_feasibleWords, mem_biUnion]
  constructor
  · rintro ⟨hp, ht⟩
    exact ⟨w.total, mem_Icc.mpr ⟨le_total_of_positive hp, ht⟩, mem_shellWords.mpr ⟨hp, rfl⟩⟩
  · rintro ⟨s, hs, hw⟩
    obtain ⟨hp, ht⟩ := mem_shellWords.mp hw
    exact ⟨hp, ht ▸ (mem_Icc.mp hs).2⟩

/-- **Terminal-only count** (paper Prop 4.1): `#{w positive : S_N ≤ B} = C(B, N)`. -/
theorem card_feasibleWords (hN : 1 ≤ N) (B : ℕ) :
    (feasibleWords N B).card = Nat.choose B N := by
  rw [feasibleWords_eq_biUnion, card_biUnion]
  · rw [← terminalCount_eq_choose hN B, terminalCount]
    refine sum_congr rfl fun s hs => ?_
    rw [card_shellWords hN (mem_Icc.mp hs).1, valuationShell_card hN (mem_Icc.mp hs).1]
  · intro s _ t _ hst
    refine disjoint_left.mpr fun w hws hwt => hst ?_
    exact (mem_shellWords.mp hws).2.symm.trans (mem_shellWords.mp hwt).2

/-! ## 3. Rotation algebra -/

theorem rotate_rotate (w : FiniteValuationWord N) (r k : ℕ) :
    (w.rotate r).rotate k = w.rotate (r + k) := by
  apply List.ofFn_injective
  simp [ofFn_rotate, List.rotate_rotate]

theorem rotate_self_length (w : FiniteValuationWord N) : w.rotate N = w := by
  apply List.ofFn_injective
  rw [ofFn_rotate]
  simpa using List.rotate_length (List.ofFn w)

theorem rotate_mod (w : FiniteValuationWord N) (k : ℕ) : w.rotate (k % N) = w.rotate k := by
  apply List.ofFn_injective
  rw [ofFn_rotate, ofFn_rotate]
  simpa using List.rotate_mod (List.ofFn w) k

/-- The chord rotation chosen by `ChordRotation.chord_rotation_nat`. -/
noncomputable def chordRot (hN : 0 < N) (w : FiniteValuationWord N) : ℕ :=
  Classical.choose (ChordRotation.chord_rotation_nat hN w w.total rfl)

theorem chordRot_spec (hN : 0 < N) (w : FiniteValuationWord N) :
    chordRot hN w < N ∧
      ∀ j ≤ N, N * (w.rotate (chordRot hN w)).prefixSum j ≤ j * w.total :=
  Classical.choose_spec (ChordRotation.chord_rotation_nat hN w w.total rfl)

/-- A rotation lying below the chord of a word with total `≤ K N` is `K`-confined, provided the
barrier dominates the chord (`hchord`). -/
theorem barrierConfined_of_chord {K : ℕ → ℕ}
    (hchord : ∀ j ≤ N, ∀ p : ℕ, N * p ≤ j * K N → p ≤ K j)
    {w : FiniteValuationWord N} (hw : w.total ≤ K N) {r : ℕ}
    (hr : ∀ j ≤ N, N * (w.rotate r).prefixSum j ≤ j * w.total) :
    BarrierConfined K (w.rotate r) := by
  intro j hj
  have hjN := (mem_Icc.mp hj).2
  exact hchord j hjN _ ((hr j hjN).trans (Nat.mul_le_mul_left j hw))

/-! ## 4. Rotation counting -/

/-- **Rotation counting.** Feasible words whose total satisfies `P` number at most `N` times the
confined words whose total satisfies `P`. -/
theorem card_filter_le_mul_card (hN : 0 < N) (K : ℕ → ℕ)
    (hchord : ∀ j ≤ N, ∀ p : ℕ, N * p ≤ j * K N → p ≤ K j) (P : ℕ → Prop) [DecidablePred P] :
    ((feasibleWords N (K N)).filter fun w => P w.total).card ≤
      N * ((confinedWords N K).filter fun w => P w.total).card := by
  classical
  refine card_le_mul_card_image_of_maps_to (f := fun w => w.rotate (chordRot hN w)) ?_ N ?_
  · intro w hw
    obtain ⟨hwF, hP⟩ := mem_filter.mp hw
    obtain ⟨hpos, htot⟩ := mem_feasibleWords.mp hwF
    have hspec := chordRot_spec hN w
    refine mem_filter.mpr ⟨?_, by simpa using hP⟩
    refine (mem_confinedWords hN).mpr ⟨(rotate_positive _ _).mpr hpos, ?_⟩
    exact barrierConfined_of_chord hchord htot hspec.2
  · intro v _
    calc #{a ∈ (feasibleWords N (K N)).filter (fun w => P w.total) |
            a.rotate (chordRot hN a) = v}
        ≤ ((range N).image fun k => v.rotate k).card := by
          apply card_le_card
          intro w hw
          obtain ⟨-, hfw⟩ := mem_filter.mp hw
          rw [mem_image]
          have hlt := (chordRot_spec hN w).1
          refine ⟨(N - chordRot hN w) % N, mem_range.mpr (Nat.mod_lt _ hN), ?_⟩
          rw [← hfw, rotate_mod, rotate_rotate,
            show chordRot hN w + (N - chordRot hN w) = N by omega, rotate_self_length]
      _ ≤ (range N).card := card_image_le
      _ = N := card_range N

/-! ## 5. The sandwich -/

/-- Upper half: `#confined ≤ C(K N, N)`. -/
theorem card_confinedWords_le_choose (hN : 1 ≤ N) (K : ℕ → ℕ) :
    (confinedWords N K).card ≤ Nat.choose (K N) N := by
  rw [← card_feasibleWords hN]
  apply card_le_card
  intro w hw
  obtain ⟨hp, hc⟩ := (mem_confinedWords hN).mp hw
  exact mem_feasibleWords.mpr ⟨hp, total_le_of_barrierConfined hN hc⟩

/-- Lower half, summed over shells: `C(K N, N) ≤ N · #confined`. -/
theorem choose_le_mul_card_confinedWords (hN : 1 ≤ N) (K : ℕ → ℕ)
    (hchord : ∀ j ≤ N, ∀ p : ℕ, N * p ≤ j * K N → p ≤ K j) :
    Nat.choose (K N) N ≤ N * (confinedWords N K).card := by
  have h := card_filter_le_mul_card (by omega) K hchord (fun _ => True)
  rw [filter_true_of_mem (fun _ _ => trivial), filter_true_of_mem (fun _ _ => trivial),
    card_feasibleWords hN] at h
  exact h

/-- Per-shell lower bound (paper Thm 5.2): `C(s-1, N-1) ≤ N · #{confined, S_N = s}`. -/
theorem shell_choose_le_mul_card (hN : 1 ≤ N) (K : ℕ → ℕ)
    (hchord : ∀ j ≤ N, ∀ p : ℕ, N * p ≤ j * K N → p ≤ K j) {s : ℕ} (hNs : N ≤ s)
    (hsK : s ≤ K N) :
    Nat.choose (s - 1) (N - 1) ≤ N * ((confinedWords N K).filter fun w => w.total = s).card := by
  have h := card_filter_le_mul_card (by omega) K hchord (fun t => t = s)
  have hshell : ((feasibleWords N (K N)).filter fun w => w.total = s) = shellWords N s := by
    ext w
    rw [mem_filter, mem_feasibleWords, mem_shellWords]
    constructor
    · rintro ⟨⟨hp, -⟩, ht⟩
      exact ⟨hp, ht⟩
    · rintro ⟨hp, ht⟩
      exact ⟨⟨hp, ht ▸ hsK⟩, ht⟩
  rwa [hshell, card_shellWords hN hNs] at h

/-! ## 6. The Collatz barrier -/

/-- The Collatz barrier `⌊jα + c⌋₊`. -/
noncomputable def collatzBarrier (c : ℕ) (j : ℕ) : ℕ := ⌊(j : ℝ) * alpha + c⌋₊

theorem alpha_pos : 0 < alpha := lt_trans zero_lt_one one_lt_alpha

theorem barrier_arg_nonneg (c j : ℕ) : 0 ≤ (j : ℝ) * alpha + c :=
  add_nonneg (mul_nonneg (Nat.cast_nonneg _) alpha_pos.le) (Nat.cast_nonneg _)

theorem barrierConfined_collatz_iff (c : ℕ) (w : FiniteValuationWord N) :
    BarrierConfined (collatzBarrier c) w ↔ PaperConfined alpha c w := by
  unfold BarrierConfined PaperConfined collatzBarrier
  constructor
  · intro h j hj1 hjN
    have := h j (mem_Icc.mpr ⟨hj1, hjN⟩)
    rw [Nat.le_floor_iff (barrier_arg_nonneg c j)] at this
    linarith
  · intro h j hj
    rw [mem_Icc] at hj
    rw [Nat.le_floor_iff (barrier_arg_nonneg c j)]
    have := h j hj.1 hj.2
    linarith

/-- The Collatz barrier dominates every chord from `(0, 0)` to `(N, s_N)` (needs `c ≥ 0`). -/
theorem collatz_chord (c : ℕ) (hN : 0 < N) :
    ∀ j ≤ N, ∀ p : ℕ, N * p ≤ j * collatzBarrier c N → p ≤ collatzBarrier c j := by
  intro j hj p hp
  unfold collatzBarrier at *
  rw [Nat.le_floor_iff (barrier_arg_nonneg c j)]
  have hfloor : (⌊(N : ℝ) * alpha + c⌋₊ : ℝ) ≤ N * alpha + c :=
    Nat.floor_le (barrier_arg_nonneg c N)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hjr : (j : ℝ) ≤ N := by exact_mod_cast hj
  have hp' : (N : ℝ) * p ≤ j * (N * alpha + c) :=
    calc (N : ℝ) * p ≤ j * ⌊(N : ℝ) * alpha + c⌋₊ := by exact_mod_cast hp
      _ ≤ j * (N * alpha + c) := mul_le_mul_of_nonneg_left hfloor (Nat.cast_nonneg _)
  have hc : (j : ℝ) * c ≤ N * c := mul_le_mul_of_nonneg_right hjr (Nat.cast_nonneg _)
  have hkey : (N : ℝ) * p ≤ N * (j * alpha + c) := by nlinarith
  exact le_of_mul_le_mul_left hkey hNr

/-- Membership in the Collatz confined set is paper-faithful confinement of a positive word. -/
theorem mem_collatzConfinedWords (c : ℕ) (hN : 1 ≤ N) {w : FiniteValuationWord N} :
    w ∈ confinedWords N (collatzBarrier c) ↔ w.Positive ∧ PaperConfined alpha c w := by
  rw [mem_confinedWords hN, barrierConfined_collatz_iff]

theorem le_collatzBarrier (c : ℕ) (N : ℕ) : N ≤ collatzBarrier c N := by
  unfold collatzBarrier
  rw [Nat.le_floor_iff (barrier_arg_nonneg c N)]
  have h1 : (N : ℝ) ≤ N * alpha := by
    nlinarith [one_lt_alpha, (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have h2 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  linarith

/-- **Collatz capacity sandwich** (paper Cor 6.1, summed form): with `s_N = ⌊Nα + c⌋₊` and
`W_c(N) = #confinedWords N (collatzBarrier c)`,
`C(s_N - 1, N - 1) ≤ C(s_N, N) ≤ N · W_c(N) ≤ N · C(s_N, N)`. -/
theorem collatz_capacity_sandwich (c : ℕ) (hN : 1 ≤ N) :
    Nat.choose (collatzBarrier c N - 1) (N - 1) ≤ Nat.choose (collatzBarrier c N) N ∧
      Nat.choose (collatzBarrier c N) N ≤ N * (confinedWords N (collatzBarrier c)).card ∧
      N * (confinedWords N (collatzBarrier c)).card ≤ N * Nat.choose (collatzBarrier c N) N := by
  refine ⟨?_, choose_le_mul_card_confinedWords hN _ (collatz_chord c (by omega)),
    Nat.mul_le_mul_left N (card_confinedWords_le_choose hN _)⟩
  obtain ⟨m, hm⟩ : ∃ m, collatzBarrier c N = m + 1 := ⟨collatzBarrier c N - 1, by
    have := le_collatzBarrier c N; omega⟩
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  rw [hm, Nat.add_sub_cancel, Nat.add_sub_cancel, Nat.choose_succ_succ]
  exact Nat.le_add_right _ _

/-- Per-shell Collatz lower bound (paper Thm 5.2): for `N ≤ s ≤ s_N`,
`C(s - 1, N - 1) ≤ N · A_N(c, s)`. -/
theorem collatz_shell_lower (c : ℕ) (hN : 1 ≤ N) {s : ℕ} (hNs : N ≤ s)
    (hs : s ≤ collatzBarrier c N) :
    Nat.choose (s - 1) (N - 1) ≤
      N * ((confinedWords N (collatzBarrier c)).filter fun w => w.total = s).card :=
  shell_choose_le_mul_card hN _ (collatz_chord c (by omega)) hNs hs

end CapacityBounds
end EOC
