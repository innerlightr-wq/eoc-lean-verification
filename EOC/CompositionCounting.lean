import EOC.FiniteValuationWord
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum

namespace EOC

open Finset

/-! # Fixed-sum shells of positive valuation words -/

/-- Positive words of length `N` and total sum `s`, represented by Mathlib compositions with
exactly `N` blocks.  The representation has the same indexing convention as the paper: a
composition of `s` into `N` positive parts. -/
abbrev ValuationShell (N s : ℕ) := {q : Composition s // q.length = N}

namespace ValuationShell

/-- The finite-function realization of a shell word. -/
def toWord {s : ℕ} (q : ValuationShell N s) : FiniteValuationWord N :=
  fun i ↦ q.1.blocksFun (Fin.cast q.2.symm i)

@[simp] theorem toWord_positive {s : ℕ} (q : ValuationShell N s) : q.toWord.Positive := by
  intro i
  simp [toWord]

@[simp] theorem toWord_total {s : ℕ} (q : ValuationShell N s) : q.toWord.total = s := by
  rcases q with ⟨q, hq⟩
  subst N
  simpa [toWord, FiniteValuationWord.total_eq_sum_univ] using q.sum_blocksFun

@[simp] theorem ofFn_toWord {s : ℕ} (q : ValuationShell N s) :
    List.ofFn q.toWord = q.1.blocks := by
  rcases q with ⟨q, hq⟩
  subst N
  exact q.ofFn_blocksFun

theorem toWord_injective {s : ℕ} : Function.Injective (toWord : ValuationShell N s → FiniteValuationWord N) := by
  intro q r h
  apply Subtype.ext
  apply Composition.ext
  rw [← ofFn_toWord q, ← ofFn_toWord r, h]

end ValuationShell

namespace Composition

/-- Removing the two endpoint boundaries of a positive-total composition leaves one boundary
per gap between consecutive blocks.  This is the length bookkeeping used by stars and bars. -/
theorem card_compositionAsSetEquiv {s : ℕ} (q : Composition s) (hs : 0 < s) :
    ((compositionAsSetEquiv s) ((compositionEquiv s) q)).card = q.length - 1 := by
  let d : CompositionAsSet s := (compositionEquiv s) q
  let interior : Finset (Fin (s + 1)) :=
    (d.boundaries.erase 0).erase (Fin.last s)
  have hlast_ne_zero : Fin.last s ≠ (0 : Fin (s + 1)) := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have hlast_mem : Fin.last s ∈ d.boundaries.erase 0 := by
    exact Finset.mem_erase.mpr ⟨hlast_ne_zero, d.getLast_mem⟩
  have hinterior_card : interior.card = d.length - 1 := by
    rw [show interior = (d.boundaries.erase 0).erase (Fin.last s) from rfl]
    rw [Finset.card_erase_of_mem hlast_mem, Finset.card_erase_of_mem d.zero_mem]
    rw [d.card_boundaries_eq_succ_length]
    omega
  have hcard : ((compositionAsSetEquiv s) d).card = interior.card := by
    classical
    let shift : Fin (s - 1) → Fin (s + 1) :=
      fun i ↦ ⟨1 + i, by omega⟩
    apply Finset.card_bij (fun i _ ↦ shift i)
    · intro i hi
      have hi' : shift i ∈ d.boundaries := by
        simpa [compositionAsSetEquiv, shift] using hi
      have hzero : shift i ≠ (0 : Fin (s + 1)) := by
        intro h
        have := congrArg Fin.val h
        simp [shift] at this
      have hlast : shift i ≠ Fin.last s := by
        intro h
        have := congrArg Fin.val h
        simp [shift] at this
        omega
      exact Finset.mem_erase.mpr ⟨hlast, Finset.mem_erase.mpr ⟨hzero, hi'⟩⟩
    · intro i hi k hk hik
      apply Fin.ext
      have := congrArg Fin.val hik
      simpa [shift] using this
    · intro b hb
      have hb' : b ∈ d.boundaries := (Finset.mem_erase.mp (Finset.mem_erase.mp hb).2).2
      have hbzero : b ≠ (0 : Fin (s + 1)) := (Finset.mem_erase.mp (Finset.mem_erase.mp hb).2).1
      have hblast : b ≠ Fin.last s := (Finset.mem_erase.mp hb).1
      have hbpos : 0 < (b : ℕ) := by
        by_contra h
        have : b = (0 : Fin (s + 1)) := Fin.ext (by rw [Fin.val_zero]; omega)
        exact hbzero this
      have hblt : (b : ℕ) < s := by
        have hble : (b : ℕ) ≤ s := Nat.le_of_lt_succ b.isLt
        by_contra h
        have : b = Fin.last s := Fin.ext (by rw [Fin.val_last]; omega)
        exact hblast this
      let i : Fin (s - 1) := ⟨(b : ℕ) - 1, by omega⟩
      have hb1 : 1 + ((b : ℕ) - 1) = b := by omega
      have hi : i ∈ (compositionAsSetEquiv s) d := by
        simpa [compositionAsSetEquiv, i, hb1] using hb'
      refine ⟨i, hi, ?_⟩
      apply Fin.ext
      show 1 + ((b : ℕ) - 1) = (b : ℕ)
      exact hb1
  rw [show (compositionEquiv s) q = d from rfl, hcard, hinterior_card]
  exact congrArg (· - 1) q.toCompositionAsSet_length

end Composition

/-- Stars-and-bars equivalence between fixed-length compositions and fixed-cardinality cut sets. -/
noncomputable def valuationShellEquivCuts {s : ℕ} (hN : 1 ≤ N) (hNs : N ≤ s) :
    ValuationShell N s ≃ {t : Finset (Fin (s - 1)) // t.card = N - 1} := by
  let e : Composition s ≃ Finset (Fin (s - 1)) :=
    (compositionEquiv s).trans (compositionAsSetEquiv s)
  have hs : 0 < s := lt_of_lt_of_le (by omega : 0 < N) hNs
  refine
    { toFun := fun q ↦ ⟨e q.1, ?_⟩
      invFun := fun t ↦ ⟨e.symm t.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · simpa [e, q.2] using Composition.card_compositionAsSetEquiv q.1 hs
  · have hlenpos : 0 < (e.symm t.1).length := (e.symm t.1).length_pos_of_pos hs
    have hcard := Composition.card_compositionAsSetEquiv (e.symm t.1) hs
    have he : (compositionAsSetEquiv s) ((compositionEquiv s) (e.symm t.1)) = t.1 :=
      e.apply_symm_apply t.1
    rw [he, t.2] at hcard
    omega
  · intro q
    apply Subtype.ext
    exact e.symm_apply_apply q.1
  · intro t
    apply Subtype.ext
    exact e.apply_symm_apply t.1

/-- Exact fixed-sum shell count: positive words of length `N` and sum `s`. -/
theorem valuationShell_card {s : ℕ} (hN : 1 ≤ N) (hNs : N ≤ s) :
    Fintype.card (ValuationShell N s) = Nat.choose (s - 1) (N - 1) := by
  classical
  rw [Fintype.card_congr (valuationShellEquivCuts hN hNs)]
  let cuts : Finset (Finset (Fin (s - 1))) := Finset.univ.powersetCard (N - 1)
  calc
    Fintype.card {t : Finset (Fin (s - 1)) // t.card = N - 1} = cuts.card := by
      rw [← Fintype.card_coe cuts]
      apply Fintype.card_congr
      exact
        { toFun := fun t ↦ ⟨t.1, by simp [cuts, t.2]⟩
          invFun := fun t ↦ ⟨t.1, (Finset.mem_powersetCard.mp t.2).2⟩
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl }
    _ = Nat.choose (s - 1) (N - 1) := by simp [cuts]

/-- The terminal-only capacity up to total sum `B`. -/
def terminalCount (N B : ℕ) : ℕ :=
  ∑ s ∈ Finset.Icc N B, Fintype.card (ValuationShell N s)

/-- Cumulative shell count: exact terminal-only count, i.e. the hockey-stick identity. -/
theorem terminalCount_eq_choose (hN : 1 ≤ N) (B : ℕ) :
    terminalCount N B = Nat.choose B N := by
  unfold terminalCount
  calc
    ∑ s ∈ Finset.Icc N B, Fintype.card (ValuationShell N s) =
        ∑ s ∈ Finset.Icc N B, Nat.choose (s - 1) (N - 1) := by
      apply Finset.sum_congr rfl
      intro s hs
      exact valuationShell_card hN (Finset.mem_Icc.mp hs).1
    _ = Nat.choose B N := by
      obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
      rcases B with _ | b
      · -- `B = 0`: the range `Icc (n + 1) 0` is empty and `choose 0 (n + 1) = 0`.
        simp
      -- `B = b + 1`: the predecessors are `b` and `n`, matching `Nat.sum_Icc_choose b n`.
      rw [Nat.add_sub_cancel, ← Nat.sum_Icc_choose b n]
      refine Finset.sum_bij (fun s _ ↦ s - 1) ?_ ?_ ?_ ?_
      · intro s hs
        rw [Finset.mem_Icc] at hs ⊢
        omega
      · intro s hs t ht hst
        rw [Finset.mem_Icc] at hs ht
        omega
      · intro m hm
        refine ⟨m + 1, ?_, by omega⟩
        rw [Finset.mem_Icc] at hm ⊢
        omega
      · intro s hs
        rfl

end EOC
