import EOC.Realizer
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Count
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# EOC/ChangHistory.lean — finite Chang-history realizability

Every finite binary "Chang history" `ys : List Bool` is realized by a positive
odd integer, using the exact realizer machinery of `EOC.Realizer`.

Construction: map each bit to a length-3 valuation block

  `false ↦ [2,1,1]`   (Chang label 0)
  `true  ↦ [2,1,2]`   (Chang label 1)

and concatenate.  The resulting valuation word `changWord ys` of length
`3 * ys.length` is admissible (all digits `≥ 1`), hence realizable.

This file is developed in stages:

* **Stage A** (this commit): the constructed word is realizable
  (`changWord_realizable`), plus the rigorous seed upper bound
  (`changSeed_lt`, `changSeed_lt'`).
* Stage B / C (later): the designated positions carry the prescribed
  `mod 16` / `mod 32` states and are the consecutive Chang events.

No claim toward the Collatz conjecture or toward pointwise Chang balance is
made here.  See `CHANG_CYLINDER_SCRATCHPAD.md`.
-/

namespace EOC.ChangHistory

open EOC Finset

/-! ## Stage A.1 — definitions -/

/-- The length-3 valuation block for one Chang bit. -/
def changBlock (b : Bool) : List ℕ := if b then [2, 1, 2] else [2, 1, 1]

/-- The concatenated valuation word of a finite Chang history, as a list. -/
def changWordList : List Bool → List ℕ
  | [] => []
  | b :: bs => changBlock b ++ changWordList bs

/-- The valuation word as a total function `ℕ → ℕ` (default `1` outside the
list, so every digit is `≥ 1` everywhere — harmless past index `3·|ys|`). -/
def changWord (ys : List Bool) : ℕ → ℕ := fun i => (changWordList ys).getD i 1

/-! ## Stage A.2 — basic combinatorial lemmas -/

@[simp] theorem changBlock_true : changBlock true = [2, 1, 2] := rfl
@[simp] theorem changBlock_false : changBlock false = [2, 1, 1] := rfl

@[simp] theorem changBlock_length (b : Bool) : (changBlock b).length = 3 := by
  cases b <;> rfl

theorem changWordList_length (ys : List Bool) :
    (changWordList ys).length = 3 * ys.length := by
  induction ys with
  | nil => rfl
  | cons b bs ih =>
    simp only [changWordList, List.length_append, changBlock_length, ih, List.length_cons]
    ring

/-- Every entry of the constructed word list is `1` or `2`. -/
theorem changWordList_mem (ys : List Bool) :
    ∀ x ∈ changWordList ys, x = 1 ∨ x = 2 := by
  induction ys with
  | nil => simp [changWordList]
  | cons b bs ih =>
    intro x hx
    rw [changWordList, List.mem_append] at hx
    rcases hx with hx | hx
    · cases b <;>
      · simp only [changBlock_true, changBlock_false, List.mem_cons,
          List.not_mem_nil, or_false] at hx
        omega
    · exact ih x hx

/-- Positivity of every digit (in fact for every index, thanks to the default). -/
theorem one_le_changWord (ys : List Bool) (i : ℕ) : 1 ≤ changWord ys i := by
  unfold changWord
  by_cases h : i < (changWordList ys).length
  · rw [List.getD_eq_getElem _ _ h]
    rcases changWordList_mem ys _ (List.getElem_mem h) with h1 | h1 <;> omega
  · rw [List.getD_eq_default _ _ (not_lt.mp h)]

theorem changWord_pos (ys : List Bool) :
    ∀ i < 3 * ys.length, 1 ≤ changWord ys i :=
  fun i _ => one_le_changWord ys i

/-- Shift past one block: `changWord (b :: bs) (i + 3) = changWord bs i`. -/
theorem changWord_cons_add (b : Bool) (bs : List Bool) (i : ℕ) :
    changWord (b :: bs) (i + 3) = changWord bs i := by
  unfold changWord
  rw [changWordList,
    List.getD_append_right (changBlock b) (changWordList bs) 1 (i + 3)
      (by rw [changBlock_length]; omega),
    changBlock_length, Nat.add_sub_cancel]

@[simp] theorem changWord_cons_zero (b : Bool) (bs : List Bool) :
    changWord (b :: bs) 0 = 2 := by
  cases b <;> rfl

@[simp] theorem changWord_cons_one (b : Bool) (bs : List Bool) :
    changWord (b :: bs) 1 = 1 := by
  cases b <;> rfl

@[simp] theorem changWord_cons_two (b : Bool) (bs : List Bool) :
    changWord (b :: bs) 2 = if b then 2 else 1 := by
  cases b <;> rfl

/-- Coordinate of the first digit of block `t`. -/
theorem changWord_block_zero (ys : List Bool) (t : ℕ) (ht : t < ys.length) :
    changWord ys (3 * t) = 2 := by
  induction ys generalizing t with
  | nil => simp at ht
  | cons b bs ih =>
    cases t with
    | zero => simp
    | succ t =>
      have h3 : 3 * (t + 1) = 3 * t + 3 := by ring
      rw [h3, changWord_cons_add]
      exact ih t (by simpa using ht)

/-- Coordinate of the second digit of block `t`. -/
theorem changWord_block_one (ys : List Bool) (t : ℕ) (ht : t < ys.length) :
    changWord ys (3 * t + 1) = 1 := by
  induction ys generalizing t with
  | nil => simp at ht
  | cons b bs ih =>
    cases t with
    | zero => simp
    | succ t =>
      have h3 : 3 * (t + 1) + 1 = (3 * t + 1) + 3 := by ring
      rw [h3, changWord_cons_add]
      exact ih t (by simpa using ht)

/-- Coordinate of the third digit of block `t` — carries the Chang label. -/
theorem changWord_block_two (ys : List Bool) (t : ℕ) (ht : t < ys.length) :
    changWord ys (3 * t + 2) = if ys.getD t false then 2 else 1 := by
  induction ys generalizing t with
  | nil => simp at ht
  | cons b bs ih =>
    cases t with
    | zero => simp
    | succ t =>
      have h3 : 3 * (t + 1) + 2 = (3 * t + 2) + 3 := by ring
      rw [h3, changWord_cons_add]
      simpa using ih t (by simpa using ht)

/-! ## Stage A.2 — cumulative valuation -/

@[simp] theorem changBlock_sum (b : Bool) : (changBlock b).sum = if b then 5 else 4 := by
  cases b <;> rfl

theorem changWordList_sum (ys : List Bool) :
    (changWordList ys).sum = 4 * ys.length + ys.count true := by
  induction ys with
  | nil => rfl
  | cons b bs ih =>
    rw [changWordList, List.sum_append, ih, changBlock_sum, List.length_cons,
      List.count_cons]
    cases b <;> simp <;> ring

/-- The prefix sum over `range (3·|ys|)` equals the list sum. -/
theorem changWord_range_sum (ys : List Bool) :
    ∑ i ∈ range (3 * ys.length), changWord ys i = (changWordList ys).sum := by
  induction ys with
  | nil => simp [changWordList]
  | cons b bs ih =>
    have hsplit : 3 * (b :: bs).length = 3 + 3 * bs.length := by
      simp only [List.length_cons]; ring
    rw [hsplit, Finset.sum_range_add]
    have h1 : ∑ x ∈ range 3, changWord (b :: bs) x
        = (changBlock b).sum := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, changWord_cons_zero,
        changWord_cons_one, changWord_cons_two]
      cases b <;> simp [changBlock]
    have h2 : ∑ x ∈ range (3 * bs.length), changWord (b :: bs) (3 + x)
        = ∑ x ∈ range (3 * bs.length), changWord bs x := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [add_comm 3 x, changWord_cons_add]
    rw [h1, h2, ih, changWordList, List.sum_append]

/-- Cumulative valuation of the constructed word. -/
theorem changWord_S (ys : List Bool) :
    S (changWord ys) (3 * ys.length) = 4 * ys.length + ys.count true := by
  unfold S s
  rw [changWord_range_sum, changWordList_sum]

/-! ## Stage A.3 — the seed -/

/-- The least realizer of the constructed word. -/
noncomputable def changSeed (ys : List Bool) : ℕ :=
  leastRealizer (changWord ys) (3 * ys.length)

theorem changSeed_def (ys : List Bool) :
    changSeed ys = leastRealizer (changWord ys) (3 * ys.length) := rfl

private theorem length_pos_of_ne_nil {ys : List Bool} (h : ys ≠ []) :
    0 < ys.length := by
  rcases ys with _ | ⟨b, bs⟩
  · exact absurd rfl h
  · exact Nat.succ_pos _

theorem changSeed_odd (ys : List Bool) (hys : ys ≠ []) : Odd (changSeed ys) := by
  have hN : 1 ≤ 3 * ys.length := by
    have := length_pos_of_ne_nil hys; omega
  exact leastRealizer_odd (changWord ys) (3 * ys.length) hN (changWord_pos ys)

theorem changSeed_realizes (ys : List Bool) (hys : ys ≠ []) :
    Realizes (changWord ys) (3 * ys.length) (changSeed ys) := by
  refine (realizerCongruence (changWord ys) (3 * ys.length) (changSeed ys)
    (changSeed_odd ys hys) (changWord_pos ys)).mpr ?_
  exact leastRealizer_modEq (changWord ys) (3 * ys.length)

/-- **Stage A — finite Chang-history realizability.**
Every nonempty finite binary history determines a positive odd integer whose
accelerated valuation word begins with the constructed word `changWord ys`. -/
theorem changWord_realizable (ys : List Bool) (hys : ys ≠ []) :
    ∃ m : ℕ, 0 < m ∧ Odd m ∧ Realizes (changWord ys) (3 * ys.length) m := by
  refine ⟨changSeed ys, ?_, changSeed_odd ys hys, changSeed_realizes ys hys⟩
  exact (changSeed_odd ys hys).pos

/-! ## Stage A.4 — rigorous seed upper bound (upper bound only) -/

theorem changSeed_lt (ys : List Bool) :
    changSeed ys < 2 ^ (S (changWord ys) (3 * ys.length) + 1) :=
  leastRealizer_lt (changWord ys) (3 * ys.length)

theorem changSeed_lt' (ys : List Bool) :
    changSeed ys < 2 ^ (4 * ys.length + ys.count true + 1) := by
  have := changSeed_lt ys
  rwa [changWord_S ys] at this

/-! ## Stage B — mod-16 / mod-32 valuation lemmas

The accelerated valuation `a n = v₂(3n+1)` and the map `T` are related to the
low residue of `n` by elementary divisibility facts.  We reduce every `a`
statement to `2^k ∣ 3n+1` (via `padicValNat_dvd_iff_le`) before invoking
`omega` on the modular arithmetic. -/

private theorem three_add_one_ne_zero (n : ℕ) : 3 * n + 1 ≠ 0 := by omega

/-- `v₂(3n+1) ≥ k  ↔  2^k ∣ 3n+1`. -/
private theorem a_ge_iff_dvd (n k : ℕ) : k ≤ a n ↔ (2 : ℕ) ^ k ∣ (3 * n + 1) := by
  unfold a
  exact (padicValNat_dvd_iff_le (p := 2) (three_add_one_ne_zero n)).symm

theorem a_ge_two_iff (n : ℕ) : 2 ≤ a n ↔ n % 4 = 1 := by
  rw [a_ge_iff_dvd]
  constructor
  · rintro ⟨c, hc⟩; omega
  · intro h; exact ⟨(3 * n + 1) / 4, by omega⟩

theorem a_eq_one_iff (n : ℕ) : a n = 1 ↔ n % 4 = 3 := by
  have h1 : (1 ≤ a n ↔ (2 : ℕ) ^ 1 ∣ (3 * n + 1)) := a_ge_iff_dvd n 1
  have h2 : (2 ≤ a n ↔ n % 4 = 1) := a_ge_two_iff n
  constructor
  · intro h
    have hd1 : (2 : ℕ) ^ 1 ∣ (3 * n + 1) := h1.mp (by omega)
    have hn2 : ¬ (n % 4 = 1) := fun hh => by have := h2.mpr hh; omega
    obtain ⟨c, hc⟩ := hd1
    omega
  · intro h
    have hle : 1 ≤ a n := h1.mpr ⟨(3 * n + 1) / 2, by omega⟩
    have hlt : ¬ (2 ≤ a n) := fun hh => by have := h2.mp hh; omega
    omega

theorem a_eq_two_iff (n : ℕ) : a n = 2 ↔ n % 8 = 1 := by
  have h2 : (2 ≤ a n ↔ (2 : ℕ) ^ 2 ∣ (3 * n + 1)) := a_ge_iff_dvd n 2
  have h3 : (3 ≤ a n ↔ (2 : ℕ) ^ 3 ∣ (3 * n + 1)) := a_ge_iff_dvd n 3
  constructor
  · intro h
    have hd2 : (2 : ℕ) ^ 2 ∣ (3 * n + 1) := h2.mp (by omega)
    have hnd3 : ¬ ((2 : ℕ) ^ 3 ∣ (3 * n + 1)) := fun hh => by
      have := h3.mpr hh; omega
    obtain ⟨c, hc⟩ := hd2
    rcases Nat.even_or_odd c with ⟨d, hd⟩ | ⟨d, hd⟩
    · exact absurd ⟨d, by omega⟩ hnd3
    · omega
  · intro h
    have hge : 2 ≤ a n := h2.mpr ⟨(3 * n + 1) / 4, by omega⟩
    have hlt : ¬ (3 ≤ a n) := fun hh => by
      obtain ⟨c, hc⟩ := h3.mp hh; omega
    omega

/-- `T n = (3n+1)/4` when `v₂(3n+1) = 2`. -/
theorem T_of_a_eq_two {n : ℕ} (h : a n = 2) : T n = (3 * n + 1) / 4 := by
  unfold T; rw [h]; norm_num

/-- `T n = (3n+1)/2` when `v₂(3n+1) = 1`. -/
theorem T_of_a_eq_one {n : ℕ} (h : a n = 1) : T n = (3 * n + 1) / 2 := by
  unfold T; rw [h]; norm_num

/-- **Event lemma.**  `n ≡ 9 (mod 16)` iff the first two valuations are `(2,1)`. -/
theorem event_iff (n : ℕ) : n % 16 = 9 ↔ a n = 2 ∧ a (T n) = 1 := by
  constructor
  · intro h
    have ha2 : a n = 2 := (a_eq_two_iff n).mpr (by omega)
    refine ⟨ha2, (a_eq_one_iff _).mpr ?_⟩
    rw [T_of_a_eq_two ha2]; omega
  · rintro ⟨ha2, ha1⟩
    have h8 : n % 8 = 1 := (a_eq_two_iff n).mp ha2
    have h4 : T n % 4 = 3 := (a_eq_one_iff _).mp ha1
    rw [T_of_a_eq_two ha2] at h4
    omega

/-- **Label lemma.**  For a Chang event `n ≡ 9 (mod 16)`, the label bit is `1`
(`n ≡ 25 mod 32`) iff the third valuation is `≥ 2`. -/
theorem label_iff (n : ℕ) (hn : n % 16 = 9) :
    n % 32 = 25 ↔ 2 ≤ a (T (T n)) := by
  obtain ⟨ha2, ha1⟩ := (event_iff n).mp hn
  rw [a_ge_two_iff, T_of_a_eq_one ha1, T_of_a_eq_two ha2]
  omega

/-! ## Stage B.3 — transfer to the constructed history -/

/-- At each designated position `3t`, the realized orbit sits in the Chang
burst-ending class `n ≡ 9 (mod 16)`, and its `mod 32` label equals the
prescribed bit `ys[t]`. -/
theorem chang_history_labels (ys : List Bool) (m : ℕ)
    (hm : Realizes (changWord ys) (3 * ys.length) m) (t : ℕ) (ht : t < ys.length) :
    orbit m (3 * t) % 16 = 9 ∧
    (orbit m (3 * t) % 32 = 25 ↔ ys.getD t false = true) := by
  have hlt0 : 3 * t < 3 * ys.length := by omega
  have hlt1 : 3 * t + 1 < 3 * ys.length := by omega
  have hlt2 : 3 * t + 2 < 3 * ys.length := by omega
  have hv0 : a (orbit m (3 * t)) = 2 := by
    have := hm.2 (3 * t) hlt0
    rwa [changWord_block_zero ys t ht] at this
  have hstep1 : orbit m (3 * t + 1) = T (orbit m (3 * t)) := orbit_succ m (3 * t)
  have hv1 : a (T (orbit m (3 * t))) = 1 := by
    have := hm.2 (3 * t + 1) hlt1
    rwa [changWord_block_one ys t ht, hstep1] at this
  have hev : orbit m (3 * t) % 16 = 9 :=
    (event_iff (orbit m (3 * t))).mpr ⟨hv0, hv1⟩
  refine ⟨hev, ?_⟩
  have hstep2 : orbit m (3 * t + 2) = T (T (orbit m (3 * t))) := by
    have h := orbit_succ m (3 * t + 1)
    rwa [hstep1] at h
  have hv2 : a (T (T (orbit m (3 * t)))) = if ys.getD t false then 2 else 1 := by
    have := hm.2 (3 * t + 2) hlt2
    rwa [changWord_block_two ys t ht, hstep2] at this
  rw [label_iff (orbit m (3 * t)) hev, hv2]
  cases ys.getD t false <;> simp

/-! ## Stage C — the designated positions are the only Chang events -/

/-- **C1 — pure word theorem.**  Inside the controlled prefix, the pattern
`(2, 1)` occurs exactly at the block boundaries `j = 3t`. -/
theorem changWord_event_positions (ys : List Bool) (j : ℕ)
    (hj : j + 1 < 3 * ys.length) :
    (changWord ys j = 2 ∧ changWord ys (j + 1) = 1) ↔ ∃ t, t < ys.length ∧ j = 3 * t := by
  constructor
  · rintro ⟨h2, h1⟩
    have hjr : j = 3 * (j / 3) + j % 3 := by omega
    have htK : j / 3 < ys.length := by omega
    rcases (by omega : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2) with h | h | h
    · exact ⟨j / 3, htK, by omega⟩
    · exfalso
      rw [show j = 3 * (j / 3) + 1 from by omega, changWord_block_one ys _ htK] at h2
      omega
    · exfalso
      have ht1K : j / 3 + 1 < ys.length := by omega
      rw [show j + 1 = 3 * (j / 3 + 1) from by omega,
        changWord_block_zero ys _ ht1K] at h1
      omega
  · rintro ⟨t, htK, rfl⟩
    exact ⟨changWord_block_zero ys t htK, changWord_block_one ys t htK⟩

/-- **C2 — transfer to the orbit.**  Inside the controlled prefix, the orbit is
in the Chang burst-ending class `≡ 9 (mod 16)` exactly at the block boundaries. -/
theorem chang_event_positions (ys : List Bool) (m : ℕ)
    (hm : Realizes (changWord ys) (3 * ys.length) m) (j : ℕ)
    (hj : j + 1 < 3 * ys.length) :
    orbit m j % 16 = 9 ↔ ∃ t, t < ys.length ∧ j = 3 * t := by
  have hv0 : a (orbit m j) = changWord ys j := hm.2 j (by omega)
  have hstep : orbit m (j + 1) = T (orbit m j) := orbit_succ m j
  have hv1 : a (T (orbit m j)) = changWord ys (j + 1) := by
    rw [← hstep]; exact hm.2 (j + 1) hj
  rw [event_iff (orbit m j), hv0, hv1]
  exact changWord_event_positions ys j hj

/-- **C3 — no internal events.**  There is no Chang event strictly between two
consecutive block boundaries `3t` and `3(t+1)`. -/
theorem no_internal_chang_event (ys : List Bool) (m : ℕ)
    (hm : Realizes (changWord ys) (3 * ys.length) m) (t : ℕ)
    (ht1 : t + 1 < ys.length) (j : ℕ) (hlo : 3 * t < j) (hhi : j < 3 * (t + 1)) :
    orbit m j % 16 ≠ 9 := by
  intro hev
  obtain ⟨s, _, hjs⟩ := (chang_event_positions ys m hm j (by omega)).mp hev
  omega

/-! ## Stage C.4 — the finite Chang-history theorem -/

/-- **Finite Chang-history realizability (full statement).**
For every nonempty finite binary history `ys` there is a positive odd seed `m`
whose accelerated orbit:

* is in the Chang burst-ending class `≡ 9 (mod 16)`, inside the controlled
  length-`3·|ys|` prefix, **exactly** at the block boundaries `0, 3, …, 3(K-1)`
  (hence the first `K` Chang events are consecutive, with none in between); and
* carries at boundary `3t` the prescribed `mod 32` label `ys[t]`. -/
theorem finite_chang_history_realizable (ys : List Bool) (hys : ys ≠ []) :
    ∃ m : ℕ, 0 < m ∧ Odd m ∧
      (∀ j, j + 1 < 3 * ys.length →
        (orbit m j % 16 = 9 ↔ ∃ t, t < ys.length ∧ j = 3 * t)) ∧
      (∀ t, t < ys.length →
        orbit m (3 * t) % 16 = 9 ∧
        (orbit m (3 * t) % 32 = 25 ↔ ys.getD t false = true)) := by
  obtain ⟨m, hpos, hodd, hm⟩ := changWord_realizable ys hys
  exact ⟨m, hpos, hodd,
    fun j hj => chang_event_positions ys m hm j hj,
    fun t ht => chang_history_labels ys m hm t ht⟩

/-! ## Stage C.5 — language corollary -/

/-- **Every finite binary list occurs as a consecutive Chang history.**
No finite binary history is forbidden: for each `ys` there is a positive odd
`m` whose first `|ys|` Chang events are consecutive (at `0, 3, …`) and whose
`mod 32` labels there read off `ys` bit for bit. -/
theorem every_finite_history_is_a_consecutive_chang_history
    (ys : List Bool) (hys : ys ≠ []) :
    ∃ m : ℕ, 0 < m ∧
      (∀ t, t < ys.length → orbit m (3 * t) % 16 = 9) ∧
      (∀ t, t < ys.length →
        (orbit m (3 * t) % 32 = 25 ↔ ys.getD t false = true)) ∧
      (∀ t j, t + 1 < ys.length → 3 * t < j → j < 3 * (t + 1) →
        orbit m j % 16 ≠ 9) := by
  obtain ⟨m, hpos, _, hm⟩ := changWord_realizable ys hys
  refine ⟨m, hpos, ?_, ?_, ?_⟩
  · exact fun t ht => (chang_history_labels ys m hm t ht).1
  · exact fun t ht => (chang_history_labels ys m hm t ht).2
  · exact fun t j ht1 hlo hhi => no_internal_chang_event ys m hm t ht1 j hlo hhi

end EOC.ChangHistory
