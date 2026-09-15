import EOC.SurvivorClusters
import EOC.CapacityBounds
import EOC.SurvivorCounting

/-!
# The split-depth bijection: odd residues mod `2^Q` ↔ valuation prefixes of sum `≤ Q − 1`

For an odd seed `r` and `Q ≥ 1`, its **`Q`-prefix** is the longest prefix `d_1 … d_k` of its
valuation word with `S_k ≤ Q − 1`; equivalently `k = prefixLen Q r` is the first index with
`S_{k+1} ≥ Q`. This is exactly the information about the valuation word carried by `r mod 2^Q`.

Main results (finite, exact):

* `prefixLen_spec` — `S_k + 1 ≤ Q ≤ S_{k+1}`, `k < Q`, and `2^(Q − S_k) ∣ 3·T^k(r) + 1`.
* `prefix_of_modEq` — **the `Q`-prefix depends only on `r mod 2^Q`**: congruent odd seeds have the
  same prefix length and the same prefix digits.
* `prefix_injective` — distinct odd residues `< 2^Q` have distinct `Q`-prefixes.
* `prefix_bijective` — the map `r ↦ (k, first k digits)` is a bijection from the `2^(Q−1)` odd
  residues below `2^Q` onto `⋃_{k<Q} {positive words of length k and total ≤ Q − 1}` (which also
  has `∑_{k<Q} C(Q−1, k) = 2^(Q−1)` elements, by `CapacityBounds.card_feasibleWords`).
* `pair_shared_survival` — **finite pair-survival theorem**: odd `x ≡ y (mod 2^Q)` share their
  first `k = prefixLen Q x` digits, hence are `c`-confined through `k` simultaneously.

In the 2-adic (Haar) model this is the combinatorial core of the split-depth survival law: for
`v₂(x − y) = Q` the shared prefix is the `Q`-prefix of `x mod 2^Q`, which is uniform over the
`2^(Q−1)` words of sum `≤ Q − 1` when `x mod 2^Q` is uniform.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace SplitPrefix

open Finset SurvivorClusters CapacityBounds SuffixTransport

theorem le_S_orbitWord {r : ℕ} (hr : Odd r) (j : ℕ) : j ≤ S (orbitWord r) j := by
  induction j with
  | zero => exact Nat.zero_le _
  | succ j ih =>
      have h1 := hd_pos_of_orbit hr j
      simp only [S] at ih ⊢
      rw [s_succ]
      simp only [orbitWord]
      omega

theorem exists_crossing (Q : ℕ) {r : ℕ} (hr : Odd r) : ∃ k, Q ≤ S (orbitWord r) (k + 1) :=
  ⟨Q, le_trans (Nat.le_succ Q) (le_S_orbitWord hr (Q + 1))⟩

open Classical in
/-- Length of the `Q`-prefix: the first `k` with `S_{k+1} ≥ Q` (and `0` for even input). -/
noncomputable def prefixLen (Q r : ℕ) : ℕ :=
  if hr : Odd r then Nat.find (exists_crossing Q hr) else 0

theorem S_succ_orbitWord (r k : ℕ) :
    S (orbitWord r) (k + 1) = S (orbitWord r) k + a (orbit r k) := by
  simp only [S]
  rw [s_succ]
  rfl

theorem prefixLen_spec {Q r : ℕ} (hQ : 1 ≤ Q) (hr : Odd r) :
    S (orbitWord r) (prefixLen Q r) + 1 ≤ Q ∧ Q ≤ S (orbitWord r) (prefixLen Q r + 1) ∧
      prefixLen Q r < Q ∧
      2 ^ (Q - S (orbitWord r) (prefixLen Q r)) ∣ 3 * orbit r (prefixLen Q r) + 1 := by
  classical
  have hdef : prefixLen Q r = Nat.find (exists_crossing Q hr) := by simp [prefixLen, hr]
  set k := prefixLen Q r with hk
  have h2 : Q ≤ S (orbitWord r) (k + 1) := by rw [hdef]; exact Nat.find_spec (exists_crossing Q hr)
  have h1 : S (orbitWord r) k + 1 ≤ Q := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0]; simp [S, s]; omega
    · obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hmin := Nat.find_min (exists_crossing Q hr) (show k' < Nat.find (exists_crossing Q hr) by
        rw [← hdef]; omega)
      rw [hk']
      omega
  have h3 : k < Q := by have := le_S_orbitWord hr k; omega
  have h4 : 2 ^ (Q - S (orbitWord r) k) ∣ 3 * orbit r k + 1 := by
    rw [S_succ_orbitWord] at h2
    exact (pow_dvd_pow 2 (by omega)).trans (two_pow_a_dvd (orbit r k))
  exact ⟨h1, h2, h3, h4⟩

/-- Characterization: `prefixLen Q r` is the unique `k` with `S_k + 1 ≤ Q ≤ S_{k+1}`. -/
theorem prefixLen_eq_of {Q r k : ℕ} (_hQ : 1 ≤ Q) (hr : Odd r) (h1 : S (orbitWord r) k + 1 ≤ Q)
    (h2 : Q ≤ S (orbitWord r) (k + 1)) : prefixLen Q r = k := by
  classical
  have hdef : prefixLen Q r = Nat.find (exists_crossing Q hr) := by simp [prefixLen, hr]
  rw [hdef]
  set nf := Nat.find (exists_crossing Q hr) with hnf
  have hspec : Q ≤ S (orbitWord r) (nf + 1) := Nat.find_spec (exists_crossing Q hr)
  have hle : nf ≤ k := Nat.find_min' _ h2
  refine le_antisymm hle ?_
  by_contra hlt
  push Not at hlt
  -- S is monotone: S_{nf+1} ≤ S_k
  have hmono : S (orbitWord r) (nf + 1) ≤ S (orbitWord r) k := by
    simp only [S, s]
    exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (by omega))
  omega

/-- The carry identity along a shared prefix: `2^{S_k} (T^k y − T^k x) = 3^k (y − x)`. -/
theorem carry_diff {x y k : ℕ} (hx : Odd x) (hy : Odd y)
    (hag : ∀ i < k, orbitWord x i = orbitWord y i) :
    (2 : ℤ) ^ S (orbitWord x) k * ((orbit y k : ℤ) - orbit x k) = 3 ^ k * ((y : ℤ) - x) := by
  have hrx : Realizes (orbitWord x) k x := ⟨hx, fun j _ => rfl⟩
  have hry : Realizes (orbitWord x) k y := ⟨hy, fun j hj => (hag j hj).symm⟩
  have cx := realizes_carry hrx le_rfl
  have cy := realizes_carry hry le_rfl
  have cx' : ((2 ^ S (orbitWord x) k * orbit x k : ℕ) : ℤ) =
      ((3 ^ k * x + q (orbitWord x) k : ℕ) : ℤ) := by
    rw [cx]
  have cy' : ((2 ^ S (orbitWord x) k * orbit y k : ℕ) : ℤ) =
      ((3 ^ k * y + q (orbitWord x) k : ℕ) : ℤ) := by
    rw [cy]
  push_cast at cx' cy'
  linarith

/-- If both next steps are divisible by `2^g`, the states differ by a multiple of `2^g`. -/
private theorem dvd_state_diff {g : ℕ} {m m' : ℕ} (h : 2 ^ g ∣ 3 * m + 1)
    (h' : 2 ^ g ∣ 3 * m' + 1) :
    (2 : ℤ) ^ g ∣ ((m' : ℤ) - m) := by
  have h1 : (2 : ℤ) ^ g ∣ 3 * ((m' : ℤ) - m) := by
    have a1 : (2 : ℤ) ^ g ∣ ((3 * m + 1 : ℕ) : ℤ) := by exact_mod_cast h
    have a2 : (2 : ℤ) ^ g ∣ ((3 * m' + 1 : ℕ) : ℤ) := by exact_mod_cast h'
    have hd := dvd_sub a2 a1
    have he : ((3 * m' + 1 : ℕ) : ℤ) - ((3 * m + 1 : ℕ) : ℤ) = 3 * ((m' : ℤ) - m) := by
      push_cast
      ring
    rwa [he] at hd
  have hcop : IsCoprime ((2 : ℤ) ^ g) 3 :=
    IsCoprime.pow_left (Int.isCoprime_iff_gcd_eq_one.mpr (by decide))
  exact hcop.dvd_of_dvd_mul_left h1

/-- **The `Q`-prefix depends only on `r mod 2^Q`.** -/
theorem prefix_of_modEq {Q x y : ℕ} (hQ : 1 ≤ Q) (hx : Odd x) (hy : Odd y)
    (hxy : x ≡ y [MOD 2 ^ Q]) :
    prefixLen Q y = prefixLen Q x ∧ ∀ i < prefixLen Q x, orbitWord x i = orbitWord y i := by
  obtain ⟨h1, h2, -, h4⟩ := prefixLen_spec hQ hx
  set k := prefixLen Q x with hk
  set Sk := S (orbitWord x) k with hSk
  have hxy' : x ≡ y [MOD 2 ^ (Sk + 1)] :=
    Nat.ModEq.of_dvd (pow_dvd_pow 2 (by omega)) hxy
  have hag := (confined_iff_of_modEq hx hy hxy' 0).1
  have hSeq : S (orbitWord y) k = Sk := by
    simp only [S, s, hSk]
    exact Finset.sum_congr rfl fun i hi => (hag i (Finset.mem_range.mp hi)).symm
  -- next-step divisibility transfers
  have hcd := carry_diff hx hy hag
  have hQdvd : (2 : ℤ) ^ Q ∣ (y : ℤ) - x := by
    have := (Nat.modEq_iff_dvd.mp hxy)
    exact_mod_cast this
  have hdiv : (2 : ℤ) ^ (Q - Sk) ∣ (orbit y k : ℤ) - orbit x k := by
    have hmul : (2 : ℤ) ^ Sk * 2 ^ (Q - Sk) ∣ 2 ^ Sk * ((orbit y k : ℤ) - orbit x k) := by
      rw [← pow_add, show Sk + (Q - Sk) = Q by omega, hcd]
      exact Dvd.dvd.mul_left hQdvd _
    exact (mul_dvd_mul_iff_left (by positivity)).mp hmul
  have h4y : 2 ^ (Q - Sk) ∣ 3 * orbit y k + 1 := by
    have a1 : (2 : ℤ) ^ (Q - Sk) ∣ ((3 * orbit x k + 1 : ℕ) : ℤ) := by exact_mod_cast h4
    have : ((3 * orbit y k + 1 : ℕ) : ℤ) =
        ((3 * orbit x k + 1 : ℕ) : ℤ) + 3 * ((orbit y k : ℤ) - orbit x k) := by
      push_cast; ring
    have hz : (2 : ℤ) ^ (Q - Sk) ∣ ((3 * orbit y k + 1 : ℕ) : ℤ) := by
      rw [this]; exact dvd_add a1 (Dvd.dvd.mul_left hdiv 3)
    exact_mod_cast hz
  have hay : Q - Sk ≤ a (orbit y k) := by
    unfold a
    exact (padicValNat_dvd_iff_le (by omega)).mp h4y
  have h2y : Q ≤ S (orbitWord y) (k + 1) := by
    rw [S_succ_orbitWord, hSeq]
    omega
  have h1y : S (orbitWord y) k + 1 ≤ Q := by rw [hSeq]; exact h1
  exact ⟨prefixLen_eq_of hQ hy h1y h2y, hag⟩

/-- Distinct odd residues below `2^Q` have distinct `Q`-prefixes. -/
theorem prefix_injective {Q x y : ℕ} (hQ : 1 ≤ Q) (hx : Odd x) (hy : Odd y) (hxQ : x < 2 ^ Q)
    (hyQ : y < 2 ^ Q) (hlen : prefixLen Q x = prefixLen Q y)
    (hag : ∀ i < prefixLen Q x, orbitWord x i = orbitWord y i) : x = y := by
  obtain ⟨h1, -, -, h4⟩ := prefixLen_spec hQ hx
  obtain ⟨-, -, -, h4y⟩ := prefixLen_spec hQ hy
  set k := prefixLen Q x with hk
  set Sk := S (orbitWord x) k with hSk
  have hSeq : S (orbitWord y) k = Sk := by
    simp only [S, s, hSk]
    exact Finset.sum_congr rfl fun i hi => (hag i (Finset.mem_range.mp hi)).symm
  rw [← hlen, hSeq] at h4y
  have hdiv := dvd_state_diff h4 h4y
  have hcd := carry_diff hx hy hag
  have hQdvd : (2 : ℤ) ^ Q ∣ 3 ^ k * ((y : ℤ) - x) := by
    rw [← hcd, show Q = Sk + (Q - Sk) by omega, pow_add]
    exact mul_dvd_mul_left _ hdiv
  have hcop : IsCoprime ((2 : ℤ) ^ Q) ((3 : ℤ) ^ k) :=
    IsCoprime.pow (Int.isCoprime_iff_gcd_eq_one.mpr (by decide))
  have hd := hcop.dvd_of_dvd_mul_left hQdvd
  have hx2 : (x : ℤ) < 2 ^ Q := by exact_mod_cast hxQ
  have hy2 : (y : ℤ) < 2 ^ Q := by exact_mod_cast hyQ
  have hx0 : (0 : ℤ) ≤ x := Int.natCast_nonneg x
  have hy0 : (0 : ℤ) ≤ y := Int.natCast_nonneg y
  have hlt : |(y : ℤ) - x| < 2 ^ Q := by
    rw [abs_lt]
    constructor <;> linarith
  by_contra hne
  have hne' : (y : ℤ) - x ≠ 0 := by omega
  have := Int.le_of_dvd (abs_pos.mpr hne') ((dvd_abs _ _).mpr hd)
  linarith

private theorem heq_apply {k k' : ℕ} {w : FiniteValuationWord k} {w' : FiniteValuationWord k'}
    (hk : k = k') (h : w ≍ w') (i : ℕ) (hi : i < k) : w ⟨i, hi⟩ = w' ⟨i, hk ▸ hi⟩ := by
  subst hk
  rw [eq_of_heq h]

open Classical in
/-- The `Q`-prefix map, as a sigma value `⟨k, first k digits⟩`. -/
noncomputable def prefixMap (Q r : ℕ) : Σ k : ℕ, FiniteValuationWord k :=
  ⟨prefixLen Q r, SurvivorCounting.prefixWord (prefixLen Q r) r⟩

/-- The target set: positive words of length `k < Q` and total `≤ Q − 1`. -/
def prefixTarget (Q : ℕ) : Finset (Σ k : ℕ, FiniteValuationWord k) :=
  (range Q).sigma fun k => feasibleWords k (Q - 1)

theorem total_prefixWord (k r : ℕ) :
    (SurvivorCounting.prefixWord k r).total = S (orbitWord r) k := by
  rw [FiniteValuationWord.total_eq_sum_univ]
  simp only [S, s, orbitWord, SurvivorCounting.prefixWord]
  exact Fin.sum_univ_eq_sum_range (fun i => a (orbit r i)) k

theorem card_feasibleWords_zero (B : ℕ) : (feasibleWords 0 B).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨fun i => i.elim0, ?_⟩
  ext w
  simp only [mem_singleton, mem_feasibleWords]
  constructor
  · intro _; funext i; exact i.elim0
  · intro _; exact ⟨fun i => i.elim0, by simp [FiniteValuationWord.total_eq_sum_univ]⟩

theorem card_prefixTarget {Q : ℕ} (hQ : 1 ≤ Q) : (prefixTarget Q).card = 2 ^ (Q - 1) := by
  rw [prefixTarget, card_sigma]
  have : ∀ k ∈ range Q, (feasibleWords k (Q - 1)).card = Nat.choose (Q - 1) k := by
    intro k _
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [card_feasibleWords_zero, Nat.choose_zero_right]
    · exact card_feasibleWords hk (Q - 1)
  rw [sum_congr rfl this]
  have h := Nat.sum_range_choose (Q - 1)
  rwa [Nat.sub_add_cancel hQ] at h

theorem card_odd_range {Q : ℕ} (hQ : 1 ≤ Q) : ((range (2 ^ Q)).filter Odd).card = 2 ^ (Q - 1) := by
  have himg : (range (2 ^ Q)).filter Odd = (range (2 ^ (Q - 1))).image fun i => 2 * i + 1 := by
    have h2 : 2 ^ Q = 2 * 2 ^ (Q - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    ext r
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hr, ⟨i, rfl⟩⟩
      exact ⟨i, by omega, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨by omega, ⟨i, rfl⟩⟩
  rw [himg, card_image_of_injective _ (fun i j h => by simpa using h), card_range]

theorem prefixMap_mem {Q r : ℕ} (hQ : 1 ≤ Q) (hr : Odd r) : prefixMap Q r ∈ prefixTarget Q := by
  obtain ⟨h1, -, h3, -⟩ := prefixLen_spec hQ hr
  rw [prefixTarget, mem_sigma]
  refine ⟨mem_range.mpr h3, mem_feasibleWords.mpr ⟨fun i => hd_pos_of_orbit hr i, ?_⟩⟩
  change (SurvivorCounting.prefixWord (prefixLen Q r) r).total ≤ Q - 1
  rw [total_prefixWord]
  omega

/-- **The split-depth bijection.** The `Q`-prefix map is a bijection from the odd residues below
`2^Q` onto the positive words of length `< Q` and total `≤ Q − 1`. -/
theorem prefix_bijective {Q : ℕ} (hQ : 1 ≤ Q) :
    Set.BijOn (prefixMap Q) ((range (2 ^ Q)).filter Odd : Set ℕ) (prefixTarget Q : Set _) := by
  have hmaps : Set.MapsTo (prefixMap Q) ((range (2 ^ Q)).filter Odd : Set ℕ) (prefixTarget Q) := by
    intro r hr
    rw [coe_filter] at hr
    exact prefixMap_mem hQ hr.2
  have hinj : Set.InjOn (prefixMap Q) ((range (2 ^ Q)).filter Odd : Set ℕ) := by
    intro x hx y hy hxy
    rw [coe_filter] at hx hy
    have hx' := mem_range.mp hx.1
    have hy' := mem_range.mp hy.1
    simp only [prefixMap, Sigma.mk.inj_iff] at hxy
    obtain ⟨hlen, hw⟩ := hxy
    refine prefix_injective hQ hx.2 hy.2 hx' hy' hlen fun i hi => ?_
    have h := heq_apply hlen hw i hi
    simpa [orbitWord, SurvivorCounting.prefixWord] using h
  refine ⟨hmaps, hinj, ?_⟩
  -- surjectivity by cardinality
  have hcard : (prefixTarget Q).card ≤ ((range (2 ^ Q)).filter Odd).card := by
    rw [card_prefixTarget hQ, card_odd_range hQ]
  intro p hp
  obtain ⟨r, hr, hrp⟩ := Finset.surj_on_of_inj_on_of_card_le (s := (range (2 ^ Q)).filter Odd)
    (t := prefixTarget Q) (fun r _ => prefixMap Q r) (fun r hr => hmaps (by simpa using hr))
    (fun x y hx hy h => hinj (by simpa using hx) (by simpa using hy) h) hcard p hp
  exact ⟨r, by simpa using hr, hrp.symm⟩

/-- **Finite pair-survival theorem.** Odd seeds congruent mod `2^Q` share their first
`k = prefixLen Q x` valuation digits, hence are `c`-confined through `k` simultaneously. -/
theorem pair_shared_survival {Q x y : ℕ} (hQ : 1 ≤ Q) (hx : Odd x) (hy : Odd y)
    (hxy : x ≡ y [MOD 2 ^ Q]) (c : ℝ) :
    prefixLen Q y = prefixLen Q x ∧
      (Confined c (orbitWord x) (prefixLen Q x) ↔ Confined c (orbitWord y) (prefixLen Q x)) := by
  obtain ⟨hlen, hag⟩ := prefix_of_modEq hQ hx hy hxy
  exact ⟨hlen, ⟨fun h => confined_congr hag h,
    fun h => confined_congr (fun i hi => (hag i hi).symm) h⟩⟩

end SplitPrefix
end EOC
