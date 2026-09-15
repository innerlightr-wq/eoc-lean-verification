import EOC.SuffixTransport

/-!
# Exact finite lemmas behind survivor clustering

Deep survivors below `X` cluster mainly along single orbits: a survivor `μ` and some of its own
orbit values `T^t μ < X` are simultaneously confined. The finite statements here are exact.

* `orbitWord_orbit` — the valuation word of `T^t μ` is the suffix `σ^t` of the word of `μ`.
* `R_shiftWord` — `R_{σ^t d}(n) = R_d(t+n) − R_d(t)`.
* `confined_orbit_iff` — **on-orbit survival**: `T^t μ` is `c`-confined for `N` steps iff the drift
  of `μ` on `[t, t+N]` stays below `R_μ(t) + c`. (For `c = 0`: `t` is a future maximum.)
* `predecessor` — **backward cluster step**: for odd `y ≡ 2 (mod 3)`, `x = (2y−1)/3` is odd,
  smaller, has `a x = 1` and `T x = y`; and if `y` is `c`-confined for `N` steps (`c ≥ 0`) then
  `x` is `c`-confined for `N+1` steps (`confined_predecessor`). So every confined `y ≡ 2 (mod 3)`
  has a smaller confined predecessor on the same orbit.
* `realizes_of_modEq` / `confined_iff_of_modEq` — **shared prefix**: odd seeds congruent modulo
  `2^(S_k+1)` (`S_k` the valuation sum of the first `k` digits of one of them) have the same
  first `k` digits, hence identical confinement status through `k`. With
  `PairValuation.orbit_pair_valuation` this identifies the shared-survival prefix of a pair with
  its 2-adic split depth.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace SurvivorClusters

open SuffixTransport

/-- The valuation word of the actual orbit of `μ`. -/
noncomputable def orbitWord (μ : ℕ) : ℕ → ℕ := fun i => a (orbit μ i)

theorem orbitWord_orbit (μ t : ℕ) : orbitWord (orbit μ t) = shiftWord (orbitWord μ) t := by
  funext i
  simp only [orbitWord, shiftWord]
  rw [orbit_add μ t i]

theorem R_shiftWord (d : ℕ → ℕ) (t n : ℕ) : R (shiftWord d t) n = R d (t + n) - R d t := by
  unfold R
  rw [s_add_shiftWord d t n]
  push_cast
  ring

/-- **On-orbit survival.** `T^t μ` is `c`-confined for `N` steps iff `R_μ(t+n) ≤ R_μ(t) + c` for
every `n ≤ N`. -/
theorem confined_orbit_iff (μ t N : ℕ) (c : ℝ) :
    Confined c (orbitWord (orbit μ t)) N ↔
      ∀ n ≤ N, R (orbitWord μ) (t + n) ≤ R (orbitWord μ) t + c := by
  rw [orbitWord_orbit]
  constructor
  · intro h n hn
    have := h n hn
    rw [R_shiftWord] at this
    linarith
  · intro h n hn
    rw [R_shiftWord]
    linarith [h n hn]

/-- The `d = 1` predecessor `(2y − 1)/3` of an odd `y ≡ 2 (mod 3)`. -/
theorem predecessor {y : ℕ} (hy : Odd y) (h3 : y % 3 = 2) :
    let x := (2 * y - 1) / 3
    Odd x ∧ x < y ∧ 3 * x + 1 = 2 * y ∧ a x = 1 ∧ T x = y := by
  intro x
  obtain ⟨k, rfl⟩ := hy
  have hx3 : 3 * x = 2 * (2 * k + 1) - 1 := by
    simp only [x]
    omega
  have hxe : 3 * x + 1 = 2 * (2 * k + 1) := by omega
  have hodd : Odd x := by
    refine Nat.odd_iff.mpr ?_
    omega
  have ha : a x = 1 := by
    unfold a
    rw [hxe, padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num)]
    have : padicValNat 2 (2 * k + 1) = 0 :=
      padicValNat.eq_zero_of_not_dvd (by omega)
    omega
  refine ⟨hodd, by omega, hxe, ha, ?_⟩
  unfold T
  rw [ha, hxe]
  omega

/-- **Backward cluster step.** If odd `y ≡ 2 (mod 3)` is `c`-confined for `N` steps (`c ≥ 0`),
its predecessor `x = (2y − 1)/3` is `c`-confined for `N + 1` steps. -/
theorem confined_predecessor {y : ℕ} (hy : Odd y) (h3 : y % 3 = 2) {c : ℝ} (hc : 0 ≤ c) {N : ℕ}
    (hconf : Confined c (orbitWord y) N) :
    Confined c (orbitWord ((2 * y - 1) / 3)) (N + 1) := by
  obtain ⟨-, -, -, ha, hT⟩ := predecessor hy h3
  set x := (2 * y - 1) / 3 with hxdef
  have hword : orbitWord (orbit x 1) = orbitWord y := by
    rw [show orbit x 1 = T x from rfl, hT]
  have hR1 : R (orbitWord x) 1 = 1 - alpha := by
    simp [R, s, orbitWord, ha]
  intro j hj
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · simpa [R, s] using hc
  · obtain ⟨n, rfl⟩ : ∃ n, j = 1 + n := ⟨j - 1, by omega⟩
    have hshift := R_shiftWord (orbitWord x) 1 n
    rw [← orbitWord_orbit, hword] at hshift
    have hyn := hconf n (by omega)
    have hα := one_lt_alpha
    linarith

/-- Odd seeds congruent to a realizer modulo `2^(S_k + 1)` realize the same first `k` digits. -/
theorem realizes_of_modEq {d : ℕ → ℕ} {k x y : ℕ} (hx : Realizes d k x)
    (hd_pos : ∀ i < k, 1 ≤ d i) (hy : Odd y) (hxy : x ≡ y [MOD 2 ^ (S d k + 1)]) :
    Realizes d k y := by
  have hcx := (realizerCongruence d k x hx.1 hd_pos).mp hx
  refine (realizerCongruence d k y hy hd_pos).mpr ?_
  have : 3 ^ k * x + q d k ≡ 3 ^ k * y + q d k [MOD 2 ^ (S d k + 1)] :=
    Nat.ModEq.add_right _ (Nat.ModEq.mul_left _ hxy)
  exact this.symm.trans hcx

/-- **Shared prefix, shared survival.** If odd `x, y` are congruent modulo `2^(S_k(x) + 1)`, they
have the same first `k` valuation digits, so they are `c`-confined through `k` simultaneously. -/
theorem confined_iff_of_modEq {k x y : ℕ} (hx : Odd x) (hy : Odd y)
    (hxy : x ≡ y [MOD 2 ^ (S (orbitWord x) k + 1)]) (c : ℝ) :
    (∀ i < k, orbitWord x i = orbitWord y i) ∧
      (Confined c (orbitWord x) k ↔ Confined c (orbitWord y) k) := by
  have hreal : Realizes (orbitWord x) k x := ⟨hx, fun j _ => rfl⟩
  have hpos : ∀ i < k, 1 ≤ orbitWord x i := fun i _ => hd_pos_of_orbit hx i
  have hry := realizes_of_modEq hreal hpos hy hxy
  have hagree : ∀ i < k, orbitWord x i = orbitWord y i := fun i hi => (hry.2 i hi).symm
  exact ⟨hagree, ⟨fun h => confined_congr hagree h,
    fun h => confined_congr (fun i hi => (hagree i hi).symm) h⟩⟩

end SurvivorClusters
end EOC
