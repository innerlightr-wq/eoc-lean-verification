import EOC.OddBlack

/-!
# Layered transfer sums and the local-window (superblock) bound

The odd-black round reduced the remaining analytic input to `OddBlack.OddDarkPressure`: an
exponential-moment
bound for the number of dark odd cells of a confined word.  The local-window route bounds that
moment by a
product over windows of `K` consecutive pair blocks, so that a *local* bound (uniform over window
anchors and
boundary states) suffices.  This file formalizes the abstract mechanism and the exponent
bookkeeping.

* `ker` / `val` — the layered transfer kernel and its total mass (`val w l n x = ∑_y ker w l n x
y`).
* `ker_add`, `val_add` — Chapman–Kolmogorov: an `(m+n)`-layer sum splits at the intermediate state.
* `val_le_pow_of_window` — **window product bound**: if every `K`-layer block started anywhere has
mass ≤ `M`,
  then a `W*K`-layer sum has mass ≤ `M^W`.  No `1/K` loss: `W = n/K` windows each contributing `M`.
* `val_le_of_window_rem` — with a remainder of `< K` layers bounded by `Mrem`, `val ≤ M^W * Mrem`.
* `logBookkeeping` — if `M ≤ 2^(2Kθ)` and the remainder is at most `s^K`, then
  `(1/J) log₂ (total) ≤ θ + K log₂ s / J`: the local exponent transfers to the global one up to
  `O(K/J)`.

The bridge from `val` to `∑_{P ∈ shellP} s^{N_odd P}` is the layered representation of the confined
word set
(classes = even prefix sums, blocks = digit pairs); `OddBlack.sum_class_prod` already factors a
class sum over
blocks.  That bridge is not formalized here, so the results below are stated for the abstract
layered sum.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace LocalWindow

open Finset

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- `ker w l n x y`: total weight of `n`-layer paths from state `x` at layer `l` to state `y`. -/
noncomputable def ker (w : ℕ → σ → σ → ℝ) : ℕ → ℕ → σ → σ → ℝ
  | _, 0, x, y => if x = y then 1 else 0
  | l, (n + 1), x, z => ∑ y : σ, w l x y * ker w (l + 1) n y z

/-- `val w l n x`: total weight of all `n`-layer paths from `x`. -/
noncomputable def val (w : ℕ → σ → σ → ℝ) (l n : ℕ) (x : σ) : ℝ := ∑ y : σ, ker w l n x y

theorem ker_zero (w : ℕ → σ → σ → ℝ) (l : ℕ) (x y : σ) :
    ker w l 0 x y = if x = y then 1 else 0 := rfl

theorem ker_succ (w : ℕ → σ → σ → ℝ) (l n : ℕ) (x z : σ) :
    ker w l (n + 1) x z = ∑ y : σ, w l x y * ker w (l + 1) n y z := rfl

theorem val_zero (w : ℕ → σ → σ → ℝ) (l : ℕ) (x : σ) : val w l 0 x = 1 := by
  unfold val
  simp only [ker_zero]
  rw [Finset.sum_ite_eq univ x (fun _ => (1 : ℝ))]
  simp

theorem ker_nonneg {w : ℕ → σ → σ → ℝ} (hw : ∀ l x y, 0 ≤ w l x y) (l n : ℕ) (x y : σ) :
    0 ≤ ker w l n x y := by
  induction n generalizing l x with
  | zero => rw [ker_zero]; split_ifs <;> norm_num
  | succ n ih => rw [ker_succ]; exact sum_nonneg fun y _ => mul_nonneg (hw l x y) (ih _ _)

theorem val_nonneg {w : ℕ → σ → σ → ℝ} (hw : ∀ l x y, 0 ≤ w l x y) (l n : ℕ) (x : σ) :
    0 ≤ val w l n x := sum_nonneg fun y _ => ker_nonneg hw l n x y

/-- **Chapman–Kolmogorov** for the layered kernel. -/
theorem ker_add (w : ℕ → σ → σ → ℝ) (l m n : ℕ) (x z : σ) :
    ker w l (m + n) x z = ∑ y : σ, ker w l m x y * ker w (l + m) n y z := by
  induction m generalizing l x with
  | zero =>
    simp only [Nat.zero_add, ker_zero, add_zero, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq univ x (fun y => ker w l n y z)]
    simp
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega, ker_succ]
    rw [sum_congr rfl (fun y _ => by rw [ih (l + 1) y])]
    simp only [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun u _ => ?_
    rw [ker_succ, sum_mul]
    refine sum_congr rfl fun y _ => ?_
    rw [show l + 1 + m = l + (m + 1) by omega]
    ring

/-- The total mass splits at the intermediate layer. -/
theorem val_add (w : ℕ → σ → σ → ℝ) (l m n : ℕ) (x : σ) :
    val w l (m + n) x = ∑ y : σ, ker w l m x y * val w (l + m) n y := by
  unfold val
  rw [sum_congr rfl (fun z _ => ker_add w l m n x z), sum_comm]
  exact sum_congr rfl fun y _ => by rw [mul_sum]

theorem val_le_of_le {w : ℕ → σ → σ → ℝ} (hw : ∀ l x y, 0 ≤ w l x y) {l m n : ℕ} {B : ℝ}
    (hB : ∀ y, val w (l + m) n y ≤ B) (x : σ) : val w l (m + n) x ≤ val w l m x * B := by
  rw [val_add]
  calc ∑ y : σ, ker w l m x y * val w (l + m) n y
      ≤ ∑ y : σ, ker w l m x y * B :=
        sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hB y) (ker_nonneg hw l m x y)
    _ = val w l m x * B := by rw [← sum_mul]; rfl

/-- **Window product bound.**  If every `K`-layer window (any anchor, any state) has mass at most
`M`, then a
`W*K`-layer sum has mass at most `M ^ W`: `W = n/K` windows, each contributing `M` — no `1/K` loss.
-/
theorem val_le_pow_of_window {w : ℕ → σ → σ → ℝ} (hw : ∀ l x y, 0 ≤ w l x y) {K : ℕ} {M : ℝ}
    (hM : ∀ l y, val w l K y ≤ M) (W l : ℕ) (x : σ) : val w l (W * K) x ≤ M ^ W := by
  have hM0 : 0 ≤ M := le_trans (val_nonneg hw l K x) (hM l x)
  induction W generalizing l x with
  | zero => rw [Nat.zero_mul, val_zero]; norm_num
  | succ W ih =>
    calc val w l ((W + 1) * K) x = val w l (K + W * K) x := by
          rw [show (W + 1) * K = K + W * K by ring]
      _ ≤ val w l K x * M ^ W := val_le_of_le hw (fun y => ih (l + K) y) x
      _ ≤ M * M ^ W := mul_le_mul_of_nonneg_right (hM l x) (pow_nonneg hM0 W)
      _ = M ^ (W + 1) := by ring

/-- **With a remainder.**  `n = W*K + ρ` layers: the windows give `M ^ W`, the remainder `Mrem`. -/
theorem val_le_of_window_rem {w : ℕ → σ → σ → ℝ} (hw : ∀ l x y, 0 ≤ w l x y) {K W ρ : ℕ}
    {M Mrem : ℝ}
    (hM : ∀ l y, val w l K y ≤ M) (hMrem : ∀ y, val w (W * K) ρ y ≤ Mrem)
    (hMrem0 : 0 ≤ Mrem) (x : σ) : val w 0 (W * K + ρ) x ≤ M ^ W * Mrem :=
  (val_le_of_le hw (by simpa using hMrem) x).trans
    (mul_le_mul_of_nonneg_right (val_le_pow_of_window hw hM W 0 x) hMrem0)

/-! ## Collatz–Wielandt relaxation: a super-eigenvector replaces the supremum -/

theorem val_succ (w : ℕ → σ → σ → ℝ) (l n : ℕ) (x : σ) :
    val w l (n + 1) x = ∑ y : σ, w l x y * val w (l + 1) n y := by
  have h : val w l (1 + n) x = ∑ y : σ, ker w l 1 x y * val w (l + 1) n y := val_add w l 1 n x
  rw [show n + 1 = 1 + n by omega, h]
  refine sum_congr rfl fun y _ => ?_
  have : ker w l 1 x y = w l x y := by
    rw [ker_succ]
    rw [sum_congr rfl (fun z _ => by rw [ker_zero])]
    simp
  rw [this]

/-- **Collatz–Wielandt / super-eigenvector bound.**  A positive weight `h` with
`∑_y w l x y * h (l+1) y ≤ M * h l x` replaces the supremum hypothesis: states where the window mass
is large are allowed, provided `h` is large there.  Then `val w l n x ≤ M ^ n * h l x / c` whenever
`c ≤ h` at the final layer.  (`h ≡ 1` recovers the crude sup bound.) -/
theorem val_le_of_superEigen {w : ℕ → σ → σ → ℝ} (hw : ∀ l x y, 0 ≤ w l x y) {h : ℕ → σ → ℝ}
    {M c : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hsuper : ∀ l x, ∑ y : σ, w l x y * h (l + 1) y ≤ M * h l x)
    (l n : ℕ) (hmin : ∀ y, c ≤ h (l + n) y) (x : σ) :
    val w l n x ≤ M ^ n * h l x / c := by
  induction n generalizing l x with
  | zero =>
    rw [val_zero]
    have h1 : c ≤ h l x := by simpa using hmin x
    rw [pow_zero, one_mul, le_div_iff₀ hc, one_mul]
    exact h1
  | succ n ih =>
    have hmin' : ∀ y, c ≤ h (l + 1 + n) y := by
      intro y; have := hmin y; rwa [show l + (n + 1) = l + 1 + n by omega] at this
    rw [val_succ]
    calc ∑ y : σ, w l x y * val w (l + 1) n y
        ≤ ∑ y : σ, w l x y * (M ^ n * h (l + 1) y / c) :=
          sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (ih (l + 1) hmin' y) (hw l x y)
      _ = (M ^ n / c) * ∑ y : σ, w l x y * h (l + 1) y := by
          rw [mul_sum]; exact sum_congr rfl fun y _ => by ring
      _ ≤ (M ^ n / c) * (M * h l x) :=
          mul_le_mul_of_nonneg_left (hsuper l x) (by positivity)
      _ = M ^ (n + 1) * h l x / c := by ring

/-- **Pinned super-eigenvector bound.**  Same hypothesis as `val_le_of_superEigen`, but for the
kernel with *both* endpoints fixed: `ker w l n x z ≤ M ^ n * h l x / h (l+n) z`.  This is the form
needed for conditional (endpoint-pinned) large deviations, where `val`'s free endpoint is not
available. -/
theorem ker_le_of_superEigen {w : ℕ → σ → σ → ℝ} (hw : ∀ l x y, 0 ≤ w l x y) {h : ℕ → σ → ℝ}
    {M : ℝ} (hh : ∀ l y, 0 < h l y) (hM : 0 ≤ M)
    (hsuper : ∀ l x, ∑ y : σ, w l x y * h (l + 1) y ≤ M * h l x)
    (l n : ℕ) (x z : σ) :
    ker w l n x z ≤ M ^ n * h l x / h (l + n) z := by
  induction n generalizing l x with
  | zero =>
    rw [ker_zero, pow_zero, one_mul, Nat.add_zero]
    split_ifs with hxz
    · subst hxz
      rw [le_div_iff₀ (hh l x), one_mul]
    · exact le_of_lt (div_pos (hh l x) (hh l z))
  | succ n ih =>
    rw [ker_succ]
    calc ∑ y : σ, w l x y * ker w (l + 1) n y z
        ≤ ∑ y : σ, w l x y * (M ^ n * h (l + 1) y / h (l + 1 + n) z) :=
          sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (ih (l + 1) y) (hw l x y)
      _ = (M ^ n / h (l + 1 + n) z) * ∑ y : σ, w l x y * h (l + 1) y := by
          rw [mul_sum]; exact sum_congr rfl fun y _ => by ring
      _ ≤ (M ^ n / h (l + 1 + n) z) * (M * h l x) :=
          mul_le_mul_of_nonneg_left (hsuper l x)
            (div_nonneg (pow_nonneg hM n) (hh (l + 1 + n) z).le)
      _ = M ^ (n + 1) * h l x / h (l + (n + 1)) z := by
          rw [show l + (n + 1) = l + 1 + n by omega]; ring

/-- **Sub-eigenvector lower bound** (dual of `val_le_of_superEigen`).  A positive weight `h` with
`M * h l x ≤ ∑_y w l x y * h (l+1) y` forces `M ^ n * h l x / C ≤ val w l n x` whenever `h ≤ C` at
the final layer.  This is the certificate form needed to bound a layered *count* from below (e.g.
the denominator `|C_J|` of a conditional large-deviation statement). -/
theorem val_ge_of_subEigen {w : ℕ → σ → σ → ℝ} (hw : ∀ l x y, 0 ≤ w l x y) {h : ℕ → σ → ℝ}
    {M C : ℝ} (hC : 0 < C) (hM : 0 ≤ M)
    (hsub : ∀ l x, M * h l x ≤ ∑ y : σ, w l x y * h (l + 1) y)
    (l n : ℕ) (hmax : ∀ y, h (l + n) y ≤ C) (x : σ) :
    M ^ n * h l x / C ≤ val w l n x := by
  induction n generalizing l x with
  | zero =>
    rw [val_zero, pow_zero, one_mul, div_le_one hC]
    simpa using hmax x
  | succ n ih =>
    have hmax' : ∀ y, h (l + 1 + n) y ≤ C := by
      intro y; have := hmax y; rwa [show l + (n + 1) = l + 1 + n by omega] at this
    rw [val_succ]
    calc M ^ (n + 1) * h l x / C = (M ^ n / C) * (M * h l x) := by ring
      _ ≤ (M ^ n / C) * ∑ y : σ, w l x y * h (l + 1) y :=
          mul_le_mul_of_nonneg_left (hsub l x) (by positivity)
      _ = ∑ y : σ, w l x y * (M ^ n * h (l + 1) y / C) := by
          rw [mul_sum]; exact sum_congr rfl fun y _ => by ring
      _ ≤ ∑ y : σ, w l x y * val w (l + 1) n y :=
          sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (ih (l + 1) hmax' y) (hw l x y)

/-! ## Exponent bookkeeping: no `1/log J` loss -/

/-- **From the local exponent to the global one.**  If each of the `W` windows of `K` blocks
contributes
`2^(2Kθ)`, the remainder at most `s ^ K`, and `J = 2 * (W * K + ρ)` steps, then
`(1/J) log₂ (total) ≤ θ + K log₂ s / J`. -/
theorem logBookkeeping {K W ρ J : ℕ} {θ s Total : ℝ} (hs : 1 ≤ s) (hθ : 0 ≤ θ)
    (hJ : (J : ℝ) = 2 * (W * K + ρ)) (hJ0 : 0 < J)
    (hTotal : Total ≤ ((2 : ℝ) ^ (2 * (K : ℝ) * θ)) ^ W * s ^ K) (hTot0 : 0 < Total) :
    Real.logb 2 Total / J ≤ θ + K * Real.logb 2 s / J := by
  have h2 : (1 : ℝ) < 2 := one_lt_two
  have hpow : (0 : ℝ) < ((2 : ℝ) ^ (2 * (K : ℝ) * θ)) ^ W * s ^ K := by
    have : (0 : ℝ) < s ^ K := pow_pos (lt_of_lt_of_le zero_lt_one hs) K
    positivity
  have hlog : Real.logb 2 Total ≤ Real.logb 2 (((2 : ℝ) ^ (2 * (K : ℝ) * θ)) ^ W * s ^ K) :=
    Real.logb_le_logb_of_le h2 hTot0 hTotal
  have hexp : Real.logb 2 (((2 : ℝ) ^ (2 * (K : ℝ) * θ)) ^ W * s ^ K) =
      (W : ℝ) * (2 * K * θ) + K * Real.logb 2 s := by
    rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow, Real.logb_pow,
      Real.logb_rpow (by norm_num) (by norm_num)]
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ0
  rw [div_le_iff₀ hJpos]
  have hWK : (W : ℝ) * (2 * K * θ) ≤ (J : ℝ) * θ := by
    rw [hJ]
    have : (W : ℝ) * (2 * K) ≤ 2 * ((W : ℝ) * K + ρ) := by
      have : (0 : ℝ) ≤ ρ := Nat.cast_nonneg ρ
      nlinarith
    nlinarith
  have := hlog.trans_eq hexp
  have hfin : (θ + K * Real.logb 2 s / J) * J = θ * J + K * Real.logb 2 s := by
    field_simp
  rw [hfin]
  nlinarith [this, hWK]

end LocalWindow
end EOC
