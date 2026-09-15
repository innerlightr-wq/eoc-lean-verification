import EOC.ResidueDiscrepancy
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# Shell Weyl sums of least realizers and the conditional Weyl ⇒ exponent chain

Fix a confinement offset `U`, a depth `N`, a dyadic cutoff `X = 2^K`, and a shell `s ≥ K`.  Every
post-fresh-bit least realizer on the shell satisfies `r_w < 2^(s+1)`, so its position relative to
`2^K` is recorded by the **top block** `⌊r_w / 2^K⌋ ∈ [0, 2^n)`, `n = s + 1 − K`, and
`r_w < 2^K ↔ ⌊r_w / 2^K⌋ = 0`.

* `blockWeyl T r K n g = ∑_{i ∈ T} e(g · ⌊r_i / 2^K⌋ / 2^n)` (characters of `ZMod (2^n)`).
* `card_filter_lt_eq_fourier` — **exact discrete Fourier identity** (no smoothing, no log loss):
  `#{i ∈ T : r_i < 2^K} = 2^{-n} ∑_{g ∈ ZMod (2^n)} blockWeyl g`.
* `card_filter_lt_le` — **discrepancy inequality**:
  `#{r_i < 2^K} ≤ #T / 2^n + 2^{-n} ∑_{g ≠ 0} ‖blockWeyl g‖`.
* `shellWeyl U N K s` — the shell Weyl sum over `W_U(N) ∩ {S_w = s}` at resolution `n = s+1−K`.
* `leastRealizerBound_of_weyl` — **conditional theorem**: if every post-fresh-bit shell satisfies
  `∑_{g ≠ 0} ‖shellWeyl g‖ ≤ (C − 1) · #shell`, then the least-realizer counting hypothesis of
  `ResidueDiscrepancy.exceptional_count_le_of_leastRealizerBound` holds.
* `exceptional_count_le_of_weyl` — the full chain: Weyl bound at depth `N ≥ A·K` ⇒
  `#(E_U ∩ [0, 2^K)) ≤ (C e^{λ* U}/2) · (2^K)^{1 − I₀ A}`.
* `weylBound_of_pointwise` — the pointwise form: `‖shellWeyl g‖ ≤ (C−1)·2^{-n}·#shell` for all
  `g ≠ 0` suffices (a power saving `2^{-n}` over the trivial bound).

Frequency cutoffs (exact, arithmetic):
* `leastRealizer_eq_prefix_add`, `topBlock_eq_suffix` — the top block above position `S_j + 1` is
  `∑_{j ≤ i < N} 2^(S_i − S_j) τ_i`: top-block characters see only the **suffix** lift digits.
* `dyadicPhase_eq_prefix` — additive phases at a dyadic frequency `2^(S_N − S_J) h` modulo
  `2^(S_N+1)` see only the **prefix** least realizer `r_J`.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace ShellWeyl

open Finset CapacityBounds FiniteValuationWord LiftDigits SuffixTransport

/-! ## The exact discrete Fourier identity for a dyadic cutoff -/

/-- The top block of `r` above position `K`, as a residue modulo `2^n`. -/
def topBlock (K n r : ℕ) : ZMod (2 ^ n) := ((r / 2 ^ K : ℕ) : ZMod (2 ^ n))

/-- The top-block Weyl sum `∑_{i ∈ T} e(g ⌊r_i/2^K⌋ / 2^n)`. -/
noncomputable def blockWeyl {ι : Type*} (T : Finset ι) (r : ι → ℕ) (K n : ℕ)
    (g : ZMod (2 ^ n)) : ℂ :=
  ∑ i ∈ T, ZMod.stdAddChar (g * topBlock K n (r i))

theorem topBlock_eq_zero_iff {K n r : ℕ} (hr : r < 2 ^ (K + n)) :
    topBlock K n r = 0 ↔ r < 2 ^ K := by
  unfold topBlock
  rw [ZMod.natCast_eq_zero_iff]
  have hlt : r / 2 ^ K < 2 ^ n := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, add_comm]; exact hr
  constructor
  · intro h
    have h0 : r / 2 ^ K = 0 := Nat.eq_zero_of_dvd_of_lt h hlt
    rwa [Nat.div_eq_zero_iff_lt (by positivity)] at h0
  · intro h
    rw [Nat.div_eq_of_lt h]
    exact dvd_zero _

/-- **Exact discrete Fourier identity.** If every `r_i < 2^(K+n)`, then
`#{i ∈ T : r_i < 2^K} = 2^{-n} ∑_g blockWeyl T r K n g`. -/
theorem card_filter_lt_eq_fourier {ι : Type*} (T : Finset ι) (r : ι → ℕ) (K n : ℕ)
    (hr : ∀ i ∈ T, r i < 2 ^ (K + n)) :
    (((T.filter fun i => r i < 2 ^ K).card : ℕ) : ℂ) =
      ((2 : ℂ) ^ n)⁻¹ * ∑ g : ZMod (2 ^ n), blockWeyl T r K n g := by
  have horth : ∀ i ∈ T, ∑ g : ZMod (2 ^ n), ZMod.stdAddChar (g * topBlock K n (r i)) =
      if r i < 2 ^ K then (2 : ℂ) ^ n else 0 := by
    intro i hi
    rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar _), ZMod.card]
    simp only [topBlock_eq_zero_iff (hr i hi)]
    split_ifs <;> push_cast <;> rfl
  unfold blockWeyl
  rw [sum_comm, sum_congr rfl horth, ← sum_filter, sum_const, nsmul_eq_mul]
  field_simp

/-- **Discrepancy inequality** (the `g = 0` term is the Haar share `#T / 2^n`). -/
theorem card_filter_lt_le {ι : Type*} (T : Finset ι) (r : ι → ℕ) (K n : ℕ)
    (hr : ∀ i ∈ T, r i < 2 ^ (K + n)) :
    (((T.filter fun i => r i < 2 ^ K).card : ℕ) : ℝ) ≤
      (T.card : ℝ) / 2 ^ n +
        ((2 : ℝ) ^ n)⁻¹ * ∑ g ∈ univ.erase (0 : ZMod (2 ^ n)), ‖blockWeyl T r K n g‖ := by
  have hid := card_filter_lt_eq_fourier T r K n hr
  rw [← add_sum_erase _ _ (mem_univ (0 : ZMod (2 ^ n)))] at hid
  have h0 : blockWeyl T r K n 0 = (T.card : ℂ) := by
    simp [blockWeyl]
  rw [h0, mul_add] at hid
  set E := ∑ g ∈ univ.erase (0 : ZMod (2 ^ n)), blockWeyl T r K n g
  have hnorm : ‖E‖ ≤ ∑ g ∈ univ.erase (0 : ZMod (2 ^ n)), ‖blockWeyl T r K n g‖ :=
    norm_sum_le _ _
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  -- take real parts
  have hre := congrArg Complex.re hid
  simp only [Complex.natCast_re, Complex.add_re] at hre
  have h1 : (((2 : ℂ) ^ n)⁻¹ * (T.card : ℂ)).re = (T.card : ℝ) / 2 ^ n := by
    rw [show ((2 : ℂ) ^ n)⁻¹ * (T.card : ℂ) = (((T.card : ℝ) / 2 ^ n : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_re _
  have h2 : (((2 : ℂ) ^ n)⁻¹ * E).re ≤ ((2 : ℝ) ^ n)⁻¹ * ‖E‖ := by
    rw [show ((2 : ℂ) ^ n)⁻¹ = (((2 : ℝ) ^ n)⁻¹ : ℝ) by push_cast; rfl, Complex.re_ofReal_mul]
    exact mul_le_mul_of_nonneg_left (Complex.re_le_norm E) (by positivity)
  rw [hre, h1]
  have h3 : ((2 : ℝ) ^ n)⁻¹ * ‖E‖ ≤
      ((2 : ℝ) ^ n)⁻¹ * ∑ g ∈ univ.erase (0 : ZMod (2 ^ n)), ‖blockWeyl T r K n g‖ :=
    mul_le_mul_of_nonneg_left hnorm (by positivity)
  linarith

/-- Shell form of the discrepancy inequality: a Weyl bound `∑_{g≠0} ‖V(g)‖ ≤ (C−1)·#T` gives
`#{r_i < 2^K} ≤ C · #T / 2^n`. -/
theorem card_filter_lt_le_of_weyl {ι : Type*} (T : Finset ι) (r : ι → ℕ) (K n : ℕ) (C : ℝ)
    (hr : ∀ i ∈ T, r i < 2 ^ (K + n))
    (hW : ∑ g ∈ univ.erase (0 : ZMod (2 ^ n)), ‖blockWeyl T r K n g‖ ≤ (C - 1) * T.card) :
    (((T.filter fun i => r i < 2 ^ K).card : ℕ) : ℝ) ≤ C * (T.card : ℝ) / 2 ^ n := by
  have h := card_filter_lt_le T r K n hr
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  have h2 : ((2 : ℝ) ^ n)⁻¹ * ∑ g ∈ univ.erase (0 : ZMod (2 ^ n)), ‖blockWeyl T r K n g‖ ≤
      ((2 : ℝ) ^ n)⁻¹ * ((C - 1) * T.card) := mul_le_mul_of_nonneg_left hW (by positivity)
  have h3 : (T.card : ℝ) / 2 ^ n + ((2 : ℝ) ^ n)⁻¹ * ((C - 1) * T.card) =
      C * (T.card : ℝ) / 2 ^ n := by
    field_simp; ring
  linarith

/-- Pointwise form: `‖V(g)‖ ≤ (C − 1) · 2^{-n} · #T` for every `g ≠ 0` implies the summed Weyl
hypothesis of `card_filter_lt_le_of_weyl` (there are `2^n − 1 < 2^n` nonzero frequencies). -/
theorem sum_norm_le_of_pointwise {ι : Type*} (T : Finset ι) (r : ι → ℕ) (K n : ℕ) (C : ℝ)
    (hC : 1 ≤ C)
    (hW : ∀ g : ZMod (2 ^ n), g ≠ 0 → ‖blockWeyl T r K n g‖ ≤ (C - 1) * T.card / 2 ^ n) :
    ∑ g ∈ univ.erase (0 : ZMod (2 ^ n)), ‖blockWeyl T r K n g‖ ≤ (C - 1) * T.card := by
  have hcard : ((univ.erase (0 : ZMod (2 ^ n))).card : ℝ) ≤ 2 ^ n := by
    rw [card_erase_of_mem (mem_univ _), card_univ, ZMod.card]
    have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    rw [Nat.cast_sub (Nat.one_le_two_pow)]
    push_cast
    linarith
  have hnn : 0 ≤ (C - 1) * (T.card : ℝ) / 2 ^ n := by
    have : 0 ≤ C - 1 := by linarith
    positivity
  calc ∑ g ∈ univ.erase (0 : ZMod (2 ^ n)), ‖blockWeyl T r K n g‖
      ≤ ∑ _g ∈ univ.erase (0 : ZMod (2 ^ n)), (C - 1) * (T.card : ℝ) / 2 ^ n :=
        sum_le_sum fun g hg => hW g (ne_of_mem_erase hg)
    _ = ((univ.erase (0 : ZMod (2 ^ n))).card : ℝ) * ((C - 1) * (T.card : ℝ) / 2 ^ n) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ 2 ^ n * ((C - 1) * (T.card : ℝ) / 2 ^ n) := mul_le_mul_of_nonneg_right hcard hnn
    _ = (C - 1) * T.card := by field_simp

/-! ## Frequency cutoffs: top blocks see suffixes, dyadic additive phases see prefixes -/

section Cutoff

variable {d : ℕ → ℕ}

/-- `r_N = r_j + 2^(S_j+1) · ∑_{j ≤ i < N} 2^(S_i − S_j) τ_i`. -/
theorem leastRealizer_eq_prefix_add {j N : ℕ} (hd : ∀ i < N, 1 ≤ d i) (hj : j ≤ N) :
    leastRealizer d N = leastRealizer d j +
      2 ^ (S d j + 1) * ∑ i ∈ Ico j N, 2 ^ (S d i - S d j) * liftDigit d i := by
  induction N, hj using Nat.le_induction with
  | base => simp
  | succ n hjn ih =>
      rw [leastRealizer_succ hd, ih (fun i hi => hd i (by omega)), sum_Ico_succ_top hjn, mul_add]
      have h2 : 2 ^ (S d n + 1) = 2 ^ (S d j + 1) * 2 ^ (S d n - S d j) := by
        rw [← pow_add]; congr 1; have := S_mono d hjn; omega
      rw [h2]; ring

/-- **Suffix cutoff for top blocks.** The part of `r_N` above position `S_j + 1` is determined by
the lift digits of the suffix `[j, N)` alone:
`⌊r_N / 2^(S_j+1)⌋ = ∑_{j ≤ i < N} 2^(S_i−S_j) τ_i`. -/
theorem topBlock_eq_suffix {j N : ℕ} (hd : ∀ i < N, 1 ≤ d i) (hj : j ≤ N) :
    leastRealizer d N / 2 ^ (S d j + 1) =
      ∑ i ∈ Ico j N, 2 ^ (S d i - S d j) * liftDigit d i := by
  rw [leastRealizer_eq_prefix_add hd hj, Nat.add_mul_div_left _ _ (by positivity),
    Nat.div_eq_of_lt (leastRealizer_lt d j), zero_add]

/-- **Prefix cutoff for dyadic additive frequencies.** For `J ≤ N`, the additive phase of `r_N` at
frequency `2^(S_N − S_J)·h` modulo `2^(S_N+1)` equals the phase of the prefix least realizer `r_J`
at frequency `h` modulo `2^(S_J+1)`:
`(2^(S_N−S_J) h r_N) mod 2^(S_N+1) = 2^(S_N−S_J) · ((h r_J) mod 2^(S_J+1))`,
i.e. `e(2^(S_N−S_J) h r_N / 2^(S_N+1)) = e(h r_J / 2^(S_J+1))`. -/
theorem dyadicPhase_eq_prefix {J N : ℕ} (hd : ∀ i < N, 1 ≤ d i) (hJ : J ≤ N) (h : ℕ) :
    (2 ^ (S d N - S d J) * h * leastRealizer d N) % 2 ^ (S d N + 1) =
      2 ^ (S d N - S d J) * ((h * leastRealizer d J) % 2 ^ (S d J + 1)) := by
  have hS := S_mono d hJ
  have hpow : 2 ^ (S d N + 1) = 2 ^ (S d N - S d J) * 2 ^ (S d J + 1) := by
    rw [← pow_add]; congr 1; omega
  rw [hpow, mul_assoc, Nat.mul_mod_mul_left, ← leastRealizer_mod hd hJ, Nat.mul_mod_mod]

end Cutoff

/-! ## Shells of confined words and the conditional chain -/

/-- The shell `W_U(N) ∩ {S_w = s}`. -/
noncomputable def shell (U N s : ℕ) : Finset (FiniteValuationWord N) :=
  (confinedWords N (collatzBarrier U)).filter fun w => w.total = s

/-- The shell Weyl sum at cutoff `2^K`: characters of the top `n = s+1−K` bits of `r_w`. -/
noncomputable def shellWeyl (U N K s : ℕ) (g : ZMod (2 ^ (s + 1 - K))) : ℂ :=
  blockWeyl (shell U N s) (fun w => leastRealizer w.toInfinite N) K (s + 1 - K) g

/-- The shell Weyl hypothesis at cutoff `2^K` with constant `C`. -/
def WeylBound (U N K : ℕ) (C : ℝ) : Prop :=
  ∀ s, K ≤ s → ∑ g ∈ univ.erase (0 : ZMod (2 ^ (s + 1 - K))), ‖shellWeyl U N K s g‖ ≤
    (C - 1) * (shell U N s).card

theorem leastRealizer_lt_shell {U N s : ℕ} {w : FiniteValuationWord N} (hw : w ∈ shell U N s)
    (K : ℕ) (hK : K ≤ s) : leastRealizer w.toInfinite N < 2 ^ (K + (s + 1 - K)) := by
  have h := leastRealizer_lt w.toInfinite N
  rw [ResidueDiscrepancy.total_eq_S] at h
  have hs : w.total = s := (mem_filter.mp hw).2
  rw [hs] at h
  rwa [show K + (s + 1 - K) = s + 1 by omega]

/-- One shell: a Weyl bound gives `#{w ∈ shell : r_w < 2^K} ≤ C ∑_{w ∈ shell} 2^K 2^{-(S_w+1)}`. -/
theorem shell_count_le {U N K s : ℕ} (C : ℝ) (hK : K ≤ s)
    (hW : ∑ g ∈ univ.erase (0 : ZMod (2 ^ (s + 1 - K))), ‖shellWeyl U N K s g‖ ≤
      (C - 1) * (shell U N s).card) :
    ((((shell U N s).filter fun w => leastRealizer w.toInfinite N < 2 ^ K).card : ℕ) : ℝ) ≤
      C * ∑ w ∈ shell U N s, (2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (w.total + 1) := by
  have h := card_filter_lt_le_of_weyl (shell U N s) (fun w => leastRealizer w.toInfinite N) K
    (s + 1 - K) C (fun w hw => leastRealizer_lt_shell hw K hK) hW
  have hsum : ∑ w ∈ shell U N s, (2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (w.total + 1) =
      (shell U N s).card * ((2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (s + 1)) := by
    rw [sum_congr rfl fun w hw => by rw [(mem_filter.mp hw).2], sum_const, nsmul_eq_mul]
  have hpow : (2 : ℝ) ^ (s + 1) = 2 ^ (s + 1 - K) * 2 ^ K := by
    rw [← pow_add]; congr 1; omega
  rw [hsum]
  convert h using 1
  rw [div_pow, one_pow, hpow]
  field_simp

/-- **Conditional theorem: Weyl bound ⇒ least-realizer counting bound.** -/
theorem leastRealizerBound_of_weyl (U N K : ℕ) (C : ℝ) (hW : WeylBound U N K C) :
    ((((confinedWords N (collatzBarrier U)).filter fun w =>
        K ≤ w.total ∧ leastRealizer w.toInfinite N < 2 ^ K).card : ℕ) : ℝ) ≤
      C * ∑ w ∈ (confinedWords N (collatzBarrier U)).filter (fun w => K ≤ w.total),
        (2 : ℝ) ^ K * (1 / 2 : ℝ) ^ (w.total + 1) := by
  set W := confinedWords N (collatzBarrier U)
  set D := W.filter fun w => K ≤ w.total
  set t := D.image fun w => w.total
  have hmap : ∀ w ∈ D, w.total ∈ t := fun w hw => mem_image_of_mem _ hw
  have hfib : ∀ s ∈ t, D.filter (fun w => w.total = s) = shell U N s := by
    intro s hs
    obtain ⟨w0, hw0, rfl⟩ := mem_image.mp hs
    have hK : K ≤ w0.total := (mem_filter.mp hw0).2
    ext w
    simp only [D, shell, mem_filter]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3 ▸ hK⟩, h3⟩
  have hK_of : ∀ s ∈ t, K ≤ s := by
    intro s hs
    obtain ⟨w0, hw0, rfl⟩ := mem_image.mp hs
    exact (mem_filter.mp hw0).2
  have hL : W.filter (fun w => K ≤ w.total ∧ leastRealizer w.toInfinite N < 2 ^ K) =
      D.filter fun w => leastRealizer w.toInfinite N < 2 ^ K := by
    rw [filter_filter]
  rw [hL, card_eq_sum_card_fiberwise (fun w hw => hmap w (mem_filter.mp hw).1),
    ← sum_fiberwise_of_maps_to hmap, mul_sum]
  push_cast
  refine sum_le_sum fun s hs => ?_
  have hc : (D.filter fun w => leastRealizer w.toInfinite N < 2 ^ K).filter
      (fun w => w.total = s) =
      (shell U N s).filter fun w => leastRealizer w.toInfinite N < 2 ^ K := by
    ext w
    simp only [D, shell, mem_filter]
    constructor
    · rintro ⟨⟨⟨h1, _⟩, h2⟩, h3⟩; exact ⟨⟨h1, h3⟩, h2⟩
    · rintro ⟨⟨h1, h3⟩, h2⟩; exact ⟨⟨⟨h1, h3 ▸ hK_of s hs⟩, h2⟩, h3⟩
  rw [hc, hfib s hs]
  exact_mod_cast shell_count_le C (hK_of s hs) (hW s (hK_of s hs))

open Classical in
/-- **The full conditional chain.** Weyl bound at depth `N ≥ A·K` ⇒
`#(E_U ∩ [0, 2^K)) ≤ (C e^{λ* U}/2) · (2^K)^{1 − I₀ A}`. -/
theorem exceptional_count_le_of_weyl (U K : ℕ) {N : ℕ} (hN : 1 ≤ N) (A C : ℝ) (hC : 1 ≤ C)
    (hNA : A * K ≤ N) (hW : WeylBound U N K C) :
    (((range (2 ^ K)).filter fun μ =>
        Odd μ ∧ ∀ M, Confined (U : ℝ) (fun i => a (orbit μ i)) M).card : ℝ) ≤
      C * Real.exp (TaoExternal.lambdaStar * U) / 2 *
        ((2 ^ K : ℕ) : ℝ) ^ (1 - TaoExternal.I0 * A) :=
  ResidueDiscrepancy.exceptional_count_le_of_leastRealizerBound U K hN A C hC hNA
    (leastRealizerBound_of_weyl U N K C hW)

/-- **Pointwise power-saving form.** If every nonzero frequency on every post-fresh-bit shell has
`‖shellWeyl g‖ ≤ (C − 1) · 2^{-(s+1−K)} · #shell`, the Weyl hypothesis holds. -/
theorem weylBound_of_pointwise (U N K : ℕ) (C : ℝ) (hC : 1 ≤ C)
    (hP : ∀ s, K ≤ s → ∀ g : ZMod (2 ^ (s + 1 - K)), g ≠ 0 →
      ‖shellWeyl U N K s g‖ ≤ (C - 1) * (shell U N s).card / 2 ^ (s + 1 - K)) :
    WeylBound U N K C :=
  fun s hs => sum_norm_le_of_pointwise _ _ _ _ C hC (hP s hs)

end ShellWeyl
end EOC
