import EOC.Carry
import EOC.FirstDivergence
import EOC.ZCRERealizerGrowth

/-!
# The terminal high-bit zero gap of the normalized carry

Companion to `docs/NORMALIZED_CARRY_TERMINAL_ZERO_GAP_AUDIT.md`.

For a confined word of length `N` and total valuation `S = S_N`, the exact realizer `r` lies in
`[1, 2^{S+1})`. Writing `h = ⌊log₂ r⌋` for the position of its highest set bit, the bits
`h+1, …, S` of the `(S+1)`-bit representative are zero. The number of them,

```
g  =  S − ⌊log₂ r⌋,
```

is the **discrete high-bit zero gap**: an exceptionally small realizer is exactly a long `g`.

This file supplies the exact discrete bridges the audit needs. All of them are translations —
the audit's verdict is that no mechanism was found that *prevents* a long gap, only coordinates
that *describe* one.

* `discreteGap`, `discreteGap_ge_iff` — `G ≤ g ↔ r < 2^{S−G+1}`, with no logarithms of reals.
* `carry_residue_of_small_realizer` — the carry-side picture: when `r < 2^S`, the residue of the
  normalized carry is literally `2^S + r`, so a gap of length `g` is "bit `S` set, then `g−1`
  zero bits, then the top bit of `r`".
* `C_split` — the exact prefix/suffix decomposition `C_N = 3^{N−k}·C_k + 2^{S_k}·C'`. The suffix
  enters only through `2^{S_k}` times its own carry; the prefix enters at **full** final
  precision, which is why the high frontier is not prefix-local.

**A correction to `docs/REALIZER_LIFT_DIGIT_POSITIVITY_AUDIT.md` §Z.** That report said the
endpoint depth `E(D) = S − log₂ r` "is exactly the terminal zero-run length". It is not: `E` is
real-valued and the integer run length is `g = ⌈E⌉`, with `g − 1 < E ≤ g`. The two agree only
when `r = 1`. `discreteGap` is the correct integer variable and is what Open Problems C and E
should be phrased against.

**Prior art.** The jump `k_N` with `r_{N+1} = r_N + k_N 2^{S_N+1}` and the criterion
`k_N = 0 ↔ v₂(3μ_N+1) = d_{N+1}` are Remark B.2 of *From Confinement Abundance to Arithmetic
Placement*; the previous round's `liftDigit` is that object and should have cited it.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace TerminalZeroGap

/-! ## 1. The discrete gap -/

/-- The discrete high-bit zero gap: the number of zero bits strictly above the top bit of `r`
inside the `(S+1)`-bit window. -/
def discreteGap (S r : ℕ) : ℕ := S - Nat.log 2 r

/-- **The gap is exactly small-realizer placement.**  For `1 ≤ r` and `G ≤ S`,

```
G ≤ discreteGap S r   ↔   r < 2^(S − G + 1).
```

This is the clean finite form of "the top `G` bits of the window are zero", stated without any
real logarithm. It is a *restatement*, not a constraint — §H of the audit. -/
theorem discreteGap_ge_iff {S r G : ℕ} (hr : 0 < r) (hG : G ≤ S)
    (hlt : r < 2 ^ (S + 1)) :
    G ≤ discreteGap S r ↔ r < 2 ^ (S - G + 1) := by
  have hle : Nat.log 2 r ≤ S := Nat.le_of_lt_succ (Nat.log_lt_of_lt_pow (by omega) hlt)
  unfold discreteGap
  constructor
  · intro h
    have hlog : Nat.log 2 r ≤ S - G := by omega
    calc r < 2 ^ (Nat.log 2 r + 1) := Nat.lt_pow_succ_log_self (by norm_num) r
      _ ≤ 2 ^ (S - G + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · intro h
    have hlog : Nat.log 2 r ≤ S - G :=
      Nat.le_of_lt_succ (Nat.log_lt_of_lt_pow (by omega) h)
    omega

/-- `r < 2^(S+1)` forces the gap to be a genuine natural number, i.e. `⌊log₂ r⌋ ≤ S`. -/
theorem log_le_of_lt (S r : ℕ) (hr : 0 < r) (h : r < 2 ^ (S + 1)) : Nat.log 2 r ≤ S :=
  Nat.le_of_lt_succ (Nat.log_lt_of_lt_pow (by omega) h)

/-- The gap vanishes exactly when the top bit of the window is set. -/
theorem discreteGap_eq_zero_iff {S r : ℕ} (hr : 0 < r) (h : r < 2 ^ (S + 1)) :
    discreteGap S r = 0 ↔ 2 ^ S ≤ r := by
  unfold discreteGap
  have hle := log_le_of_lt S r hr h
  constructor
  · intro h0
    have : Nat.log 2 r = S := by omega
    calc (2 : ℕ) ^ S = 2 ^ Nat.log 2 r := by rw [this]
      _ ≤ r := Nat.pow_log_le_self 2 (by omega)
  · intro hge
    have : S ≤ Nat.log 2 r := Nat.le_log_of_pow_le (by norm_num) hge
    omega

/-! ## 2. The carry-side picture -/

/-- **Carry-side form of a gap.**  The exact realizer satisfies
`r = (Z + 2^S) mod 2^{S+1}` (audit §F, verified numerically). When the realizer is small,
`r < 2^S`, the residue of the normalized carry is literally `2^S + r`.

So "a gap of length `g`" reads, on the carry side, as: **bit `S` of `Z mod 2^{S+1}` is set, and
the next `g − 1` bits below it are zero.** That is the whole content of the carry-side
translation, and §H of the audit records that it is a restatement of `r` being small. -/
theorem carry_residue_of_small_realizer {S Z r : ℕ}
    (hZ : r = (Z + 2 ^ S) % 2 ^ (S + 1)) (hsmall : r < 2 ^ S) (hZlt : Z < 2 ^ (S + 1)) :
    Z = r + 2 ^ S := by
  have hpow : (2 : ℕ) ^ (S + 1) = 2 ^ S + 2 ^ S := by ring
  rcases Nat.lt_or_ge Z (2 ^ S) with h | h
  · -- then `Z + 2^S < 2^{S+1}`, so the residue is `Z + 2^S ≥ 2^S`, contradicting `r < 2^S`
    have : Z + 2 ^ S < 2 ^ (S + 1) := by omega
    rw [Nat.mod_eq_of_lt this] at hZ
    omega
  · -- `2^S ≤ Z`, so `Z + 2^S − 2^{S+1} = Z − 2^S` is the residue
    have hge : 2 ^ (S + 1) ≤ Z + 2 ^ S := by omega
    have h1 : Z + 2 ^ S - 2 ^ (S + 1) = Z - 2 ^ S := by omega
    have hlt2 : Z - 2 ^ S < 2 ^ (S + 1) := by omega
    have h3 : (Z + 2 ^ S) % 2 ^ (S + 1) = Z - 2 ^ S := by
      rw [Nat.mod_eq_sub_mod hge, h1, Nat.mod_eq_of_lt hlt2]
    rw [h3] at hZ
    omega

/-! ## 3. Prefix/suffix decomposition of the carry -/

/-- **Exact carry split.**  `C_N = 3^{N−k}·C_k + 2^{S_k}·(suffix carry)`.

The suffix contributes only through `2^{S_k}` times a carry built from the shifted word, and the
prefix contributes through `C_k` multiplied by `3^{N−k}`. In particular, to know `C_N` modulo
`2^{S_N+1}` one needs `C_k` modulo `2^{S_N+1}` — the **full final precision**, not `2^{S_k+1}`.
That is the formal reason the high frontier is not prefix-local (audit §J, §L). -/
theorem C_split (d : ℕ → ℕ) (k n : ℕ) :
    ∃ C' : ℕ, C d (k + n) = 3 ^ n * C d k + 2 ^ s d k * C' := by
  have hq : ∀ m, C d (m + 1) = 3 * C d m + 2 ^ s d m := by
    intro m; rw [← q_eq_C, ← q_eq_C]; exact q_succ d m
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
      obtain ⟨C', hC'⟩ := ih
      have hmono : s d k ≤ s d (k + n) := FirstDivergence.s_mono' d (Nat.le_add_right k n)
      have hsplit : (2 : ℕ) ^ s d (k + n) = 2 ^ s d k * 2 ^ (s d (k + n) - s d k) := by
        rw [← pow_add]; congr 1; omega
      refine ⟨3 * C' + 2 ^ (s d (k + n) - s d k), ?_⟩
      have hks : k + (n + 1) = (k + n) + 1 := by omega
      rw [hks, hq (k + n), hC', hsplit]
      ring

end TerminalZeroGap
end EOC
