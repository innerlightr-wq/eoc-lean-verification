import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Nat.Choose.Sum

/-!
# A lower bound for binomial coefficients

Mathlib provides only `Nat.pow_le_choose` as a lower bound on `Nat.choose`, which is far too weak for
counting confined words (it gives `129` bits against the true `294.6` at `J = 200`).  This file proves
the standard entropy bound in its division-free form:

  **`1 ≤ (n+1) · C(n,k) · p^k · q^(n-k)`,  `p = k/n`, `q = (n-k)/n`**  (`one_le_succ_mul_choose_mul`),

equivalently `C(n,k) ≥ 2^{n H(k/n)} / (n+1)`.

The proof is the classical max-term argument: the terms `T j = C(n,j) p^j q^{n-j}` of the binomial
distribution sum to `1` (`sum_binom_eq_one`), and `T` is maximised at `j = k` when `p = k/n`
(`term_le_term_max`), via the division-free recurrence

  `T (j+1) · (j+1) · q = T j · (n-j) · p`   (`term_succ_mul`),

which follows from `Nat.choose_succ_right_eq`.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace BinomialEntropy

open Finset

variable {n : ℕ} {p q : ℝ}

/-- The terms of the binomial distribution. -/
noncomputable def term (n : ℕ) (p q : ℝ) (j : ℕ) : ℝ := (n.choose j : ℝ) * p ^ j * q ^ (n - j)

theorem term_nonneg (hp : 0 ≤ p) (hq : 0 ≤ q) (n j : ℕ) : 0 ≤ term n p q j := by
  unfold term; positivity

/-- The binomial distribution sums to `1`. -/
theorem sum_binom_eq_one (n : ℕ) (hpq : p + q = 1) :
    ∑ j ∈ range (n + 1), term n p q j = 1 := by
  have h := add_pow p q n
  rw [hpq, one_pow] at h
  have hrw : ∑ j ∈ range (n + 1), term n p q j
      = ∑ m ∈ range (n + 1), p ^ m * q ^ (n - m) * (n.choose m : ℝ) := by
    refine sum_congr rfl fun j _ => ?_
    unfold term
    ring
  rw [hrw, ← h]

/-- **Division-free recurrence.** `T (j+1) · ((j+1) · q) = T j · ((n-j) · p)` for `j < n`. -/
theorem term_succ_mul (n j : ℕ) (hj : j < n) (p q : ℝ) :
    term n p q (j + 1) * (((j : ℝ) + 1) * q) = term n p q j * (((n : ℝ) - j) * p) := by
  unfold term
  have hrec : n.choose (j + 1) * (j + 1) = n.choose j * (n - j) := Nat.choose_succ_right_eq n j
  have hrec' : ((n.choose (j + 1) : ℝ)) * ((j : ℝ) + 1)
      = (n.choose j : ℝ) * ((n : ℝ) - (j : ℝ)) := by
    have hc := congrArg (fun m : ℕ => (m : ℝ)) hrec
    push_cast [Nat.cast_sub hj.le] at hc
    linarith
  have hq : q ^ (n - (j + 1)) * q = q ^ (n - j) := by
    rw [← pow_succ]
    congr 1
    omega
  calc (n.choose (j + 1) : ℝ) * p ^ (j + 1) * q ^ (n - (j + 1)) * (((j : ℝ) + 1) * q)
      = ((n.choose (j + 1) : ℝ) * ((j : ℝ) + 1)) * p ^ j * p * (q ^ (n - (j + 1)) * q) := by
        rw [pow_succ]; ring
    _ = ((n.choose j : ℝ) * ((n : ℝ) - (j : ℝ))) * p ^ j * p * q ^ (n - j) := by rw [hrec', hq]
    _ = (n.choose j : ℝ) * p ^ j * q ^ (n - j) * (((n : ℝ) - j) * p) := by ring

section Ratio

variable (n k j : ℕ)

private theorem cast_pos (hk0 : 0 < k) (hkn : k < n) : (0 : ℝ) < n := by
  have : 0 < n := by omega
  exact_mod_cast this

/-- With `p = k/n`, the terms increase up to `j = k`. -/
theorem term_le_succ (hk0 : 0 < k) (hkn : k < n) (hjk : j < k)
    (hp : p = (k : ℝ) / n) (hq : q = ((n : ℝ) - k) / n) :
    term n p q j ≤ term n p q (j + 1) := by
  have hn0 : (0 : ℝ) < n := cast_pos n k hk0 hkn
  have hkn' : (k : ℝ) < n := by exact_mod_cast hkn
  have hjn : j < n := by omega
  have hjn' : (j : ℝ) < n := by exact_mod_cast hjn
  have hjk' : (j : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hjk
  have hp0 : 0 < p := by rw [hp]; positivity
  have hq0 : 0 < q := by rw [hq]; exact div_pos (by linarith) hn0
  have hrec := term_succ_mul n j hjn p q
  have hTj : 0 ≤ term n p q j := term_nonneg hp0.le hq0.le n j
  have hA : (0 : ℝ) < ((j : ℝ) + 1) * q := by positivity
  have hk' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
  have hnum : ((j : ℝ) + 1) * ((n : ℝ) - k) ≤ ((n : ℝ) - j) * (k : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hjk' hn0.le]
  have hkey : ((j : ℝ) + 1) * q ≤ ((n : ℝ) - j) * p := by
    have e1 : ((j : ℝ) + 1) * q = (((j : ℝ) + 1) * ((n : ℝ) - k)) / n := by rw [hq]; ring
    have e2 : ((n : ℝ) - j) * p = (((n : ℝ) - j) * (k : ℝ)) / n := by rw [hp]; ring
    rw [e1, e2]
    gcongr
  have hstep : term n p q j * (((j : ℝ) + 1) * q) ≤ term n p q (j + 1) * (((j : ℝ) + 1) * q) := by
    calc term n p q j * (((j : ℝ) + 1) * q)
        ≤ term n p q j * (((n : ℝ) - j) * p) := mul_le_mul_of_nonneg_left hkey hTj
      _ = term n p q (j + 1) * (((j : ℝ) + 1) * q) := hrec.symm
  exact le_of_mul_le_mul_right hstep hA

/-- With `p = k/n`, the terms decrease after `j = k`. -/
theorem term_succ_le (hk0 : 0 < k) (hkn : k < n) (hkj : k ≤ j) (hjn : j < n)
    (hp : p = (k : ℝ) / n) (hq : q = ((n : ℝ) - k) / n) :
    term n p q (j + 1) ≤ term n p q j := by
  have hn0 : (0 : ℝ) < n := cast_pos n k hk0 hkn
  have hkn' : (k : ℝ) < n := by exact_mod_cast hkn
  have hjn' : (j : ℝ) < n := by exact_mod_cast hjn
  have hkj' : (k : ℝ) ≤ (j : ℝ) := by exact_mod_cast hkj
  have hp0 : 0 < p := by rw [hp]; positivity
  have hq0 : 0 < q := by rw [hq]; exact div_pos (by linarith) hn0
  have hrec := term_succ_mul n j hjn p q
  have hTj1 : 0 ≤ term n p q (j + 1) := term_nonneg hp0.le hq0.le n (j + 1)
  have hB : (0 : ℝ) < ((n : ℝ) - j) * p := by
    apply mul_pos (by linarith) hp0
  have hk' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
  have hnum : ((n : ℝ) - j) * (k : ℝ) ≤ ((j : ℝ) + 1) * ((n : ℝ) - k) := by
    nlinarith [mul_le_mul_of_nonneg_left hkj' hn0.le]
  have hkey : ((n : ℝ) - j) * p ≤ ((j : ℝ) + 1) * q := by
    have e1 : ((j : ℝ) + 1) * q = (((j : ℝ) + 1) * ((n : ℝ) - k)) / n := by rw [hq]; ring
    have e2 : ((n : ℝ) - j) * p = (((n : ℝ) - j) * (k : ℝ)) / n := by rw [hp]; ring
    rw [e1, e2]
    gcongr
  have hstep : term n p q (j + 1) * (((n : ℝ) - j) * p)
      ≤ term n p q j * (((n : ℝ) - j) * p) := by
    calc term n p q (j + 1) * (((n : ℝ) - j) * p)
        ≤ term n p q (j + 1) * (((j : ℝ) + 1) * q) := mul_le_mul_of_nonneg_left hkey hTj1
      _ = term n p q j * (((n : ℝ) - j) * p) := hrec
  exact le_of_mul_le_mul_right hstep hB

end Ratio

/-- **The maximum of the binomial terms is at `j = k`.** -/
theorem term_le_term_max (n k : ℕ) (hk0 : 0 < k) (hkn : k < n)
    (hp : p = (k : ℝ) / n) (hq : q = ((n : ℝ) - k) / n) :
    ∀ j ≤ n, term n p q j ≤ term n p q k := by
  intro j hj
  rcases le_or_gt j k with hjk | hjk
  · -- climb from `j` up to `k`
    have aux : ∀ d : ℕ, ∀ i : ℕ, i + d = k → term n p q i ≤ term n p q k := by
      intro d
      induction d with
      | zero => intro i hi; rw [show i = k by omega]
      | succ d ih =>
        intro i hi
        have h1 : term n p q i ≤ term n p q (i + 1) :=
          term_le_succ n k i hk0 hkn (by omega) hp hq
        exact le_trans h1 (ih (i + 1) (by omega))
    exact aux (k - j) j (by omega)
  · -- descend from `k` up to `j`
    have aux : ∀ d : ℕ, ∀ i : ℕ, k + d = i → i ≤ n → term n p q i ≤ term n p q k := by
      intro d
      induction d with
      | zero => intro i hi _; rw [show i = k by omega]
      | succ d ih =>
        intro i hi hin
        have hprev : term n p q (k + d + 1) ≤ term n p q (k + d) :=
          term_succ_le n k (k + d) hk0 hkn (by omega) (by omega) hp hq
        have := ih (k + d) rfl (by omega)
        rw [show i = k + d + 1 by omega]
        exact le_trans hprev this
    exact aux (j - k) j (by omega) hj

/-- **Binomial entropy bound, division-free form.**  For `0 < k < n`,
`1 ≤ (n+1) · C(n,k) · (k/n)^k · ((n-k)/n)^(n-k)`. -/
theorem one_le_succ_mul_choose_mul (n k : ℕ) (hk0 : 0 < k) (hkn : k < n) :
    (1 : ℝ) ≤ ((n : ℝ) + 1) * (n.choose k : ℝ) *
      ((k : ℝ) / n) ^ k * (((n : ℝ) - k) / n) ^ (n - k) := by
  set p : ℝ := (k : ℝ) / n with hp
  set q : ℝ := ((n : ℝ) - k) / n with hq
  have hn0 : (0 : ℝ) < n := cast_pos n k hk0 hkn
  have hpq : p + q = 1 := by
    rw [hp, hq]
    field_simp
    ring
  have hsum := sum_binom_eq_one (p := p) (q := q) n hpq
  have hmax := term_le_term_max n k hk0 hkn hp hq
  have hbound : (1 : ℝ) ≤ ((n : ℝ) + 1) * term n p q k := by
    calc (1 : ℝ) = ∑ j ∈ range (n + 1), term n p q j := hsum.symm
      _ ≤ ∑ _j ∈ range (n + 1), term n p q k :=
          sum_le_sum fun j hj => hmax j (by have := mem_range.mp hj; omega)
      _ = ((n : ℝ) + 1) * term n p q k := by
          rw [sum_const, card_range, nsmul_eq_mul]
          push_cast
          ring
  unfold term at hbound
  calc (1 : ℝ) ≤ ((n : ℝ) + 1) * ((n.choose k : ℝ) * p ^ k * q ^ (n - k)) := hbound
    _ = ((n : ℝ) + 1) * (n.choose k : ℝ) * p ^ k * q ^ (n - k) := by ring

/-- **Entropy bound, multiplicative form.**  `(n/k)^k · (n/(n-k))^(n-k) / (n+1) ≤ C(n,k)`. -/
theorem le_choose (n k : ℕ) (hk0 : 0 < k) (hkn : k < n) :
    ((n : ℝ) / k) ^ k * ((n : ℝ) / ((n : ℝ) - k)) ^ (n - k) / ((n : ℝ) + 1)
      ≤ (n.choose k : ℝ) := by
  have hn0 : (0 : ℝ) < n := cast_pos n k hk0 hkn
  have hk' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
  have hnk : (0 : ℝ) < (n : ℝ) - k := by
    have : (k : ℝ) < n := by exact_mod_cast hkn
    linarith
  have hbase := one_le_succ_mul_choose_mul n k hk0 hkn
  have hA : ((k : ℝ) / n) ^ k = 1 / ((n : ℝ) / k) ^ k := by
    rw [one_div, ← inv_pow]
    congr 1
    rw [inv_div]
  have hB : (((n : ℝ) - k) / n) ^ (n - k) = 1 / ((n : ℝ) / ((n : ℝ) - k)) ^ (n - k) := by
    rw [one_div, ← inv_pow]
    congr 1
    rw [inv_div]
  rw [hA, hB] at hbase
  have hP : (0 : ℝ) < ((n : ℝ) / k) ^ k := by positivity
  have hQ : (0 : ℝ) < ((n : ℝ) / ((n : ℝ) - k)) ^ (n - k) := by positivity
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
  have hexp : ((n : ℝ) + 1) * (n.choose k : ℝ) * (1 / ((n : ℝ) / k) ^ k) *
      (1 / ((n : ℝ) / ((n : ℝ) - k)) ^ (n - k))
      = ((n : ℝ) + 1) * (n.choose k : ℝ) / (((n : ℝ) / k) ^ k *
        ((n : ℝ) / ((n : ℝ) - k)) ^ (n - k)) := by
    field_simp
  rw [hexp, le_div_iff₀ (by positivity)] at hbase
  nlinarith [hbase, hP, hQ]

end BinomialEntropy
end EOC
