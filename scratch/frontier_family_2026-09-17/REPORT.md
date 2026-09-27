# Scalar closure in Lean for an infinite family; focused frontier attempt (research round, 2026-09-17)

Nothing committed or pushed.
Labels: PROVED (LEAN) / PROVED (MATH) / EXTERNAL THEOREM / COMPUTATIONAL / HEURISTIC / CONJECTURAL / REFUTED / OPEN.

## 0. Headline

**Stage One is complete: positive stop conditions 1 and 2.**

**`EOC.FrontierFamily.exceptional_bound_family_exponent`** (PROVED (LEAN), standard axioms only). For every m ≥ 100, with
j₀ = P·m, P = 675 000 000 and K = b₀(j₀) + 1:

  PowerOfTwoDangerousWindowSparsityAt (on the good pairs of the family)
  ⟹ #(E₀ ∩ [0, 2^K)) ≤ (3/2) · (2^K)^{H₂(1/α) − I₀/(2·10⁹)}.

* The **only** hypothesis besides `100 ≤ m` is the arithmetic frontier Prop.
* There are no abstract |V|, `hfin`, `hweight`, sieve, `hL`, `hρ`, `hscalar` or parameter-choice hypotheses.
* The exponent improvement is ε = I₀/(2·10⁹) ≥ 3.96·10⁻¹¹. It is **positive, tiny, and conditional**.

**This is not a proof of Collatz.** It is a conditional bound on the size of the exceptional set E₀ (the U = 0
confinement exceptional set), conditional on an open arithmetic statement about powers of 2.

**Stage Two (focused frontier attempt):** no positive stop condition fired.
* **Danger sets (COMPUTATIONAL):** exact danger sets in phase coordinates show structure. Symmetry under T ↦ T + 1/2,
  correlation under ×2 for r ≤ 4 dilations then independence, Fourier peaks at c·2^a·3^b with c ≤ 11. But the Fourier
  ℓ¹ mass is not small, so the hit count reduces to the same short Korobov sums (known obstruction).
* **λ = 1 windows:**
  * no exact local anti-persistence, no congruence restriction, no 2-of-9 law (REFUTED as exact laws at the surrogate
    parameters tested);
  * the danger rate is driven by the number of start states per window;
  * after detrending, consecutive windows look independent.

## 1. Repository

* Branch `research-sparse-visits-2026-09-16`, HEAD `14dea46` (unchanged).
* Build at the start of the round: 8809 jobs. At the end: **8810 jobs, success**.
* New file: `EOC/FrontierFamily.lean` (≈560 lines). Modified: `EOC.lean` (+1 import).
* Earlier uncommitted modules are unchanged: `ShapeRegion`, `FrontierRegion`, `ConditionalChain`, `ShellCounts`,
  `BinomialTail`, `FinalChain`.
* Scratch: `scratch/frontier_family_2026-09-17/`.
* No commit, no push.
* `#print axioms` gives exactly `[propext, Classical.choice, Quot.sound]` for:
  `alpha_ge`, `alpha_le`, `scalar_rho`, `scalar_main`, `hnum_fam`, `pairData_fam`, `A_ge`,
  `exceptional_bound_of_frontier_family`, `exceptional_bound_family_exponent`. No `sorry`, no `native_decide`.

## 2. Scalar closure (Stage One)

### 2.1 Remaining scalar assumptions at the start

These are the hypotheses of `FinalChain.exceptional_bound_of_frontier_and_scalar`, with b = b_U(j₀), B = b_U(N),
L = N − j₀, M₀ = B − b + 1, and f̄(y) = (b−j₀)/(b−1) · (M₀+y)/(M₀+y−L).

| name | inequality | monotone / asymptotics |
|---|---|---|
| hKN | K ≤ B | automatic once B − b ≥ 1 |
| hNA | A·K ≤ N | equality with A = N/K |
| hL | L < B − b + 1 | B − b ≈ αL |
| hρ | f̄(x*+1) < 1 | f̄ decreasing in y; holds once x* ≥ L |
| hscalar | N·∏_{y≤x*} f̄(y)/(1 − f̄(x*+1)) ≤ κ·2^K·2^{−(B+1)} | LHS ~ poly·(3r₀r₁³)^L against RHS ~ 3^{−L}: easier as L grows |
| per pair: region/rate | 300 ≤ j, 2 ∣ j, b₀ ≤ σ+δ, δ ≤ j/300, 63σ+37 ≤ 100j, budget, k+n ≤ K_b, hlarge, νj ≤ n, θ′+γ ≤ ν, γj ≤ j/300 − δ, γj·ln 2 ≤ 8kd²/N₀, 0 < K_win ≤ A·log₂j + 1 | linear in j; fixed constants |
| per pair: hnum | (1+(σ+1)/2)(s+1)·4·4^t·L ≤ ε²·C(t−1, L−1)·2^{γj} | easier as j grows at fixed L/j |

### 2.2 Chosen family and rational margins

| parameter | value |
|---|---|
| m | index, m ≥ 100 |
| j₀ | P·m, P = 675 000 000 = 2⁶·3³·5⁸ (all Nat divisions exact) |
| L | m |
| N | (P+1)·m |
| x* = δ | 4m |
| K | b₀(j₀) + 1 |
| U | 0 |
| γ | 1/25 000 000, so γj₀ = 27m |
| θ′ | 1/6 + 1/1000 |
| ν | 1/6 + 1/500 |
| d | 1/108 |
| N₀ | 133 |
| K_b | 118 250 000·m |
| n | 113 850 000·m |
| k | 4 400 000·m |
| frontier parameters | K_win = ⌊7·log₂ j₀⌋, A_win = 7, a = b = 2 |
| ε, κ | 1, 1 |

Rational margins (all exact):
* **α:** 79/50 ≤ α ≤ 317/200. Proof: 2⁷⁹ ≤ 3⁵⁰ and 3²⁰⁰ ≤ 2³¹⁷, the latter by kernel `Nat.ble`.
* **q:** (b−j₀)/(b−1) ≤ 37/100, from 63b + 37 ≤ 100j₀.
* **Ratio majorants:** from M₀ ≥ (79/50)L, r₀ = (37/100)(79/29) everywhere and r₁ = (37/100)(129/79) for y ≥ L.
  Both satisfy 3r₀r₁³ ≤ 67/100 and 1 − r₁ = 3127/7900.
* **2^{B−b} ≤ 2·3^m:** B − b < mα + 1 and 2^α = 3.
* **Rate budget:** γj₀·ln 2 = 18.72m < 8kd²/N₀ = 22.69m; γj₀ = 27m ≤ j₀/300 − δ = 2 249 996m.
* **hlarge:** (3·9.3/(1/1000))² = 778 410 000 ≤ j₀.

### 2.3 Threshold and proofs

**J\*:** m ≥ 100, i.e. j₀ ≥ 6.75·10¹⁰. Proofs:
* **hL, hKN** (`gap_ge`): B − b > mα − 1 ≥ m − 1, so B − b ≥ m.
* **hρ** (`scalar_rho`): f̄(4m+1) ≤ r₁ < 1.
* **hscalar** (`scalar_main`):
  * LHS·2^{B−b} ≤ (P+1)m·r₀^m·r₁^{3m}·(7900/3127)·2·3^m ≤ 6(P+1)m·(67/100)^m;
  * `six_mul_pow_le`: 6(P+1)m·67^m ≤ 100^m for m ≥ 100, by induction.
* **hnum** (`hnum_fam`):
  * using C(t−1, L−1) ≥ 1, t ≤ 6m, σ ≤ 2Pm and s ≤ 3Pm: LHS ≤ 32P²m³·2^{12m};
  * `pair_poly_le`: 32P²m³ ≤ 2^{15m}; so LHS ≤ 2^{27m} = 2^{γj₀}.
* **Per-pair data** (`pairData_fam`): all 29 fields of `ExplicitPairData` by `omega`, `norm_num` or `nlinarith`
  (log 2 < 0.6931471808 from Mathlib).
* **Final** (`exceptional_bound_of_frontier_family`): instantiates `FinalChain.exceptional_bound_of_frontier_and_scalar`.
* **Exponent** (`A_ge`, `exceptional_bound_family_exponent`): A = N/K ≥ 1/α + 1/(2·10⁹). Then use I₀ > 0 and
  1 − I₀/α = H₂(1/α) (`ExceptionalPowerBound.one_sub_I0_div_alpha_eq`), and monotonicity of x^e in e for x ≥ 1.

### 2.4 Quantitative result

* **γ:** exactly 1/25 000 000 = 4·10⁻⁸. The budget allows up to ≈ 4.85·10⁻⁸ at these constants; the previous
  asymptotic optimum was 8.6·10⁻⁸ with other constants.
* **ε:** exactly I₀/(2·10⁹), where I₀ = α(1 − H₂(1/α)). Numerically ε ≥ 3.96·10⁻¹¹.
  * The true family gain is I₀(A − 1/α) ≈ I₀/(αP) = 7.4·10⁻¹¹; the rational slack loses a factor ≈ 1.9.
* **Exponents:** baseline H₂(1/α) = 0.9499555; improved ≤ 0.94995550 − 3.96·10⁻¹¹.
* **Comparison:** the external instance certificate from the last round gave 8.7·10⁻¹⁰. The Lean family is ≈ 20×
  weaker, because it uses C(t−1, L−1) ≥ 1 instead of the |V| entropy, fixed rational slack, and γ = 4·10⁻⁸.
  Not optimized, by design.
* **Dominant quantitative loss (unchanged):** white contraction d²/N₀ inside γ (§5).

## 3. Arithmetic frontier (Stage Two)

### 3.1 Exact statement (from `FrontierRegion.lean`)

`PowerOfTwoDangerousWindowSparsityAt U j σ t Us K d a b` holds iff: for every u ≤ Us and every λ ∈ cshell(σ+1, t, u)
(λ ∈ [1, 2^{σ+1+t}) not divisible by 2^t, with centered bit-length u), there is a set bad ⊆ [0, W),
W = ⌊(j/2)/K⌋, such that:
* |bad| ≤ (2/9)·W + (a·log₂ j + b)/K;
* for every window i ∉ bad and every start state y ∈ {0, …, σ}:
  val_i(y) := Σ_z ker(geoW)(iK → iK+K)(y, z) ≤ 2^{2K/10}.

Here the one-block kernel is geoW_r(x, y) = p²·q^{y−x−2}·Σ_{z∈(x,y), z ≤ b_U(2r+1)} (3 if z+1 ∈ (x,y) ∧ Dark_r(z) else 1), with
* p = (j−1)/(σ−1), q = (σ−j)/(σ−1);
* Dark_r(z) ⇔ ‖λ·3^{−(2r+2)}·2^z / 2^m‖ < d (with 3^{−(2r+2)} taken mod 2^m);
* m = σ + 1 + t.

In the final family: U = 0, j = Pm, K = ⌊7·log₂ j⌋, d = 1/108, a = b = 2, Us = σ + t (all shells).

### 3.2 λ = 1 specialization

* u = 0 gives cshell = {1, 2^m − 1}, and these have identical dark sets (`DangerousWindows.nodd_companion`).
* So the u = 0 part is exactly the λ = 1 statement: dark ⇔ the balanced top digits of 2^{z−m} mod 3^{2r+2}
  (reciprocity; the correction term needs 2^{m−z} > 108).

### 3.3 Fixed-target formulation (PROVED (MATH), previous round; restated exactly)

* Window i reads rows r ∈ [iK, (i+1)K); the last row has depth B_i = 2(i+1)K.
* With ξ = λ·2^{−m} ∈ ℤ₃ and T_i(x₀) := frac(2^{x₀}·(ξ mod 3^{B_i})/3^{B_i}), the uncapped black-model danger of
  window i from state x₀ is **T_i(x₀) ∈ 𝔇_K**, a fixed finite union of arcs independent of i, j, λ (given p, q).
* Dark ⊆ black and the cap only removes weight, so danger_i ⇒ ∃x₀ ∈ X_i with T_i(x₀) ∈ 𝔇_K, where
  |X_i| = top(2iK) − 2iK + 1 ≈ 0.585·2iK.
* For λ = 1, T_i(x₀) = (2^{x₀−m} mod 3^{B_i})/3^{B_i}: short exponent ranges of length ≍ depth.

### 3.4 Structure of danger sets (COMPUTATIONAL, exact cell evaluation; `dangerset.c` → `DANGERSET.txt`)

Idealized window (x₀ = 0, no cap, s = 3, η = 1/54, p = 1/α, columns z ≤ Z). All breakpoints are multiples of
1/(54·2^Z·9^{K−1}).

| K | Z | μ(𝔇_K) | arcs | E[val] | max val |
|---|---|---|---|---|---|
| 1 | 12 | 1/18 = 0.05556 | 4 | 1.0272 | 1.738 |
| 2 | 11 | 0.06070 | 32 | 1.0368 | 2.914 |

* **Symmetry.** 𝔇_K + 1/2 = 𝔇_K: every test uses 2^z·T with z ≥ 1. All odd Fourier coefficients vanish exactly.
* **Fourier.**
  * The top coefficients sit at n = c·2^a·3^b with c ∈ {1, 5, 7, 11}.
  * K = 1: n = 4, 8, 12, 16 carry |ĝ|/μ ≈ 0.99, 0.97, 0.94, 0.90.
  * K = 2: n = 144, 72, 18, 36, 54, 288 carry 0.87, 0.66, 0.54, …
  * The ℓ¹ mass is **not small**: Σ_{n≤1500}|ĝ(n)|/μ = 26.4 (K = 1) and 34.0 (K = 2), growing with the range.
    The share on n = 2^a·3^b is about 29%.
* **Dilation overlap.** μ(𝔇 ∩ 2^{−r}𝔇)/μ² = 12, 6, 3, 1.5, 1.1, … (K = 1) and 9.5, 4.8, 2.5, 1.4, 0.8, 1.0 (K = 2).
  * Start states within ≈ 4–5 doublings are strongly correlated; beyond that, independent to within a few percent.
  * **Effective number of independent start states ≈ |X_i|/5.**
* **Distinguishing structure against the adversarial targets of the Erdős round:** 1_{𝔇_K} = F(N₁T, …, N_qT)
  with N ∈ {2^z·9^f}.
  * So the Fourier support lies in {Σ c_i·2^{z_i}·9^{f_i}}. Adversarial arc-unions around orbit points do not have
    this.
  * **But** the orbit sum Σ_x e(c·2^z·9^f·2^{x−m}/3^B) is again a short Korobov sum at depth B − 2f with small c.
    Kill condition 4 (no new cancellation at length ≍ depth).

### 3.5 λ = 1 window data (COMPUTATIONAL; exact Lean dark predicate; `windows_lam1.py` → `WINDOWS_LAM1.txt`, `ANALYZE_RUNS.txt`, `TREND.txt`)

j ∈ {1600, 3200}, t ∈ {1, 7, j/6}, disjoint windows K ∈ {3, 4, 6, 8, 12}. The formal threshold is rate > 0.1. With the
production K = ⌈2 log₂ j⌉ or K = ⌊7 log₂ j⌋ there are **zero** dangerous windows (earlier rounds), so run statistics
can only be taken at surrogate small K.

| j | K | dangerous fraction (t = 1 / 7 / j/6) | max rate |
|---|---|---|---|
| 1600 | 6 | 0.43 / 0.43 / 0.41 | 0.18 |
| 1600 | 8 | 0.13 / 0.13 / 0.16 | 0.13–0.14 |
| 1600 | 12 | 0 / 0 / 0 | 0.096 |
| 3200 | 8 | 0.29 / 0.29 / 0.28 | 0.19–0.21 |
| 3200 | 12 | 0.03 / 0.03 / 0.02 | 0.11–0.14 |

* **Trend.** The danger fraction by quarter of the word (j = 3200, K = 8) is 0.04, 0.20, 0.38, 0.52, while states per
  window run 1, 468, 936, 1404. **Danger is driven by the union over start states.**
* **Persistence.** Raw P(D_{i+1} | D_i) > P(D) (clustering; runs up to 97 at K = 4). After detrending it matches the
  local rate: 0.357 vs 0.339 (K = 8) and 0.731 vs 0.731 (K = 6). No anti-persistence, no excess clustering.
* **Congruences.** Dangerous windows are uniform mod 2, 3, 9. Dangerous exponents a = m − x₀ are uniform mod 6
  (e.g. 634/636/638/633/601/613). **No exact zero cells.**
* **2-of-9.** The fraction of 9-blocks with ≤ 2 dangerous windows ranges 0.06–0.88, tracking P(D). Disjoint 9-blocks
  with 9/9 dangerous occur. **No 2-of-9 mechanism** (REFUTED as an exact law at these parameters).
* **t-independence.** t = 1 and t = 7 give identical window patterns at j = 1600 (only m − z matters, and the state
  scan absorbs the shift).

### 3.6 K-spacing, order of 2^K, good K

* **LTE (PROVED (MATH)):**
  * v₃(2^K − 1) = 0 for K odd, and 1 + v₃(K) for K even;
  * v₃(2^K + 1) = 1 + v₃(K) for K odd;
  * ord_{3^D}(2^K) = 2·3^{D−1}/gcd(K, 2·3^{D−1}).
* **Irrelevant for windows (PROVED (MATH)).** Consecutive windows are not related by ×2^K. The phase chain gives
  9^K·θ_{i+1} ≡ 2^G·θ_i with a path-dependent column advance G. No fixed sampling multiplier exists.
* **Good K.** Downstream needs only 0 < K ≤ A·log₂ j + 1 per j (existence), so K may be chosen per j.
  `FrontierFamily` fixes K = ⌊7 log₂ j⌋; its proof uses K only through 0 < K ≤ 7·log₂ j + 1.
  No arithmetic advantage of special K was found. **No good-K theorem.**

### 3.7 Candidate lemma and status

* No exact local law emerged. The data support "window danger ≈ independent events with probability
  ≈ 1 − exp(−|X_i|·δ_K/5)".
* The only structural candidate is the per-window statement: *the short orbit {2^{x−m}/3^B : x ∈ X} (|X| ≍ 0.6B) hits
  𝔇_K at most (|X|/5)·μ(𝔇_K)·(1+o(1)) times, for most windows* (Conjecture DN, previous round). It is not
  proved, and no route below Korobov length was found.

## 4. Negative findings

39. **Still dead:**
    * mixing of ×2 on ℤ₃;
    * the finite exponent-digit transducer;
    * small weighted automata;
    * complexity plus measure;
    * generic exponential sums at N ≍ D (now also for Fourier-structured danger sets);
    * Lagarias counting on O(log j) digits;
    * Borel–Cantelli;
    * t-averaging and frequency averaging.
40. **New counterexamples / REFUTED laws:**
    * exact local anti-persistence;
    * mod-2/3/9 restrictions on dangerous windows or exponents;
    * a 2-of-9 block law.

    All refuted at the surrogate K where dangerous windows exist.
41. **Strongest obstruction to λ = 1.** Danger is a union over ≈ 0.6·B start states (≈ B/5 effectively independent)
    of fixed-target hits by the short orbit 2^{x−m}/3^B. Bounding it needs short-range equidistribution at length ≍ depth.
    No current method reaches that, and Fourier structure only reduces it to the same sums at smaller depth.

## 5. White contraction

42. **Exact source** (`WhiteContraction.wfac_le_of_pair` and `pair_factor_le_of_good`, then
    `AverageOddDark.lean:190`).
    * Block factor W = ‖Σ_{z∈B} e(φ_z)‖/|B|, with φ_{z+1} ≈ 2φ_z.
    * The proof uses **one** consecutive pair z, z+1 whose phase difference is at distance ≥ d from ℤ:
      ‖Σ‖ ≤ (|B| − 2) + ‖e(φ_z) + e(φ_{z+1})‖ ≤ |B| − 2 + 2cos(πd).
    * Hence W ≤ 1 − 2(1 − cos πd)/|B| ≤ κ(d, N₀) = 1 − 2(1 − cos πd)/N₀ for |B| ≤ N₀.
    * Then κ^{2k} ≤ exp(−8kd²/N₀), using 1 − cos πd ≥ 2d².
    * So γ ≤ 8(k/j)·d²/(N₀·ln 2).
43. **Structural vs proof-induced.**
    * d²: structural for one pair (the angle between two unit vectors).
    * 1/N₀: **proof-induced**. Only one white pair among ≤ N₀ choices is used, and the other |B| − 2 terms are bounded
      trivially.
    * The constant: 1 − cos πd ≈ (π²/2)d² against the 2d² used. A trivial ×2.47 is lost (PROVED (MATH)).
44. **Possible improvement mechanism (PROVED (MATH) for the inequality; the input is OPEN).**
    * Pair the elements of B into ⌊|B|/2⌋ disjoint consecutive pairs; let w be the number of white pairs.
      Then W ≤ 1 − 2w(1 − cos πd)/|B|.
    * If a fixed fraction ω of consecutive pairs in good blocks is white, κ = 1 − ω(1 − cos πd), **independent of N₀**.
      N₀ then enters only through the class loss α/(N₀+2), giving up to a ×N₀ ≈ 133 gain in γ (≈ 2 orders).
    * The required input is a white-pair-fraction statement for all choices in a block. The current pressure frontier
      controls only the own odd choice (N_odd). This would be a **restated arithmetic frontier**, not free.
45. **Locality / cluster lemma.**
    * PROVED (MATH): black cells with pairwise disjoint 3-adic digit windows [b_i − 3, b_i) are **exactly** Haar
      independent, each with probability 1/27. The fresh digits are uniform conditionally, and C_i ∈ F_{b_i} ⊆ F_{b_{i+1}−3}.
    * Within a component, the sequential fresh-digit rank gives μ ≤ 3^{−rank_seq}. The column-gap refinement
      (exact rank 3 + δ·log₃2 for same-row cells, previous round) is not proved in general. OPEN.

## 6. Final verdict

46. **Strongest PROVED (LEAN) result:** `FrontierFamily.exceptional_bound_family_exponent`: for all m ≥ 100,
    frontier ⇒ #(E₀ ∩ [0, 2^K)) ≤ (3/2)(2^K)^{H₂(1/α) − I₀/(2·10⁹)}.
47. **Strongest PROVED (MATH) result:**
    * the exact danger-set symmetry and fixed-target form;
    * exact Haar independence of window-separated black cells;
    * the white-contraction constant trace, with 1/N₀ proof-induced.
48. **Strongest COMPUTATIONAL result:**
    * λ = 1 window danger is explained by start-state counting;
    * detrended windows are uncorrelated;
    * no exact congruence or 2-of-9 law;
    * the start-state correlation length is ≈ 4–5 doublings.
49. **Strongest negative:** every exact local law tested is refuted, and the Fourier structure of danger sets gives no
    cancellation beyond short Korobov sums.
50. **Is the conditional chain now completely closed except arithmetic?** **Yes, for the explicit family.** The final
    Lean theorem's only substantive hypothesis is `PowerOfTwoDangerousWindowSparsityAt` on the good pairs.
51. **Did λ = 1 move?** **No.**
52. **Is there a credible local route to the 2/9 bound?** **No.** Danger is governed by a union over growing start-state
    sets, not by local interactions between windows.
53. **Continue the frontier or redesign white contraction next round?** **Redesign white contraction next.**
    * The frontier has no new structural handle.
    * White contraction has an identified ×2.47 constant gain (trivial) and a potential ×N₀ gain.
    * The ×N₀ gain needs a white-pair-fraction input, which should be checked against the existing pressure machinery
      before being treated as a new frontier.
54. **Exact next theorem:** a multi-pair block contraction W ≤ 1 − 2·w_B(1 − cos πd)/|B|, plus a pressure-style bound
    showing that good blocks have w_B ≥ ω|B| except on an exponentially small class mass. That would replace d²/N₀ by
    ω·d² in γ.
55. **Top three Lean tasks:**
    1. `wfac_le_of_pairs` (multi-pair contraction) and the constant 1 − cos πd ≥ (π²/2 − ε)d² in place of 2d²;
    2. strengthen `FrontierFamily` to use the |V| entropy and the optimal γ (×20 in ε, optional);
    3. generalize `FrontierFamily` from K = ⌊7 log₂ j⌋ to any 0 < K ≤ A·log₂ j + 1.
56. **Top three arithmetic tasks:**
    1. formulate the white-pair-fraction input and test it numerically at λ = 1 (is it implied by the existing dark
       statistics?);
    2. a per-window short-orbit hit bound for |X| ≍ 0.6B at a single fixed depth (the real frontier core);
    3. a rank/locality lemma with column-gap credit (needed for any rigorous multi-path improvement).
57. **EOC level:** **LEVEL 3**. The analytic/combinatorial chain is fully closed in Lean for an explicit infinite family,
    and the frontier is the only input. The frontier itself is untouched (LEVEL 1 on that axis).

## Files

| file | content |
|---|---|
| `EOC/FrontierFamily.lean` | α bounds, barrier facts, ratio majorants, growth lemmas, per-pair data, final theorems |
| `dangerset.c` → `DANGERSET.txt` | exact phase danger sets (measure, arcs, Fourier, dilation overlap) |
| `windows_lam1.py` → `WINDOWS_LAM1.txt`, `windows_lam1.json` | λ = 1 window danger data |
| `analyze_runs.py` → `ANALYZE_RUNS.txt`; `TREND.txt` | runs, conditional frequencies, 2-of-9, residues, detrending |
