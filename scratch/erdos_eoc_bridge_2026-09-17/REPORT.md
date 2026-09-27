# Erdős/Lagarias ↔ EOC bridge: powers of 2 in ℤ₃ (research round, 2026-09-17)

Nothing committed or pushed. **No Lean changes** (no module was ready; see §15).

Labels: PROVED (LEAN) / PROVED (MATH) / EXTERNAL THEOREM / COMPUTATIONAL / HEURISTIC / CONJECTURAL / REFUTED / OPEN.
Unless stated otherwise, "Haar" statements are about a Haar-random 3-adic phase, **not** about λ = 1.

**Level scale used in the verdict.**
* LEVEL 1: no new theorem; only negatives or computations.
* LEVEL 2: new rigorous results that do not touch the open input (Haar-level, structural, or reformulations).
* LEVEL 3: a rigorous theorem that materially weakens a named open input, or a new Erdős-type bound.
* LEVEL 4: resolves a named open input.

## 0. Headline

1. **No bridge theorem for λ = 1.** Nothing in Lagarias 2009, Abram–Lagarias 2014 or Abram–Bolshakov–Lagarias 2017
   implies any part of `PowerOfTwoDangerousWindowSparsityAt`. Their counting mechanism controls only
   O(log j) rows. Their dimension theorems are about all-digit Cantor restrictions, which have dimension 0 already
   for 3 multipliers. In phase coordinates the EOC frontier is a **fixed-target, short-range (length ≍ depth)
   equidistribution problem for 2^x/3^B in ℤ[1/3]/ℤ**. The literature has no result in that regime: Korobov needs
   N ≥ exp(C·k^{2/3}), and Bourgain/Vandehey need N ≥ 3^{εk}.
2. **PROVED (MATH), exactly verified.** There is an exact, K-independent single-path phase chain
   θ_{r+1} = frac(2^{g_r}(θ_r + D_r)/9) with D_r uniform on {0..8}. Its finite cell majorant, a weighted automaton
   with 55 296 phase states, gives
   **P_Haar(K-window mass > 2^{K/5}) ≤ 5.562 · 3^{−0.14276 K}**, uniformly in q ∈ [0.367, 0.37] and in the start phase.
   It is certified by an exact-integer super-eigenvector check. Previous rigorous bounds: 0.1002 (β = 1), 0.1364 (β = 2),
   0.1396 (best β). This fires positive stop condition 2, but the gain is small: A_min goes from 4.52 to 4.42.
3. **COMPUTATIONAL: the "c ≈ 0.5" is not an automaton or coupling effect.**
   * The exact single-path operator converges to c ≈ 0.148 (Jensen β ≈ 2) and blows up for β ≥ 3.
   * The coarse 2-state LP is already within 0.001 of exact at β = 1.
   * The measured asymptotic danger exponent is ≈ 0.43 (black model, η = 1/54) and ≈ 0.50 (η = 1/108).
   * Quenched multi-path moments E[val^β] reach it: the Chernoff exponent is ≈ 0.29 / 0.37 / 0.43 at β = 3 / 4 / 5.
   * The missing information is **path averaging (replica structure)**, not phase resolution.
4. **Erdős side (COMPUTATIONAL; one erratum).**
   * AL13 Table 5.2 lists dim C(1, 2⁸) = 0.287416. Three independent methods give **0.306871**: automaton spectral
     radius, brute-force prefix counts, and the exact characteristic polynomial.
   * Extending the table to 2³⁰: dim C(1, 2^a) for a = 16…30 lies in [0.2597, 0.2630]. At a = 30 it is 0.261895.
     This concentrates at **log₃(4/3) = 0.261860**, the independent-digit value. Random multipliers of the same size
     behave identically.
   * CONJECTURAL: lim dim C(1, 4^m) = log₃(4/3). If true, ABL's inequality (6.2) gives Γ ≤ 0.2619, improving the
     published log₃ φ ≈ 0.438. It would also show that the single-multiplier route cannot go lower.
5. **Structural negatives.**
   * Exponential sparsity plus polynomial automaton complexity does **not** control orbit hits (explicit counterexample).
   * n ↦ digit_D(2^{−n}) has Hankel rank ≈ 2·3^{D/2} in the exponent digits. So there is no polylogarithmic-memory
     matrix-product representation. This is strictly stronger than the refuted deterministic transducer.
   * x ↦ 2x on ℤ₃^× has pure point spectrum, so no mixing shortcut exists.

---

## 1. Part I — repository state (verified this round)

* Branch `research-sparse-visits-2026-09-16`, HEAD 14dea46.
* Uncommitted: `EOC.lean`, `docs/LITERATURE_CONTEXT.md`, `docs/RESEARCH_STATUS.md`, plus the new modules
  `EOC/ConditionalChain.lean`, `EOC/FrontierRegion.lean`, `EOC/ShapeRegion.lean`. All are imported by `EOC.lean`.
* `lake build EOC`: **Build completed successfully (8806 jobs)**. No errors; no `sorry` in the log.
* `#print axioms` gives exactly `[propext, Classical.choice, Quot.sound]` for all of:
  `ShapeUnconditional.shapeTail_allEven`, `ShapeRegion.shapeTail_region`, `PressureBridge.sum_pow_nodd_le_geo`,
  `DangerousWindows.summedPressure_of_tenth_twoNinths`, `DangerousWindows.val_le_ceiling`,
  `ArithmeticFrontier.black_fiftyfourth_iff`, `ArithmeticFrontier.lowFreqDecay_of_powerOfTwoSparsity`,
  `FrontierRegion.lowFreqDecay_of_sparsityAt`, `ConditionalChain.weightedFourier_of_sparsityAt`,
  `ConditionalChain.exceptional_bound_of_pairInputs`.

The authoritative status in the brief is confirmed:
* PROVED (LEAN): top-shell and region ShapeTail, PressureBridge, the dangerous-window wrapper, the frequency-summed
  route, `…SparsityAt ⇒ LowFreqDecay`, and `exceptional_bound_of_pairInputs`.
* OPEN: the frontier Prop, the |V_{σ,s}| lower bound, the high-frequency sieve, `hweight`, and persistence.
* Local constants: θ_d = 1/10, allowed fraction 2/9, target 1/6.
* Worst certified sampled rate 0.09124. That is 8.8% below 0.10, **not** a wide margin.
* Haar bound 1.055·3^{−0.100K}: PROVED (MATH). The 0.136 figure uses β = 2.

## 2. Part II — primary sources read (PDFs in `lit/`, text extracted)

### Lagarias, "Ternary expansions of powers of 2", J. LMS 79 (2009) 562–588, arXiv:math/0512006v4 (§§1, 3, 4, 5 read)

* **Erdős's conjecture** (as stated there): (2ⁿ)₃ omits the digit 2 only for n ∈ {0, 2, 8}. Lagarias's "Conjecture of
  Erdős" is the weak form: finitely many n.
  * Gupta: no other solutions for n < 4374.
  * Narkiewicz 1980: N₁(X) ≤ 1.62·X^{log₃2}.
* **Thm 1.4** (EXTERNAL): for every nonzero λ ∈ ℤ₃, Ñ_λ(X) = #{n ≤ X : λ2ⁿ omits 2} ≤ 2X^{log₃2}.
  * Proof: 2 is a primitive root mod 3^k, so n ↦ λ2ⁿ mod 3^k runs over all 2·3^{k−1} units in one period.
  * Exactly 2^{k−1} of those units omit 2 in their lowest k digits.
  * Choose 2·3^{k−2} < X ≤ 2·3^{k−1}.
* **Thm 1.5** (EXTERNAL):
  * dim E^{(1)}(ℤ₃) = log₃2.
  * ½log₃2 ≤ dim E^{(2)} ≤ ½, using Σ_A ⊂ C(1, 4).
  * dim E^{(3)} ≥ (1/6)log₃2, using C(1, 4, 256).
* **Thm 1.6**: dim C(1, M) ≤ ½ if M is not a power of 3. The proof pairs digits (d_{2lm+k}, d_{(2l+1)m+k}): at most
  3 of the 4 values are admissible. Also dim C(1, 7) = log₃φ.
* **Thm 1.7** (lower bound via N with N·M_i ∈ Σ).
* **Conjectures A, B**: the real and 3-adic exceptional sets have dimension 0. **Conjecture E**: Furstenberg-type
  pattern occurrence.
* **Thm 1.1–1.3**: the truncated real system (N_λ(X) ≤ 25X^{0.9725}; dim E_T = log₃2).

### Abram–Lagarias, "Intersections of multiplicative translates of 3-adic Cantor sets", arXiv:1308.3133 (read in full)

* **Thm 1.6 / 3.1 / 3.3** (EXTERNAL):
  * C(1, M₁, …, M_n) is a 3-adic path-set fractal with a right-resolving, essential presentation of
    ≤ ∏(1 + ⌊M_i/2⌋) vertices.
  * dim = log₃β, where β is the Perron root (a Perron number in [1, 2]).
* **Algorithm A**, for M ≡ 1 mod 3: the state is the carry N.
  * Digit a ∈ {0, 1} is allowed iff (a + N) mod 3 ∈ {0, 1}.
  * Update N′ = ⌊(N + Ma)/3⌋; reachable 0 ≤ N ≤ ⌊M/2⌋.
  * **Algorithm B**: label product of the per-multiplier automata.
* **Thm 4.2 / 1.7**: dim C(1, L_k) = log₃β_k with β_k^k − β_k^{k−1} − 1 = 0, and → 0.
* **Thm 4.4 / 1.8**: dim C(1, 3^k + 1) = log₃φ; the automaton has 2^k vertices.
* **Thm 4.1**: last nonzero digit 2 ⇒ {0}; all digits in {0, 1} ⇒ positive dimension.
* **Thm 1.9 / 5.1**: dim E⋆ ≥ ½log₃2, so general multipliers cannot give dimension 0.
* **Thm 5.2**: dim E^{(2)} ≥ log₃φ and dim E^{(3)} ≥ log₃β₁ ≈ 0.228392, via C(1, 4, 256).
* Table 5.2: powers of two (see the erratum in §11).

### Abram–Bolshakov–Lagarias, "… II: two infinite families", arXiv:1508.05967 (Exp. Math. 2017) (§§1–2, 6–7 read)

* **Thm 2.1–2.2**: P_k = 2·3^k + 1 has 2^{k+1} vertices and 1 + ⌊k/2⌋ nested SCCs; lim inf dim ≥ (1/8)log₃2.
* **Thm 2.3–2.4**: Q_k = 3^{2k} − 3^k + 1 has 4^k vertices and dim = log₃φ.
* **Thm 2.5**: Γ ≤ lim α_n, using Stewart 1980 (the number of nonzero ternary digits of 2^m → ∞) and
  E₁^{(n+1)} ⊂ ∪_{m ≥ n} C(1, 2^m) (eq. 6.1–6.2).
* **Thm 2.6 / 6.2**: dim C(1, M) ≤ log₃φ for **all** M ≡ 1 mod 3, via an injection into C(1, N_k). Hence
  **dim E(ℤ₃) ≤ Γ ≤ log₃φ ≈ 0.438018**.
* §7: block number and intermittency statistics (empirical).

### Current status of Erdős (literature agent, `lit/LIT_SEARCH.md`; confidence tags there)

* Open.
* Saye (J. Integer Seq. 25 (2022), arXiv:2202.13256) verified no further exceptions for n ≤ 2·3⁴⁵ ≈ 5.9·10²¹, using
  the 2-of-3 lifting lemma.
* No improvement of the exponent log₃2 in Narkiewicz's bound was found. Zhao–Li (arXiv:2405.06220) extend it to
  number fields with the same exponent.
* Dupuy–Weirich (JNT 2016) is full-cycle only.

### Directly relevant existing theorems for EOC (Part XXV)

* **Shrinking targets / Borel–Cantelli**: Kurzweil, Fayad, Tseng, D. H. Kim. All are for almost every starting point
  with fixed-centre or monotone targets. Nothing was found for x ↦ ax on ℤ_p or for single orbits.
* **Lacunary / S-unit metric theory**: Philipp 1994 (LIL for S-unit sequences), Aistleitner–Berkes–Tichy. All are
  Lebesgue-a.e., so they say nothing at the rational points a/3^k that EOC needs.
* **×2×3**: Host; Hochman–Shmerkin; Shmerkin and Wu (2019); Bourgain–Lindenstrauss–Michel–Venkatesh (effective, but
  about density for Diophantine-generic real x). No counting bound for one orbit in thin targets.
* **Korobov sums** (via Vandehey, arXiv:1606.07911): Σ_{n ≤ N} e(a·2ⁿ/3^k) is nontrivial only for
  N ≥ exp(C·k^{2/3}) (Korobov, prime power), or N ≥ exp(k/log log k) to 3^{εk} (Bourgain, Vandehey).
* **None** of these covers N ≍ k, which is where EOC lives (§8).
* **Not claimed as novel** below: anything that is a routine consequence of these.

## 3. Part III — the Erdős problem, precisely

Σ := Σ_{3,2̄} = {x ∈ ℤ₃ : all digits ∈ {0, 1}}; dim = log₃2; Haar measure 0.

| object | definition | status |
|---|---|---|
| Erdős (strong) | 2ⁿ ∈ Σ ∩ ℕ only for n ∈ {0, 2, 8} | OPEN (verified to 2·3⁴⁵) |
| Erdős (weak) | finitely many n | OPEN |
| E(ℤ₃) | {λ : λ2ⁿ ∈ Σ for infinitely many n} | Conj. B: dim 0. PROVED ≤ log₃φ (ABL) |
| E^{(k)}(ℤ₃) | ≥ k hits = ∪_{m₁<…<m_k} C(2^{m₁}, …, 2^{m_k}) | dim E^{(2)} ∈ [log₃φ, log₃φ]; dim E^{(3)} ≥ 0.228 |
| fixed-λ count | #{n ≤ X : λ2ⁿ ∈ Σ} ≤ 2X^{log₃2} | EXTERNAL (Lagarias Thm 1.4) |

**Three levels, kept separate.**

* **(a) Finite digit restriction.** For example "the lowest k digits of λ2ⁿ omit 2". This is a clopen set of Haar
  measure (2/3)^k.
  * It is the only thing Thm 1.4 uses: full membership is weakened monotonically to the lowest k ≈ log₃X digits.
* **(b) Whole-expansion restriction**, λ2ⁿ ∈ Σ.
  * A closed null set of dimension log₃2.
  * Intersections over k multipliers are path-set fractals.
* **(c) Infinitely many orbit hits** (E(ℤ₃)). A limsup of (b). Its dimension is controlled only through the E^{(k)}.

## 4. Part IV — the Abram–Lagarias automaton

`automata.py` is a generalized Algorithm A/B. It supports constraints "digits of M·x + c lie in allowed(n)", with
M coprime to 3 and c ∈ {0, −1/2}; the label product is implicit because states are carry tuples.

* **States**: carry tuples (N₁, …, N_n).
* **Transitions** on digit a: tot = N + M·a + c_n; output tot mod 3; N′ = ⌊tot/3⌋.
* **Adjacency**: the row sum is the number of admissible digits.
* **Perron root** = spectral radius (max over SCCs). dim = log₃β (AL13 Prop 2.2; EXTERNAL).

**Validated** (`validate_AL.py` → `VALIDATE_AL.txt`, COMPUTATIONAL). All published examples reproduce:
* C(1, 7), C(1, 19) (8 vertices, β = 1.465571), C(1, 7, 19), C(1, 43) = dim 0.
* L_k for k = 2..9 (k vertices), N_k for k = 1..8 (2^k vertices), P_k for k = 1..8 (vertex counts and β exactly as in
  ABL Table 2.1), Q_k for k = 2..5 (4^k vertices).
* ABL Table 7.1 (all 20 rows: vertices and β), C(1, 4, 256) = 0.228392, and the zero entries of AL13 Table 5.2.

Every "MISMATCH" line except C(1, 2⁸) is sixth-decimal rounding of log₃β **in the papers**: β agrees to 6 decimals.
For example log₃ 1.392067 = 0.301098, while ABL prints 0.30101 for P₇. See §11 for C(1, 2⁸).

**What depends on M_i = 2^{a_i}?** Algorithm A/B works for any M coprime to 3.

**New for powers of 2 — carry collapse (PROVED (MATH)).**
* If M | M′, then ⌊M·t⌋ = ⌊⌊M′·t⌋/(M′/M)⌋ for t = (x mod 3ⁿ)/3ⁿ.
* So for multipliers 2^{a₁} | … | 2^{a_k}, the carry tuple is a function of the top carry.
* Hence **#states C(1, 2^{a₁}, …, 2^{a_k}) ≤ #states C(1, 2^{a_max}) ≤ 1 + 2^{a_max−1}**, instead of ∏(1 + 2^{a_i−1}).
* Checked on all 28 pairs a < b ≤ 16 (0 violations; `COLLAPSE_EOCFAMILY.txt`).
* The same holds with the additive constant −1/2: the carry of (Mx − 1/2) is ⌊(⌊2Mt⌋ + 1)/2⌋ for units.

## 5. Part V — two different automaton statements (explicit)

* **REFUTED earlier, still valid** (`scratch/sparsevisits_2026-09-16`): no bounded-memory **transducer from the base-3
  digits of the exponent a** to the digits of 2^{−a} mod 3^D.
  * Input alphabet: digits of a.
  * Output: digits of the residue.
  * Memory must grow like the depth.
* **Abram–Lagarias** (EXTERNAL, and valid): a finite automaton reading **the 3-adic digits of the point x itself**
  recognizes x ∈ ∩ M_i^{−1}Σ.
  * Input alphabet: digits of x.
  * The multipliers are fixed.
  * Membership of the orbit point is **not** decided by it.
* **Why they do not conflict.**
  * The AL automaton answers "is this point in the set?".
  * The transducer would answer "where does the orbit point 2^{−a} lie, given a?".
  * Composing them would need the orbit map a ↦ digits(2^{−a}), which is exactly the non-finite-state step.
* **This round strengthens the negative** (§12.4). Even a *linear* (weighted / matrix-product) representation of
  a ↦ digit_D(2^{−a}) needs dimension ≈ 2·3^{D/2}.
* **AL-type automata on the phase ξ do exist for every fixed EOC window** (§7). They are not rejected.

## 6. Part VI — the EOC phase in Lagarias's language

From the Lean definitions:
* `oddW (collatzBarrier U) (σ+1+t) d 3 lam` gives m = σ + 1 + t.
* `OddBlack.Dark m d λ r z` means distZ(λ·uInv(m, 2r+1)·2^z/2^m) < d.
* uInv(m, 2r+1) = 3^{−(2r+2)} mod 2^m.

**Reciprocity (PROVED (MATH); exact check in `IDENTITIES.txt`).**
Let A = 3^{−b} mod 2^m and B = 2^{−m} mod 3^b. Then A/2^m + B/3^b = 1 + 1/(2^m 3^b). Hence
λ·2^z·A/2^m ≡ −(λ2^{z−m} mod 3^b)/3^b + λ2^z/(2^m 3^b)   (mod 1).

**EOC phase:**
* ξ = λ·2^{−m} ∈ ℤ₃ (a unit when 3 ∤ λ); for the u = 0 shell, λ = 1.
* Row r reads depth b_r = 2r + 2.
* Cell (r, z) tests the multiplicative translate **2^z·ξ**, with z the odd-position prefix sum:
  z ∈ Bset(r, x, y) = (x, y) ∩ [0, collatzBarrier U (2r+1)].
* Window i: rows r ∈ [iK, (i+1)K), start state x₀ ∈ Fin(σ+1), multipliers 2^{z−x₀} relative to the window.
* Equivalently, in the repo's exponent: 2^{−a} with a = m − z.
* Along a path the exponents are z_r = x_{2r} + i_r, where x_{2r+2} − x_{2r} = i_r + k_r and i, k are two
  Geom(p) ≥ 1 odd steps. The black test applies to the "own odd choice", with eligibility k_r ≥ 2.

## 7. Part VII — one black event as a 3-adic set (PROVED (MATH); exhaustive check b ≤ 10)

`black_cylinder.py` → `BLACK_CYLINDER.txt`. For x ∈ ℤ₃ and b ≥ 3, the following are equivalent:
* (i) 54·|centered(x mod 3^b)| < 3^b (the Lean `black_fiftyfourth_iff` form);
* (ii) balanced digits e_{b−3} = e_{b−2} = e_{b−1} = 0;
* (iii) the ordinary digits b−3, b−2, b−1 of x − 1/2 equal 1 (since −1/2 = …111₃ ≡ (3^b − 1)/2 mod 3^b);
* (iv) ‖x mod 3^b / 3^b‖ < 1/54.

So **B_b = 1/2 + W_b**, where W_b = {w : w_{b−3} = w_{b−2} = w_{b−1} = 1}.
* Haar measure exactly **1/27**; exactly 3^{b−3} residues mod 3^b.
* **Not a single cylinder** (3-adic ball). Its minimal ball decomposition needs all 3^{b−3} balls of radius 3^{−b}:
  none of radius 3^{−(b−1)} fits.
* In real-phase coordinates t_b = (x mod 3^b)/3^b it **is one arc**, (−1/54, 1/54).
* It is an **additive** translate (by 1/2) of a finite digit-window set. In balanced digits it is a pure window set.

The event at cell (r, z) is ξ ∈ 2^{−z}·B_{b_r}, a multiplicative-and-additive translate.

## 8. Parts VIII–X — sets of black events; transient intersections; the danger set

**Part VIII.** Black events at (z_r, b_r) for r ∈ S give ξ ∈ ∩_{r∈S} 2^{−z_r}B_{b_r}. Formal differences from
AL's C(1, 2^{a₁}, …):

| AL intersection | EOC |
|---|---|
| target Σ at all digit positions | 3-digit window at depth b_r (transient) |
| ordinary digits {0, 1} (2 of 3) | balanced digits = 0 (1 of 3), additive shift 1/2 |
| fixed finite multiplier set | multipliers chosen by a random P* path (union / average over paths) |
| hard intersection | weighted: val = E*[∏_r 3^{B_r}], danger iff val > 2^{K/5} |
| always applies | eligibility k_r ≥ 2 and cap z ≤ b(2r+1) (both only remove weight: monotone) |

**Part IX — transient constraint sets (definitions).**

Let F_n = σ(ξ mod 3ⁿ) under Haar measure. A **constraint** is a triple (C_i, p_i, q_i) with C_i ∈ F_{q_i} and
P(C_i | F_{p_i}) ≤ ε_i a.s. (window [p_i, q_i)). For digit-window constraints C_i = {digits [p_i, q_i) of M_iξ + c_i ∈ A_i}
with M_i a unit, the conditional law of those digits given F_{p_i} is **exactly uniform**, so ε_i = |A_i|·3^{−(q_i−p_i)}.
Define T((C_i)) = ∩ C_i.

**Theorem T1 (hard; PROVED (MATH)).**
* (a) If the windows are pairwise disjoint: μ(T) ≤ ∏ε_i.
* (b) Sort by q_i. If P(C_i | F_{max(p_i, q_{i−1})}) ≤ ε′_i, then μ(T) ≤ ∏ε′_i. For single-pattern windows,
  ε′_i = 3^{−f_i} with **refresh count** f_i = q_i − max(p_i, q_{i−1}).
* (c) If every digit position lies in ≤ M windows (interval-graph clique ≤ M, hence M colours), then
  μ(T) ≤ (∏ε_i)^{1/M}.

Proof:
* Tower property: C_j ∈ F_{q_j} ⊆ F_{p_i} for earlier disjoint windows.
* Interval graphs are perfect, and the minimum over the M colour classes is ≤ the geometric mean.

**Theorem T2 (weighted, bounded overlap; PROVED (MATH)).** For weights s_i ≥ 1:
E[∏ s_i^{1_{C_i}}] ≤ ∏_i (1 + (s_i^M − 1)ε_i)^{1/M}.
Proof: Hölder over the M colour classes, then T1(a) inside each class.

**Theorem T3 (Markov-boundary form; PROVED (MATH)).** Suppose consecutive windows share a boundary block whose
status X_i ∈ F_{q_{i−1}} takes finitely many values, and the conditional laws satisfy linear marginal constraints.
Then E[∏ s^{1_{C_i}}] ≤ 1ᵀ∏M_i 1 with LP-extremal matrices. The existing EOC 2-state operator is the case
"1 shared digit".

**Codimension and overlap for EOC (PROVED (MATH)).**
* One path with black-eligible rows S: windows [b_r − 3, b_r), overlap multiplicity M = 2 (consecutive rows share
  position b_r − 1).
* T1(b) gives codim ≥ 2|S| + (#maximal runs of consecutive rows in S) ≥ 2|S| + 1.
* T1(c) gives only 1.5|S|. **Colouring is weaker than sequential conditioning.**
* Across windows the digit blocks are nested (§9), so M = 1.

**Part X — does danger lie in a union of transient intersections?** Yes (PROVED (MATH)):
* val ≤ max_path 3^{N_path}, so danger ⇒ ∃ path with N ≥ ⌊0.1262K⌋ + 1 =: n₀ eligible blacks.
* So {danger} ⊆ ∪_{ω∈Ω_K} T_ω, with ω = (S, (z_r)_{r∈S}), |S| = n₀, and codim T_ω ≥ 2n₀ + 1.

**The union bound fails (REFUTED as a route).**
* |Ω_K| ≳ C(K, n₀)·(c₁K)^{n₀}, with c₁K ≈ 3.17K reachable columns.
* log₃(Σ_ω μ(T_ω))/K ≥ H₃(0.126) + 0.126·log₃(3.17K) − 0.252 ≈ 0.093 + 0.126·log₃(3.17K) > 0 for every K.
* **Kill condition 1/3.** This is why the moment method is essential; it re-expresses, not improves, the Haar bound.

## 9. Parts XI–XIII, XXXIV–XXXVI — automata, the phase operator, and the 0.5 question

### 9.1 Finite automata for fixed data (Part XI) — PROVED (MATH)

For fixed finite data, T((a_i, B_i)) is clopen, so a finite automaton trivially exists. The useful form:
* Read ξ's digits low-first.
* Take as state the top carry c = ⌊2^{Z+1}·(ξ mod 3ⁿ)/3ⁿ⌋ ∈ [0, 2^{Z+1}), with Z the largest multiplier exponent.
* The transition is exactly c′ = ⌊(c + 2^{Z+1}d)/3⌋. This is Algorithm A for M = 2^{Z+1}.
* By carry collapse, every black test for exponents ≤ Z is a function of (c, current digits).

The exact window automaton therefore has ≤ 2^{Z+1} carry states per layer, with Z ≈ 3.17K + O(√K):
**exponential in K (≈ 9^{1.6K})**.

With paths added, a **weighted** automaton (nondeterministic runs = Collatz paths, weight 3 per eligible black) computes
val(ξ) exactly (Part XXXIV). That is correct but state-explosive (kill condition 3 for the literal construction).

### 9.2 The K-independent phase chain (PROVED (MATH); exact checks `IDENTITIES.txt` (1))

Along one path, let θ_r := frac(2^{x_r}·t_{b_r}(ξ)), x_r = x_{2r}. With D_r = digits b_r, b_r + 1 of 2^{x_r}ξ:
* **θ_{r+1} = frac(2^{g_r}(θ_r + D_r)/9)**, g_r = i_r + k_r;
* D_r is uniform on {0, …, 8}, independent of F_{b_r} and of the path;
* row r is black iff ‖2^{i_r}θ_r‖ < 1/54;
* 9θ_{r+1} ≡ 2^{g_r}θ_r (mod 1): the fine phase is deterministic, and the coarse 1/9-cell is fresh.
* Lebesgue measure is invariant for every g.
* In Fourier terms, the Markov operator sends mode k to mode 2^g·k/9 if 9 | k and kills it otherwise
  ("two fresh digits per row" = frequencies not divisible by 9 die in one step).

Structural remark: the barrier drift is E[g] = 2/p ≈ 2log₂3 = log₂9. The EOC diagonal is exactly the direction in
which ×2^g/9 is **isometric on average**: phase information neither decays nor explodes. This is the precise sense
in which the constraints are "transient": they persist only through the 1/9-scale fine phase, and each row refreshes
the coarse 1/9 scale.

**Jensen-β operator** (β ≥ 1):
(L_βf)(θ) = Σ_{i,k≥1} p²q^{i+k−2}·3^{β[k≥2][‖2^iθ‖<1/54]}·(1/9)·Σ_D f(frac(2^{i+k}(θ + D)/9)).
* Jensen over the sub-probability path measure gives E_ξ[val^β] ≤ sup_θ (L_β^K 1)(θ). This holds conditionally on
  F_{b_{r₀}}, uniformly in the start phase.
* Cap, dark ⊆ black, and state truncation are all monotone.

**Cell majorant** (`phaseop/phaseop.c`):
* P = 54·2^{Lc} arcs.
* (L̃F)(I) = Σ_g w_g·((g−1) + (s−1)·cnt_g(I))·(1/9)·Σ_D max{F(J) : J meets image of I}, plus a tail term.
* Here cnt_g(I) = #{i ≤ g−2 : I meets black_i}; i > Lc + 8 counts as meeting.
* f ≤ F cellwise ⇒ L_βf ≤ L̃F. Hence **E[val^β] ≤ ρ′^K·maxV/minV** whenever L̃V ≤ ρ′V.

### 9.3 Results (Method A = 2-state LP; B = phase majorant; C = Monte Carlo)

| method | β | ρ | c = β·log₃2/5 − log₃ρ | status |
|---|---|---|---|---|
| A (LP, q = 0.37) | 1 | 1.028950 | 0.1002 | PROVED (MATH), previous round |
| A | 2 | 1.135854 | 0.1364 | PROVED (MATH), previous round |
| A | 1.8 (best) | — | 0.1396 | PROVED (MATH), previous round |
| B, Lc = 2, 4, 6, 8 | 1 | 1.07203, 1.04183, 1.03255, 1.02959 | 0.063 … 0.0997 | float; converging to ≈ 1.0282 |
| C (quenched Λ(1)) | 1 | 3^{0.0252} = 1.0281 | 0.101 | COMPUTATIONAL; agrees with B's limit |
| **B, Lc = 10, weights uniform in q ∈ [0.367, 0.37]** | 2 | **1.12797** | **0.14276** | **PROVED (MATH)**: exact-integer super-eigenvector check, `VERIFY_L10_b2_uniform.txt`; constant maxV/minV = 5.562 |
| B, Lc = 8, q = 37/100 | 2 | 1.12857 | 0.14228 | PROVED (MATH), exact check, `VERIFY_L8_b2.txt` |
| B, Lc = 12, q = 0.37 | 2 / 1.8 | 1.12227 / 1.09307 | 0.1474 / 0.1461 | float; single-path limit ≈ 0.148 |
| B, Lc = 8 | 3, 4, 6, 8 | 1.517, 3.47, 30.2, 271 | −0.001, −0.63, −2.3, −4.1 | float: **single-path Jensen explodes** |

The q range covers every shell allowed by `FrontierRegion`: 63σ + 37 ≤ 100j gives q ≤ 0.37, and
σ ≥ ⌊jα⌋ − j/300 with j ≥ 300 gives q ≥ 0.3674.

**Theorem H (PROVED (MATH)).** For the black model (η = 1/54) with any cap, any start phase and any
q ∈ [0.367, 0.37]:
P(K-window mass from a fixed state > 2^{K/5} | F_{b_{r₀}}) ≤ 5.562·3^{−0.14276K}.
* The union over σ + 1 ≤ 2j start states needs K ≥ A·log₂j with **A > 4.42** (previously 4.52 at c = 0.1396,
  and 6.30 at β = 1).
* **Not enough for the empirically successful A = 2**, which needs c ≥ 0.3155.

### 9.4 Monte Carlo of the Haar window (Method C; COMPUTATIONAL)

`mc/haarwin.c` uses exact 256-bit residues, uniform ternary digits and the exact kernel recurrence. It was
cross-checked against a direct O(Z²) path sum to 1e−13, and at K = 1: E[val] = 1.02739 against the predicted
1 + 2q/27 = 1.02734. There are 6·10⁶ samples per K. Output is in `MC_ANALYSIS.txt`.

| K | P(danger), η = 1/54 | −log₃P/K | P(danger), η = 1/108 | −log₃P/K |
|---|---|---|---|---|
| 8 | 4.08e−3 | 0.626 | 1.30e−3 | 0.756 |
| 12 | 6.52e−4 | 0.556 | 1.61e−4 | 0.663 |
| 16 | 1.09e−4 | 0.519 | 2.10e−5 | 0.613 |
| 20 | 1.92e−5 | 0.494 | 2.0e−6 | 0.597 |
| 24 | 2.5e−6 | 0.489 | 6.7e−7 (40 events) | 0.539 |

* Asymptotic slopes: ≈ **0.42–0.43** (η = 1/54, K = 12→24) and ≈ **0.50** (η = 1/108, K = 12→20).
* The earlier "3^{−(2.2+0.5K)}" fit is consistent with this.

Quenched log₃E[val^β]/K slopes for K = 12→24 (η = 1/54), and the resulting Chernoff exponent:

| β | 1 | 1.5 | 2 | 2.5 | 3 | 4 | 5 |
|---|---|---|---|---|---|---|---|
| Λ(β) | 0.0252 | 0.0391 | 0.0541 | 0.0706 | 0.0893 | 0.138 | 0.204 |
| Chernoff c | 0.101 | 0.150 | 0.198 | 0.245 | 0.289 | 0.367 | 0.427 |

The β ≥ 4 entries are dominated by rare samples and are indicative only.

### 9.5 Answer to Part XIII (COMPUTATIONAL, with PROVED (MATH) components)

**No: the empirical c ≈ 0.43–0.5 is not an automaton spectral effect of the single-path operator.**
* β = 1: coupling loss is ≈ 0.001 (LP 0.1002 vs exact 0.101).
* Jensen β = 2: coupling loss is ≈ 0.011 (0.1364 vs ≈ 0.148).
* Single-path Jensen caps at ≈ 0.148 whatever the phase resolution.

The gap from 0.15 to 0.43 is lost at the **Jensen step** val^β ≤ E*[∏w^β]:
* val averages over exponentially many paths that decorrelate (their offset performs a mean-zero walk).
* Quenched moments with β ≥ 3 reach the true rate: Λ(2) = 0.054 against the Jensen 0.110.

The relevant object is a **moment (generalized) Lyapunov exponent of a random product of nonnegative matrices**
driven by the phase chain (Le Page / Guivarc'h-type), i.e. a replica (tensor-power) operator. It is not a topological
pressure (§14).

## 10. Parts XIV–XVI — "constraint refresh", general theorem, Cantor specialization

**Definitions (Part XIV), aligned with existing notions.**
* **Refresh count** f_i (T1(b)).
* **Overlap multiplicity** M (interval-graph clique number).
* **Persistence length**: the number of rows through which a constraint's digit block remains unrevealed. For EOC it
  is 1 row: the block [b−3, b) shares only b−1 with the next row. In phase language it is the fine-phase memory of §9.2.
* **Entropy deficit** Δ_D = D − log₃N_D is *not new*: Δ_D/D → 1 − h_top/log 3 = the (box/Hausdorff) codimension of a
  path set. "Refresh rate" = lower box codimension.

| constraint system | Δ_D/D |
|---|---|
| Σ (all digits in {0, 1}) | 1 − log₃2 = 0.369 |
| generic C(1, M) | ≈ 1 − log₃(4/3) = 0.738 (§11) |
| generic C(1, M₁, M₂) | 1 (dim 0) |
| EOC all-black single path | 1 (2 fresh digits per 2 digits) |

**General theorem (Part XV).** T1–T3 are the rigorous statements.
* "≥ cK genuinely new restrictions with overlap ≤ M ⇒ μ ≤ 3^{−cK/M}" is T1(c), and T1(b) gives the sharper
  sequential form.
* Weighted versions are T2 and T3.
* All are elementary: tower property plus Hölder plus LP.

**Counterexample to stronger versions:** the theorem is false for **unions over adaptively many** constraint systems
(§8, the union-bound failure) and says nothing about orbits (§12).

**Cantor specialization (Part XVI).**
* For B_i = "digits in window [p_i, q_i) avoid 2", T1 gives μ ≤ (2/3)^{Σf_i}, the transient analogue of (2/3)^D.
* **Full-depth multiplicative Cantor intersections are the wrong object for EOC.**
  * Among even exponents ≤ 16: k = 1 has 8/8 positive dimension, k = 2 has 1/28 (only (2, 8), 0.2284), k = 3 has 0/56,
    k = 4 has 0/70 (`COLLAPSE_EOCFAMILY.txt`).
  * EOC exponent patterns (gaps = sums of two Geom ≥ 1 steps) contain odd gaps, which give {0} immediately, and
    even-gap subsets are generic, so dimension 0.
  * Kill condition 4 for Parts XVI–XVII as an EOC tool (Hausdorff dimension gives no finite-depth estimate beyond T1).

## 11. Parts XVII, XXXI–XXXIII, XXXVIII — Erdős-side results

**11.1 Erratum (COMPUTATIONAL, three independent methods).** AL13 Table 5.2 lists dim_H C(1, 2⁸) = 0.287416 (β = 1.37130).
* Algorithm A (35 states) gives β = 1.400925.
* Brute-force prefix counts give N₂₀, N₃₀, N₄₀ = 1616, 46022, 1344844, with (N₄₀/N₃₀)^{1/10} = 1.40143.
* The exact characteristic polynomial (degree 35) has largest real root 1.400924990.
* **dim_H C(1, 256) = 0.306871.** All other powers-of-2 entries agree to rounding (`CHECK_256.txt`, `CHARPOLY_256.txt`).
* This does not affect any theorem of AL13/ABL. It is consistent with dim C(1, 4, 256) = 0.228 ≤ 0.307.

**11.2 dim C(1, 2^a) up to a = 30 (COMPUTATIONAL; `POW2_DIMS.txt`).**

| a | 2 | 4 | 6 | 8 | 10 | 12 | 14 | 16 | 18 | 20 | 22 | 24 | 26 | 28 | 30 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| states | 2 | 5 | 14 | 35 | 77 | 181 | 442 | 1079 | 2531 | 6089 | 14863 | 35495 | 83926 | 201743 | 494324 |
| dim | .4380 | .2560 | .2780 | **.3069** | .2152 | .2440 | .2671 | .2619 | .2597 | .2623 | .2627 | .2607 | .2630 | .2617 | **.261895** |

* States grow like ≈ 2.43^{a/2}.
* Control (`RANDOM_M_DIMS.txt`): random M ≡ 1 mod 3 with 11, 13, 16 ternary digits give dimension means
  0.2610, 0.2640, 0.2616. At 16 digits all 8 lie in [0.2602, 0.2625].
* Random pairs: 0/120 positive.
* **HEURISTIC**: independent digits. Each digit of x has 2 choices and the corresponding output digit survives with
  probability 2/3, so β = 4/3 for one multiplier and 2·(2/3)² = 8/9 < 1 for two.
* **CONJECTURAL (C1): lim_{m→∞} dim_H C(1, 4^m) = log₃(4/3) = 0.261860.**
* Consequence via ABL (6.2), where Γ ≤ sup_{m≥n} dim C(1, 2^m) for every n: **C1 ⇒ Γ ≤ log₃(4/3), hence
  dim_H E(ℤ₃) ≤ 0.2619**, versus the published log₃φ = 0.4380. This is conditional.
* Also C1 ⇒ the single-multiplier relaxation cannot go below 0.2619. Γ = 0 would require ≥ 2 multipliers, where
  the generic dimension is 0 but exceptions such as (2, 8) exist.
* Novelty: the concentration at log₃(4/3) is not stated in the three papers read. A general literature check for it
  was **not** done.
* HEURISTIC mechanism: N_{n+1} = N_n + Z_n with Z_n = #{surviving prefixes whose carry digit is 0}, so β = 4/3 iff
  the carry digit is equidistributed under the surviving-prefix measure. This is a ×2^a-versus-×3 transversality
  statement of Host / Fourier-decay type. Not proved.

**11.3 Carry collapse** (§4): the presentation size for any powers-of-2 family is ≤ that of the largest multiplier.
PROVED (MATH); minor.

**11.4 Dimension bound for the EOC-generated family (Parts XVII, XXXII).** There is no meaningful family:
EOC multiplier sets give Cantor intersections of dimension 0 generically (§10). The finite-depth consequence
(Part XXXIII) that EOC actually uses is T1/Theorem H, not a Hausdorff dimension.

## 12. Parts XX–XXIX, XXXIX–XLIV — orbit (λ = 1) questions

**12.1 Lagarias's fixed-λ count adapted to moving targets (Part XX; PROVED (MATH) negative).** Ingredients of Thm 1.4:
* full membership is used **only** through the monotone weakening to the lowest k ≈ log₃X digits;
* the orbit structure is used through primitivity (exact equidistribution over one period 2·3^{k−1});
* there is no λ-dependence.

The adaptation to targets E_n works iff E_n ⊇ E′_n, with E′_n depending only on the digits below log₃(#orbit points)
and constant over the period.

EOC window i involves depth ≈ 2iK, so only i ≲ log₃j/(2K) windows qualify: **O(1) windows**, already inside the
allowance (a log₂j + b)/K. In the dual 2-adic form, black tests read the top bits at position a = m − z of 3^{−b}.
Lagarias-type exact counting applies only when a ≲ log₂j, i.e. the last O(log j) rows with small shift t. Quantified
kill condition 5.

**12.2 Mixing (Part XXVI; PROVED (MATH) with EXTERNAL input).**
* ℤ₃^× ≅ ℤ/2 × ℤ₃, and 2 is a topological generator, since 2 is a primitive root mod 9 and hence mod 3^k.
* x ↦ 2x is a group rotation, minimal and uniquely ergodic on each sphere 3^jℤ₃^× (cf. Fan–Li–Yao–Zhou 2007).
* It is an isometry with **pure point spectrum**: eigenfunctions are the characters, eigenvalues are the roots of unity
  of order 2·3^k. Entropy 0. **Not weakly mixing.**
* What holds: every orbit equidistributes for every **fixed** clopen target E, with discrepancy exactly 0 over each
  full period 2·3^{k−1} and ≤ 2·3^{k−1}/N otherwise.
* EOC targets have depth k ≍ j while the number of relevant orbit points is ≍ j, so the error term 3^{j}/j dominates.
  No mixing shortcut exists.

**12.3 Fixed-target reformulation (Parts XXI, XXIV; PROVED (MATH); `IDENTITIES.txt` (3)).**
* For window i, let B = depth of its last row and T := frac(2^{x₀}·t_B(ξ)).
* Row r's tests read ‖2^{z−x₀}·9^{K−1−(r−r₀)}·T‖.
* So **danger_i ⇔ T ∈ 𝔇_K**, a **fixed** finite union of arcs, independent of i, λ and j (given p, q; cap and
  dark ⊆ black are monotone).
* For λ = 1: T = the class of 2^{x₀−m}/3^B in ℤ[1/3]/ℤ, i.e. (2^{x₀−m} mod 3^B)/3^B.
* **The moving target is an artefact of coordinates.** The EOC orbit problem is: how often do the points
  2^{x₀−m}·3^{−B_i} (x₀ ranging over ~0.585·B_i states, B_i = 2(i+1)K) meet one fixed set of measure
  δ_K ≈ 3^{−0.43K}?
* Targets are **non-adaptive** (fixed shape) and **phase-equivariant** (x₀ acts by ×2^{x₀}).
* The exponent range per window is **linear in the depth**, the regime where Korobov-type bounds are unavailable (§2).

**12.4 No small matrix-product representation in exponent digits (Part XXVIII; COMPUTATIONAL; `HANKEL.txt`).**
For f(n) = [digit_D(2^{−n} mod 3^{D+1}) = 0] and for the black indicator, read n in mixed radix (2, 3, …, 3). The
Hankel matrices at every cut i have GF(2³¹ − 1) ranks, which are lower bounds on the ℚ-rank and hence on the
minimal weighted-automaton / matrix-product dimension (Carlyle–Paz, Fliess; EXTERNAL):

| D | 5 | 6 | 7 | 8 | 9 |
|---|---|---|---|---|---|
| max rank over cuts | 18 | 22 | 54 | 76 | 162 |

Pattern: rank = min(2·3^i, 2·3^{D−i−1} + 1) for the digit indicator, so the maximum is ≈ 2·3^{⌊D/2⌋} ≈ √period.

PROVED (MATH) partial: H[r][h] = g(r·h) on the cyclic group (ℤ/3^{D+1})^× with the subgroup 1 + 3^{i+1}ℤ, and
rank ≤ #{ψ ∈ Ĥ : some extension χ of ψ has ĝ(χ) ≠ 0}.

**Consequence: no logarithmic-memory, matrix-product or discrete-log-pullback representation.**
* Automaton × cyclic exponent product (Part XXVII): the state count equals the period. Kill condition 3.
* Hierarchical recursion (Part XXIX): exists only for full-period counts (the 2-of-3 lift of Saye/Lagarias, boundary
  state = last digit); not for sub-period ranges.

**12.5 Adversarial targets (Parts XXIII, XLIV; REFUTED principle; `ADVERSARIAL.txt`).**
* Moving: E_n = ball(λ2ⁿ, 3^{−D}) has Haar measure 3^{−D}, a (D+1)-state DFA, and is hit at every n.
* **Fixed, n-independent**: T_{D,N} = {2ⁿ mod 3^D : n ≤ N} has Haar measure (N+1)/3^D and is hit by every n ≤ N.
  Its minimal DFA sizes (exact Myhill–Nerode):

| D | N | measure | DFA (low-first / high-first) |
|---|---|---|---|
| 12 | 144 | 2.7·10⁻⁴ | 556 / 561 |
| 14 | 196 | 4.1·10⁻⁵ | 1045 / 1050 |
| 14 | 2744 | 5.7·10⁻⁴ | 3260 / 3925 |

* **Exponential sparsity plus polynomial automaton complexity does not imply sparse hits** (kill condition 6).
* The EOC targets carry extra structure: a fixed shape in phase coordinates, independence from λ and n, and
  digit-local fresh randomness. Even so, the λ = 1 count remains a short-range equidistribution statement.

**12.6 Haar version of the frontier (Parts XL–XLII; PROVED (MATH)).**
* Window i's event is F_{2(i+1)K}-measurable. Theorem H holds conditionally on F_{2iK+2}.
* So for a Haar phase, #bad windows is stochastically dominated by Binomial(W, δ), with
  δ = (σ+1)·5.562·3^{−0.14276K}.
* Hence P_Haar(sparsity fails at level j) ≤ exp(−W·KL(2/9 ‖ δ)) when δ < 2/9.
* **Separation is unnecessary at the Haar level** (the filtration is nested; colouring M = 1 across windows).
  It does not help for orbits.

**EOC exceptional set (Level-C statement; PROVED (MATH)).**
* Define E_EOC := {λ ∈ ℤ₃^× : the black-model window sparsity fails for the phase λ·2^{−m_j} at infinitely many j},
  with K = A·log₂j, A > 1/(0.14276·log₂3) ≈ 4.42, the dark ⊆ black reduction as in item 8, and all start states.
* Haar measure is invariant under ×2^{−m_j}, so Borel–Cantelli gives μ(E_EOC) = 0.
* Bad_j is a union of ≤ 3^{j+2}ε_j balls of radius 3^{−(j+2)}, with
  −log₃ε_j = (j/9)(c − log₃2/A)(1 + o(1)). The Hausdorff series then gives
  **dim_H E_EOC ≤ 1 − (c − log₃2/A)/9** with c = 0.14276. As A → ∞ this is ≈ 0.984. (Asymptotic constants; audited
  here, not in Lean.)
* The frontier for the u = 0 shell at level j follows from 2^{−m_j} ∉ Bad_j. So "**1 ∉ E_EOC**" is the EOC analogue of
  "1 ∉ E(ℤ₃)" (Erdős).
* Honest scope: a measure/dimension statement only. Nothing about λ = 1 (Part XLII), exactly as Conjecture B
  says nothing about 2ⁿ.

**12.7 Parts XXII, XXXIX: a λ = 1 sparse-hit theorem or parameter regime.** **None proved.**
* A = 7: no. Specific offsets U: no. Separated windows: no, since they reduce to the same short-range statement.
* Averaged families over t, u or j: already shown not to weaken the input (previous round).
* The only unconditional orbit control is Lagarias-type exact counting on the O(log j) corner rows (§12.1).

## 13. Parts XLV — minimal common hypotheses and the resulting conjecture

Hypotheses that suffice at Haar level:
* (H1) targets are finite intersections or weighted unions of multiplicative translates of fixed digit windows;
* (H2) conditional window probability ≤ ε uniformly given the past;
* (H3) nested or bounded-overlap digit blocks.

These give T1–T3 and Theorem H. **For orbits, (H1)–(H3) are insufficient** (§12.5). The missing hypothesis is
arithmetic.

**Conjecture DN (diagonal short-range equidistribution; CONJECTURAL).** There are κ > 0 and R such that, for every
fixed union 𝔇 of ≤ R arcs, every K, and W → ∞:
#{i < W : ∃x₀ ∈ X_i with frac(2^{x₀−m}·3^{−B_i}) ∈ 𝔇} ≤ W·|X_i|·μ(𝔇)·(1 + o(1)) + O(log W),
where B_i = 2(i+1)K, X_i is the EOC state interval (|X_i| ≍ B_i), and m = m_j.

* DN with 𝔇 = 𝔇_K and δ_K|X_i| < 2/9 implies `PowerOfTwoDangerousWindowSparsityAt` for the u = 0 shell.
* A uniform-in-u version is **false**: adversarial ξ ≡ 2^{m′} realise rates 0.32–0.35 (previous round).
* DN is of Korobov type at length ≍ depth. It is open and beyond current exponential-sum technology.

## 14. Parts XXXVII, XXXVI — the common master object; pressure

**Master object.** A weighted automaton over the 3-adic digits of the phase:
* state = (carry or phase cell, path state); weights ≥ 0; runs = paths.
* 𝔓(β) := lim (1/n)·log₃E_Haar[(Σ_runs ∏w)^β].

Special cases:
* **Erdős / AL** (deterministic, one run, 0/1 weights): E[·] = N_D/3^D, so 𝔓 = log₃ρ(A) − 1 = dim − 1.
* **EOC annealed** (β = 1): 𝔓 = log₃ρ(L₁), the single-path phase operator.
* **EOC Jensen**: log₃ρ(L_β).
* **EOC quenched** (β > 1): a moment Lyapunov exponent of random nonnegative matrix products (replica / tensor-power
  operator).

**Is it new?** No. It is standard weighted-automaton and random-matrix-product theory (Furstenberg–Kesten; moment
Lyapunov exponents). Its *instances* here are new computations.

**Pressure.** For β = 1, and for Jensen-β, log ρ is literally the topological pressure of the skew product
(digit shift × path chain) with a potential that is **not** locally constant (it depends on the continuous phase).
The finite cell majorants are its locally-constant upper approximations.

For the quenched moments that govern the true danger rate, there is no single-system topological pressure; the
correct notion is the generalized Lyapunov exponent. EOC's word "pressure" matches thermodynamic formalism only
in the annealed case.

## 15. Part XLVI–XLVII — Lean strategy and downstream EOC tasks

* **No module created.** T1–T3 are elementary, but they need Haar measure on ℤ₃ and conditional expectation, and they
  do not feed the λ = 1 chain.
* Theorem H would need a verified-float or rational majorant certificate over 55 296 cells. That is possible in
  principle (`decide +kernel` is too large; better an external certificate checker), but it too gives only Haar
  information.
* The black-cylinder equivalence is already in Lean (`black_fiftyfourth_iff`).
* **Downstream EOC tasks:** |V_{σ,s}| binomial lower bound, high-frequency confined-shell sieve, `hweight`, N_u/hX
  parameters.
  * The phase-chain viewpoint gives a Haar large-deviation tool (Theorem H plus binomial domination), which might be
    reusable for `hweight`. That is a Haar-weight statement, so possibly relevant. **Not examined this round.**
  * No Erdős/Lagarias input helps the sieve tail or shell counting.
  * Leave all of them for the next EOC-only round.

---

## Required final report

### Literature
1. **Lagarias 2009 exact results:**
   * Thm 1.4: for every λ ≠ 0, #{n ≤ X : λ2ⁿ ∈ Σ} ≤ 2X^{log₃2}.
   * Thm 1.5: dim E^{(1)} = log₃2; ½log₃2 ≤ dim E^{(2)} ≤ ½; dim E^{(3)} ≥ (1/6)log₃2.
   * Thm 1.6: dim C(1, M) ≤ ½; dim C(1, 7) = log₃φ.
   * Thm 1.7 (constructive lower bound). Real-system Thms 1.1–1.3. Conjectures A, B, E.
2. **Abram–Lagarias 2014:**
   * Path-set automaton (Algorithm A/B), ≤ ∏(1 + ⌊M_i/2⌋) states, dim = log₃(Perron root).
   * L_k: dim → 0. N_k: dim = log₃φ.
   * dim E⋆ ≥ ½log₃2; dim E^{(2)} ≥ log₃φ; dim E^{(3)} ≥ 0.228392.
   * Table 5.2 has an erratum at 2⁸ (§11.1).
3. **Abram–Bolshakov–Lagarias 2017:**
   * P_k: 2^{k+1} states, nested SCCs, dim ≥ (1/13)log₃2.
   * Q_k: dim = log₃φ.
   * α_n = log₃φ for n ≥ 2; **dim E(ℤ₃) ≤ Γ ≤ log₃φ ≈ 0.438**.
4. **Erdős conjecture:** OPEN. Verified to n ≤ 2·3⁴⁵ (Saye 2022). No exponent improvement over Narkiewicz.
5. **Directly relevant theorems:**
   * Korobov / Bourgain / Vandehey short exponential sums: need N ≥ exp(Ck^{2/3}) or 3^{εk}.
   * Unique ergodicity of ×2 on ℤ₃^×.
   * Senge–Straus / Stewart (nonzero digits → ∞).
   * Shrinking-target and lacunary results are a.e. only.
   * **No result covers N ≍ depth.**

### Common dynamical object
6. **Phase:** ξ = λ·2^{−m}, m = σ + 1 + t, exact via reciprocity.
   * Relative phase θ_r = frac(2^{x_r}·(ξ mod 3^{b_r})/3^{b_r}), b_r = 2r + 2.
   * Chain θ_{r+1} = frac(2^{g}(θ + D)/9).
7. **Multipliers:** 2^{z}, with z = odd-position prefix sum ∈ (x_{2r}, x_{2r+2}], z ≤ collatzBarrier U (2r+1).
   Relative to the window, 2^{z−x₀}. Equivalently 2^{−a}, a = m − z.
8. **Black set:** B_b = 1/2 + {digits b−3..b−1 = 111} = {‖x/3^b‖ < 1/54}.
   * Measure 1/27; 3^{b−3} balls; one real arc; not a cylinder.
   * Dark (d = 1/108) ⊆ black, provided the reciprocity term λ2^{z−m}/3^b is < 1/108 (low λ, as in the 2026-09-16
     codimension round).
9. **Transient intersection:** T = ∩C_i with windows [p_i, q_i) and exactly uniform fresh digits. Theorems T1–T3 (§8).
10. **Relation to Cantor intersections:**
    * The same automaton class (carry states; AL Algorithm A with an additive constant).
    * Finite moving windows instead of all digits; 1-of-3 instead of 2-of-3; weighted and path-averaged instead of hard.
    * Full-depth Cantor intersections are dimension 0 for ≥ 3 multipliers and irrelevant to EOC.

### Automata
11. **Known Cantor automaton reproduced?** Yes: all tables in AL13 and ABL15, plus one erratum.
12. **Finite-cylinder automaton?** Yes (additive constant, windows). Carry collapse: ≤ 2^{Z+1} states.
13. **EOC constraint automaton?** Yes, in two forms:
    * the exact weighted automaton (state = top carry × path), exponential in K;
    * the K-independent continuous phase operator with finite cell majorants (P = 54·2^{Lc}).
14. **State counts:**
    * exact window automaton ≈ 2^{3.2K};
    * phase majorant 216 … 221 184 cells, K-independent;
    * C(1, 2^a) ≈ 2.43^{a/2} (494 324 at a = 30);
    * the exponent-digit representation needs ≥ 2·3^{⌊D/2⌋}.
15. **Adjacency matrices:** for C(1, 2⁸), the exact characteristic polynomial is in `CHARPOLY_256.txt`. Phase majorants
    are sparse operators (§9.2).
16. **Spectral radii:**
    * phase β = 1 → 1.0282;
    * β = 2: 1.12797 (verified, uniform q), 1.1223 (Lc = 12);
    * C(1, 2^a) → β ≈ 4/3.

### Codimension
17. **Current EOC c:** 0.1002 (β = 1), 0.1364 (β = 2), 0.1396 (best), all 2-state LP.
18. **Exact automaton c:** PROVED 0.14276 (β = 2, uniform in q). Single-path limit ≈ 0.148 (float).
19. **Empirical c:** ≈ 0.43 asymptotic (η = 1/54); ≈ 0.50 (η = 1/108).
20. **0.5 explained?** Yes, negatively for automata. It is a multi-path (quenched/replica) effect. Single-path phase
    information caps at ≈ 0.148; quenched Chernoff reaches ≈ 0.43.
21. **Constraint refresh:** 2 fresh digits per row. The fine phase is carried isometrically along the barrier drift
    log₂9. Persistence is 1 row. Coarse refresh has probability 1/9 per row.

### General theorem
22. **Statement:** T1(b) μ ≤ ∏3^{−f_i}; T1(c) μ ≤ (∏ε_i)^{1/M}; T2 weighted; T3 LP-boundary. Theorem H for EOC.
23. **Hypotheses:** constraints adapted to the digit filtration; exactly uniform fresh digits (unit multipliers);
    bounded overlap or boundary state.
24. **Proof status:** PROVED (MATH), elementary. Theorem H has an exact-integer certificate. Not in Lean.
25. **Counterexamples considered:**
    * the union over paths (fails);
    * moving balls and fixed polynomial-DFA sets containing 2ⁿ (orbit statements fail);
    * uniform-in-phase statements (adversarial ξ).
26. **Finite-depth consequence:** N_D ≤ 3^{D−Σf_i}. EOC: P(danger | past) ≤ 5.562·3^{−0.14276K}; binomial
    domination across windows.
27. **Dimension consequence:** dim_H E_EOC ≤ 1 − (c − log₃2/A)/9. Cantor intersections: dim ≤ 1 − Σf/D.

### Erdős side
28. **New Cantor-intersection theorem?** Only minor: carry collapse (state bound for powers-of-2 families).
29. **New dimension bound?** No rigorous one. The erratum dim C(1, 256) = 0.306871; the table extended to 2³⁰;
    CONJECTURE C1 (lim = log₃(4/3)) ⇒ Γ ≤ 0.2619.
30. **New fixed-λ count?** No. Lagarias's mechanism does not extend to moving or deep targets (§12.1).
31. **Relevance to the classical conjecture:** C1 would improve the best exceptional-set dimension bound (0.438 → 0.262,
    conditionally) and shows the ceiling of the single-multiplier route. Nothing toward finiteness.
32. **Genuinely advances the programme?** Marginally: an erratum, data, and a sharp conjecture with a stated
    consequence. No theorem.

### EOC side
33. **Effect on `PowerOfTwoDangerousWindowSparsityAt`:** none on its truth status. It is reformulated as a fixed-target,
    short-range ℤ[1/3]/ℤ equidistribution problem (DN), which is outside known results.
34. **Parameter regime proved:** none for λ = 1. The Haar-phase version is proved: measure ≤ e^{−W·KL}, E_EOC null.
35. **Effect on the 2/9 dangerous count:** none for λ = 1.
36. **Effect on the Haar exponent:** 0.1396 → 0.14276 (rigorous); A_min 4.52 → 4.42.
37. **Effect on the high-frequency sieve / `hweight`:** none shown. Phase-chain large deviations may be reusable for
    `hweight` (unexamined).
38. **Remaining arithmetic blocker:** short-range (length ≍ depth) distribution of 2^{x−m}/3^B along the EOC
    diagonal (Conjecture DN).

### Shared framework
39. **Master object:** weighted digit automata; 𝔓(β) = moment growth (§14).
40. **Weighted transfer operator:** L_β on the circle, with rigorous cell majorants.
41. **Pressure interpretation:** literal for β = 1 and Jensen-β. Quenched EOC danger is a moment Lyapunov exponent,
    not a pressure.
42. **Transient / weak / variable formulation:** T1–T3; phase chain (fine phase deterministic, coarse phase fresh);
    fixed target in phase coordinates.
43. **Standalone paper or repo?** Not yet. At most a short note: the erratum, the C(1, 4^m) → log₃(4/3) data and
    conjecture, and the EOC exceptional-set formulation. The framework itself is standard.

### Verdict
44. **Strongest theorem:** Theorem H, P_Haar(window mass > 2^{K/5} | past) ≤ 5.562·3^{−0.14276K}, uniform in q ∈ [0.367, 0.37].
    Together with binomial domination and dim_H E_EOC < 1.
45. **Strongest computational result:** dim_H C(1, 2^a) concentrates at log₃(4/3) (a ≤ 30; 0.261895 at a = 30), with the
    AL13 erratum. Also the quenched-vs-Jensen decomposition of the EOC exponent (0.101 / 0.148 / 0.43).
46. **Strongest structural insight:** the EOC moving targets are one fixed arc-union in phase coordinates. The Collatz
    barrier is the isometric direction of ×2^g/9. The EOC arithmetic frontier is a linear-length Korobov-type
    equidistribution problem, and its Haar exponent gap is a replica (path-averaging) effect, not automaton
    information.
47. **Strongest negative:**
    * No small automaton, matrix-product or discrete-log representation in exponent digits (Hankel rank ≈ √period).
    * Sparsity plus low complexity does not control orbit hits.
    * Lagarias counting controls only O(log j) rows.
48. **Did the Erdős route materially help EOC?** No. Level-B/C tools gave a modest Haar improvement and a clean
    reformulation, but no λ = 1 content.
49. **Did EOC machinery materially help an Erdős-type problem?** No theorem. The fresh-digit / independent-digit
    viewpoint predicted log₃(4/3), which the automata confirm numerically.
50. **Permanent second track?** **No, not as a co-equal track.** Keep a small, occasional Erdős-side thread: C1 is
    concrete and potentially publishable. The EOC blocker is not addressed by this literature.
51. **Exact next theorem:**
    * Erdős side: prove lim sup_m dim C(1, 4^m) ≤ log₃(4/3) + o(1). Weaker but useful: ≤ 0.43 < log₃φ for all large m.
    * EOC Haar side, if needed: a rigorous 2-replica phase operator, targeting c ≈ 0.198.
52. **Top three EOC tasks:**
    1. |V_{σ,s}| suffix-shell binomial lower bound.
    2. High-frequency confined-shell sieve exponent.
    3. `hweight`, testing whether Theorem H / phase-chain large deviations apply.
53. **Top three Erdős-side tasks:**
    1. A C implementation of dim C(1, 4^m) for m ≤ 20 (a ≤ 40) with exact β bounds.
    2. A proof attempt for C1 via equidistribution of the carry digit under the surviving-prefix measure
       (Host / Fourier-decay route).
    3. A census of pairs (a, b) ≤ 40 with dim C(1, 2^a, 2^b) > 0, and their characterization (digit identities like
       256 = 100111₃), since Γ = 0 needs ≥ 2 multipliers.
54. **LEVEL assessment:**
    * EOC direction (frontier): **LEVEL 1**. EOC Haar codimension: **LEVEL 2** (Theorem H; small gain).
    * Erdős direction: **LEVEL 1–2** (an erratum and a conjecture with a conditional improvement; no new rigorous bound).
    * Common framework: **LEVEL 2** (T1–T3, the phase chain, fixed-target reformulation; framework not new).

## Files

| file | content |
|---|---|
| `automata.py`, `validate_AL.py` → `VALIDATE_AL.txt` | generalized Algorithm A/B; reproduction of all AL13/ABL15 tables |
| `check_256.py` → `CHECK_256.txt`, `charpoly_256.py` → `CHARPOLY_256.txt` | erratum for C(1, 2⁸) (three methods) |
| `pow2_dims.py` → `POW2_DIMS.txt`, `random_M_dims.py` → `RANDOM_M_DIMS.txt` | dim C(1, 2^a), a ≤ 30; random-multiplier control |
| `collapse_and_eocfamily.py` → `COLLAPSE_EOCFAMILY.txt` | carry collapse; Cantor intersections along exponent sets |
| `black_cylinder.py` → `BLACK_CYLINDER.txt` | exact black-cell characterization |
| `identities_check.py` → `IDENTITIES.txt` | phase chain, reciprocity, fixed-target identity (exact) |
| `phaseop/phaseop.c`, `JENSEN_BETA.txt`, `JENSEN_L10.txt` | phase-majorant spectral radii |
| `phaseop/verify_exact.py`, `VERIFY_L8_b2.txt`, `VERIFY_L10_b2_uniform.txt`, `v_*.txt` | exact-integer super-eigenvector certificates |
| `mc/haarwin.c`, `run_mc.sh`, `out_*.txt`, `analyze_mc.py` → `MC_ANALYSIS.txt` | Haar-window Monte Carlo (6·10⁶ samples per K) |
| `hankel.py` → `HANKEL.txt` | Hankel ranks (exponent-digit representations) |
| `adversarial.py` → `ADVERSARIAL.txt` | sparse low-complexity targets hit by every 2ⁿ |
| `lit/*.pdf`, `lit/*.txt`, `lit/LIT_SEARCH.md` | primary sources; literature search (Part XXV) |

Reproduction: `gcc -O3 -o phaseop phaseop/phaseop.c -lm` (and likewise `mc/haarwin.c`), then run the scripts above
with `python3` (standard library only).
