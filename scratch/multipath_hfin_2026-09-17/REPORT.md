# Closing the explicit conditional inputs; multi-path pressure; log₃(4/3) (research round, 2026-09-17)

Nothing committed or pushed.
Labels: PROVED (LEAN) / PROVED (MATH) / EXTERNAL THEOREM / COMPUTATIONAL / HEURISTIC / CONJECTURAL / REFUTED / OPEN.

## 0. Headline

**Positive stop condition 1 fired, and most of 3–4 as well.**

**(a) The |V_{σ,s}| lower bound is PROVED (LEAN)** (`ShellCounts.choose_le_mul_card_shellV`):
C(t−1, L−1) ≤ L·|V_{σ,s}| for L ≤ t ≤ b_U(N) − σ. The shifted Collatz barrier satisfies the cycle-lemma chord condition
directly.

**(b) `hsplit`, `N_u`/`hX`, the |V| division and `hweight` no longer appear as abstract hypotheses.**
The new final theorem is **`FinalChain.exceptional_bound_of_frontier_and_scalar`** (PROVED (LEAN), standard axioms). It
assumes only:
* the arithmetic frontier Prop `PowerOfTwoDangerousWindowSparsityAt`, on the good pairs, at all frequency shells
  u ≤ σ + t;
* explicit numerical inequalities:
  * the existing region/rate conditions;
  * one per-pair binomial inequality `hnum`;
  * two scalar tail conditions `hρ` and `hscalar`.

**(c) The final theorem is not vacuous (COMPUTATIONAL certificate, `INSTANCE_CHECK.txt`).** Every numerical hypothesis
holds on one concrete instance:
* d = 1/108, N₀ = 133, U = 0, j₀ = 10¹², L = 17 363, x* = 39 429, K = b(j₀) + 1;
* the exponent gain over H₂(1/α) is 8.7·10⁻¹⁰.

**(d) The high-frequency sieve is no longer needed. Structural finding (PROVED (MATH)):** no sieve exponent θ ≤ 1 can
confine the frontier Prop to u ≲ t. The low-frequency range must reach U_s ≥ (2−H)t/θ > t. So the choice is
between:
* the frontier Prop on all shells (the chosen route: no sieve at all);
* a sieve with θ > 0 and frontier range U_s ≈ ((2−H)t + O(log j))/θ.

For the second option, a Cauchy–Schwarz sieve with θ = log₂α/α = 0.4186 is PROVED (MATH) (§4). It is not in Lean.

**(e) Multi-path pressure:** no rigorous improvement over c = 0.14276 (stop condition 5 not fired).
* Exact constraint-rank computations explain where the multi-path gain comes from.
* A naive pair operator has state size exponential in the replica offset (kill condition 4 for that construction).

**(f) Erdős side.** The literature search found no statement or conjecture of dim C(1, M) → log₃(4/3).
* Newly computed: dim C(1, 2³²) = 0.261839 (log₃(4/3) = 0.261860).
* Shmerkin–Wu do **not** apply (same contraction ratio).
* The AL13 C(1, 2⁸) erratum is confirmed independently, in the journal version too. It remains CONJECTURAL/COMPUTATIONAL.

## 1. Repository (Part I)

* Branch `research-sparse-visits-2026-09-16`; starting HEAD `14dea46ae5af816754cf3883475fa73dea598130`.
* Starting build: `lake build EOC` = 8806 jobs, success.
* Final build: **8809 jobs, success** (three new modules).
* New Lean files (untracked):
  * `EOC/ShellCounts.lean` (116 lines)
  * `EOC/BinomialTail.lean` (≈250 lines)
  * `EOC/FinalChain.lean` (≈480 lines)
* Modified: `EOC.lean` (3 imports added).
* Scratch: `scratch/multipath_hfin_2026-09-17/`.
* No commit, no push, no branch change.
* `#print axioms` gives exactly `[propext, Classical.choice, Quot.sound]` for:
  `choose_le_mul_card_shellV`, `card_shellV_le_choose`, `hsplit_of_allShells`, `pairInputs_of_explicit`,
  `hweight_of_badMass`, `badPairMassBound_of_binomialTail`, `exceptional_bound_of_powerOfTwoSparsity`,
  `exceptional_bound_of_frontier_and_tail`, `BinomialTail.deficit_tail_le`, `exceptional_bound_of_frontier_and_scalar`.
* No `sorry`, `native_decide`, or `axiom`.

## 2. Suffix shell V (Parts II–VIII)

**Definition (Lean, `PrefixCollision.shellV`).**
V_{σ,s} = shellV (collatzBarrier U) N j₀ σ t is the set of positive words v of length L = N − j₀ with total t = s − σ and
prefix sums S_i(v) ≤ b_U(j₀+i) − σ for 1 ≤ i ≤ L.

* It is the set of suffixes whose concatenation with a prefix of total σ is b_U-confined (`mem_split`).
* In `hfin` it appears only as the factor |V| on the right-hand side of `WeightedFourier`, and hence in `hsplit`.

**Combinatorial model (PROVED (MATH) + LEAN).**
* V is the set of compositions of t into L parts under a barrier.
* It sits inside all compositions: |V| ≤ C(t−1, L−1) (`card_shellV_le_choose`).
* The chord lemma `shift_chord`: L·p ≤ i·(b_U(N) − σ) ⇒ p ≤ b_U(j₀+i) − σ. Proof:
  p ≤ (i/L)(Nα + U − σ) = iα + (i/L)(j₀α + U − σ) ≤ (j₀+i)α + U − σ, using σ ≤ j₀α + U.
* The cycle lemma then gives C(t−1, L−1) ≤ L·|V| (`choose_le_mul_card_shellV`), with no loss of exponential rate.

**Exact counts (COMPUTATIONAL, `VRATIO.txt`, j₀ = 300, L ∈ {10, 20, 40, 80}, deficit x ∈ {0, 3, 10}).**
R = |V|/C(t−1, L−1) behaves as follows:
* bulk: R = 1.000–0.97;
* near the top: R ≈ 0.3–0.8;
* at the top shell t = t_max: R·L = 1.7–12, i.e. R = Θ(1/L) (a ballot effect).

The Lean factor 1/L is therefore the correct order at the top shell.

## 3. `hfin` / `hsplit` (Part IX)

**Theorem `FinalChain.hsplit_of_allShells` (PROVED (LEAN)).**
* Take U_s = σ + t (every frequency shell treated as low), so the high-shell sieve sum in `hsplit` is empty.
* Then `hsplit` follows from
  **hnum**: (1 + (σ+1)/2)(s+1)·4·4^t·L ≤ ε²·C(t−1, L−1)·2^{γ j₀}.
* **N_u ≡ 1** (`hX_one`): Xmax(1) = 2^{b_U(0)} = 2^U, so hX ⇔ U + 1 ≤ σ + 1 + t.
* The floor conditions 1 ≤ N_u < j₀ are trivial.

`ExplicitPairData` bundles the explicit per-pair conditions together with the frontier Prop at U_s = σ + t;
`pairInputs_of_explicit` turns it into `PairInputs`.

**Minimum sieve exponent (Part X; PROVED (MATH)).** If instead U_s < σ + t is wanted, the high part needs
Σ_{u>U_s} 2^{t−u}·sieve_u²/|P_σ|² ≤ ε²|V|/((σ+3)2^t).
* A per-frequency bound sieve_u²/|P_σ|² ≤ poly·2^{(1−θ)u} gives
  U_s ≥ ((2 − H_V)t + O(log j₀))/θ, where H_V = log₂|V|/t ≤ H₂(L/t) ≤ 1.
* So **any θ > 0 suffices, but U_s > t for every θ ≤ 1.**
  * θ = 0.705 (tilted-model value) gives U_s ≈ 1.5t.
  * θ_CS = 0.4186 (§4) gives U_s ≈ 2.5t.
* The frontier Prop is therefore needed beyond the reciprocity-small range u ≲ t − 7 regardless of sieve quality.
  The sieve only trades range (all shells versus ≈ 2.5t).

## 4. Confined-shell sieve (Parts X–XIII)

**Exact statement needed** (for the U_s < σ+t variant).
For 1 ≤ N_u < j₀, 2·Xmax(N_u) ≤ 2^{σ+1+t} and H = 2^u, `PsiShellBound.sieveBound` must satisfy
Σ_{u>U_s} min(1, 2^{t−u−1})·2·sieveBound(j₀, σ, N_u, 2^u)² ≤ (ε²/2)·|P_σ|²|V|/((1+(σ+1)/2)·2^t).

**Cauchy–Schwarz sieve (PROVED (MATH), not in Lean).** Write P_{N,S} for prefix shells of length N and V′_{N,S} for
suffix shells of length j₀ − N, and set M_N = Σ_S |V′_{N,S}|.
* sieveBound² ≤ (⌊Xmax(N)/3^N⌋ + 1)·(H + 2·3^N(1 + N ln 3))·M_N·|P_σ|. This uses Cauchy–Schwarz and the gluing
  identity Σ_S |P_{N,S}||V′_{N,S}| = |P_σ|.
* Xmax(N)/3^N ≤ N·2^U/3, because 2^{b_U(i)} ≤ 3^i·2^U.
* M_N ≤ C(σ−N, j₀−N) (hockey stick) and |P_σ| ≥ C(σ−1, j₀−1)/j₀ (cycle lemma).
* Therefore M_N/|P_σ| ≤ j₀·∏_{i<N}(j₀−i)/(σ−i) ≤ j₀·((j₀−1)/(σ−1))^{N−1} ≈ α^{−N}.
* With 3^N ≤ 2^u: sieve²/|P_σ|² ≤ poly(j₀)·2^u·2^{−θ_CS·u}, where **θ_CS = log₃2·log₂α = 0.4186**.

**Tilted versus confined (Parts XI–XII; PROVED (MATH)).**
* The uniform law on the composition shell {S_N = s} is exactly P*(· | S_N = s), for the tilted i.i.d. Geom(p) law
  (the weight p^N q^{s−N} is constant on the shell).
* Confined ⊆ shell with |confined| ≥ |shell|/N (cycle lemma), so P_conf(A) ≤ N·P*(A)/P*(S_N = s).
* With p = N/s, the entropy bound `EntropyBounds.pow_le_succ_mul_choose_mul_pow` gives P*(S_N = s) ≥ (N/s)/(s+1).
* Hence **P_conf(A) ≤ s(s+1)·P*(A)**: a polynomial Radon–Nikodym distortion.
* **Every exponential rate proved in the tilted model transfers to the confined shell.**
* The earlier "COMPUTATIONAL 0.64–0.80 on the confined shell" spread is a finite-size effect, not an exponential
  change (kill condition 2 not fired).
* The tilted θ_M = 0.705 would transfer. Its proof lives in the earlier tilted-model analysis and was not re-audited
  this round.
* ShapeTail (Part XIII) was not needed.

**Lean status.** The sieve is not formalized. It is also not needed by the final theorem, which uses U_s = σ + t.
OPEN (Lean) for the low-shell variant.

## 5. `hweight` (Parts XIV–XVI)

**Exact problem.**
`hweight`: Σ_{s ∈ [K, b_U(N)]} Σ_{σ<K} c(s,σ)·haarShare(s,σ) ≤ C·HaarMass, with
* haarShare = |P_σ||V_{σ,s}|·2^{K−s−1};
* HaarMass = Σ_{confined w, total ≥ K} 2^{K−total−1} = Σ haarShare (`haar_mass_eq`).

Take c = 1 + ε on good pairs and 2^{s+1−K} on bad pairs. A bad pair costs exactly |P_σ||V_{σ,s}| words.

**Reduction (PROVED (LEAN)).**
* `hweight_of_badMass`: `hweight` holds with C = 1 + ε + κ whenever badMass ≤ κ·HaarMass.
* `badPairMassBound_of_binomialTail`: that follows from
  N·Σ_{σ<K, σ+x*<b} C(σ−1, j₀−1)·C(B−σ, L) ≤ κ·C(B−1, N−1)·2^{K−B−1}.
  * Here b = b_U(j₀), B = b_U(N), and "good" means deficit x = b − σ ≤ x* with a nonempty suffix range.
  * Proof ingredients: shell upper bounds, a hockey-stick lemma `sum_range_choose_le`, and the cycle-lemma lower bound
    for the top Haar shell s = B.
* `BinomialTail.deficit_tail_le` (Vandermonde single term plus an exact ratio identity) reduces that to
  **hscalar**: N·∏_{y≤x*} f̄(y)/(1 − f̄(x*+1)) ≤ κ·2^{K−B−1}, with **hρ**: f̄(x*+1) < 1, where
  f̄(y) = (b−j₀)/(b−1)·(M₀+y)/(M₀+y−L) and M₀ = B − b + 1.

**Tail region and rate function (PROVED (MATH)).** The trivial branch is the region x > x*.
* Per unit deficit, the log-ratio is ln q₀ + ln((αL+y)/((α−1)L+y)), with q₀ = 1 − 1/α.
* The threshold solves I(c) := c·ln q₀ + ∫₀^c ln((α+u)/(α−1+u)) du = −α ln 2.
* Solution: **c* = x*/L = 2.2686** (q₀ = 0.36907); 2.2768 at q₀ = 0.37 (`RATE_CONSTANT.txt`).
* This matches the downstream COMPUTATIONAL estimate x* ≈ 2.1L.

**Lean status.** `hweight` is PROVED (LEAN) modulo the scalar inequalities hρ and hscalar. These are explicit in
(j₀, L, x*, U) and certified numerically for the instance in §7 (COMPUTATIONAL). A symbolic Lean proof for a parameter
family is OPEN.

The Fourier region needs no separate estimate: it is the good pairs, carried by `ExplicitPairData`.

## 6. Multi-path pressure (Parts XVII–XXIII; about 20% of the round)

**Definition.** Z(ξ) = val(x₀) = E*[∏_r 3^{B_r}] = Σ_P w(P)·∏_r 3^{B_r(P,ξ)}.
* Z^β = Σ_{P₁…P_β} ∏_i w(P_i)·∏_i ∏_r 3^{B_r(P_i,ξ)}.
* E_ξ Z^β = Σ_{tuples} ∏w·E_ξ[3^{Σ_i N(P_i)}].
* The joint black-cell set of a tuple is a Bohr-type set {T : ‖2^{z_c}·9^{K−1−r_c}·T‖ < 1/54 for all cells c}.

**Exact pair structure (PROVED (MATH)).**
* Both paths share the phase: θ₂ = frac(2^d·θ₁), with offset d = x′_r − x_r.
* Joint chain: θ′ = frac(2^g(θ+D)/9), d′ = d + g′ − g.
* Path 2's black test ‖2^{i′+d}θ‖ < 1/54 needs θ resolved to scale 2^{−d}.

**Minimal state and state count.**
* The naive state (θ-cell, d) needs about 54·2^{|d|} cells. Since d is a mean-zero walk, the state is
  2^{O(√K)} typically and 2^{O(K)} in the worst case. **Kill condition 4 fires for this construction.**
* The fresh-digit LP on (X₁, X₂, d mod 6) is rigorous but reduces to the full-correlation (Jensen) bound. The
  worst-case carry c ∈ ℤ/9 makes D₂ = 2^d·D + c coincide with D.
* No rigorous β = 2 or β = 3 bound beyond 0.14276 was obtained (**kill condition 5** for this round).

**Numerical c_β** (quenched Chernoff from the previous round's 6·10⁶-sample Monte Carlo, η = 1/54, slopes K = 12→24;
COMPUTATIONAL):

| β | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|
| c_β | 0.101 | 0.198 | 0.289 | 0.367* | 0.427* | 0.486* |

\* β ≥ 4 is dominated by rare samples.

* Increments: 0.097, 0.091, 0.078, 0.060, 0.059 (decreasing).
* The data are consistent with saturation at the true danger rate ≈ 0.43 (η = 1/54). A fit is not a theorem.

**Constraint rank (exact rational measure computations, `RANK_CELLS.txt`).** Rank = −log₃ μ(joint black set).
* One cell: rank 3.
* Same row, column gap δ: rank = 3 + δ·log₃2 **exactly** for δ ≤ 5 (the cells are nested), then ≈ 6 (independent).
* Consecutive rows: rank 5 for column step g ≤ 3 (one shared digit); 5.52 at g = 4; ≈ 6 beyond.
* Two paths over 3 rows with identical steps and offset d: added rank = d·log₃2 in total, **not per row** (0.63, 1.26,
  1.89, 3.16, 5.05 for d = 1, 2, 3, 5, 8).
  * Parallel replicas stay correlated.
  * Fresh rank accrues only when the offset changes or grows past about log₂54 ≈ 5.75.

**Interpretation (HEURISTIC).** The quenched gain comes from path tuples whose offsets wander: each change of relative
offset adds up to ≈ 3 fresh ternary constraints. A rigorous version needs a locality lemma:
* joint black-cell measures factor over clusters of cells with column gaps ≤ log₂(54·m) and row gaps ≤ 1;
* equivalently, bounded solutions of S-unit relations Σ k_c·2^{z_c}·9^{−r_c} = 0 with |k_c| ≲ 54.

That would give a fixed-β, finite-state operator. It is OPEN and is the exact next multi-path theorem. The target is
rank(P₁, …, P_β) ≥ Σ_i rank(P_i) − O(#coalescence epochs).

## 7. Conditional EOC theorem and quantitative payoff (Parts XXVIII–XXX)

**Strongest final theorem (PROVED (LEAN)):** `FinalChain.exceptional_bound_of_frontier_and_scalar`

#(E_U ∩ [0, 2^K)) ≤ ((1+ε+κ)·e^{λ*U}/2)·(2^K)^{1−I₀A}

It holds under:
* ExplicitPairData on every pair with deficit ≤ x* and L ≤ t ≤ B − σ. That is:
  * the existing region/rate inequalities;
  * j₀ < N, U ≤ σ;
  * hnum;
  * the frontier Prop;
* hL: L < B − b + 1;
* hρ and hscalar;
* A·K ≤ N and b_U(j₀) < K ≤ b_U(N).

**Instance certificate (COMPUTATIONAL, `instance_check.py` → `INSTANCE_CHECK.txt`).**
* Setting: d = 1/108, N₀ = 133, θ′ = 1/6 + 10⁻³, window constant A_win = 2, ca = cb = 0, U = 0, j₀ = 10¹².
* Parameters: γ = 7.872·10⁻⁸, γj₀ = 78 723; L = 17 363 (largest feasible, by binary search); x* = 39 429;
  K = b(j₀) + 1.
* **All numerical hypotheses hold.** The hnum margin is −4.31 bits at the worst pair.
* Arithmetic: exact integers and rationals; ⌊jα⌋ via 80-digit Decimal; three log/rpow inequalities in float log₂ form
  with margins ≥ 10⁻³. This is a certificate script, not a Lean proof.
* A = N/K = 0.630929764526, against 1/α = 0.630929753571. Exponent 1 − I₀A = 0.949955499, a **gain of 8.7·10⁻¹⁰**.

**Payoff per input.** Asymptotically ΔE = (I₀/α)·L/j₀ with L = γj₀/Q (PROVED (MATH) scaling).

| input | effect on Q | ΔE |
|---|---|---|
| hnum without the |V| entropy (C ≥ 1) | Q = 2(α + c*) = 7.72 | 0.0065γ |
| **with the |V| lower bound** | Q = 2T − T·H₂(1/T), T = α + c* = 3.862 → 4.537 | **0.0110γ** |
| hweight tail if x* → 0 (ideal) | Q = α(2 − H) = 1.664 | 0.030γ (upper limit) |
| sieve | none on the exponent (only moves the frontier shell range) | — |
| multi-path pressure | none on γ (affects only the plausibility/window size K of the arithmetic Prop) | — |

At d = 1/108 (γ ≤ 8.6·10⁻⁸): ΔE ≈ 9.5·10⁻¹⁰. **The dominant loss is still white contraction** (d²/N₀ ≈ 6.4·10⁻⁷ inside
γ), then the pressure rate 1/6 against the 0.19 budget. The |V| theorem improves the constant by a factor 1.7;
nothing else closed this round changes the rate.

**Remaining open inputs.**
* **Arithmetic:** `PowerOfTwoDangerousWindowSparsityAt` on the good pairs, at all frequency shells u ≤ σ + t (or
  u ≤ ≈2.5t with a formalized sieve).
* **Counting (explicit, scalar):** hρ and hscalar. They are symbolic only for the instance; a parametric Lean proof
  is OPEN (straightforward, ratio monotonicity).
* **Sieve:** not required by the final theorem. θ_CS = 0.4186 is PROVED (MATH), not Lean.

## 8. Erdős side (Parts XXIV–XXVII)

**Literature (`lit/LOG34_LIT.md`, agent search, confidence tags there).**
* No statement, conjecture or refutation of dim C(1, M) → log₃(4/3) was found, for generic M or for M = 4^m.
* **Pointwise ≤ log₃(4/3) is false**: C(1, 4) = 0.438, C(1, 2⁸) = 0.307.
* Shmerkin–Wu (Ann. Math. 2019) require multiplicatively independent bases or irrational contraction-log ratios.
  Both sets here are 1/3-homogeneous, so the theorems **do not apply** (real or 3-adic).
* log₃(4/3) = 2·log₃2 − 1 is the Marstrand a.e.-slice value.
* Additive translates: Hawkes gives a.e. dim C ∩ (C + t) = (1/3)log₃2 ≈ 0.210 < log₃(4/3). This was recalled from
  memory, not read. So the independence heuristic is not automatic even for "random" translates.
* Candidate rigorous framework: a Kenyon–Peres-style Lyapunov formula for Haar-random multipliers (not found in the
  literature).

**New computation.** dim C(1, 2³²) = 0.261839: 1 170 037 states, β = 1.333303 (`POW2_32.txt`). The sequence
a = 16…32 stays within [0.2597, 0.2630], and the last two values are 0.261895 and 0.261839.

**Heuristic, made precise (Part XXV).** Let N_D = #{x ∈ {0,1}^D : digits 0..D−1 of M·x lie in {0,1}}, with M ≡ 1 mod 3.
* Reading digit n, the output digit is (x_n + c_n) mod 3, where c_n = (carry + digit n of M·x_{<n}) mod 3 is determined
  by the prefix. Hence exactly: **N_{n+1} = N_n + Z_n**, Z_n = #{surviving prefixes with c_n = 0}.
* So dim C(1, M) = log₃(4/3) ⇔ Z_n/N_n → 1/3 in the exponential-average sense, i.e. the carry digit is equidistributed
  under the uniform measure on surviving prefixes.
* The counting "3^D·(2/3)·(2/3)… = (4/3)^D" is this statement with the digit restriction on x (2/3) and on M·x (2/3).
* **What must be proved (for M = 4^m, m → ∞):** asymptotic decorrelation between x ∈ Σ and 4^m·x ∈ Σ under the
  self-similar measure on the surviving set. That is equidistribution mod 3 of the digits of 4^m·x for x distributed by
  the (non-Bernoulli, Markov) measure on C(1, 4^m) prefixes.
* This is a ×4^m versus ×3 digit-independence statement of Host/Fourier-decay type, restricted to a sofic measure.
* No theorem was proved (kill condition 6 not fired: not already known).

**AL13 erratum confidence:**
* **Our own methods:** three independent ones agree on dim C(1, 256) = 0.306871: automaton spectral radius; exact degree-35
  characteristic polynomial (largest root 1.400924990); brute-force counts (N₄₀/N₃₀)^{1/10} = 1.40143.
* **Independent recheck:** the agent recomputed the same value and found that the journal version still prints 0.287416.
  It found no erratum, and no M ≡ 1 mod 3 below 800 reproduces 0.287416.
* **Other entries:** all other table entries match to 10⁻⁵.
* **Verdict:** high confidence this is an uncorrected table error. Not publicized; nobody contacted.

## Required final report

### Repository
1. **Branch:** `research-sparse-visits-2026-09-16`.
2. **Starting HEAD:** 14dea46ae5af816754cf3883475fa73dea598130.
3. **Build:** 8806 jobs at the start → 8809 jobs, success.
4. **Files changed:**
   * new: `EOC/ShellCounts.lean`, `EOC/BinomialTail.lean`, `EOC/FinalChain.lean`;
   * modified: `EOC.lean` (imports);
   * scratch: `scratch/multipath_hfin_2026-09-17/*`.
5. **Commit/push:** none; no branch change.

### Suffix shell V
6. **Definition:** positive words of length L = N − j₀ with total t, confined by b_U(j₀+i) − σ.
7. **Combinatorial model:** barrier-constrained compositions; the chord condition holds (cycle lemma applies).
8. **Exact counts tested:** j₀ = 300, L ≤ 80, x ∈ {0, 3, 10}, t across the range (`VRATIO.txt`).
9. **Asymptotic ratio:** R → 1 in the bulk; R = Θ(1/L) at the top shell.
10. **Lower-bound theorem:** C(t−1, L−1) ≤ L·|V| for L ≤ t ≤ b_U(N) − σ, σ ≤ b_U(j₀). Also the upper bound
    |V| ≤ C(t−1, L−1).
11. **Lean status:** PROVED (LEAN), and instantiated into `hsplit_of_allShells`.
12. **Axioms:** propext, Classical.choice, Quot.sound.

### hfin
13. **Explicit low-shell instantiation:** U_s = σ + t (all shells); high sum empty; `hsplit` ⇐ hnum (PROVED (LEAN)).
14. **N_u:** N_u ≡ 1.
15. **hX:** 2·2^U ≤ 2^{σ+1+t} ⇐ U ≤ σ (PROVED (LEAN), `hX_one`).
16. **Remaining high-shell theorem:** none for the final theorem. For the low-range variant: the Cauchy–Schwarz sieve
    with θ_CS = 0.4186 (PROVED (MATH)).
17. **Minimum sieve exponent:** any θ > 0, giving U_s ≈ ((2−H)t + O(log j))/θ > t for every θ ≤ 1. No exponent
    confines the frontier to u ≲ t.

### Confined sieve
18. **Tilted theorem:** θ_M = 0.705 (earlier round, tilted model).
19. **Conditioning relation:** P_conf(A) ≤ s(s+1)·P*(A) (PROVED (MATH)).
20. **ShapeTail-assisted transfer:** not needed; the polynomial change of measure suffices.
21. **Rigorous confined exponent:** θ_CS = 0.4186 directly (PROVED (MATH)). θ_M transfers with polynomial loss, but its
    tilted proof was not re-audited.
22. **Lean status:** not formalized; not needed by the final theorem.

### hweight
23. **Exact tail region:** prefix deficit x = b_U(j₀) − σ > x* ≈ 2.27·L. Pairs with empty V cost nothing.
24. **Rate function:** I(c) = c·ln q₀ + ∫₀^c ln((α+u)/(α−1+u)) du. The threshold solves I(c*) = −α ln 2, with
    c* = 2.2686.
25. **Trivial-branch theorem:** `badPairMassBound_of_binomialTail` + `deficit_tail_le` (PROVED (LEAN)) reduce to the
    scalar conditions hρ/hscalar. These are numerically certified for the instance.
26. **Remaining Fourier-region estimate:** none. The good pairs are handled by ExplicitPairData (hnum + frontier).
27. **Lean status:** `hweight` PROVED (LEAN) modulo explicit scalar inequalities. A symbolic scalar proof for a parameter
    family is OPEN.

### Multi-path pressure
28. **Z^β:** Σ over β-tuples of paths of ∏w·E_ξ[3^{ΣN}]; the joint black sets are Bohr sets
    {‖2^z·9^{K−1−r}·T‖ < 1/54}.
29. **Minimal state:** candidates are (phase cell, offset) or local cell clusters (gap ≤ ≈ log₂54). The needed locality
    lemma is OPEN.
30. **State count:** naive pair state ≈ 54·2^{|d|}, exponential in the offset (kill condition 4 for the naive state).
31. **β = 2 result:** no rigorous bound beyond Jensen. COMPUTATIONAL c₂ = 0.198.
32. **β = 3 result:** no rigorous bound. COMPUTATIONAL c₃ = 0.289.
33. **Best rigorous c_β:** 0.14276 (single-path, previous round).
34. **Comparison with 0.14276:** not beaten rigorously.
35. **Comparison with the empirical 0.43–0.50:** quenched c_β rises 0.10 → 0.43 by β = 5, consistent with saturation at
    the true rate.
36. **Constraint-rank interpretation:** exact ranks 3 + δ·log₃2 (same row), 5 (adjacent rows), parallel replicas add
    only d·log₃2 in total. The multi-path gain comes from offset changes.

### Erdős side
37. **Literature status of the log₃(4/3) limit:** not found; Shmerkin–Wu inapplicable; pointwise version false.
38. **Additional computed dimensions:** dim C(1, 2³²) = 0.261839.
39. **Asymptotic-independence heuristic:** N_{n+1} = N_n + Z_n exactly. The conjecture ⇔ equidistribution of the carry
    digit under the surviving-prefix measure.
40. **AL13 table discrepancy confidence:** high. Three methods plus an independent agent recomputation; the journal
    version is unchanged.
41. **Any theorem actually proved:** none on the Erdős side.

### Conditional EOC theorem
42. **Strongest final theorem:** `FinalChain.exceptional_bound_of_frontier_and_scalar` (PROVED (LEAN)).
43. **Remaining open inputs:** the frontier Prop on the good pairs; hρ/hscalar as a symbolic Lean proof (numerically
    certified on one instance).
44. **Arithmetic:** `PowerOfTwoDangerousWindowSparsityAt` only.
45. **Counting/sieve:** only the explicit scalar tail inequalities. The sieve is no longer an input.
46. **Final conditional exponent:** ≤ H₂(1/α) − 0.011γ. That is 0.949955499 at the instance (gain 8.7·10⁻¹⁰), and
    ≈ −9.5·10⁻¹⁰ asymptotically at d = 1/108.
47. **Dominant quantitative loss:** white contraction d²/N₀; then the pressure rate 1/6 against the 0.19 budget; then the
    tail cost x* (factor 2.7 against the ideal).

### Verdict
48. **Strongest new theorem:** `exceptional_bound_of_frontier_and_scalar`. The only non-numeric hypothesis is the
    arithmetic frontier Prop, with |V| from `choose_le_mul_card_shellV`.
49. **Strongest structural insight:**
    * no sieve can keep the frontier inside the reciprocity-small range (U_s > t for every θ ≤ 1), so dropping the sieve
      (all shells) costs nothing structurally;
    * the confined shell is a polynomially distorted tilted measure (P_conf ≤ s(s+1)·P*).
50. **Strongest negative:**
    * the naive multi-path state is exponential in the replica offset;
    * no rigorous β ≥ 2 gain was obtained;
    * the payoff of every closed input on the final exponent stays at ~10⁻⁹ (white contraction dominates).
51. **Are the non-arithmetic inputs nearly closed?** **Yes.** Only explicit scalar inequalities remain: certified
    numerically, with a symbolic Lean proof straightforward but not done.
52. **Does multi-path pressure materially improve the route?** Not yet, rigorously. Numerically it would allow K ≈ 2·log₂j
    windows (plausibility of the frontier), but it cannot improve γ.
53. **Should the Erdős thread remain active?** Only as a low-priority side thread: a concrete conjecture, not in the
    literature, with no proof route in hand.
54. **Exact next theorem:** a parametric Lean proof of hρ/hscalar. For example: for L ≥ L₀ and x* ≥ 2.3·L + C·log N,
    N·∏f̄/(1 − ρ) ≤ 2^{K−B−1}. This makes the final theorem hypothesis-free apart from the frontier and the rate
    parameters.
55. **Top three Lean tasks:**
    1. symbolic proof of hρ/hscalar for an explicit family;
    2. a parametric instantiation lemma packaging the rate/budget conditions (d, N₀, θ′) for all large even j₀;
    3. (optional) formalize the Cauchy–Schwarz sieve bound to allow U_s ≈ 2.5t.
56. **Top three mathematical tasks:**
    1. a locality/S-unit rank lemma for multi-path Bohr-set measures (a rigorous β = 2 operator);
    2. improve white contraction (d²/N₀), the dominant loss;
    3. reduce the tail constant c* (e.g. sharper Haar-mass lower bounds than the single top shell).
57. **EOC level:** **LEVEL 3**. The non-arithmetic chain is closed down to explicit scalar inequalities (Lean), which
    materially weakens the open-input list. The arithmetic frontier is untouched.
58. **Erdős-side level:** **LEVEL 1**. Computation, literature check, erratum confidence; no theorem.

## Files

| file | content |
|---|---|
| `EOC/ShellCounts.lean` | shift chord, suffix/prefix shell binomial sandwich |
| `EOC/BinomialTail.lean` | Vandermonde term, ratio identity, deficit tail |
| `EOC/FinalChain.lean` | hsplit (all shells), ExplicitPairData, hweight reduction, final theorems |
| `vratio.py` → `VRATIO.txt` | exact |V| vs binomial |
| `tail_params.py` → `TAIL_PARAMS.txt`, `RATE_CONSTANT.txt` | x*/L constant, ΔE scaling |
| `instance_check.py` → `INSTANCE_CHECK.txt` | numeric certificate for the final theorem |
| `rank_cells.py` → `RANK_CELLS.txt` | exact joint black-cell measures (constraint rank) |
| `pow2_32.py` → `POW2_32.txt`, `automata.py` | dim C(1, 2³²) |
| `lit/LOG34_LIT.md` | literature check (log₃(4/3), AL13 erratum) |
