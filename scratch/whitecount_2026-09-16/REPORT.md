# Critical white count: Tao's mechanism at the critical slope (round of 2026-09-16)

Nothing committed or pushed (working tree on `main` @ `317c765` plus the files below).  New Lean:
`EOC/WhiteContraction.lean` (imported in `EOC.lean`; `lake build` 8788 jobs, 0 errors, standard axioms only, no sorry).
Scripts/data here (pure Python, exact big-integer arithmetic unless stated): `wc_dp.py` → `WC_FULL.txt`, `WC_LIGHT.txt`,
`WC_SHELL.txt`; `gb_dp.py` → `GB.txt`, `GB_ETA.txt`, `GAMMA_ETA.txt`; `block_worst.py` → `BLOCK_WORST.txt`;
`tri_paths.py` → `TRI_PATHS.txt`.  Tao's source read directly (`scratch/tao_2026-09-15/src/collatz.tex`, l.1150–1860).

**Verdict.**  The local analytic input is now PROVED (LEAN) with the *actual* pair-block factor: white-cell contraction,
exact phase identification with Tao cells, and the interface `CriticalWhiteCount ⇒ LowFreqDecay ⇒ WeightedFourier`.
Stop condition 6 fires for the Ridout route: Ridout removes Tao's linear-size Case-3 triangles but the architecture
yields at best a white count ≳ L/R_max (sublinear), and not even that without controlling hops at deep exits.
`CriticalWhiteCount` is OPEN; exact numerics show its lower tail is exponentially small with a rate close to the pure
digit large deviation (the environment costs ≈ 2.5% of the good-block mean).  Rigorous γ = 0; A > 1/α not proved.

## 1–3. Tao's white-count argument and what Ridout removes (read from source)
Dependency graph (Tao §7):
* **Cancellation for white points** (l.1164): pairs with b_j = a₁+a₂ = 3 have |f(x,3)| = cos(πθ) — a pair block with two
  choices — ⇒ `jeo-prop` (l.1188): E exp(−ε³·#{renewal points in W}) ≪ n^{−A}.
* **Structure of the black set** (`black`, l.1212): disjoint triangles, separation ≥ (1/10)log(1/ε) [deterministic].
* **Holding time** (`Exptail`, l.1399): renewal on pairs with b = 3; exponential tail; mean (4,16), i.e. slope 4.
* **First passage** (`stop`, l.1423): exit location concentrated at j ≈ s/4 ± √s.
* **Monotonicity induction** (`mono-prop`, l.1505) on Q_m with weight m^{−A}: Case 1 (white) gain e^{−ε³};
  Case 2 (s ≤ m/log²m) exit lands O(1) outside Δ, white w.p. ≫ 1 — uses (1/4)log 9 < log 2 (l.1593);
  Case 3 (s > m/log²m) needs P(exit time ≥ 0.8m) ≪ e^{−cm}, using s ≤ (log9/log2)m and **0.8 > (1/4)(log9/log2) = 0.792**
  (l.1633), then `77` (l.1702; again uses (1/4)log 9 < log 2) and `rip` (l.1660).
* **Exponential tails already present**: Hold, the first-passage law, and `rip` (exponential moment in the number of
  triangles crossed: #white ≳ ε·#triangles).  The polynomial loss is the m^{−A} induction, where each case extracts only
  O_{A,ε}(1) white points.
At the critical slope 2α = log9/log2 the Case-3 exit time is ≈ s/(2α), which reaches m for a linear-size triangle.
**What Ridout removes (formal):** R_max(L) = o(L) ⇒ for every ε there is m₀(ε) (ineffective) with s_Δ ≤ εm for all
triangles met at depth m ≥ m₀, hence P(exit time ≥ 0.8m) ≤ e^{−cm} at criticality (the first step of Case 3 is restored).
It does **not** restore `77`: its step "(j′, l_Δ) ∈ Δ" needs (1/slope)·log 9 < log 2 strictly; at criticality the landing
column is at the corner ± O(s^{0.6}) (OPEN).  And Tao's scheme only needs, and only yields, O(1) whites per case.

## 4–5. Strongest consequences of R_max = o(L) (PROVED MATH / PROVED LEAN)
* Deterministic (Lean `run_decomposition_54`, `occ_eq_zero_of_maxTriangleLE`): n ≤ (2H+1)W + H·N₆ + 2H,
  H = ⌊R_max/ln3⌋ + 1.  Every confined path has N₆ ≤ (sg − J)/5 ≈ 0.117J (digit budget, PROVED MATH), so
  W ≥ J(1 − 0.117H)/(2H+1) − 1: a deterministic positive white density whenever H ≤ 8, i.e. R_max < 8 ln 3 ≈ 8.79
  (true for J ≤ 6400: R_max(6400) = 8.17 from `ridout_2026-09-15/RMAX_J200-6400.txt`, giving only W ≥ 0.0037J − 1),
  vacuous asymptotically.
* With the tilted digit law (N₆ ≈ p₆J with LD, p₆ = 0.00685): positive density iff H·p₆ < 1 (R_max ≲ 160).
* Asymptotically nothing: even W_L → ∞ needs control of distinct-triangle hops at run ends; memorylessness of the digit
  law controls apex-row exits (P(hop) ≤ p₆) and shallow hypotenuse exits (P ≤ r^{6−d_exit}), but not deep hypotenuse
  exits (OPEN).  With that control one gets W ≳ L/R_max(L) with probability 1 − exp(−cL/R_max) — sublinear.
* Fourier consequences: W ≥ δL with exponential tail ⇒ |Γ|² ≤ κ^{δL}+… (γ > 0); W ≳ L/R_max ⇒ exp(−cL/R_max)
  (subexponential, no exponent gain); W → ∞ ⇒ o(1) only.

## 6–9. White-cell contraction, phase identification, interface — PROVED (LEAN), `EOC/WhiteContraction.lean`
* Pair-block factor (exact, `blockCubeHyp_pair`): W_λ(c,r) = ‖Σ_{x∈B} e(φ_{2r+1}(x))‖/|B|, B = admissible internal
  prefix sums; |B| = 1 gives W = 1 (no contraction is possible there).
* `wfac_le_of_pair`: x, x+1 ∈ B and distZ(φ(x) − φ(x+1)) ≥ d ⇒ W ≤ 1 − 2(1 − cos πd)/|B|;
  `pair_factor_le_of_good`: with |B| ≤ N₀, **W ≤ κ(d,N₀) = 1 − 2(1 − cos πd)/N₀ < 1** (`kappa_lt_one`).
  η = 1/54, d = η − ε: κ(·,2) = cos(π/54) = 0.998308, κ(·,4) = 0.999154.  (Tao's |f(x,3)| = cos πθ is |B| = 2.)
* Phase identification: `collatzPhase_sub_succ` (φ(x) − φ(x+1) ≡ λu_i2^x/2^m), `phase_reciprocity`
  (λu_i2^x/2^m + λy(m−x,i+1)/3^{i+1} − λ2^x/(2^m3^{i+1}) ∈ ℤ), `distZ_phase_ge`, `distZ_phase_ge_of_white`
  (λ = 1: a Tao-white cell (m−x, i+1) gives distZ ≥ η − 2^x/(2^m3^{i+1})), `goodPair_of_white_step` (a white odd step
  of a confined word with admissible next choice ⇒ good block of its class, d = η/2).  Negative (centered) frequencies:
  the phase of 2^m − λ is minus that of λ mod 1 (PROVED MATH; not in Lean).
* `CriticalWhiteCount b j0 σ t U N0 d k ρ` (class-weighted fraction of the confined shell with fewer than k good pair
  blocks is ≤ ρ, for every low frequency) ⇒ `lowFreqDecay_of_criticalWhiteCount` (κ^{2k} + ρ ≤ C2^{−γj0} ⇒ LowFreqDecay)
  ⇒ `weightedFourier_of_criticalWhiteCount`.  `sum_nCls_filter_eq_card`: the class-weighted mass is the number of words.
  Rate: with k = g·(j0/2), κ^{2k} = 2^{−g j0 log₂(1/κ)}, so **γ = min(g·log₂(1/κ), ρ-rate)**.

## 10–17. Renewal formulation, moments, dependence (PROVED MATH / COMPUTATIONAL / OPEN)
* Visits (maximal same-triangle runs) as renewal blocks: reward = residence, cost = the exit (white, or a hop with d ≥ 6).
  Positive white density with exponential tail follows if residences satisfy E[e^{τR_j} | past] ≤ C for some τ > 0 and
  exits are white with conditional probability ≥ c (Chernoff for conditionally sub-exponential sums; PROVED MATH sketch).
  A uniform mean E[R_j] ≤ C alone gives only a law of large numbers, not exponential concentration; δ ≈ 1/(C+1).
* Dependence: sizes are deterministic functions of the path position; the only randomness is the digits; the environment
  process Z_i = U(m − S_i, i+1) is a deterministic function of the Markov chain (i, S_i) (time-inhomogeneous: b grows).
  No finite-state compression: each step reveals a new 3-adic digit (kernel U′ = centered((2^dU + j_d)/3), j_d from the
  array); the black indicator is not Markov.
* One-step / k-step (exact, `WC_FULL.txt`): sup over states of P*(next black) = 0.98–1.000 (black and white states);
  sup P*(next k cells all black) ≥ 0.94 for k ≤ 5 at J ≥ 300, and the k at which it vanishes grows with J (7 at
  J = 150, 11 at J = 400).  **Uniform Doeblin (fixed k, ε) fails**; scale-dependent k(L) ~ R_max gives only exp(−cL/k) (HEURISTIC).
* Small-triangle frequency (`TRI_PATHS.txt`, 95% CIs): visits with size ≤ 3: 0.80–0.86; path time in triangles of size
  > 3: 0.007–0.011, > 6: ≤ 0.0016 (J = 1600); mean visit size 1.63–1.76, mean residence 1.36–1.40 (stable in J).

## 18–23. Path numerics (COMPUTATIONAL)
* Conditional sizes: weak dependence on entry digit (means 1.6–2.2, mildly increasing in d), previous size (1.1–2.2)
  and headroom in the bulk; low-headroom bins are small samples (n < 130).
* Autocorrelation of successive visit sizes, lags 1–10: |ρ| ≤ 0.14 for J = 200–800 (one outlier −0.47 at lag 9,
  J = 200, few pairs), ≤ 0.05 at J = 1600 (1/√n ≈ 0.024).
* E[e^{τR}] over visits (true env): τ = 0.25: 1.57–1.67; 0.5: 2.7–3.4; 0.75: 5.3–9.5; 0.9: 8–21 (growing in J);
  random env (one ξ): comparable at J = 1600 (1.73, 3.77, 10.7, 22.3), heavier at J = 400 (1.98, 5.95, 29, 89).
* White-count lower tail (exact): **P(W_J < δJ) = 0 for every δ ≤ 0.705**: the maximum black count over all
  confined paths is 0.21, 0.23, 0.28, 0.26, 0.27, 0.26, 0.30, 0.29 × J at J = 150, 200, 300, 400, 600, 800, 1200,
  1600 (shell law: 0.22, 0.27 at J = 100, 200).  Black-count upper tail P(N_B ≥ 0.1J) = 2^{−(0.04–0.08)J}.
* **Good-block count (the `CriticalWhiteCount` quantity, λ = 1, exact):** mean 0.285 R (N₀ = 2) / 0.525 R (N₀ = 4);
  P(#good < 0.1R) rate 0.098, 0.086, 0.081, 0.078 bits/step at J = 200, 400, 800, 1200 (N₀ = 2);
  0.346, 0.329, 0.322, 0.316 (N₀ = 4; shape-only 0.361, 0.346, 0.338, 0.335);
  shape-only control (every cell white) 0.103, 0.093, 0.087: the environment lowers the mean by ≈ 2.5% and the rate by
  ≈ 7%.  Minimum over all words = 0 (adversarial words exist).

## 24–29. Strip averages, correlations, variance, martingale (exact / PROVED MATH)
* μ_i = P_conf(B_i = 1): mean 0.032–0.049, bulk ≈ 2η; near the endpoint the conditioned path is nearly frozen and μ_i
  is the colour of one cell (up to 0.4–0.78).
* Σ_i Cov(B_i, B_{i+s}) over bulk anchors: positive at s = 1, 2 (same-triangle runs), ≈ 0 for s ≥ 5.
* **Var(N_B)/J = 0.034–0.056, stable in J = 60…1600 (linear variance)**; independent benchmark 0.024–0.034.
* Martingale: B_{i+1} − β_i is a bounded martingale difference, β_i = E[B_{i+1} | F_i] (P*: Σ_d P*(d)B(i+1, S_i+d));
  Freedman gives P(N_B ≥ Σβ + εL) ≤ e^{−cε²L}.  Predictable occupation: β_i > 1 − P*(d = k) forces the k cells
  (a−1..a−k, b+1) black, hence (same-row lemma) one triangle of size ≥ (k−1)log 2 adjacent (PROVED MATH).  So
  Σβ ≤ (1 − P*(k))L + (steps adjacent to triangles of size ≥ (k−1)log 2): the predictable bound reduces to occupation
  of large-triangle neighbourhoods (OPEN); numerically the path average of β is 0.033.  Ridout excludes only
  linear-length stretches near 1, not an average bound.
* Tilted law first: P_conf(E) ≤ P*(E)/P*(C_n), n^{3/2}P*(C_n) ∈ [0.43, 1.12] (endpoint ⌌nα⌋) — transfer valid for
  endpoints within O(√(n log n)) of nα; shell-only law gives the same statistics (`WC_SHELL.txt`).

## 30–36. Surrogate, true vs random, strongest formulation
* Coarse (headroom-bin, black, size-bin) chain: P(next black | white, bulk) = 0.023–0.029 (true) vs 0.028 (random);
  | black, size < 2: 0.03–0.13 vs 0.107; | black, size ≥ 2: 0.45–0.51 vs 0.50–0.54.  Nearly identical.
* Deterministic decomposition refuted (`BLOCK_WORST.txt`): over confined class paths, max(#bad − θ·#shape) grows
  linearly for every θ < 1 (maximizers have bad fraction 0.98–1.00), so no deterministic "white among good-shape blocks"
  bound exists; `CriticalWhiteCount` is a genuinely joint (digits × environment) large deviation.
* **`CriticalTaoWhiteCount` (cell form):** ∃δ, c > 0: P*(#{i ≤ L : |U(m − S_i, i+1)| ≥ η} < δL) ≤ e^{−cL} — numerically
  it holds deterministically with δ ≈ 0.7 for the tested J = 150–1600.  **Block form (what the chain needs; Lean `CriticalWhiteCount`):**
  ∃g, c > 0: P_conf(#{r : pair block r good at λ} < g·j0/2) ≤ 2^{−c j0} for all low frequencies λ.
* Lean: `lowFreqDecay_of_criticalWhiteCount`, `weightedFourier_of_criticalWhiteCount` PROVED (LEAN) with the actual
  pair factor and κ(d, N₀); the hypothesis itself is OPEN.

## 37–46. Payoff and status
* Best rigorous δ: none; best rigorous γ: 0; **A > 1/α not proved**; exceptional exponent H₂(1/α) ≈ 0.949956.
* Conditional payoff (`GAMMA_ETA.txt`, J = 400 exact rates, N₀ = 2, κ = cos πη): γ = 0.0006 (η = 1/54), 0.017 (1/8),
  0.025 (1/5, 1/4), **0.030 (η = 0.3)**; via the decay round's chain formula (HEURISTIC) E ≈ H₂ − 0.0301γ = 0.94906
  (model 1) or H₂ − 0.0916γ = 0.94723 (model 2), if `CriticalWhiteCount` held with these rates for all low λ.
* Strongest positive: the exact local contraction and phase identification in Lean, and the clean conditional chain;
  exponentially small good-block lower tails (rate ≈ 0.078/step, stable to J = 1200) with the environment behaving like
  a random unit; deterministic white density ≥ 0.70 on every confined path for the tested J = 150–1600.
* Strongest negative: Ridout + Tao's renewal architecture cannot give more than a sublinear white count at criticality
  (stop condition 6); `77` fails at critical slope; uniform Doeblin fails; the deterministic block decomposition fails.
* Exact remaining lemma: `CriticalWhiteCount` (block form above), i.e. a large-deviation lower bound for the number of
  good pair blocks under the confined law, uniformly over low frequencies.
* Next research: (1) a joint LD for (pair-shape, Tao-white) along confined paths — e.g. a transfer-operator bound on
  the pair (S mod 2^k, U at resolution η) with the lift digit treated as the only unknown; (2) repair `77` at critical
  slope (landing near the corner) to get a Tao-type critical white count ≳ L/R_max rigorously; (3) study the
  deterministic worst-case white density (≈ 0.70 up to J = 1600) as an arithmetic statement.
* Next Lean: (1) negative-frequency symmetry of `pairPhase` and the smallness side condition for all λ ∈ cshell;
  (2) a digit-shape large-deviation lemma (pair-sum statistics under the confined law, via P* and the confinement
  transfer); (3) Freedman/Azuma for bounded martingale differences to formalize the predictable-occupation route.
* LEVEL 1 (no A > 1/α), with the analytic interface reduced to a single probabilistic white-count hypothesis on the
  actual pair-block factor.
