# Odd-cell black count: upper large deviations (round of 2026-09-16, part 3)

Nothing committed or pushed.  New Lean: `EOC/OddBlack.lean` (imported in `EOC.lean`; `lake build` 8789 jobs, 0 errors,
axioms `propext, Classical.choice, Quot.sound`, no sorry).  Scripts/data (pure Python, exact big integers unless
stated): `odd_dp.py` → `ODD_{true,random}_J.txt`; `superblock.py` → `SUPERBLOCK.txt`; `adversary.py` + `depth_true.py`
→ `ADV_xi_*.txt`; `constants.py` → `CONSTANTS.txt`; `q_shape.py` → `Q_SHAPE.txt`; `rates.py` → `RATES.txt`;
`LAMBDA.txt` (fixed unit multipliers).

**Summary.**  (1) The odd-black upper LD for the true environment remains OPEN, but every numerical indicator is
positive: N_odd is Poisson-like with mean 0.025–0.036 R and exact tail rates above the Poisson benchmark at every J.
(2) PROVED (MATH): for a Haar-generic 3-adic environment ξ the odd-black pressure bound holds, hence
`CriticalWhiteCount` (λ = 1 form) holds with rate 0.026 bits/step for all ξ outside a set of Haar measure 2^{−cJ}.
(3) REFUTED route: no bound on triangle sizes (Ridout, or even R_max ≈ 3) controls N_odd — an explicit ξ with smaller
triangles than the truth has E N_odd = 0.127R.  (4) PROVED (LEAN): `ShapeTail + OddDarkPressure ⇒ CriticalWhiteCount
⇒ WeightedFourier` with an improved (mgf) reduction that only needs the exponential moment of N_odd.  No stop
condition fired for the true environment.

## 1. Definition and indexing (Parts I–II)
Odd cell of pair block r: (m − S_{2r+1}, 2r+2), m = σ+1+t (Lean `goodPair_of_white_step`, `gb_dp.py`, `wc_dp.py` agree).
Black at η = 1/54 ⟺ 54|y| < 3^b ⟺ **the three leading balanced-ternary digits (positions b−3, b−2, b−1) of
ξ2^{−a} mod 3^b vanish** (PROVED MATH; 27η = 1/2).  N_odd = #{r < R : odd cell black}.  Lean: `Ntao` (this count) and
`Nodd` (own odd choice eligible and phase-dark); `nodd_one_le_ntao`: Nodd ≤ Ntao at λ = 1, d = η/2.

## 2. Exact distribution (COMPUTATIONAL, exact big-integer DP over the confined law)
| J | E N_odd / R | Var/R | P(N ≥ 0.05R) | 0.06R | 0.075R | 0.10R (rate bits/step) |
|---|---|---|---|---|---|---|
| 100 | 0.0390 | 0.026 | 0.0173 | 0.0173 | 0.0352 | 0.0613 |
| 200 | 0.0250 | 0.021 | 0.0174 | 0.0258 | 0.0470 | 0.0739 |
| 400 | 0.0320 | 0.027 | 0.0084 | 0.0140 | 0.0248 | 0.0486 |
| 800 | 0.0301 | 0.030 | 0.0069 | 0.0119 | 0.0217 | 0.0441 |
| 1200 | 0.0361 | 0.034 | 0.0037 | 0.0075 | 0.0156 | 0.0347 |
Random unit ξ (J = 200…1200): means 0.049, 0.038, 0.032, 0.037; rates at 0.075R: 0.017, 0.018, 0.020, 0.013.
Fixed units λ ∈ {5, 7, 11, 13, 101, 1025} (environment λ2^{−a}): means 0.034–0.047 R, rates at 0.075R 0.013–0.022.
Fits (J ≥ 400) of the rate at q = 0.075: limit 0.013 (a + b/J) or 0.006 (a + b/√J); q = 0.10: 0.031 / 0.020.
The exact rate exceeds the Poisson benchmark μh(q/μ)/(2 ln 2) with the exact mean μ at every J; Var/mean ≈ 0.66–1.05 (true and random).
The decrease in J is explained by the environment-specific mean (0.025 → 0.036), not by a vanishing rate
(stop condition 4 not met).  Pressure (1/J)log₂E[s^N] at J = 1200: s = 2: 0.0250, 3: 0.0480, 6: 0.1113.

## 3. Predictable probabilities (Parts VII–XXIV)
Q_r(S) = Σ_d p q^{d−1} black(m−S−d, 2r+2) (P* kernel); β_r(S) exact bridge kernel.  Exact identity (PROVED MATH,
checked to all digits): E_conf Σβ_r = E_conf N_odd; E*Q_r(S_{2r}) = P*(B_r = 1).  E_conf ΣQ_r/R = 0.026–0.038.
Distribution over the path marginal: median 0, 90%: 0.004–0.016, 99%: 0.86–0.95, 99.9%: 0.98–0.998, sup = 1.000.
Occupation E#{r : Q_r ≥ q₀}/R (J = 1200): q₀ = 0.1: 0.063, 0.2: 0.054, 0.5: 0.036, 0.8: 0.018, 0.95: 0.005.
Predictor (J = 800): Q is determined by the leading black run k in the row (k = 0: 0.007; 1: 0.63; 2: 0.86; 3: 0.95;
≥5: 0.995), not by headroom (0.018–0.035 across bins) or position; black even cell ⇒ mean Q 0.23.
Triangle implication (PROVED MATH): Q_r(S) > 1 − p q^{k−1} ⇒ cells d = 1..k all black ⇒ one triangle of depth
≥ (k−1) ln 2; so Q ≥ 1 − ε forces size ≥ 0.695 ln(0.63/ε).  Ridout then gives Q ≤ 1 − e^{−o(J)}: useless for averages.
Strip: no endpoint spike in Q/β; endpoint blocks carry Σβ = 0.004 R (ε = 0.05) … 0.016 R (ε = 0.2).
Autocovariances of Q (bulk anchor sums, J = 1200): lag 1: +0.064, 2: +0.015, 5: +0.002, 10: +0.001 (scale 0.59);
memory ratio E[Q_{r+l} | odd cell r black]/E[Q_{r+l}] = 2.0, 1.56, 1.08, 1.12 at l = 1, 2, 5, 10 (short memory; noisy).
Tilted pressure of A_Q, A_β (state-only Feynman–Kac, exact): Chernoff rates for P(A_β ≥ q) at J = 1200: q = 0.05:
0.003, 0.06: 0.008, 0.075: 0.019, 0.10: 0.047 — the predictable occupation is not easier than N_odd itself.

## 4. Theorems (PROVED MATH unless marked)
* **Martingale split (Bennett).**  Under any law, with β_r the conditional black probability given F_{2r}:
  P(N ≥ qR, Σβ_r ≤ θR) ≤ exp(−R[q ln(q/θ) − q + θ]).  With `PredictableBlackBound θ` (Σβ ≤ θR w.h.p.) this gives
  the odd-black LD for q > θ; e.g. θ = 0.06, q = 0.10: 0.008 bits/step.
* **Block Chernoff.**  P*(C′, Σ_r Q_r ≥ θR) ≤ e^{−τθR} Π_blocks sup_S M_K(τ, S) (killed P* chain, Markov property);
  transfer P_conf(E) ≤ J·P*(E ∩ C′)/P*(S_J = sg) (cycle lemma).  Numerically (sampled anchors) the worst-state
  threshold q*_K at K = 64 grows with J: 0.046, 0.063, 0.070 (J = 200, 400, 800; random 0.067, 0.080), and the rate at
  θ = 0.075 falls 0.0126 → 0.0003: fixed-K superblocks fail; K ~ log J would be needed (HEURISTIC).
* **Improved reduction (PROVED LEAN, `criticalWhiteCount_of_shape_and_oddPressure`).**  Given the class, internal
  choices are independent uniform; in a bad block every eligible choice is dark and ≥ half the choices are eligible,
  so E[s^{own dark} | class] ≥ (1+s)/2.  Hence
  P(G_true < gR) ≤ P(G_sh < (g+β)R) + E_conf[s^{N_odd}]·((1+s)/2)^{−βR}.  With the J = 1200 true pressure:
  rate 0.037 bits/step at β = 0.17, s = 3 (N₀ = 4, g = 0.1; COMPUTATIONAL input); the weakest input actually needed is
  (1/J)log₂E_conf[3^{N_odd}] < 0.085 − rate (true value 0.048).  Original Hoeffding form needs P(N_odd ≥ 0.075R).
* **Generic environment.**  For ξ Haar on 3-adic units and ANY fixed path, each odd cell's three digits are fresh
  uniform given the lower digits of ξ; consecutive cells share one digit position.  Worst-case alignment gives
  E_ξ[s^{N_odd}] ≤ (3ρ(s)−2)·ρ(s)^R, ρ(s) = spectral radius of the 2-state max operator (`constants.py`;
  per step 0.0282, 0.0594, 0.168 bits at s = 2, 3, 6; Monte Carlo over ξ confirms).  Fubini + Markov: for all ξ outside
  Haar measure e^{−εR}, E_conf[s^{N_odd}] ≤ C e^{εR}ρ(s)^R; combined with ShapeLD and the reduction:
  **`CriticalWhiteCount` (Tao-cell form, N₀ = 4, g = 0.1) holds with rate 0.026 bits/step for all ξ outside a set of
  Haar measure 2^{−0.026J}**.  For a fixed unit λ the environment is λξ (also Haar), so the same holds per λ.

## 5. Obstruction to size-based proofs (REFUTED route, exact)
Every deterministic triangle lemma holds for every unit ξ.  Greedy digit-by-digit ξ (`adversary.py`, J = 400):
max depth of black support cells 3.18 (true ξ: 4.71 at J = 400, 6.72 at J = 1200) yet E N_odd = 0.127R and
P(N_odd ≥ 0.075R) ≈ 1 (exact); depth cap 8: 0.302R; uncapped: 0.98R.  So R_max (Ridout) or any triangle-size bound
cannot give the black count: the needed input is a **density** statement about the specific environment 2^{−m}λ.

## 6. Status
* PROVED (LEAN): finite Chernoff; interval lemma; class-product sum; #good ≥ #shape − #bad; class mgf lower bound;
  `ShapeTail + OddDarkPressure ⇒ CriticalWhiteCount ⇒ WeightedFourier`; λ = 1 dark ⇒ Tao-black.
* PROVED (MATH): shape LD (previous round); Bennett split; block Chernoff; generic-environment theorem.
* OPEN: `OddDarkPressure` / odd-black LD for the true environment 2^{−m}λ at low frequencies λ (even λ = 1).
* Best rigorous g, c, γ for the true environment: none, 0, 0.  A > 1/α not proved.  LEVEL 1.
* Remaining lemma: ∃ s > 1, P < β log₂((1+s)/2)/2 with β + g < p_g:  (1/J) log₂ E_conf[s^{N_odd}] ≤ P for the
  environment ξ = λ·2^{−m}, all low λ — equivalently: these specific ξ are not in the exponentially small exceptional
  set of the generic theorem.
