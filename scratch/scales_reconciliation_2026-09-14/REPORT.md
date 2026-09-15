# Reconciliation: *Three Scales of Confinement* PDF vs the EOC repo (2026-09-14)

Source: `~/Downloads/ScalesConfinement (1).pdf`: 28 pp., "second revision", PDF CreationDate 2026-09-08. No LaTeX source or tracked copy exists anywhere locally. Nothing was committed or pushed, and no archive was modified.

Files in this directory (all untracked):

| File | Purpose |
|---|---|
| `ladder_identity_check.py` | Exhaustive check of the identities used in PDF Lemmas 8.10 and 8.12 |
| `renewal_dp.c` | Exact lattice DP for the renewal functions U and Û |
| `phase_prediction.py`, `phase_prediction_U0_{3e4,1e5}.out` | PDF phase formula vs the exact ρ data |
| `harmonic_check.out` | Numerical check of the U(β)=α identity |
| `survivor_bound.py`, `survivor_bound_U{0,2}.out` | Exact optimized seed bound |

Labels: PROVED (LEAN), PROVED (MATH), COMPUTATIONAL, EXTERNAL THEOREM, HEURISTIC, CONJECTURAL, STALE / SUPERSEDED, MISSING FROM CURRENT REPO.

Notation: α = log₂3, β = α−1, ρ = 1/α, s_N = ⌊αN+c⌋, φ_N = {αN+c} = {βN} (c an integer), g = h_conf = αH₂(ρ) = 1.505644, g′ = log₂(α/β) = 1.438033.

---

## 1. PDF theorem inventory and PDF-to-Lean mapping

Lean classes:
- **A** = already formalized exactly.
- **B** = formalized in a weaker form.
- **C** = formalized only as ingredients.
- **D** = not in Lean.

| PDF item | Statement | Proof dependencies | Lean |
|---|---|---|---|
| Prop 3.1 | ε_j = ⌊β(j+1)+c⌋ − ⌊βj+c⌋ ∈ {0,1}; this is a lower mechanical (Sturmian) word | Elementary; Morse–Hedlund for the Sturmian property | D |
| Prop 4.1 | W̃_c(N) = Σ_{s=N}^{s_N} C(s−1,N−1) = C(s_N,N) = (s_N/N)·C(s_N−1,N−1) | Hockey-stick identity | B. `terminalCount_eq_choose` is the first two equalities. The link from "S_N ≤ αN+c" to `terminalCount N s_N` is not stated. |
| Lemma 5.1 | Chord rotation, for real entries | Elementary (App. B) | A for ℕ-words (`chord_rotation_nat`, `chord_rotation_real`). The real-entry version is not needed. |
| Thm 5.2 | (1/N)·C(s−1,N−1) ≤ A_N(c,s) ≤ C(s−1,N−1) for c ≥ 0 | Rotation orbits of size ≤ N; chord ≤ barrier | C. Have: `chord_rotation_nat`, `ValuationShell.rotate`, `rotate_injective`, `valuationShell_card`. Missing: chord ≤ barrier, the orbit count, a Finset of confined words. |
| Prop 5.4 | Negative admissible c: A_N ≥ (ρ/2)^k/N · C | Elementary | D |
| Cor 6.1 | (1/N)·C(s_N−1,N−1) ≤ W_c(N) ≤ C(s_N,N) | Thm 5.2 and Prop 4.1 | C |
| Thm 6.2 | lim (1/N)·log₂ W_c = αH₂(ρ) | Cor 6.1 + Stirling (crude binomial-entropy bounds suffice) | D. Mathlib has `Stirling.lean` and `Real.binEntropy`. |
| Prop 6.3 | W_c ≤ W̃_c ≤ s_N·W_c | Cor 6.1 | C |
| Thm 7.1 | 2^{−I₀N−C√N} ≤ p_N(c) ≤ e^{a*c}·2^{−I₀N} | Upper: Chernoff. Lower: Donsker (App. D). | B. The upper bound is exactly `geometric_persistence_upper_bound_bits` (same e^{λ*c}, same I₀ formula). I₀ is the Cramér rate by `I0_eq_geom2_cramer_rate`. The lower bound is D. |
| Lemmas 8.1–8.2 | Stars-and-bars path encoding; R_j ≤ c ⇔ D ≤ b = c+β; endpoint gap b − e′ = φ_N + x | Elementary | C. `valuationShellEquivCuts` is a different form of the bijection. |
| Prop 8.3 | D never equals b = c+β, so U(b⁻) = U(b) | Irrationality of β | D. There is no irrationality lemma for log₂3 in EOC/. |
| Lemma 8.6 | U(H), Û(H) < ∞ | Ladder process + Chernoff | D |
| Lemma 8.8 | Binomial local limit theorem (LLT) and sup_k P(K_i = k) ≤ C·min(1, i^{−1/2}) | EXTERNAL: de Moivre–Laplace | D |
| **Lemma 8.9** | P(D_t ≤ b ∀t ≤ m, D_m = y) ≤ C(1+b)(1+b−y)·m^{−3/2} | (I1) LLT, (I2) Feller one-sided survival, (I4) duality, (I5) oscillation, Wald | D |
| Lemma 8.10 | One-sided local ballot: n·P(D>0, D_n = x) = P(D_n = x)·[U(x⁻)+o(1)] | Adds (I3) Alili–Doney, via Caravenna | D |
| Lemma 8.11 | Tie-freeness | Irrationality | D |
| Lemma 8.12 | Exact decomposition at the unique extremal time | Elementary, given 8.11 | D |
| Lemma 8.13 | (i) A + B = U(b⁻)·Û(z⁻) − Δ; (ii) asymptotics | (i) algebra; (ii) Lemmas 8.8–8.10 | D |
| Lemma 8.14 | Diagonal term Δ → 0 | Unique M − Nβ representation; tails of convergent series | D |
| **Thm 8.7** | Two-sided bounded-endpoint local ballot: n·P(D ≤ b, K_n = k) = P(K_n = k)·[U(b⁻)·Û((b−y_k)⁻) + o(1)] | Lemmas 8.8–8.14 | D |
| Props 8.15–8.18 | S₊ = {1−{nβ}}, S₋ = {{nβ} ≤ β}; J₊ = {m−nβ > 0}, J₋ = {nβ−m > 0}; both dense; pure-jump | Elementary + Weyl | D. Mathlib has density of AddSubgroup.closure{a,b} for an irrational ratio. |
| Thm 8.20 | A_N(c, s_N−x) = (1/N)·C(s_N−x−1,N−1)·[ρU(c+β)Û((φ_N+x)⁻) + o(1)] | Thm 8.7 | D |
| Lemma 8.21 | F_N(c,x) ≤ C(1+x) for x ≤ C₀ log N | Lemma 8.9 + LLT | D |
| **Thm 8.22** | N^{3/2}·2^{−gN}·W_c(N) / C_term − F_c(φ_N) → 0 | Thm 8.20, Lemma 8.21, App. F, Stirling | D |
| **Thm 8.23** | The same for p_N(c) with G_c, for a < 2 | As Thm 8.22, with ratio 2β/α | D |
| Remark 8.25 | Catalan calibration | Elementary | — |
| Obs 8.26 | U(β) = α (numerical only in the PDF) | — | D. **PROVED (MATH) this round**, see §5. |
| Prop 9.1 / Cor 10.1 / App. G | h_lift = ρ·h_conf; H(P*) = h_conf; D(P*‖P_{1/2}) = I₀ | Algebra | C. `I0`, `lambdaStar` and the Cramér identity exist; entropy and KL of Q_a do not. |
| App. E | General slope a | Same | C. `PaperConfined a c`, the chord and `terminalCount` are slope-general. |
| App. F | Shell ratio → (β/a)^x | Elementary | D |
| App. H | Numerics | — | Reproduced independently this round (§10). |
| App. I | Phase → realizer question; Conj. I.1 | — | CONJECTURAL / open; not addressed. |
| App. J | γ = ½ + 1 + 0 | Bookkeeping | — |

In short, Lean contains the exponential layer only: Chernoff with I₀, the Cramér identity, the hockey-stick count and rotation existence. The polynomial layer (§8), the phase and the Beatty structure are all MISSING FROM CURRENT REPO, both in Lean and in `docs/`.

## 2. Status of N^{−3/2} (Part III)

**The proof is complete and internally coherent.** I checked every step of Lemmas 8.9, 8.10 and 8.12–8.14 and Thms 8.7, 8.20–8.23 by hand. The only defect found is cosmetic: in Lemma 8.9 Step 1, "τ_R⁺" should be the descending passage time.

**Exhaustive check of three identities** (`ladder_identity_check.py`, all 2ⁿ paths for n ≤ 16): 0 failures in 383 cases.
- The Alili–Doney identity (I3), in exactly the form used.
- The Lemma 8.10 Step-2 identity.
- The Lemma 8.12 decomposition.

**Citation dependence of the Θ statement.**
- The upper bound needs only Lemma 8.9. Its inputs are (I1) de Moivre–Laplace, (I2) P(τ⁺ > n) ≤ C·n^{−1/2}, (I5) oscillation and Wald's identity, all EXTERNAL THEOREMs from textbooks, plus duality (elementary).
- The lower bound is elementary (Cor 6.1).
- The Θ statement does not use Alili–Doney. Only the sharp constant does.

**Statuses:**

| Claim | Status |
|---|---|
| \|W_c(N)\| = Θ_c(N^{−3/2}·2^{(α−I₀)N}) | **PROVED (MATH)**, paper-level. The lower bound is elementary, with Lean ingredients. The upper bound is MISSING FROM CURRENT REPO. |
| p_N(c) = Θ_c(N^{−3/2}·2^{−I₀N}) | **PROVED (MATH)**, via Thm 8.23; α < 2 holds. |
| Sharp limits with the explicit phase (Thms 8.20, 8.22, 8.23) | **PROVED (MATH)** modulo (I3), which is cited through Caravenna only. (I3) is COMPUTATIONALLY confirmed for this walk up to n = 16. |
| My earlier "status C" this morning, and the Sept 12–13 CONJ/COMP labels | **STALE / SUPERSEDED.** These were `EOC_repository_audit_2026-09-12` §8(b), `PAUSE_CHECKPOINT` §6–7 and `SNAPSHOT_…09-13` §5. None of them cites the Sept 8 PDF. |

## 3. Exact phase formula (Part IV)

**Word count:**

W_c(N) = N^{−3/2}·2^{gN}·[K_c(φ_N) + o(1)], where

- K_c(φ) = C_term(c,φ)·F_c(φ)
- C_term(c,φ) = 2^{(c+β−φ)g′ − g}·(2πβ/α)^{−1/2}
- F_c(φ) = ρ·U(c+β)·Σ_{x≥0} (β/α)^x·Û((φ+x)⁻)

**Survival probability:**

p_N(c) = N^{−3/2}·2^{−I₀N}·[2^{φ_N−c}·C_term·G_c(φ_N) + o(1)], where G_c(φ) = ρ·U(c+β)·Σ_{x≥0} (2β/α)^x·Û((φ+x)⁻).

**Shells:**

A_N(c, s_N−x) = N^{−1}·C(s_N−x−1, N−1)·[ρU(c+β)Û((φ_N+x)⁻) + o(1)].

**Dependence on c and φ.**
- The coefficient factorizes exactly: K_c(φ) = κ(c)·Ψ(φ), with κ(c) = 2^{c·g′}·U(c+β), and Ψ(φ) = ρ·2^{(β−φ)g′−g}·(2πβ/α)^{−1/2}·Σ_{x≥0} (β/α)^x·Û((φ+x)⁻).
- So c enters only through κ(c).
- φ enters through the continuous factor 2^{−g′φ} and the pure-jump sum.

**Shape of the phase function.**
- It is not periodic in N: φ_N = {βN} is equidistributed and never repeats.
- On the circle, F_c is nondecreasing, left-continuous and pure-jump (Û is purely atomic).
- F_c jumps exactly at the rotation orbit {{nβ} : n ≥ 1}, which is dense. The first few points are 0.5850, 0.1699, 0.7549, 0.3399, 0.9248, 0.5098, 0.0947, 0.6797, …
- The jump at {nβ} is ρU(c+β)·Σ_x (β/α)^x·u_Û{{nβ}+x}, which is of order n^{−3/2}. The largest is at {β}, where Û's atom is exactly 1/α.
- Since Û(0⁻) = 0, F_c(0) = (β/α)·F_c(1⁻). Combined with C_term(0)/C_term(1⁻) = α/β, this gives K_c(0) = K_c(1⁻). So **K_c is continuous across the wrap point** (PROVED (MATH), this round, from the PDF formula).
- K_c is therefore an exponential factor 2^{−g′φ} times an increasing dense-jump function, whose total increase over one turn is exactly the factor α/β.

**Left/right limits.**
- The PDF uses Û(·⁻). The evaluation point φ_N + x is itself always a point of J₋ (east-index N), but that atom has mass O(N^{−3/2}), so the convention matters only inside the o(1).
- U(b) = U(b⁻) by Prop 8.3.
- Along subsequences φ_{N_j} → φ* ∈ {nβ}, the limit depends on the side of approach (Remark 8.24).

**Bounds.** ρU(c+β) ≤ F_c ≤ C·U(c+β), and C_term is bounded above and below, so K_c is bounded away from 0 and ∞.

## 4. Role of the renewal functions

- **U** is the strict ascending ladder-height renewal function of the auxiliary walk D (step +1 with probability β/α, step −β with probability 1/α).
  - Evaluated at b = c+β, it measures the start-side distance to the barrier.
  - It is the only c-dependence of the phase.
  - Values (DP): U(β) = α, U(1+β) = 3.13364, U(2+β) = 4.68675, U(3+β) = 6.24534; slope ≈ 1/E[H⁺] ≈ 1.556.
- **Û** is the descending renewal function, evaluated at the endpoint gaps φ_N + x. It carries all of the φ-dependence.
- By duality, the atoms are exact path counts: u_U{h} = P(D₁..D_t > 0, D_t = h), and the value h determines t. So U and Û can be computed exactly by monotone lattice DP; `renewal_dp.c` is exact up to its cutoff, with Richardson extrapolation in U₀^{−1/2}.
- **Obs 8.26 is now proved** (PROVED (MATH) modulo Blackwell's renewal theorem, an EXTERNAL THEOREM):
  - Decomposing on the last step gives U(x) = 1 + (β/α)·U(x−1) + (1/α)·[U(x+β) − U(β)] for x ≥ 0. This is exact.
  - Blackwell applies because H⁺ is non-arithmetic: its support contains 1 and 2−α. It gives U(x+h) − U(x) → h/E[H⁺].
  - Therefore U(β)/α − 1 = lim[(β/α)(U(x−1) − U(x)) + (1/α)(U(x+β) − U(x))] = 0, so **U(β) = α**, and then U(2β) = α².
  - Numerically the identity holds to ≤ 3·10⁻⁶, with U(β) = 1.5849624.

## 5. Beatty jump-set structure

The precise content is Props 8.15–8.16:
- First-ladder supports: S₊ = {1 − {nβ} : n ≥ 0}, S₋ = {{nβ} : n ≥ 1, {nβ} ≤ β}. The atom 1 − {nβ} equals ⌊nβ⌋ + 1 − nβ, so it is indexed by the Beatty sequence ⌊nβ⌋.
- Jump sets: J₊ = {m − nβ > 0 : m ≥ 1, n ≥ 0} and J₋ = {nβ − m > 0 : n ≥ 1, m ≥ 0}. These are positive cones of ℤ + βℤ, countable and dense.

The abstract's phrase "the jump sets are exactly the Beatty sequences of β" is loose wording for this. For F_c, the relevant jump locations are the rotation orbit {nβ}.

## 6. Two irrational structures (Part V)

| | Sturmian capacity clock (§3) | Renewal-phase structure (§8.4) |
|---|---|---|
| Object | ε_j = ⌊β(j+1)+c⌋ − ⌊βj+c⌋, the barrier K_j(c) on X_j = S_j − j | Ladder heights of the auxiliary walk; renewal functions U, Û |
| Scale | Step-by-step shape of the barrier; its terminal state is φ_N | O(1) coefficient |
| Mechanism | Irrational rotation (mechanical word) | First-passage / fluctuation theory; atoms nβ − m |
| Affects entropy? | No | No |
| Affects the N^{−3/2}? | No | No |
| Affects the O(1) term? | Only by choosing where the phase is evaluated (φ_N), plus the smooth Stirling factor 2^{−g′φ} | Yes: it determines which function F_c is |

In the auxiliary walk the staircase barrier becomes the constant barrier b = c+β. The clock's interior pattern is absorbed completely; only its endpoint φ_N survives.

## 7. Recent scratch results vs the PDF (Part VI)

| Recent item | Verdict |
|---|---|
| Tilted law P* = Q_α, mean zero under the tilt | Rediscovery (PDF App. D, §8.2). Already in Lean since Sep 4 (`lambdaStar`). |
| h_conf, KL rate I₀ | Rediscovery (Thms 6.2, 7.1, Cor 10.1) |
| N^{−3/2} for words and for mass (slopes −1.495 / −1.46) | Rediscovery. The phase-matched fits are stronger numerical confirmation of Thms 8.22–8.23. |
| My "three-piece" upper-bound argument and the "tilt makes the barrier constant" remark | Rediscovery of Lemma 8.9 and Lemma 8.1 |
| Phase-dependent limits of ρ_tot | Rediscovery; now matched quantitatively (§10) |
| Survivor mass vs count, and the slower mass convergence | Rediscovery (Thm 8.23; ratio 2β/α = 0.738) |
| U(β) = α | New proof of a PDF observation (§4) |
| Record stopping times M₀(X) through 2⁴⁰; survivors ≈ (X/2)p_N beyond the fresh-bit regime | New application (extreme-value theory under an independence HEURISTIC). The realizer-level data are genuinely new. |
| Orbit clustering (471 long survivors → 152 orbit-merge clusters; prefix clustering) | Genuinely new |

## 8. What is genuinely new after the PDF (Part VII)

| Topic | PDF | Current repo | New contribution |
|---|---|---|---|
| Entropy, capacity sandwich | Proved | Lean ingredients only | none |
| N^{−3/2} (words and mass) | Proved | Chernoff exponent only (Lean); scratch numerics | none (confirmation only) |
| Renewal phase, Beatty jumps | Proved | absent | proof of Obs 8.26; independent numerics |
| Exact realizer cylinders | Mentioned as non-claims | Lean: `Realizer`, `RealizerLift` | beyond the PDF |
| PairValuation: v₂(r(E)−r(D)) = S_k + min(a,b) | — | PROVED (LEAN) | new |
| SuffixTransport, TransportCollapse, PrescribedMatching | — | PROVED (LEAN) | new |
| LogCorridor, UpperEscape, UpperCertificates; divergence ⇔ log-wall anchor | — | PROVED (LEAN); the García–Tal/Curry step enters only as an explicit hypothesis | new (orbit classification) |
| SurvivorCounting: exact fresh-bit count; seeds ≤ (X/2)p_N + W | — (PDF: ensemble only) | PROVED (LEAN) | new; the only bridge from ensemble to seeds |
| Records to 2⁴⁰, clustering, survivor ratios beyond fresh-bit | — | COMPUTATIONAL | new |
| Phase → realizer question | App. I.3, Conj. I.1 (test problem) | not addressed | open |

## 9. Formalization evaluation of the local ballot theorem (Part VIII)

| Component | Assessment |
|---|---|
| Binomial LLT and concentration bound | Likely reusable from Mathlib (Stirling), but the uniform local theorem is new work (moderate) |
| One-sided survival O(N^{−1/2}) (I2) | Requires a new probability framework (Sparre Andersen / Wiener–Hopf). No simple finite inequality found. **This is the real obstacle.** |
| Duality | Cheap in finite path-counting form (reversal bijection) |
| Ladder epochs/heights, renewal finiteness (Lemma 8.6) | Requires an infinite-horizon process framework (heavy) |
| Alili–Doney (I3) | A finite path-count identity (checked to n=16). Provable by a cyclic-shift argument; moderate–heavy. |
| Extremal-time decomposition (8.12), tie-freeness | Moderate (finite, needs log₂3 irrational) |
| Recombination 8.13(i) | Cheap (series algebra) |
| 8.13(ii), diagonal vanishing, the final asymptotic | Heavy (uniform limits over countable sums) |

**Verdict:** Tier 3. Not feasible as a current Lean priority.

## 10. Phase numerics vs the PDF (Part XI)

**Yes: the different limiting constants in the scratch audit are exactly the PDF's renewal-phase values.** No parameters were fitted.

Predictions: ρ_tot = N|W|/C(s_N, N) → ρ·F_c(φ_N), and ρ_shell → ρ·U(c+β)·Û(φ_N⁻).

At N ≈ 4000, over all 12 (c, window) cells:

| c | φ = 0.2094 obs / pred | φ = 0.4545 obs / pred | φ = 0.7192 obs / pred |
|---|---|---|---|
| 0 | 2.4688 / 2.4695 | 2.7593 / 2.7603 | 3.4640 / 3.4653 |
| 3 | 9.7141 / 9.7311 | 10.8551 / 10.8771 | 13.6245 / 13.6550 |

- The relative error is −2.8·10⁻⁴ (c=0) to −2.2·10⁻³ (c=3). It halves with each doubling of N, i.e. O(1/N), as the PDF's App. H observed.
- The predictions agree between the DP cutoffs U₀ = 3·10⁴ and 10⁵ to within 10⁻⁵.
- The ratio ρ_tot(c)/ρ_tot(0) is the same in all three windows: data 1.976, 2.954, 3.934, against predicted U(c+β)/α = 1.97712, 2.95706, 3.94051. This confirms the factorization κ(c)·Ψ(φ).
- The "noisy" middle window is the renewal jump at {6β} = 0.50978: N = 2001 has φ = 0.5100 and sits just above it.

## 11. Formalize vs keep paper-level

**Lean now (Tier 1):**
- Capacity sandwich (Thm 5.2, Cor 6.1, Prop 6.3). Use the summed form C(s_N,N) ≤ N·|W_c(N)| ≤ N·C(s_N,N).
- The seed-density theorem (see §13).
- Entropy limit (Thm 6.2) via 2^{nH}/(n+1) ≤ C(n,k) ≤ 2^{nH}.
- Irrationality of log₂3, with tie-freeness and barrier non-hitting (Lemma 8.11, Prop 8.3).
- The mechanical-clock lemma (Prop 3.1) and the encoding (Lemmas 8.1–8.2).

**Tier 2 (later):**
- KL and entropy identities for Q_a (Cor 10.1).
- The shell-weight identities p_N = Σ_x A_N(c,s_N−x)·2^{−(s_N−x)}, and App. F.

**Paper-level (Tier 3):** Lemma 8.9 and everything after it (local ballot theorem, renewal phase, Beatty jumps, Thms 8.20–8.23). The Θ upper bound has no cheap finite route.

## 12. Citation and provenance issues (Part X)

1. **(I3) Alili–Doney** is secondary (via Caravenna 2005, eq. 2.8), and the PDF says so itself. It is needed only for the sharp constants. It was COMPUTATIONALLY confirmed here for this walk. Keep the PDF's caveat, and add that the Θ results do not depend on it.
2. **(I2)** is cited as "Caravenna Remark 1, citing Feller XII.7 / XVIII.5". It is a standard textbook result, but I did not check the section numbers.
3. **"Gnedenko's theorem"** is invoked but has no bibliography entry. The proof actually uses de Moivre–Laplace, which is also uncited. Donsker, Portmanteau, Weyl, Wald and Chernoff are uncited textbook results.
4. **Missing related literature to check before any novelty claim:** Doney (2012), local first-passage behaviour; Caravenna–Chaumont (2013), uniform bridge estimates. Either might already contain Thm 8.7-type statements for "b + cℤ" lattice walks. This needs a web or library check.
5. **Wording and typos:**
   - The abstract's "exactly the Beatty sequences" overstates it (see §5).
   - App. J has a broken reference ("Section ??").
   - App. H has the q-typo (already corrected in I.1).
   - "Extends to admissible negative c… O(1) terms only" holds at the Θ level, but the sharp formulas are proved only for integer c ≥ 0.
6. **Provenance:** the only copy is this Downloads PDF, with no source. The repo docs from Sept 12–13 are stale relative to it.

## 13. Sharpened exceptional-seed bound (Part XIII)

From `card_seeds_le_sum` (PROVED (LEAN)): for every N,
#{odd μ < X : R_j ≤ U ∀j ≤ N} ≤ (X/2)·p_N(U) + W_U(N).

Take N ≈ (log₂X − 1 − U + φ)/α (the fresh-bit balance point). Then:

| Input | Resulting bound | Status |
|---|---|---|
| Current: Chernoff + entropy | C_U·X^{H₂(ρ)}, effective constants | Current theorem |
| Stirling + P(S_N ≤ s_N) | Gain factor (log X)^{−1/2}, effective | PROVED (MATH), elementary |
| PDF Lemma 8.9 / Thms 8.22–8.23 | **#(E_U ∩ [1,X]) ≤ C_U·X^{H₂(1/α)}·(log X)^{−3/2}** | PROVED (MATH); C_U is not explicit, because (I2) has unspecified constants |

- **Exponent:** unchanged, H₂(1/α) = 0.949956. A polynomial factor cannot move it.
- **Logarithmic correction:** (log X)^{−3/2}.
- **Constant:** asymptotically explicit through K_U(φ). The exact optimized bound B(X) = min_N[…], computed by exact DP, gives B(X) ≈ 11.6–12.1·X^{H₂}·(log₂X)^{−3/2} for U = 0 and ≈ 68–70 for U = 2, flat over log₂X ∈ [600, 3850].
- A better exponent would need realizer-level correlations, i.e. beating the union bound. The PDF cannot supply that.

## 14. Are the stopping-time extremes a new scale? (Part XII)

No. Under the independence HEURISTIC, (X/2)·p_N ≈ 1 gives
M(X) = [log₂X − (3/2)·log₂N + log₂K(φ_N) + O(1)] / I₀.
- Scale 1 gives the leading term log₂X / I₀.
- Scale 2 gives −(3/(2I₀))·log₂N, which is about 160 steps at 2⁴⁰. It explains why M/log₂X ≈ 8.7 rather than 1/I₀ = 12.6.
- Scale 3 shifts M by about ±6 steps.
- The Gumbel spread of about 18 steps is extreme-value randomness, not a new scale.
- What is new is realizer-level: independence works to N ≈ 250 at 2⁴⁰ (survivor ratios ≈ 1.00), then fails through clustering (ratio 1.25 at N = 300; 471 → 152 clusters).

## 15. Remaining frontier (Part XIV)

The ensemble question is solved (paper-level). What remains open:

1. **Pointwise:** is E_U ≠ ∅, i.e. does some integer realize an infinite confined word? By the UpperEscape/UpperCertificates theorems this is equivalent to a divergent orbit.
2. **Realizer and orbit dependence beyond the fresh-bit regime:** pair-survival covariance, second moments, clustering, backward-tree coalescence.
3. **Phase → realizer placement** (PDF Conj. I.1).
4. **Formalization gaps** listed in §11.
5. **Unproved rates:** the O(1/N) convergence rate; novelty of Thm 8.7.

## 16. Suggested documentation structure (Part XV; nothing moved)

- **`docs/ensemble/`**: entropy, N^{−3/2}, renewal phase (PDF), plus a PDF ↔ Lean ledger (§1 of this report).
- **`docs/realizer/`**: PairValuation, SuffixTransport, TransportCollapse, PrescribedMatching.
- **`docs/orbit/`**: LogCorridor, UpperEscape, UpperCertificates, divergence equivalence.
- **`docs/seed-statistics/`**: SurvivorCounting, the (log X)^{−3/2} bound, records, clustering.
- **Status:** mark the Sept 12–13 audit files STALE for §8, or add an erratum pointing to the PDF.

## 17. Next steps

**Research:**
1. Second moment and pair-survival covariance via PairValuation split depths, to explain the clustering and the survivor excess beyond N ≈ 250.
2. The PDF's App. I.3 phase-sensitivity test on least realizers. It is cheap now that `renewal_dp` supplies the predicted phase.
3. Citation closure: the primary Alili–Doney source, Doney 2012 and Caravenna–Chaumont 2013. Also add the U(β) = α proof to the manuscript.

**Lean:**
1. Capacity sandwich.
2. The Lean survivor-density theorem.
3. The entropy limit, with irrationality of log₂3 and tie-freeness.

## 18. Overall assessment

- The ensemble layer is closed at paper level. The PDF's sharp formulas match independent exact data to about 10⁻³ at N ≈ 4000, and one of its open observations is now proved.
- Lean covers the exponential layer only.
- The realizer/orbit layer is Lean-verified and lies entirely outside the PDF.
- The two layers are joined only at first-moment level (SurvivorCounting's union bound).
- The open seams are the second moment and dependence between seeds, and the pointwise existence question.
