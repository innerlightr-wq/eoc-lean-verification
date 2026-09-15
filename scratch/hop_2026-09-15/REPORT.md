# Distinct-triangle hops and the TriangleGapBridge (round of 2026-09-15, twelfth)

Nothing committed or pushed.  New Lean: `EOC/TriangleHop.lean` (imported in `EOC.lean`; `lake build` 8787 jobs, 0 errors,
standard axioms only, no sorry).  Scripts/data here: `witness.py`→`WITNESS.txt`, `ld_tables.py`→`LD_TABLES.txt`,
`hops.py`→`HOPS.txt` (log-space sampler; an earlier float-sampler output, which underflows at J = 1600, is not committed).
Literature audit of the quantitative Subspace Theorem: § XIX–XXIII (constants NOT independently re-verified; NOT USED).

**Verdict.**  The long-jump lemma is exact and sharp (d ≥ 6 at η = 1/54, PROVED LEAN incl. a kernel-checked witness),
and the run decomposition is PROVED (LEAN).  But stop conditions 1 and 5 fire: the "many d ≥ 6 digits" LD route is
REFUTED, and maximum-size control cannot give positive-density good angles without a triangle-occupation (size-tail) theorem.
The exact remaining input is `TriangleOccupation` (below), which is weak in size but needs exponential concentration.

## I–III. Jump threshold (PROVED MATH + PROVED LEAN)
Consecutive path cells (a,b) → (a−d, b+1), both black.  Always y(a−d,b+1) ≡ 2^d y(a,b) (mod 3^b).
* Same triangle ⇔ y(a−d,b+1) = 2^d y(a,b) (`SameTri`; common generator ⇒ linked: `sameTri_of_common_corner`;
  linked ⇒ common corner (a,b+1): `corner_eq`).
* Distinct ⇒ 3^b ≤ |y′ − 2^d y| < 3η3^b + 2^dη3^b ⇒ **(2^d + 3)η > 1** (`black_distinct_imp_large_digit`,
  `distinct_hop_pow_gt`).  **d_min(η) = min{d : (2^d+3)η > 1} = ⌊log₂(1/η − 3)⌋ + 1** (η < 1/4).
* η = 1/54: 2^d > 51 ⇒ **d ≥ 6** (`distinct_hop_digit_ge_six`).  **Sharp**: cells (160,5), (154,6), y = 4, y′ = 13,
  13 − 64·4 = −3^5 (`distinct_hop_witness_d6`, kernel `decide`).  Exact witnesses at d_min also for η = 1/20 (d=5),
  1/100 (d=7), 1/200 (d=8) (`WITNESS.txt`).
* Same row: distinct black triangles in one row are ≥ 6 columns apart (2^k > 1/η − 1 = 53; `sameRow_of_small_gap`).

## IV–VI. Run decomposition (PROVED LEAN: `chain_value`, `run_offset_lt`, `run_decomposition(_54)`)
A linked run of r steps from a black cell s has a corner generator (a_s, b_s + r) with the same y, generating every run cell,
of size s(a_s,b_s) + r ln3 > r ln3.  Hence runs outside triangles of size ≥ R₁ have length < H₁ = ⌊R₁/ln3⌋ + 1, and
**n ≤ W + Occ(R₁) + H₁(1 + W + W′ + J)**, W′ ≤ W + 1, J ≤ N₆ (η = 1/54), i.e.
**n ≤ (2H₁+1)W + Occ(R₁) + H₁N₆ + 2H₁**  (W white, J distinct hops, N₆ = #{d_i ≥ 6}, Occ = black cells in triangles of size ≥ R₁).
Max-only: R_max ≤ R₀ < R₁ ⇒ Occ = 0 (`occ_eq_zero_of_maxTriangleLE`), so n ≤ (2H+1)W + HN₆ + 2H.
Correct inversion (Part V): if W ≤ δn, Occ = 0, then N₆ ≥ ((1 − (2H+1)δ)n − 2H)/H — vacuous unless δ < 1/(2H+1).
The proposed J ≥ (1−δ)n/(C R_max) − 1 is false as stated (it omits runs started after white cells).
Checked on every sampled path (0 violations).

## VII–XI. Large digits (PROVED MATH / COMPUTATIONAL; `LD_TABLES.txt`)
p_{d₀} = P*(d ≥ d₀) = r^{d₀−1}, r = 1 − 1/α = 0.36907:  p₅ = 0.01855, **p₆ = 0.006848**, p₇ = 0.002527, p₈ = 0.000933.
Chernoff: P*(N_{≥d₀}(n) ≥ qn) ≤ 2^{−nI(q‖p)}, I(q‖p) = q log₂(q/p) + (1−q) log₂((1−q)/(1−p)); d₀ = 6: I = 0.0009, 0.0121,
0.0825, 0.2589, 0.7240 bits at q = 0.01, 0.02, 0.05, 0.1, 0.2.
Confined law = P*(· | C_n) exactly (P*-weight depends only on the sum), so **P_conf(E) ≤ P*(E)/P*(C_n)**; n^{3/2}P*(C_n) ∈
[0.43, 1.12] for n = 60…300 (COMPUTATIONAL; phase-dependent constant.  Θ(n^{−3/2}) is a paper-level result of the author's
ScalesConfinement note, not contained in this repository — see `scratch/scales_reconciliation_2026-09-14/REPORT.md`), hence
P_conf(N₆ ≥ qn) ≤ C n^{3/2} 2^{−nI(q‖p₆)} (PROVED MATH given the confinement asymptotic).  Valid where P*(C) ≥ n^{−A}: endpoint
within O(√(n log n)) of the drift line (the EOC shells: endpoint ⌊nα⌋), any start headroom ≥ 0; not uniform for linear endpoint
deviations.  Exact means E[N₆]/n: confined 0.0059–0.0066, shell-only 0.0059–0.0066, iid 0.00685 (n = 60…300); confined tails
are *smaller* than iid (rate 0.15 vs 0.08 bits at q = 0.05).

## XII–XIV. Obstruction (stop conditions 1 and 5)
* Low white density requires only ≈ n/H hops, H ≈ R_max/ln3 → ∞, i.e. hop density → 0, below the typical p₆ ≈ 0.0066: **no LD
  penalty — naive route REFUTED**.
* Even with J = 0, max-only control gives W ≥ (n − 2H)/(2H+1): density ~1/(2H+1) → 0.  Combinatorially sharp: runs of length H
  separated by single white cells satisfy every proved local constraint.  Max-only + LD gives positive density iff H·q < 1,
  i.e. R_max ≲ 165 (q ≈ 0.0066): true numerically for every feasible L (R_max(6400) = 8.17 ⇒ density ≥ 0.056), not provable
  asymptotically (R_max grows ≈ log L, HEURISTIC).
* Forcing J ≥ cn with c > p₆ is impossible from geometry alone; what is needed is that each visited triangle contributes O(1)
  steps on average — an occupation theorem (TriangleDensity).

## XV–XVIII. Size-weighted formulation; minimal count theorem (PROVED MATH; Lean glue)
Occ(R₁) ≤ Σ_{T meets path, s_T ≥ R₁} (⌊s_T/ln3⌋ + 1) (a path visits each row once).  Positive density follows from
**TriangleOccupation(R₁, θ)**: path weight of {Occ(R₁) > (1−θ)n} ≤ ρ₂, with **θ > q·H₁** (q = LD hop cutoff).  With V_n(R) =
#triangles of size ≥ R met by the path ≤ n f(R): suffices ∃R₁ with F(R₁) + q(⌊R₁/ln3⌋+1) < 1, F(R₁) = (1/ln3)∫_{R₁}^∞ f +
(R₁/ln3 + 1) f(R₁); e.g. f = Ce^{−cR} or CR^{−1−ε} with small enough constants; dyadically Occ ≤ Σ_j (2^{j+1}/ln3 + 1)V_n(2^j).
Example: R₁ = 3 (H₁ = 3), Occ ≤ n/2, N₆ ≤ 0.02n ⇒ W ≥ 0.063n − 1.  Lean: `positiveDensityGoodAngles_of_runBound`
(`LargeJumpLD`, `TriangleOccupation` as hypotheses).  For γ > 0 both exception weights must be exponentially small.

## XIX–XXIII. Quantitative Subspace and fixed-fraction counts
Each triangle is one integer point (all its cells share X = 2^{a*}y*), so exceptional lines ↔ triangles.
A literature audit (sub-agent reading of author preprints: Evertse 1996, Evertse–Schlickewei 2002, Evertse–Ferretti 2013,
Evertse's 2010 survey, Bugeaud–Evertse 2008) reported explicit bounds on the *number* of exceptional subspaces that are
polynomial in 1/δ, with ineffective *location*.  **The specific exponents and constants have NOT been independently
re-verified; they are NOT USED in any claim here (REQUIRES RECHECK).**  Only the qualitative consequence is recorded:
* Fixed fraction: apexes of size ≥ εL over cells with D ≤ KL are δ-exceptional for δ = min(½, ε/2K), so the set of apexes
  ever ε-large is finite uniformly in L (**PROVED LEAN** `largeApexes_finite`, from `SubspaceInstance`).  R_max = o(L)
  already gives none for L ≥ L₀(ε); a verified quantitative Subspace Theorem would make the *cardinality* effective.
* Scale-dependent δ = R/(2KL): any count polynomial in 1/δ is polynomial in L/R, which for fixed R or R = C log L exceeds
  the number of cells a path visits — such counts are useless for occupation (HEURISTIC, pending the recheck above).

## XXIV–XXXVI. Hopping (PROVED MATH / COMPUTATIONAL; `HOPS.txt`, J = 100…1600, 40–400 paths, true and random units)
* **Exact kernel**: from black (a,b), z = (2^a y − 1)/3^b: y(a−d,b+1) = centered_{3^{b+1}}(2^d y + 3^b j_d), j_d ≡ −z(−1)^{a−d}
  (mod 3); next black ⇔ dist(2^dU + j_d, 3ℤ) < 3η; same triangle ⇔ j_d = 0 (3 | z) and 2^d|U| < 3η.  0 mismatches on all steps.
* Q(a,b) = Σ_{d≥6} P*(d)1{(a−d,b+1) black, distinct} ≤ p₆ trivially (a uniform q = p₆ < 1: stop condition 2 fires
  trivially, but it is useless); **sup over visited black cells ≈ 0.99 p₆** (Q/p₆ = 0.997), so no deterministic bound meaningfully
  below p₆ holds; mean Q ≈ (1.2–2.8)·10⁻⁴ ≈ random model p₆·2η = 2.5·10⁻⁴.  Geometric weights: w(6)/p₆ = 1 − r = 0.63.
* P(next black | d ≥ 6): from white 1.4–4.6% (2η = 3.7%); from black 3/99.
* Observed: black fraction 0.032–0.038 (random 2η = 0.037); **white density ≥ 0.90 on every path** (≥ 0.949 at J = 1600);
  distinct hops 2 (true) / 1 (random) among ≈ 11 000 / 6 300 black steps, digits 7, 7 / 6; runs mean 1.35–1.44, max 8;
  episodes = 1 triangle (max 2); entry depth mean 0.79–0.92 (random-model Exp(1)); visited apex size mean 1.7.
* Coarse chain: P(W→E) 0.024–0.028; P(E→S) 0.26–0.33; P(S→S) 0.23–0.36; P(→ new triangle | black) ≤ 10⁻³.
  Runs are short because visited triangles are small, not because of any hopping mechanism.

## XXXVII–XLI. Combining hops with R_max = o(L)
B ≤ H(1 + W + W′ + J): the W term remains, so neither B = o(L) nor B ≤ (1−δ)L follows; P(J ≥ k) ≤ q^k gives nothing without
occupation control.  The proposed B ≤ (J+1)R_max/ln3 is false.  **B_L = o(L) is false numerically** (B/L ≈ 0.035 ≈ 2η):
good-angle density tends to ≈ 1 − 2η, not 1.  Needed: bounded average visited-triangle height with exponential concentration.

## XLII–XLIV. Moments
Markov: (1/n)Σ_visits e^{τs} ≤ C ⇒ Occ(R₁) ≤ Cn e^{−τR₁}(R₁/ln3 + 1) ⇒ TriangleOccupation when this + qH₁ < 1 (PROVED MATH).
Σ_a e^{τ s(a,b)} = (η3^b)^τ Σ_a |y(a,b)|^{−τ}1{black}: over a full period (2 is a primitive root mod 3^b) the average is finite for
τ < 1 (trivial); along paths a runs over windows of length O(√b) against period 2·3^{b−1} — Kloosterman/Burgess/Korobov/BGK
need ≥ q^ε: **not applicable**.  Reformulation: s(a,b) ≈ ln3 × (run of equal digits 0 or 2 ending at position b−1 in the
3-adic expansion of 2^{−a}); occupation = digit-run statistics of powers of 2 along paths — the Senge–Straus / Stewart circle,
where only o(L)-type results are known (CONJECTURAL / open).

## Summary
* Strongest positive: exact sharp jump threshold and run decomposition (PROVED LEAN); conditional chain TriangleOccupation + LD
  ⇒ PositiveDensityGoodAngles (PROVED LEAN glue, explicit); positive density whenever R_max ≲ 165; finiteness (uniform
  in L) of ε-large triangles (PROVED LEAN from `SubspaceInstance`).
* Strongest negative: max-size + hopping cannot give positive density unless R_max stays bounded (combinatorially sharp);
  the LD route fails (required hop density → 0 < p₆); no weighted-hop bound below p₆; B_L = o(L) is false.
* Remaining lemma: TriangleOccupation(R₁, θ > qH₁) with exponentially small exceptions along confined paths, plus
  white-point contraction for the pair-block factors (good ⇔ white).  Rigorous γ = 0; A > 1/α not proved.  LEVEL 1.
