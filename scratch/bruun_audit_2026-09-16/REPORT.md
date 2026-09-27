# Constructive audit of R. Bruun, arXiv:2105.11334 (research round, 2026-09-16)

Nothing committed or pushed. No Lean changes.

**Files.**
* `bruun_v6.pdf` (authoritative), with `bruun_v1/v4/v5.pdf` for comparison, `v6_plain.txt` / `v6.txt` (pdftotext),
  and `img/` (rendered formula pages).
* `bruun.py` → `BRUUN_REPRO.txt`: three independent counts, a class tree to level 27, and stopping times for
  n ≤ 10⁶.
* `membership.py` → `MEMBERSHIP.txt`: integer membership and the EOC translation.

**Labels.** PROVED IN PAPER · VERIFIED (MATH) · EXTERNAL KNOWN RESULT · COMPUTATIONAL · HEURISTIC · CLAIMED ·
REQUIRES ADDITIONAL JUSTIFICATION · OPEN · POTENTIALLY USEFUL FOR EOC · NOT RELEVANT TO CURRENT EOC BLOCKER.

Literature statements marked "(recalled)" were not re-checked against the sources this round. OEIS was unreachable
(Cloudflare challenge).

## 1. The paper

**Versions.**

| Version | Date | Pages | Title |
|---|---|---|---|
| **v6 (latest)** | 31 Aug 2025 | 66 | "Explanation of the Dynamics involved in the 3N+1 Problem — A proof for The Collatz Conjecture" |
| v4 / v5 | Nov 2023 | 26 | "The Dynamics involved in the 3N+1-problem" |
| v1 | May 2021 | 14 | "The Collatz Graph as Flow-Diagram" |

* Author: R. (Rolf) Bruun, Copenhagen.
* The v4/v5 abstract contains the 2X, 4X−3 and binary-tree wording quoted in the round prompt.
* v6 abstract: "The scope of the present work is to explain why it is true that all N have a distinct position in The
  Collatz Tree."
* v6 keeps the same method and final claim as v4, and adds flowcharts, trees, lists and appendices.
* **Final Theorem (v6 p. 42):** "The Collatz Conjecture can not be false, because it is impossible for a
  counterexample to exist."

**Glossary (Bruun → standard).**

| Bruun | Standard meaning |
|---|---|
| Type Odd / Even operation | n ↦ 3n+1 / n ↦ n/2 |
| O E-tile / E-tile | the Terras steps (3n+1)/2 and n/2 |
| s = #O | number of odd steps |
| r = #E | number of halvings = number of tiles |
| j = s + r | number of standard operations |
| class [AX−B], X ∈ ℕ | the residue class {AX − B}, least member P = A − B |
| IV-class [2^r X − B₀] | the residue class n ≡ −B₀ (mod 2^r) = the Terras parity-vector cylinder of length r |
| TV-class [3^s X − B'] | the image T^r(2^r X − B₀) = 3^s X − B' (same X) |
| Class-series | the parity word of a class |
| *reducing combination (s, r_s) | r_s = ⌈sZ⌉ with Z = log₂3; the first k with 3^s < 2^k (Formula (1)) |
| *Converging IV-class | a class whose parity word first reaches 3^s < 2^k at k = r_s |
| Criterion P_TV < P_IV | all members reduce (Cor. 3) |
| ϕDiverging IV-class | not yet reducing at its level ("unresolved"; in EOC terms, confined) |
| ΔRedundant | a proper subclass of an already-reducing class |
| †End class | the class whose least member reaches 1 at a given step |
| Domino Tree / Base-2 Tree | the complete binary tree of parity words ↔ residues mod 2^r (Lemma 3) |
| Fibonacci Tree | the standard-operation tree with O–O pruned |
| Reverse Fibonacci Tree | the Collatz inverse tree |
| G(s, r_s) = \|Con(r_s)\| | number of reducing classes at level r_s (Formulas (2a)–(2c)) |
| F = G/2^{r_s}, S = Σ F | reduced fraction; cumulative density (Formulas (3), (4)) |
| Formula (5) | 1 − S(k) = Σ_{s>k} F(s) |
| B-values | follow the 3N−1 map (the Collatz map on −B) |
| Threshold values N_T | least unresolved integer at a level |

**Dependency graph (v6).**
1. Definition 1; Axioms 1–3; Corollary 1 (pp. 1–3). Axiom 1 is "all n > 2 reduce ⇔ Collatz", by well-ordering.
   VERIFIED (MATH).
2. Class operations (p. 4): [AX−B] →O [3AX − (3B−1)] for odd B, and →E [(A/2)X − B/2] for even B. VERIFIED (MATH).
3. Lemma 1 and Theorem 1 (p. 6): the valuation parity pattern mod 6; the only cycle of the form 3n+1 = n·2^r is
   n = 1. VERIFIED (MATH), elementary.
4. Lemma 2 (p. 12): the side-branch triple structure mod 3. VERIFIED (MATH), not used later. Page 12 also states
   candidly that when all printed flowcharts are shown to be connected, "then The Collatz Conjecture will be proven
   true".
5. Theorem 2 and Corollary 3 (pp. 16–17): for every s, reducing classes exist at r_s = ⌈sZ⌉.
   * Existence: VERIFIED (MATH); for example s OE-tiles followed by E-tiles.
   * Corollary 3 ("B_j < B₀ ⇔ reducing combination", i.e. every reducing class satisfies P_TV < P_IV) is argued by
     an approximation ("the estimate is a little too low"). REQUIRES ADDITIONAL JUSTIFICATION (see §4).
6. Lemma 3 (p. 22): residues mod 2^r ↔ parity words of length r. EXTERNAL KNOWN RESULT (Terras 1976, Everett 1977);
   VERIFIED (MATH).
7. Formulas (2a)–(2c) (pp. 30–31): the recursion G(s) = C(r_s, s) − Σ_{t<s} G(t)·C(r_s − r_t, s − t).
   VERIFIED (MATH) and COMPUTATIONAL (§2).
8. Formulas (3)–(5) and Resultlists 1–2 (pp. 32–33).
   * The formulas are VERIFIED.
   * S → 1 is EXTERNAL KNOWN RESULT (Terras); the paper cites it and shows tables rather than a proof.
   * Tabulated rows s ≥ 15 differ from the formula (§2).
9. Lemma 4 (p. 34): the average gap 2^r/|Div(r)| → ∞. VERIFIED (MATH) as a statement about averages. The inference
   that "the distance between elements in the union" tends to infinity REQUIRES ADDITIONAL JUSTIFICATION: an average
   gap does not control individual members.
10. Page 41, "The lowest value in a ϕDiverging IV-class can not be unlucky forever", and "r_s < 2^P ... No N can
    visit the power-set of N different layers". CLAIMED from observation; REQUIRES ADDITIONAL JUSTIFICATION (§4).
11. Final Theorem (p. 42). The bullet chain is: formulas exact ⇒ Formula (5) ⇒ "no uncovered area" ⇒ "the union of
    *Converging classes is a Covering System" ⇒ r_s ≤ 2^N ⇒ the least unresolved element eventually belongs to a
    *Converging class ⇒ no least counterexample.
    * The first arrow is VERIFIED (given Terras).
    * The arrows "density one ⇒ covering ℕ" and "the least element is eventually resolved" REQUIRE ADDITIONAL
      JUSTIFICATION.

## 2. Verified content and reproduction (COMPUTATIONAL unless stated)

* **Affine form (VERIFIED (MATH), standard).** For n ≡ P (mod 2^k) with s odd tiles, T^k(n) = (3^s n + c)/2^k.
  Bruun's TV-class encodes this as B' = (3^s B − c)/2^k, and his P_TV < P_IV test is T^k(P) < P at X = 1, which is
  monotone in X. The terminal residue is T^k(n) ≡ c·2^{−k} (mod 3^s); this was checked for every class with k ≤ 14.
* **Counts.** G(s) was computed three independent ways: Formula (2a), a lattice-path DP, and a residue-class tree to
  2^27. All three agree. Values for s = 0..22: 1, 1, 1, 2, 3, 7, 12, 30, 85, 173, 476, 961, 2652, 8045, 17637,
  **51033, 108950, 312455, 663535, 1900470, 5936673, 13472296, 39993895**. G(s) > 0 for every s ≤ 80.
* **Resultlist 1 erratum.** Bruun's table matches exactly in all six columns for s ≤ 14. From s = 15 on, the
  tabulated \|Div\| and \|Con\| differ from the values of Bruun's own Formula (2a). At s = 15 the paper has 47118
  reducing and 290496 unresolved; the correct values are 51033 and 286581, so 1 − S is 0.017082, not 0.017315. The
  row totals still equal 2^r. This is a slip in the tables, not in the formula, and the paper's logic does not
  depend on these values.
* **Unresolved sets D_k** (residue classes mod 2^k not yet reducing).
  * Nesting: D_{k+1} ⊆ lift(D_k). VERIFIED (MATH).
  * Density: 0.0171 at k = 24, 3.3·10⁻³ at k = 50, 2.4·10⁻⁴ at k = 100, 1.2·10⁻⁹ at k = 400. The per-step ratio is
    about 0.961.
  * Density → 0: EXTERNAL KNOWN RESULT (Terras/Everett).
  * **Count** \|D_k\| grows: log₂\|D_k\| = 41.8, 88.0, 181.7, 370.3 at k = 50, 100, 200, 400 (about 2^{0.93k}).
* **Class criterion.** All 502,524 reducing classes with level ≤ 27 satisfy P_TV < P_IV (the loop class P = 1
  excepted). For 2 ≤ n ≤ 10⁶, χ(n) = σ(n) with no exception (coefficient stopping time = stopping time).
* **Threshold values N_T** (least unresolved integer): 3, 7, 27, 703, 10087, 35655, 270271, …, i.e. exactly the
  classical stopping-time records (χ = 4, 7, 59, 81, 105, 135, 164, …). This reproduces Bruun's list
  {1, 3, 7, 27, 703}. Bruun's remark χ(N) < 3N holds for 3 ≤ N ≤ 10⁶, with maximum ratio 59/27 = 2.185 at N = 27.
* **Samples.**
  * The classes [2X], [4X−3], [16X−13], [32X−21], [32X−9], [128X−121/113/69] are reproduced (Appendix Alpha
    u ≤ 8).
  * Bruun's algorithm examples 999 ∈ [2^10 X − 25] → [3^6 X − 17] and 255 ∈ [2^13 X − 7937] → [3^8 X − 6356] are
    reproduced.
  * The merge example T^9(387) = T^9(391) = 62 is reproduced.
* **Membership.** Bruun's certification level for n is exactly χ(n) = σ(n) (Terras steps). Examples: 27 → 59,
  703 → 81, 626331 → 176. So the certification time is the actual stopping time, not a proxy for it
  (`MEMBERSHIP.txt`).

## 3. Literature comparison

* **Terras 1976 / Everett 1977** (EXTERNAL KNOWN RESULT).
  * Parity words of length k ↔ residues mod 2^k.
  * Stopping time finite on a set of natural density 1.
  * Terras computes the densities through the same binomial/ceiling structure; Bruun says his formulas "deliver
    identical results".
  * Lemma 3, Formula (1), Formulas (2)–(5) and density → 0 are **Type I** (reformulation).
* **Lagarias 1985 survey** (recalled): the coefficient stopping time χ(n) ≤ σ(n), and the Coefficient Stopping Time
  Conjecture χ(n) = σ(n) for n ≥ 2 (Terras). Bruun's Corollary 3 applied to all reducing classes is this conjecture
  in class form. **Type I** (an open conjecture, restated).
* **Bernstein 1994 / Bernstein–Lagarias 1996** (recalled): the parity-vector map is a measure-preserving
  homeomorphism of ℤ₂ conjugating T to the shift. Every infinite parity word, including non-reducing ones, is
  realized by exactly one 2-adic integer. Relevant to §4; Bruun does not use it.
* **Counting recursion (2a)**: the same counts are catalogued in OEIS (entry recalled as A100982, not re-checked).
  **Type I–II** (a clean inclusion–exclusion presentation).
* **B-values / 3N−1 viewpoint and flowcharts**: **Type II** (useful exposition of the affine constant; the 3x−1
  cycles {1}, {5, 7, 10}, {17, …} are classical).
* **Tao 2019/2022**: log-density "almost bounded values", much deeper in descent depth. Bruun's established content
  is a Terras-type natural-density descent below the start value, so it is weaker on the descent axis, and the
  density notions differ.
* **Novelty.** No **Type III** ingredient was found.

## 4. Covering, nested chains, persistence

* **Exact covering statement.**
  * The reducing classes are pairwise disjoint. VERIFIED (MATH).
  * Their union covers ℤ₂ up to a Haar-null set. EXTERNAL KNOWN RESULT (Terras).
  * The complement E = ∩_k D_k ⊂ ℤ₂ is a **nonempty, closed, uncountable, null** set.
    * −1 = …111₂ has the all-OE word: 3^k ≥ 2^k forever, with least class members 2^k − 1 → ∞.
    * Inserting freely chosen, sparse E-tiles into the all-OE word gives uncountably many points.
  * No finite subfamily covers ℕ, since D_K ∋ 2^K − 1 for every K. So Bruun's cover must be countably infinite; he
    notes this himself.
* **Nested-chain test.**
  * For fixed n the classes C_k(n) = n + 2^kℤ form a nested chain whose density tends to 0.
  * For 2^k > n the least member of C_k(n) is n itself, so the least member does **not** grow.
  * n survives every level iff χ(n) = ∞. Density → 0 of C_k and of D_k is fully compatible with a surviving
    integer.
  * None of the candidate mechanisms (growing representative, incompatible refinements, forced reduction, finite
    cover) is established in the paper. Forced reduction is the missing lemma itself.
* **Minimal-counterexample argument** (VERIFIED as logic up to the gap).
  * A least N_ce satisfies σ(N_ce) = ∞.
  * The paper's step "the lowest element of ∪D_k is at some higher level shown to belong to a *Converging class" is
    χ(N_T) < ∞ for that integer, which is the claim to be proved.
  * N_T(k) is non-decreasing, and N_T(k) → ∞ ⇔ E ∩ ℕ_{≥2} = ∅.
* **Figure 5 heuristic** ("only one of four grandchildren is less reducing"). This counts residues, not the fixed
  path of a fixed n. The 2-adic −1 is "unlucky forever".
* **Replication / persistence.**
  * No theorem of the form "one exceptional integer ⇒ many exceptional classes" appears.
  * A hypothetical exceptional n contributes exactly one class per level.
  * \|D_k\| already grows like 2^{0.93k}, so counting alone gives no contradiction. Even c^k descendants would
    contradict nothing unless c exceeded that growth.
  * The "not enough ϕDiverging routes" remark (p. 41) is contradicted by this growth (COMPUTATIONAL; the growth rate
    is standard large deviations).
* **Missing lemmas.**
  * **L1 (covering).** Every n ≥ 2 has finite coefficient stopping time; equivalently, no positive integer realizes
    an infinite confined parity word (E ∩ ℕ_{≥2} = ∅). Collatz ⇒ L1, and the converse is not known.
    **Level C**: it excludes every counterexample whose multiplicative coefficient never drops below 1 from the
    start, which contains the hard core (never-descending orbits); no known technique reaches it. The quantitative
    form r_s < 2^N (p. 41) is stronger (**Level D**).
  * **L2 (class criterion, Cor. 3).** Every reducing class satisfies P_TV < P_IV, i.e. the Coefficient Stopping Time
    Conjecture. **Level C** (a known open conjecture). Verified here for all classes up to level 27 and for all
    n ≤ 10⁶.
  * Bruun's Final Theorem requires L1 + L2. **Density → 1 plus well-ordering does not give L1.**
* **Relation to EOC's persistence gap.** It is the same missing mechanism: a small or density-zero exceptional set
  does not exclude one infinite exceptional orbit. The residue tree adds no structure that makes it easier. The tree
  is the full parity tree (a Terras cylinder tree pruned at first reduction), and every infinite unpruned path is
  realized in ℤ₂.

## 5. EOC translation

* **Parameters.** Bruun's s = EOC's j (odd steps), r = the halving count S, Z = α = log₂3.
  * Reducing combination r = ⌈sα⌉ ⇔ the first bit-level crossing S > αj, i.e. R_j > 0. At block resolution:
    S_{j−1} + e > αj for some e ≤ d_j ⇔ S_j > αj.
  * Bruun unresolved (ϕDiverging) ⇔ the EOC confinement S_i ≤ ⌊iα⌋ for all completed blocks up to that bit level.
  * VERIFIED (MATH).
* **Threshold vs descent.** 2^r > 3^s is only multiplicative (R > 0). Actual descent is m_j < m₀ ⇔ R_j > log₂U_j
  (the exact orbit identity m_j = m₀U_j2^{−R_j}).
  * Bruun's P_TV < P_IV is R > log₂U at the least class member.
  * It is argued approximately (Cor. 3), not proved.
  * Sample at certification (`MEMBERSHIP.txt`): R ∈ [0.069, 1.0] and log₂U ∈ [0.00001, 0.245], so the criterion
    holds with small margins for small n.
  * **No drift floor for every seed.**
* **Additive correction.** Handled exactly per class through B-values (the Collatz map on −B), but not bounded.
  No cleaner control than EOC's U_j = Π(1 + 1/(3m_i)).
* **Class ↔ cylinder.**
  * Bruun's parity class mod 2^r corresponds to an EOC valuation cylinder, which needs modulus 2^{S+1} for exact
    valuations. Bruun's P corresponds to EOC's `leastRealizer`.
  * Bruun's "P or B lucky" at each doubling corresponds to EOC's lift digit in {0, 1} per halving.
  * EOC already formalizes this more precisely: `RealizerLift.leastRealizer_succ_eq`, `liftDigit_lt`,
    `existsUnique_zero_lift_digit`, `TaoLike.Cylinder`.
  * **Kill condition 6** (restatement of already-formalized content).
* **ShapeTail.** Bruun counts all confined words aggregated at bit level, i.e. the ballot/binomial count behind
  EOC's `SurvivorCounting` / `ExceptionalPowerBound`. There are no shells, offsets or shape statistics. **Bruun's
  residue counting and EOC ShapeTail appear to control different structures.**
* **Power-of-two frontier.**
  * The only appearance of 2^{−a} mod 3^b is the terminal residue T^k(n) ≡ c·2^{−k} (mod 3^s), plus the observation
    that TV-classes "run out" of residues mod 3^s (merging).
  * There is no statement on the distribution, ternary digits, windows or orbit of 2^{−a} mod 3^b.
  * **Kill condition 2** (2^r vs 3^s drift, with no control of 2^{−a} mod 3^b). NOT RELEVANT TO CURRENT EOC BLOCKER.
* **Haar codimension.** Bruun's exponential sparsity lives in seed-residue space (Haar on ℤ₂, rate ≈ 0.961 per
  Terras step), equivalently parity-word space. EOC's Haar codimension lives in 3-adic phase space. These are
  different domains with no transfer.
* **2/9 window count.** No mechanism; the paper has no windows and no phases. Kill conditions 2 and 3.
* **Direct descent.** No new drift-floor statement; Corollary 3 is a per-class approximation. Kill condition 5
  (only density-type information).
* **Curry / García–Tal.** No genuine interface found; the paper has no value-space sparsity for orbits.

## 6. Constructive assessment

* **Strongest established contribution** (VERIFIED (MATH), EXTERNAL KNOWN RESULT content). For every s ≥ 0 exactly
  G(s) residue classes mod 2^{r_s} (r_s = ⌈sα⌉, r₀ = 1) first reach 3^s < 2^k at k = r_s. G is given by the
  inclusion–exclusion recursion (2a). These classes are pairwise disjoint, and the unresolved density
  1 − Σ_{t≤s} G(t)2^{−r_t} → 0 (Terras). The class calculus [2^r X − B] ↦ [3^s X − B'] with
  B' = (3^s B − c)/2^r is exact.
* **Strongest reusable idea.** The B-value (3N−1) bookkeeping of the affine constant, and the explicit
  first-crossing recursion (2a), as a compact way to compute confined-word counts at bit resolution.
* **Strongest reproduced computation.** Resultlist 1 for s ≤ 14 exactly, recursion values to s = 80, and the class
  criterion for all 502,524 classes up to level 27.
* **Strongest potential EOC connection.** A citation-level cross-reference for the Terras-type counting and the
  coefficient-stopping-time viewpoint on the critical line R = 0.
* **Point requiring justification.** Final Theorem, bullet 4 onward (L1), together with Corollary 3 (L2).
  L1 is Level C and L2 is Level C; neither is genuinely weaker than a known hard open Collatz subproblem.
* **Lean.** No module proposed. The class ↔ parity-word correspondence and least-realizer lifts are already
  formalized in stronger form, and the recursion (2a) would not move any EOC blocker.

**Roadmap.**
* Outcome 3: the strongest established results overlap Terras/Everett stopping-time density work. Cite in
  `LITERATURE_CONTEXT.md` if desired, as an expository reformulation. Retain the EOC roadmap.
* Relevance: **LEVEL 2** (on the scale 1 = unrelated, 2 = background/citation, 3 = useful for a secondary gap,
  4 = advances a blocker).
