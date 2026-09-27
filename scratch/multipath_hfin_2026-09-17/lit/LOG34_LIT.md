# LOG34_LIT: literature check, dim_H C(1,M) vs log_3(4/3), and the Abram–Lagarias C(1,2^8) entry

Date: 2026-09-17. Confidence tags: [full] = I read the text; [abstract] = abstract or summary only; [memory] = my own recollection, not re-checked.

## Q1. Is dim_H C(1,M) -> log_3(4/3) (for generic M, or M = 4^m) already in the literature?

**Short answer.** I found no statement, conjecture or refutation that dim_H C(1,M) tends to log_3(4/3) for random/generic M or for M = 2^{2m}. There is also no theorem giving dim_H C(1,M) <= log_3(4/3) for every M, and none could exist: known exact values already break that bound. The ×2,×3 intersection theorems do not apply here, because both sets have the same base and so the same contraction ratio.

### Abram–Lagarias I and II (the sources closest to this question)
- W. C. Abram, J. C. Lagarias, *Intersections of multiplicative translates of 3-adic Cantor sets*, J. Fractal Geom. 1 (2014) 349–390, DOI 10.4171/JFG/11, arXiv:1308.3133 (v1 only). [full: arXiv v1 and the journal PDF]
  - The dimension is always log_3 β, with β a Perron root.
  - Families: L_k=(1^k)_3 has dimension -> 0. N_k = 3^k+1 has dimension exactly log_3 φ = 0.438018 for every k.
  - They say only that the dependence on M is "very complicated". There is no limit or typical-value statement and no mention of log_3(4/3).
- W. C. Abram, A. Bolshakov, J. C. Lagarias, *... II: two infinite families*, arXiv:1508.05967 (v2 15 Dec 2015); Experimental Math., DOI 10.1080/10586458.2016.1205532. [full: arXiv v2]
  - Thm 2.4: dim C(1,Q_k) = log_3 φ for Q_k = (2^k 0^{k-1} 1)_3, for all k >= 2.
  - Thm 2.6: α_n := sup{dim C(1,M) : d_3(M) >= n} = log_3 φ for every n >= 2. So the number of nonzero digits alone does not force the dimension down to log_3(4/3) or below.
- Citing papers (Semantic Scholar): Abram–Lagarias–Slonim arXiv:2010.15215 and 2101.02441; Deng–Li–Qiu arXiv:2206.08559. None extends the C(1,2^m) tables. [abstract]

**The "≤ log_3(4/3)" bound is false for individual M, including powers of 2.**
- C(1,4) = log_3 φ = 0.438 (A–L Thm 1.8, N_1 = 4).
- C(1,2^6) = 0.278, C(1,2^8) >= 0.287 (their value; ours is 0.3069), C(1,2^14) = 0.267112 (their value; our check gives the same).
- So any "log_3(4/3)" statement can at most be about averages, typical M, or a limit. It cannot be a pointwise upper bound.

### Shmerkin / Wu: does their theorem apply?
- P. Shmerkin, *On Furstenberg's intersection conjecture, self-similar measures, and the L^q norms of convolutions*, Ann. of Math. 189 (2019), arXiv:1609.07802. [full, main statements]
  - **Thm 1.2:** p, q multiplicatively independent; A closed and T_p-invariant, B closed and T_q-invariant on [0,1); g invertible affine. Then dim_B(A ∩ g(B)) <= max(dim_H A + dim_H B − 1, 0).
  - **Cor 7.3:** A_1, A_2 homogeneous self-similar sets satisfying the OSC, with contraction ratios λ_1, λ_2 and **log λ_1 / log λ_2 ∉ Q**. The same bound then holds for all affine g.
- M. Wu (Ann. of Math. 189, 2019) has the same hypothesis. [memory]
- **They do not apply.**
  - *Real analogue:* C_{0,1} and uC_{0,1}+v are both 1/3-homogeneous, so log λ_1/log λ_2 = 1 is rational. Scaling does not change the contraction ratio, so u = 2^a being multiplicatively independent of 3 does not help. Neither set is ×2-invariant.
  - *Integer slope u:* the projected IFS x/3 + (a − u b)/3 has integer translations and similarity dimension log_3 4 > 1, so exact overlaps are unavoidable. That is exactly the case where fiber bounds of this kind can fail.
  - *3-adic setting:* |M|_3 = 1, so multiplying by M is an isometry of Z_3. Σ and M^{-1}Σ both have ratio 1/3, and there is no irrational ratio to exploit. I found no 3-adic version of Shmerkin–Wu, and I would not expect a naive transfer to work. The A–L values above (0.438, 0.307) break the bound outright.
- The coincidence log_3 2 + log_3 2 − 1 = log_3(4/3) is the Marstrand slicing value: dim(E ∩ ℓ) <= dim E − 1 for a.e. line in a fixed direction, with E = C×C. [full: quoted as remark (a) after Shmerkin Cor 8.3] This is an a.e. statement and says nothing about the particular line through the origin with slope M.

### Same-base "typical translate" results (for comparison)
- J. Hawkes, *Some algebraic properties of small sets*, Q. J. Math. 26 (1975) 713–747. For Lebesgue-a.e. t, dim(C ∩ (C+t)) = (1/3) log_3 2 ≈ 0.2103, for the middle-thirds Cantor set. [memory, matched by a web-search snippet; original not read]
  - This is strictly below log_3(4/3) = 0.2619. For additive translates the "independent digits × survival" heuristic gives the wrong answer at a.e. t, because a uniformly random digit of t allows freedom only at digit 0.
  - So whether log_3(4/3) is right for multiplicative translates is a real question, not a formal consequence of Marstrand.
- R. Kenyon, Y. Peres, *Intersecting random translates of invariant Cantor sets*, Invent. Math. 104 (1991) 601–629, DOI 10.1007/BF01245092. [abstract]
  - For ×b-invariant X, Y, dim((X+t) ∩ Y) is a.e. constant and equals a top Lyapunov exponent of a random matrix product.
  - Translations only. By Jensen, a quenched Lyapunov value is <= the annealed (first-moment) value, and log_3(4/3) looks like an annealed value. This is my own inference, not a cited statement.
- Alibabaei arXiv:2512.02675 and MacVicar arXiv:2604.19986 cover additive translates only. [abstract]
- L. Jiang, B. Li, R. Li, Y. Wu, *Dimension drop for intersections of Cantor sets*, arXiv:2607.19813 (22 Jul 2026). [abstract]
  - Upper Minkowski dimension of f(E) ∩ E is strictly less than dim_H E for C^1 diffeomorphisms f, under a log-irrationality condition. That is a drop below dim E, not the dim E + dim E − 1 bound.

**Conclusion for Q1.** As far as this search reached, dim_H C(1,M) -> log_3(4/3) for typical M or for M = 4^m is **not known and not conjectured**. It is **not refuted as a limit or typical-value statement**, and it **is refuted as a pointwise bound**. The Shmerkin–Wu theorems **do not give** an upper bound here, in either the real or the 3-adic setting. The best candidate for a rigorous "typical M" statement is a Kenyon–Peres-style Lyapunov formula for Haar-random multipliers u ∈ Z_3^×. I did not find one.

## Q2. Is the C(1,2^8) = 0.287416 entry ever corrected?

- **arXiv:1308.3133 has only v1** (14 Aug 2013), confirmed on the arXiv abs page. [full] Table 5.2 lists C(1,2^8) 0.287416.
- **The journal version (JFG 1 (2014), Table 6.1, p. 389) still prints 0.287416.** [full: EMS PDF] Crossref shows no erratum or update record for DOI 10.4171/JFG/11. Part II does not revisit 2^8. The only C(1,2^m)-type value in Part II is C(1,64) = 0.278004 in Table 7.1, against 0.278002 in Part I.
- A typo is present in both versions: "2^8 = 256 = (10111)_3". The correct expansion is 256 = (100111)_3; (10111)_3 = 94.

**Independent checks (scratchpad script, carry automaton, state = carry, digits {0,1}):**

| M | automaton states | β | log_3 β | A–L value |
|---|---|---|---|---|
| 4 | 2 | 1.618034 | 0.438018 | 0.438018 |
| 16 | 5 | 1.324718 | 0.255959 | 0.255960 |
| 64 | 14 | 1.357193 | 0.278004 | 0.278002 |
| **256** | **35** | **1.400925** | **0.306871** | **0.287416** |
| 1024 | 77 | 1.266705 | 0.215198 | 0.215201 |
| 4096 | 181 | 1.307425 | 0.243998 | 0.244002 |
| 16384 | 442 | – | 0.267110 | 0.267112 |
| (4,256) | 10 | – | 0.228391 | C(1,2^2,2^8) = 0.228392 |

- Every other entry agrees to about 1e-5. The small differences come from the power-iteration estimate.
- Our value of 0.306871 matches your figure and 35-state automaton exactly.
- A–L's C(1,2^2,2^8) matches too, so they did handle M = 256 correctly in that computation.
- Using 94 (the typo) gives 0.3247, and using 118 (its digit reversal) gives 0.3176. Neither reproduces 0.287416 (β = 1.37130).

**Conclusion for Q2.** No correction exists: the arXiv v1 and the journal version both print 0.287416. The entry is almost certainly a transcription or table error in the paper; I could not identify where it came from. The correct value is log_3(1.400925) = 0.306871. Confidence is high: the check is independent, and every neighbouring entry reproduces.

