# The record staircase: record-only reduction in Lean, frontier to 10⁸ (round of 2026-09-16, part 15)

Nothing committed or pushed.  Lean: `EOC/DirectDescent.lean` extended (`MinimalConfined`,
`linearFloor_of_minimal`); `lake build` 8792 jobs, standard axioms, no sorry.  Data: `scan.py` → `RECORDS_1e8.txt`.
**Stop condition 1 fired** (record-only reduction formalized).

## 1. Record-only reduction — PROVED (LEAN)
`MinimalConfined c M N` := `M` odd, its own word `c`-confined to depth `N`, and no smaller odd seed is
(equivalently `M = r_min(N,c)`).  **`linearFloor_of_minimal`**: if every minimally confined `M` at depth
`N ≥ N₀` satisfies `A·N − B ≤ M`, then `LinearRealizerFloor c A B N₀` holds for *all* odd seeds (strong
induction on `M`: a non-minimal witness is replaced by a smaller one).  Chained with part 8 this gives
  **record-only floor ⇒ eventual descent ⇒ Collatz (finite base check).**
Equivalently, with `M(X) = max_{odd m ≤ X} L₁(m)`: `M(X) < CX` eventually ⟺ `L₁(m) < Cm` on record seeds,
the binding case at each record being `N = L₁(m)`.

## 2. The record staircase to 10⁸ (COMPUTATIONAL, exhaustive)
25 records; deepest `L₁ = 238` at `m = 63 728 127`.  Selected rows:
| i | m_i | N_i | N_i/m_i | m_i/N_i | log₂m_i/N_i | m_{i+1}/m_i | ΔN |
|---|---|---|---|---|---|---|---|
| 0 | 27 | 39 | **1.4444** | **0.692** | 0.1219 | 26.0 | 11 |
| 1 | 703 | 50 | 0.0711 | 14.06 | 0.1891 | 1.33 | 1 |
| 9 | 35 655 | 85 | 0.0024 | 419 | 0.1779 | 1.71 | 10 |
| 16 | 837 799 | 134 | 0.0002 | 6 252 | 0.1468 | 1.34 | 6 |
| 19 | 1 859 241 | 144 | 0.0001 | 12 911 | 0.1446 | 3.58 | 46 |
| 22 | 10 507 503 | 194 | 4·10⁻⁵ | 54 162 | 0.1202 | 5.42 | 3 |
| 23 | 56 924 955 | 197 | 3·10⁻⁶ | 288 959 | 0.1308 | 1.12 | 41 |
| 24 | 63 728 127 | 238 | 4·10⁻⁶ | 267 765 | 0.1089 | — | — |
* **Maximum record ratio is still `N/m = 13/9 = 1.4444` at m = 27**; the tail envelope collapses immediately
  (≤ 0.071 from the second record on) and is `≤ 4·10⁻⁶` past 10⁷.
* **Inverse-cost envelope** `A_i = m_i/N_i`: 0.692, 14.06, 18.4, …, 267 765 — the required threshold
  `A > 0.4809` binds **only at 27**, with margin ≥ 29× everywhere after.
* Record jumps `m_{i+1}/m_i` are mostly 1.06–1.8 (occasionally 3.6–26); record-length increments ΔN are 1–46.
* `log₂m_i/N_i` drifts slowly down, 0.12–0.19, consistent with `r_min(N) ≈ 2^{0.11…0.19·N}`.
* Consequently **`M(X) < 2X` is verified for every `X ≤ 10⁸`** (binding case `M(27) = 39 < 54`), and the dyadic
  floor `r_min(2^k,1) ≥ 2^k` is now verified for **6 ≤ k ≤ 26** (no seed ≤ 10⁸ reaches `L₁ = 239`).

## 3. Survivor sieve (Parts XXX–XL) — COMPUTATIONAL
Survivors at depth `N` among odd `m ≤ 10⁸`:
| N | 10 | 20 | 30 | 40 | 50 | 60 | 70 | 80 |
|---|---|---|---|---|---|---|---|---|
| density | 1.47e-1 | 4.69e-2 | 1.76e-2 | 7.57e-3 | 3.40e-3 | 1.58e-3 | 7.39e-4 | 3.77e-4 |
| least survivor | 27 | 27 | 27 | 703 | 703 | 10 087 | 35 655 | 35 655 |
| 1/density | 6.8 | 21.3 | 56.7 | 132 | 294 | 632 | 1 353 | 2 654 |
The least survivor tracks `1/density` within a factor 0.5–13: **the first survivor behaves like a generic gap**,
not an extreme anomaly.  Density decays like `2^{−0.06N}`, so "first survivor ≈ 1/density" *is* the exponential
floor — but density alone cannot bound a minimum (Part XXXIX), and no maximal-gap/Jacobsthal structure was
found: the escape classes at depth `j` are residue classes mod `2^{S_j}` whose union is not of covering type.

## 4. What did not yield
* Dominance/pruning and Pareto-state compression (Parts XV–XX): a prefix with larger `r` can still lead to the
  smaller future realizer (the record seeds themselves are such continuations), so no dominance rule survives;
  the min-plus formulation has no finite state, since the value `r(D)` is a residue whose comparison needs full
  precision.
* Dyadic induction (Parts XLIII–XLVI): a seed in `[2^k, 2^{k+1})` is not controlled by the previous dyadic
  floor, and Collatz admits no rescaling that maps it to a smaller instance.
* Shell crossings (Parts L–LIV): the shell index is `⌊log₂m_j⌋ = ⌊log₂m + X_j⌋`, and `X_j = log₂U_j − R_j`, so
  crossing counts are a floor-discretization of the drift already studied — circular (Part LIII's own warning).

## 5. Status
* PROVED (LEAN): the record-only reduction (`linearFloor_of_minimal`), on top of the part-8 chain to Collatz.
* COMPUTATIONAL: full record staircase to 10⁸ (25 records, deepest 238); `M(X) < 2X` for `X ≤ 10⁸`; dyadic floor
  for `6 ≤ k ≤ 26`; survivor-sieve densities and least survivors.
* REFUTED/closed this round: dominance-based frontier compression; dyadic one-scale induction; shell-crossing
  invariants (circular).
* OPEN: `L₁(m) < Cm` on record seeds for some `C < 3 ln 2` — the binding case in all data is `m = 27`.
* Collatz not proved.  LEVEL 1.
