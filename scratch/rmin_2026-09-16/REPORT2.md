# Dyadic scales suffice; the word search collapses to a seed search (round of 2026-09-16, part 9)

Nothing committed or pushed.  Lean: `EOC/DirectDescent.lean` extended (`confined_mono`, `DyadicRealizerFloor`,
`linearFloor_of_dyadic`, `reachesOne_of_dyadicFloor`); `lake build` 8791 jobs, standard axioms, no sorry.
Scripts/data: `dyadic.py`, `scan.py` → `SCAN_2e7.txt`.

## 1. Dyadic scales suffice (PROVED (LEAN)) — stop condition 1
`confined_mono`: confinement to depth `N` gives confinement to every smaller depth.  Hence for
`2^k ≤ N < 2^{k+1}` a dyadic floor gives `M ≥ 2^k > N/2`:
* **`linearFloor_of_dyadic`**: `DyadicRealizerFloor c k₀ → LinearRealizerFloor c (1/2) 0 (2^{k₀})`;
* **`reachesOne_of_dyadicFloor`**: at `c = 1`, since `3·(1/2)·ln 2 = 1.0397… > 1`, the dyadic floor plus a
  finite base check gives **every odd seed reaches 1**.
With `k₀ = 6` the threshold is `mstar = max(0.5/0.03972, 65/(3 ln 2)) = 31.3`, so the base check is *odd m ≤ 31*.
> **If `r_min(2^k, 1) ≥ 2^k` for all `k ≥ 6`, then Collatz holds** (base check: odd m ≤ 31).

## 2. The word search collapses to a seed search (PROVED (MATH))
*Prefix locking*: for `D = PQ`, the realizer class of `D` refines that of `P` with spacing `2^{S(P)}`, and
`r(P) ≤ r(D)`; so if `r(D) ≤ AN < 2^{S(P)}` then **`r(D) = r(P)`**.  Since a critical confined prefix has
`S(P) ≈ α|P|`, this applies as soon as `|P| ≳ log₂(AN)/α`.  Consequently a word with `r(D) ≤ AN` is realized by
a seed `m = r(D) ≤ AN` whose *own orbit* produces the whole word, i.e. `L_1(m) ≥ N`.  Therefore
  **`r_min(N,1) ≥ AN` ⟺ every odd `m ≤ AN` has `L_1(m) < N` ⟺ `L_1(m) < m/A` for all large odd `m`.**
Checking the shrinking-target condition over *words* is therefore equivalent to checking `L_1` on the ~`AN/2`
odd *seeds* below `AN` — a vastly smaller, finite search.  This makes the backward-interval propagation,
meet-in-the-middle, and symbolic-minimizer programs (Parts II–XIII, XV–XXIV) **unnecessary**: the exhaustive
seed scan already performs the optimal falsification search in every range it covers.

## 3. Computational status (COMPUTATIONAL, exhaustive odd seeds ≤ 2·10⁷)
| k | 2^k | r_min(2^k,1) | 2^k ≤ r_min? |
|---|---|---|---|
| 2–4 | 4, 8, 16 | 7, 27, 27 | yes |
| **5** | 32 | **27** | **no** |
| 6 | 64 | 10 087 | yes |
| 7 | 128 | 837 799 | yes |
| 8–24 | 256 … 1.68·10⁷ | > 2·10⁷ (scan exhaustive, deepest `L_1` = 194) | yes |
So `DyadicRealizerFloor 1 6` is **verified for 6 ≤ k ≤ 24**; k = 5 is the single dyadic failure and is excluded by
`k₀ = 6`.  Growth is exponential: `log₂ r_min(N)/N ∈ [0.119, 0.242]` for N ≥ 20.
`max L_1(m)/m = 2.000` at the trivial `m = 1`; excluding it, the max is **1.444 at m = 27** (`L_1 = 39`), and
the ratio decays quickly afterwards (`L_1 ≈ 8 log₂ m` in the record range).  No counterexample to
`r(D)/N < 0.4809` exists below 2·10⁷ (falsification search: negative).

## 4. New structural facts (PROVED (MATH))
* `R_j ≤ 1` for a 1-confined prefix gives `m_j = m·U_j·2^{−R_j} ≥ m/2` — **every state of a confined prefix is
  at least `m/2`**, without assuming non-descent.  This is a lower bound only: `R_j` may be very negative, so the
  states are still unbounded above and collision-free packing (Curry/harmonic) remains inapplicable (as in part 7).
* `L_1` formulation: the target `A = 1/2` reads `L_1(m) < 2m`; `A = 1` reads `L_1(m) < m`; the critical
  coefficient reads `L_1(m) < 2.079 m`.  Empirically `L_1(m) = Θ(log m)`, so the margin is exponential.
* Monotonicity `r_min(N+1) ≥ r_min(N)` holds by prefix restriction (used for the dyadic reduction).

## 5. Status
* PROVED (LEAN): dyadic floor ⇒ 1/2-linear floor ⇒ eventual descent ⇒ (with base check ≤ 31) Collatz.
* PROVED (MATH): prefix locking and the word→seed collapse; `m_j ≥ m/2` on confined prefixes; monotonicity.
* COMPUTATIONAL: dyadic floor verified for 6 ≤ k ≤ 24; record frontier to N = 194; no counterexample.
* REFUTED/unnecessary: backward-interval, MITM and symbolic-minimizer programs over words (they reduce to the
  seed scan); packing arguments still inapplicable.
* OPEN: the floor itself, cleanest form **`L_1(m) < 2m` for all large odd m** (equivalently `r_min(2^k,1) ≥ 2^k`
  for `k ≥ 6`).  This is a stopping-time-type statement: no unconditional bound of any size is known for all m.
* Collatz not proved.  LEVEL 1.
