# The linear realizer floor: Lean implication + exact record frontier (round of 2026-09-16, part 8)

Nothing committed or pushed.  New Lean: `EOC/DirectDescent.lean` (imported in `EOC.lean`; `lake build` 8791 jobs,
0 errors, axioms `propext, Classical.choice, Quot.sound`, no sorry).  Scripts/data: `scan.py` → `SCAN_2e7.txt`.

## 1. The direct-Collatz implication is now formalized (PROVED (LEAN))
`EOC/DirectDescent.lean`:
* `carryU_le_of_nondescent` — under non-descent, `U_N = ∏(1+1/(3m_k)) ≤ (1+1/(3M))^N`;
* `R_le_of_nondescent` — hence `R_N ≤ N/(3M ln 2)` (via the repo's `orbit_mul_two_rpow_R`);
* `confined_of_nondescent` — **non-descent for `N ≤ 3cM ln 2` steps ⇒ the own word is `c`-confined to depth N**;
* `LinearRealizerFloor c A B N₀` — `∀ odd M, ∀ N ≥ N₀`, word `c`-confined to `N` ⇒ `A·N − B ≤ M`;
* `descent_of_linearFloor` — if `3Ac ln 2 > 1`, every odd `M > mstar` has an iterate `< M`, with
  **`mstar = max((A+B)/(3Ac ln2 − 1), (N₀+1)/(3c ln2))`**;
* `reachesOne_of_linearFloor` — floor + finite base check below `mstar` ⇒ every odd seed reaches 1
  (minimal-counterexample induction, using `orbit_add` and `odd_orbit`).

**Explicit thresholds** (c = 1, B = 0, N₀ = 3): `A = 0.49` gives `3A ln2 − 1 = 0.018926` and **`mstar ≈ 25.9`** —
so a floor `r_min(N,1) ≥ 0.49N` for `N ≥ 3` plus a check of odd seeds ≤ 25 proves Collatz.  At the empirically
observed `A = 0.692`, `mstar ≈ 1.9`.

**liminf suffices** (PROVED (MATH)): `liminf r_min(N,c)/N > 1/(3c ln2)` yields some `A > A_crit`, `B`, `N₀`.
**Sparse scales suffice** (PROVED (MATH)): non-descent to `N` implies non-descent to every `N' ≤ N`, and the
contradiction needs a floor only at some `N' ∈ ((M+B)/A, 3c ln2·M]`.  That window is multiplicatively wide by
the factor `3Ac ln 2 > 1`, so a floor along **any sequence `N_k` with `N_{k+1}/N_k < 3Ac ln 2`** is enough.

## 2. Exact record frontier (COMPUTATIONAL, exhaustive seed scan)
`r_min(N,1) = min{odd m : L_1(m) ≥ N}`, by scanning every odd seed ≤ 2·10⁷ (exact, no word enumeration):
| N | 39 | 50 | 85 | 100 | 144 | 170 | 194 |
|---|---|---|---|---|---|---|---|
| r_min(N,1) | 27 | 703 | 35 655 | 270 271 | 1 859 241 | 6 649 279 | 10 507 503 |
| r_min/N | 0.692 | 14.1 | 419 | 2 703 | 12 911 | 39 113 | 54 162 |
| log₂r_min/N | 0.122 | 0.189 | 0.178 | 0.180 | 0.145 | 0.133 | 0.120 |
* **inf over N ≥ 3 of r_min(N,1)/N = 0.692, attained at N = 39 (the seed 27)** — a margin of only **1.44×**
  over `A_crit = 0.480898`.  For N ≥ 50 the inf is 14.1 (29× margin); for N ≥ 80 it is 419 (872×).
* Since no odd seed ≤ 2·10⁷ has `L_1 ≥ 195`, `r_min(N,1) > 2·10⁷` for all `N ≥ 195`, hence **the linear floor
  `r_min(N,1) ≥ 0.49N` is verified for all `N ≤ 4.08·10⁷`** (and the minimizers are the classical stopping-time
  record seeds 27, 703, 35655, …).
* Growth is exponential: `log₂ r_min/N ≈ 0.12–0.19`, i.e. `r_min ≈ 2^{0.15N}` — astronomically more than the
  linear floor that is needed.
* `c` dependence: for c = 2 and c = 3 the same scan gives `A_crit(c) = 0.240, 0.160` with small-N ratios
  0.25 and 0.143 — the small-N dips (from the seed m = 1) are absorbed by `N₀`, exactly as the theorem allows.

## 3. Structure of the problem (PROVED (MATH))
Exact realizer: `m ≡ −C_N·3^{−N} (mod 2^{S_N})`, `C_{j+1} = 3C_j + 2^{S_j}`, so in ℤ₂
  **ξ_N = −Σ_{j<N} 2^{S_j}·3^{−(j+1)}** and `r(D) = ξ_N mod 2^{S_N}`.
Because the terms have strictly increasing 2-adic valuations `S_j`, the bits of `r(D)` below position `S_j` are
fixed by the first `j` terms.  Hence:
* **`O(log N)` truncation is REFUTED** (Parts VII–IX): `r(D) ≤ AN` says every bit of `ξ_N` in
  `[log₂(AN), S_N)` vanishes — a *top-bit* property of a residue with `Θ(N)` bits.  Knowing `ξ_N mod 2^k` for
  `k = O(log N)` (which the prefix determines) cannot decide it, so no small-modulus DP decides `r(D) ≤ AN`,
  and this is why exact `r_min` was computed by seed scan rather than by word DP.
* Equivalent shrinking-target form: `r_min(N,c) ≥ AN` ⟺ no `c`-confined word has `ξ_N mod 2^{S_N} ∈ [0, AN]`,
  i.e. the normalized anchor avoids the interval `[0, AN·2^{−S_N}]` of exponentially small length.

Not attempted this round (budget): meet-in-the-middle over prefix/suffix, reverse interval propagation,
minimizer complexity statistics, carry automaton reachability, SAT/SMT encodings.

## 4. Status
* PROVED (LEAN): the whole implication chain from a linear floor to "every odd seed reaches 1", with explicit
  constants; plus the non-descent ⇒ confinement bridge.
* COMPUTATIONAL: the exact record frontier to N = 194 / m ≤ 2·10⁷; floor verified for N ≤ 4.08·10⁷;
  tightest ratio 0.692 at N = 39.
* REFUTED: deciding `r(D) ≤ AN` from `O(log N)` low bits.
* OPEN: the floor itself — `r_min(N,1) ≥ 0.49N` for large N (or any sparse-scale version).
* Best proven floor: none (unconditional); `LogCorridor.logFloor_window_bound'` lives in the divergent sector.
* Collatz not proved.  Best rigorous γ = 0; A > 1/α not proved.  LEVEL 1.
