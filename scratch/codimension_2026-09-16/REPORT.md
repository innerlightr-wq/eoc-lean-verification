# Dangerous windows as ternary codimension (round of 2026-09-16, post-dangerous-windows)

Nothing committed or pushed (commit 5aa96a2 is pushed; PR #9 open, Lean CI green).  No Lean changes this round.
Scripts: `haar_bound.py` → `HAAR_BOUND.txt` (exact rational matrices), `mc_check.py` / `mc_check2.py` →
`MC_CHECK*.txt` (Monte Carlo sanity check).  **Positive stop condition 2 fired** (rigorous Haar density bound).

## Target (unchanged, PROVED LEAN)
`DangerousWindows.summedPressure_of_tenth_twoNinths`: for every low frequency, all but (2/9)W + (a log₂ j + b)/K of
the K-block windows must satisfy `val(geoW p q oddW) (iK) K y ≤ 2^{2K/10}` from every state y.  Window mass from x₀:
val(x₀) = E*[∏_r 3^{B_r}; survive], B_r = own odd choice eligible (d₂ ≥ 2, z+1 ≤ cap) and dark.

## Codimension (PROVED MATH)
1. Dark (d = 1/108, Lean predicate, low λ) ⇒ Tao-black at η = 1/54 ⇔ balanced-ternary digits b−3, b−2, b−1 of the
   phase residue ξ·2^{z−m} mod 3^b vanish (exact equivalence; 54|y| < 3^b ⇔ top three balanced digits zero).
2. Given ξ mod 3^{b−2}, for every unit multiplier (every column), digits b−2, b−1 are uniform on {−1,0,1}²:
   **two fresh digits per block**, independent of the P* path.
3. Consecutive odd rows share exactly one digit position: X_r := [digit b_r − 3 = 0] is determined by ξ mod 3^{b_r−2},
   and P(X_{r+1} = 1 | past) = 1/3.
4. Hence P(B_r | past) ≤ X_r·q/9 (q ≤ 37/100), and the worst coupling of (B_r, X_{r+1}) gives the 2-state LP operator
   M_β = [[(q/9)3^β + 1/3 − q/9, 2/3], [1/3, 2/3]] with E_ξ[val(x₀)^β] ≤ eᵀM_β^K 1 (β ≥ 1; Jensen over the
   substochastic path weights, Fubini over the ξ-independent path).
5. Markov: **P_ξ(val(x₀) > 2^{K/5}) ≤ eᵀM_β^K 1 / 2^{βK/5}**:
   β = 1: ρ = 1.028950, eᵀM^K 1 ≤ 1.0546 ρ^K ⇒ δ_K ≤ 1.055·3^{−0.1002 K};
   β = 2 (exact): ρ = 1.135854 ⇒ δ_K ≤ C·3^{−0.1364 K}  (best real β ≈ 1.8: c = 0.1396).
   Explicit β = 1 values: K = 16: 0.181; K = 24: 0.075; K = 26: 0.060; K = 32: 0.031.
The deterministic form (dangerous ⇒ some path has ≥ 0.126K black eligible cells, each fixing 3 digits of which 2 are
fresh) is true but its density conversion needs a union over exponentially many paths; the moment method avoids that.
Black count is used only one-way (dangerous ⇒ structure), never as a sufficient statistic.

## Strength (PROVED MATH arithmetic on the bound)
* Rigorous c = 0.100–0.136 vs empirical ≈ 0.5 (previous round's δ_K fit).
* Union over ≈ 0.585 j start states: Haar-dangerous windows vanish asymptotically for K = A log₂ j when
  A > 1/(c log₂ 3): 6.30 (c = 0.100), 4.64 (c = 0.136); empirical success at A = 2 needs c ≳ 0.32.
* So the rigorous Haar bound does not yet cover K = ⌈2 log₂ j⌉; it covers K = ⌈7 log₂ j⌉ (with the formal chain's
  K ≤ k₁ log₂ j + k₀ interface this only changes C).

## Sanity check (COMPUTATIONAL)
J = 400, K = 8, true d = 1/108 eligible-dark predicate, Haar ξ: 720-sample per-state means max 1.155 (1357 pairs),
average 1.096, versus the bound 1.325.  (A 24-sample run showed 1.388 at one pair; re-estimated with 720 samples it is
1.111 ± 0.011 — sampling noise.)

## Not done (stop condition)
Haar density ≠ orbit density: nothing here is about the specific environment λ·2^{−m}.  Common-depth lift, exact
small-K exponent sets, gap / difference structure, occupancy, faster large-j engine, j = 12800, the LowFreqDecay
wrapper, and large-u averaging were not started.
