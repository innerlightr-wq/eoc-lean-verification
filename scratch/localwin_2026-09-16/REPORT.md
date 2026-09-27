# LocalWindowPressure at logarithmic scale (round of 2026-09-16, part 5)

Nothing committed or pushed.  New Lean: `EOC/LocalWindow.lean` (imported in `EOC.lean`; `lake build` 8790 jobs,
0 errors, axioms `propext, Classical.choice, Quot.sound`, no sorry).  Scripts/data here: `exhaust.py` →
`EXHAUST.txt`; `perstate.py`, `density.py` → `DENSITY.txt`; `local_state.py`; `PAYOFF.txt`.

**Summary.**  The local-window route is now quantitatively specified and, in its per-state form, genuinely local:
a window of `K` pair blocks started at a fixed state depends on the environment through only `O(K)` ternary
digits (verified: 16 leading digits of the deep part pin `P_K` to 10⁻⁴), so each condition lives modulo
`3^{O(K)} = J^{O(1)}`.  Exhaustive worst-window scans give `P_K^max` and the exact payoff table shows the route
tolerates `θ` up to ≈ 0.14 (s = 3, β = 0.3), comfortably above the measured `P_K^max = 0.105` at `K = 6log₂J`.
The Haar density of bad local states decays at `κ ≈ 0.29` bits/block, which *predicts* the observed maxima.
No stop condition fired.  What remains is a digit-pattern-avoidance statement for the orbit `2^{j}λ mod 3^{O(K)}`.

## 1. Definitions and the chain (Parts I–IV) — PROVED (LEAN) for the abstract mechanism
`M_K(r0,S;ξ,s) = E*_{S}[ s^{#black odd cells in blocks r0..r0+K-1} ; confined through the window ]` (killed P*
pair chain; exactly the object computed by `exhaust.py`).  `P_K = (1/2K)log₂M_K` is in **bits per step** because a
pair block is two steps — the normalization in `LocalWindowPressure` is `2Kθ`, not `Kθ` (checked against the
`OddDarkPressure` normalization `(1/J)log₂E[s^{N_odd}] ≤ θ`, `J = 2R`).
Lean (`EOC/LocalWindow.lean`): `ker`/`val` (layered transfer kernel and mass), `ker_add`/`val_add`
(Chapman–Kolmogorov), **`val_le_pow_of_window`**: if every `K`-layer window from any anchor and any state has
mass ≤ `M`, then a `W·K`-layer sum is ≤ `M^W`; `val_le_of_window_rem` adds the remainder; **`logBookkeeping`**:
`Total ≤ (2^{2Kθ})^W·s^K` and `J = 2(WK+ρ)` give `(1/J)log₂Total ≤ θ + K·log₂s/J`.  **No 1/log J loss**: `W = n/K`
windows each contributing `2^{2Kθ}` give exactly `2^{θJ}`.  The bridge from `val` to `∑_P s^{N_odd}` (the layered
representation of the confined word set) is not formalized; `OddBlack.sum_class_prod` already supplies the
per-class factorization.

## 2. Exhaustive worst windows (Parts V–VII) — COMPUTATIONAL (exact, all anchors and all confined states)
`P_K^max` (s = 3), `K = c₀⌊log₂J⌋`:
| c₀ | J = 100 | 200 | 400 | 800 |
|---|---|---|---|---|
| 2 | 0.1250 | 0.1902 | 0.2073 | 0.2060 |
| 4 | 0.0870 | 0.1105 | 0.1272 | 0.1280 |
| 6 | 0.0567 | 0.0820 | 0.0926 | 0.1053 |
| 8 | — | 0.0692 | 0.0805 | 0.0906 |
| 10 | — | 0.0601 | 0.0706 | 0.0769 |
Worst anchors sit anywhere in the bulk (r₀/R = 0.2–0.84) with start-state headroom 20–343; the worst windows at
J ≥ 400 have a black cell in every row of the band.  Sampled scans (previous round) underestimate these by
0.01–0.02.  At smaller tilts: s = 2 gives 0.061 and s = 1.5 gives 0.032 at c₀ = 4 (J = 800).

## 3. Locality: how many digits a window inspects (Parts XIII–XX) — PROVED (MATH) + COMPUTATIONAL
With `A = ξ2^{S₀} mod 3^{b₀+2K}` split as `A = A_low + 3^{b₀}H` (`b₀ = 2r₀+2`), for `l ≤ 2K`
  **U_l = ⟨ 2^{ΔS_l}(U₀ + H) / 3^l ⟩**,  `U₀ = centered(A_low)/3^{b₀} ∈ [−1/2,1/2]`,
so a window at a **fixed start state** depends on ξ only through the real `U₀` and the `2K` new digits, and `U₀`
is needed only to precision `η·3^l/2^{ΔS_l}` (= O(η) for typical paths, `3^{−O(K)}` in the worst case).
Verified (`perstate.py`, J = 200, 400): keeping `n` leading digits of the deep part changes `P_K` by
≤ 6·10⁻² (n = 0), 10⁻² (n = 8), 10⁻⁴ (n = 16), 0 (n = 32).  **So each (window, state) condition is a condition
modulo `3^{O(K)}`, polynomial in J when `K ≍ log J`.**
Caveat (important): the states of one window are linked by `U₀(S+1) = ⟨2U₀(S)⟩`, so the *sup over all states*
of one window still involves Θ(J) digits.  Locality is restored by treating the `O(J/K)` windows × `O(J)` states
as `O(J²/K)` separate local conditions — each modulo `3^{O(K)}`, all on the same orbit `λ2^{j} mod 3^{O(K)}`.

## 4. Bad local states: density and the union bound (Parts XXI–XXIII, XXXVII) — COMPUTATIONAL
Arbitrary local residues do **not** satisfy the bound (a residue with `U ≈ 0` makes every cell black, `M_K = s^K`,
`P_K = log₂s/2 = 0.79`), so Part XX's optimistic case fails.  Haar density of bad per-state windows
(`density.py`, J = 200, 400 samples per K):
| K | P(P_K ≥ 0.08) | κ | P(P_K ≥ 0.10) | κ | P(P_K ≥ 0.12) | κ |
|---|---|---|---|---|---|---|
| 6 | 0.170 | 0.426 | 0.103 | 0.548 | 0.073 | 0.631 |
| 8 | 0.165 | 0.325 | 0.105 | 0.406 | 0.060 | 0.507 |
| 12 | 0.133 | 0.243 | 0.080 | 0.304 | 0.043 | 0.380 |
| 16 | 0.110 | 0.199 | 0.043 | 0.285 | 0.020 | 0.353 |
| 20 | 0.075 | 0.187 | 0.018 | 0.292 | 0.0025 | 0.432 |
κ = −log₂P/K settles near **0.29 bits/block at θ = 0.10** (0.19 at θ = 0.08).  With `K = c₀log₂J` the density is
`J^{−κc₀}`; the union bound over `O(J²/K)` conditions needs `κc₀ > 2`, i.e. **c₀ ≳ 7** at θ = 0.10.
Consistency check: the same model predicts the exhaustive maxima — `θ*` solves `κ(θ*)c₀ = 2`, giving 0.09 at
c₀ = 8, against the measured 0.0906 at J = 800.  The true environment's worst window behaves exactly like a Haar
sample with `J²/K` trials, which also explains the mild upward drift in J and predicts it saturates.

## 5. Exact payoff (Parts XLIV–XLV) — PROVED (MATH) arithmetic on measured inputs
Requirement: rate = min( c_shape(g+β), β·log₂((1+s)/2)/2 − θ ), N₀ = 4, g = 0.1.  Largest admissible local
exponent `θ_max(β,s) = β·log₂((1+s)/2)/2 − c_shape(0.1+β)`:
| s \ β | 0.15 | 0.20 | 0.25 | 0.30 | 0.35 |
|---|---|---|---|---|---|
| 1.5 | −0.017 | 0.001 | 0.019 | 0.035 | 0.050 |
| 2 | 0.002 | 0.027 | 0.051 | 0.074 | 0.096 |
| 3 | 0.034 | 0.068 | 0.103 | 0.137 | 0.168 |
| 4 | 0.058 | 0.101 | 0.144 | 0.185 | 0.225 |
Combined rate at the measured exponents (s = 3): θ = 0.077 → **0.0282**, 0.0906 → 0.0249, 0.105 → ≈0.0215,
0.128 → 0.0150 bits/step.  So the route is robust: even the c₀ = 4 value (0.128) still pays, and c₀ = 6 (0.105)
gives ≈ 0.021.  η is kept at 1/54 (Part XLVI).

## 6. Arithmetic form of the remaining lemma (Parts XXIV–XXXIX)
All local states arising anywhere in the problem are orbit elements `λ2^{j} mod 3^{cK}` for `j` in an interval of
length Θ(J) (since the environment is `λ2^{−m}` and the states are `ξ2^{S}`).  The local modulus is
`3^{cK} = J^{O(1)}` but its period `2·3^{cK−1} = J^{4.75c₀}` still dwarfs the orbit segment Θ(J): full-period
local averaging (Part XXVII) is unavailable, and the interval/period ratio `J^{1−4.75c₀}` is far below every known
equidistribution range for powers of 2 (which need interval ≥ modulus^{c}).  What the reduction buys is that the
statement is now **local and pattern-based**: bad local states are characterized by their `O(K)` ternary digits,
with density `J^{−κc₀}`, so the lemma reads:
> **no window of `O(log J)` consecutive ternary digits of `λ2^{j}` (j in an interval of length Θ(J)) exhibits a
> bad pattern** — a pattern class of density `J^{−κc₀}` with `κc₀ > 2`.
Stewart's bound (log m/log log m nonzero digits) and Lagarias's 3-adic results remain far too weak; the local
Subspace/Baker route is still not applicable (heights are polynomial in J but the number of conditions is too
large and the patterns are shallow).

## 7. Status
* PROVED (LEAN): layered transfer kernel, Chapman–Kolmogorov, window product bound (no 1/K loss), remainder
  handling, exponent bookkeeping (`EOC/LocalWindow.lean`).
* PROVED (MATH): per-state locality formula for `U_l`; the union-bound restructuring; the payoff arithmetic.
* COMPUTATIONAL: exhaustive `P_K^max` tables; κ ≈ 0.29; the Haar-model prediction of the exhaustive maxima;
  per-state digit-sensitivity.
* REFUTED (this round): the hope that *arbitrary* local residues satisfy the bound (Part XX).
* OPEN: `LocalWindowPressure` for the true orbit; equivalently the digit-pattern-avoidance statement above.
* Best rigorous γ = 0; A > 1/α not proved; LEVEL 1.
