# Logarithmic dangerous windows (round of 2026-09-16, post-bridge, part 2)

Nothing committed or pushed.  Lean: `EOC/DangerousWindows.lean` (imported by `EOC.lean`; `lake build EOC` = 8802 jobs;
axioms `propext, Classical.choice, Quot.sound` for every theorem below).
Scripts/data: `logk2.py` → `logk2.jsonl`, `ANALYZE2.txt` (float scan); `certify.py`/`certify2.py` →
`certify.jsonl`/`certify2.jsonl` (exact integer certification); `delta.py` → `DELTA.txt`; `CONSTANTS.txt`.
(`logk.py` is last round's aborted version; its `apply_int` is reused.)

## PROVED (LEAN)
* `summedPressure_of_dangerousWindows` (unchanged): per-frequency `|bad| ≤ φW + E`, safe windows `≤ 2^{2Kθ_d}` ⇒
  `SummedOddDarkPressure (θ_d + φ(2/5 − θ_d)) C` whenever `log₂(σj/p) + (4/5 − 2θ_d)KE + (4/5)K ≤ C log₂ j`.
* `summedPressure_of_tenth_twoNinths` (new, Variant A): `θ_d = 1/10`, `φ = 2/9`, output **θ = 1/6**, excess
  `(a log₂ j + b)/K` windows, `K ≤ k₁ log₂ j + k₀`, explicit `C = 2 + (3/5)a + (4/5)k₁ + (2 + (3/5)b + (4/5)k₀)/8`.
  Uses `logb_bridge_le` (`log₂(σj/p) ≤ 2 log₂ j + 2`) and `eight_le_logb` (j ≥ 300).  The `K·E = O(log² j)` defect is
  removed: the excess cost is `(3/5)(a log₂ j + b)`.
* `dark_companion`, `nodd_companion` (new): `λ` and `2^m − λ` have the same dark pairs and the same `N_odd`; the u = 0
  shell `{1, 2^m − 1}` reduces to λ = 1.

## Interface comparison (PROVED MATH / arithmetic, `CONSTANTS.txt`)
* A (chosen, formalized): logarithmic excess at no rate cost.
* B: `|bad| ≤ W/5 + E` is covered by A's statement when `E ≤ W/45`; with `K = ⌈2 log₂ j⌉` this absorbs
  0.2 / 2.7 / 33 / 278 windows at j = 400 / 6400 / 10⁵ / 10⁶ — useful only for large j.
* C: `A (log₂ j)² ≤ (0.1745 − 1/6) j` needs j ≥ 2.8·10⁴ (A = 1), 6.5·10⁴ (A = 2), 4.5·10⁵ (A = 10) — worse cutoffs.
* Downstream cutoff of `lowFreqDecay_of_summedPressure` with `C = 3.95` (K ≤ 2 log₂ j + 1, zero excess):
  `(3C/(θ' − 1/6))²` = 2.6·10⁶ at θ' = 0.174 (needs N₀ ≥ 98), 1.1·10⁶ at θ' = 0.178 (N₀ ≥ 131).

## Logarithmic-K scan (COMPUTATIONAL, floats; `ANALYZE2.txt`)
36 environments: j = 400…6400; λ = 1 at t ∈ {1, 7, j/6, j, 5j}, λ ∈ {3, 17}, one Haar unit per j (j = 6400: λ = 1 at
t ∈ {1, j/6, j} + Haar).  K = ⌈A log₂ j⌉, disjoint windows, sup over all start states.
* θ_d = 1/10: A = 1 dangerous fraction max 0.05–0.09, stable in j (0.091, 0.050, 0.069, 0.060, 0.053);
  **A ≥ 2: zero dangerous windows in every environment**.
* Max window rate at A = 2: 0.081, 0.083, 0.076, 0.077, 0.091 (worst: j = 6400, λ = 1, t = 1).
* θ_d = 0.08: A = 1 reaches 0.22–0.25 (near the 0.271 allowance); A = 2 ≤ 0.09 (j ≤ 800), 0 from j = 1600.
* **The fixed-K growth disappears under K ≍ log j.**

## Exact certification (`certify*.jsonl`)
K = ⌈2 log₂ j⌉, every disjoint window, every start state: `val(x) ≤ 2^{K/5}` checked as `G(x)^5 ≤ 2^K D^{5(T−x)}` in
exact integers — precisely the per-window hypothesis of `summedPressure_of_tenth_twoNinths`.
**31 certified runs (30 distinct environments; j = 3200, t = 533 was run twice), 1602 windows, 0 unsafe.**
j = 400/800/1600/6400: λ = 1 at t ∈ {1, 7, j/6, j, 5j} and λ = 17 at t = j/6; j = 3200: the same plus the duplicate.
Exact worst rates 0.0615, 0.0832, 0.0641, 0.0770, 0.0908 at j = 400…6400 (all < 1/10).
j = 12800 was started and stopped (≈ 1 h per environment in pure Python); no float scan at 12800 either.

## Danger density (COMPUTATIONAL, `DELTA.txt`)
Per-(window, start-state) density δ_K at j = 1600: −log₃ δ_K = 3.15, 4.22, 5.08, 6.22, 7.11, 9.39 at K = 2…12 (Haar);
λ = 1 the same within noise; 0 observed from K = 12/16.  Fit δ_K ≈ 3^{−(2.2 + 0.5K)} (HEURISTIC).  With ~j start
states per window, a window is dangerous with probability ≈ j δ_K, small once K ≳ 2 log₃ j ≈ 1.26 log₂ j — the
observed transition between A = 1 and A = 2.  For A = 2 the heuristic dangerous fraction is ≈ j^{−0.58}.

## Ternary structure (PROVED MATH)
* Shift action: Dark(λ, m = σ+1+t, r, z) ⇔ 108 |centered(λ 2^{−(σ+1+t−z)} mod 3^{2r+2})| < 3^{2r+2} (up to the reciprocity
  term, exact once 2^{t+1} > 108λ).  Changing t translates every exponent a = σ+1+t−z by the same amount; a window at
  block r₀ reads exponents a ∈ [t + σ + 1 − cap, t + σ + 1 − x₀] at moduli 3^b, b ∈ [2r₀+2, 2r₀+2K]: all translates of
  the critical line a ≈ t + α(j − b).  Not a single cyclic group (the modulus varies with the row).
* Depth: from a start state x₀ the window's columns are x₀ < z ≤ cap(2r₀+2K−1) and all its rows read the one residue
  λ2^{−a₀}·2^{z−x₀} (a₀ = m − x₀); deciding darkness with margin 2^{−g} needs ternary digit positions
  [b₀ − L, b₀ + 2K) with L = ⌈(Δ + log₂ 108 + g)/log₂ 3⌉, Δ = z_max − x₀ ≤ h₀ + ⌈α(2K − 1)⌉.  Hence
  D(K, h₀, g) ≤ 2K + ⌈(h₀ + 2αK + log₂ 108 + g)/log₂ 3⌉ ≈ 4K + 0.631 h₀ + 4.26 + 0.631 g; cells at the threshold need
  unbounded depth (so exact classification is by margin, not by fixed depth).
* Polynomial scale: K = 2 log₂ j ⇒ D ≈ 8 log₂ j ⇒ 3^D ≈ j^{8 log₂ 3} = j^{12.7} per start state (the geometric weights
  make distant columns negligible; h₀ enters only through the start column).

## Ceiling
The row-sum ceiling ½log₂(1 + 2q) → 0.39877 and ξ ≡ 2^m windows reach 0.398–0.399 (sup-norm, previous round):
**no universal improvement below ≈ 0.3988 in this norm** (REFUTED for 1/3, 3/8).

## Not done
Discrete-log occupancy M_D(L), anticlustering, conflict graph, large-u averaging, character sums (the λ = 1 data show
no dangerous windows at A ≥ 2, so the needed arithmetic statement is currently the pointwise local one).
