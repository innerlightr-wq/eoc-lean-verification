# Excursion shape cost: persistence is nearly free (round of 2026-09-16, part 13)

Nothing committed or pushed; no new Lean.  Data: `shape.py` (exact; seed scan to 3·10⁶ plus exact word-level
realizers for periodic families).  **Stop condition 1 fired** (persistence adds essentially no seed cost beyond
depth).

## 1. Magnitude/direction coordinates (PROVED (MATH))
`X_j = log₂(m_j/m) = log₂U_j − R_j`, and under minimal-counterexample non-descent with `j ≤ 2m`,
`0 ≤ log₂U_j ≤ 2/(3 ln 2) = 0.9618`, so `−R_j ≤ X_j ≤ −R_j + 0.962`.
`ΔX_j = log₂(1 + 1/(3m_j)) + α − d_{j+1}`, hence **sign classification**: `d = 1` is outward
(`+0.585 + tiny`); `d ≥ 2` is inward for every odd `m_j ≥ 3` (`α − 2 + log₂(10/9) ≤ −0.263`); `m_j = 1` is the
fixed point (`ΔX = 0`).  With `V_± = Σ(±ΔX)_+`, trivially `X_N − X_0 = V_+ − V_−`, and `V_+` is the weighted
count of `d = 1` steps, `V_−` of `d ≥ 2` steps.

## 2. Persistence is (nearly) free — the round's decisive measurement (COMPUTATIONAL, exact)
`r_stay(Q,L)` = least seed staying below `−Q` for `L` consecutive steps inside its 1-confined prefix:
| Q\L | 1 | 2 | 3 | 4 | 6 | 8 | 10 |
|---|---|---|---|---|---|---|---|
| 2 | 27 | 27 | 27 | 27 | 27 | 27 | 27 |
| 4 | 27 | 27 | 27 | 27 | 27 | 27 | 27 |
| 6 | 27 | 27 | 1 819 | 1 819 | 1 819 | 4 255 | 4 255 |
| 8 | 4 255 | 4 255 | 4 255 | 4 255 | 9 663 | 9 663 | 26 623 |
In `log₂`: at `Q = 8`, `12.05 → 13.24 → 14.70` as `L = 1 → 6 → 10`, i.e. **≈ 0.3 bits per extra step of
persistence**, and at `Q ≤ 4` the cost is exactly **flat**.  So an additive law `log₂m ≥ c₁Q + c₂L` with a
useful `c₂` is **not supported**: duration *at fixed depth* is cheap.  (The depth coefficient from part 12 was
`c₁ ≈ 0.79`, over ten times larger per unit.)

## 3. Periodic families cost ≥ 1 bit per step (COMPUTATIONAL + PROVED (MATH) mechanism)
Exact least realizers of `P^k` (word level, `r = −C_N3^{−N} mod 2^{S_N}`):
| pattern | log₂r/L | log₂r/(−R_N) |
|---|---|---|
| `(1)` all-ones | **1.000** | **1.710** |
| `(1,2)` | 1.500 | 17.66 |
| `(1,1,2)` | 1.23–1.32 | 4.9–5.2 |
| `(1,1,1,2)` | 1.20–1.22 | 3.57–3.63 |
| `(1,2,1,1,2)`, `(1,1,2,1,2)` | 1.20–1.40 | 6.5–7.6 |
Mechanism: a periodic word's realizer class converges 2-adically to the fixed point `x = C/(2^S − 3^n)`, and
`r(P^k) = x mod 2^{kS}` grows like `2^{kS}` unless `x` is a non-negative integer — which happens only for the
trivial cycle.  Hence `log₂r/L ≥ S/N ≥ 1` for periodic words, with equality exactly for all-ones
(`x = −1`, whose 2-adic expansion is all ones, giving `r = 2^N − 1`).  **All-ones is extremal on both axes.**
But genuinely cheap words are *aperiodic*: the orbits of small seeds achieve `log₂r/L ≈ 0.15`
(`r_min(N) ≈ 2^{0.15N}`), an order of magnitude below any periodic family.  So periodicity is expensive and the
periodic analysis does not bound the general case.

## 4. Seed 27 has no repeatable motif (COMPUTATIONAL)
Its 39-step word is `121111221211211123112121111131114224311`: 24 steps with `d = 1`, 15 with `d ≥ 2`,
`max d = 4`, `min R = −6.719`, final `R = −0.814`.  The `d = 1` run profile
`[1,4,0,1,2,3,0,2,1,5,3,0,0,0,0,2]` shows **no repeated structural unit**, so there is nothing to pump: 27 looks
like a finite arithmetic accident rather than a member of a family (consistent with it extremizing every
frontier measured so far while all successors fall away sharply).

## 5. Where this leaves the endgame
Writing the cost per unit of *total* duration, the only coefficient that matters is the one in
`log₂m ≥ c₂·L₁(m)`: **any `c₂ > 0` gives `L₁(m) = O(log m) ≪ 2m` and hence Collatz** — far more than the linear
floor needs.  But that coefficient is exactly the `r_min` growth rate, i.e. the open problem itself; the shape
decomposition (depth, persistence, area, reversals) does not isolate a cheaper sub-target, because the cheap
words are precisely the orbits of small seeds.

## 6. Status
* PROVED (MATH): magnitude/direction identities and the sign classification; the periodic-word cost mechanism;
  the all-ones benchmark (`r = 2^N − 1`, `log₂r/L = 1`, `log₂r/(−R) = 1.710`).
* COMPUTATIONAL: `r_stay` table (persistence nearly free); periodic-family ratios; seed-27 anatomy.
* REFUTED this round: the depth+duration additive shape-cost programme (`c₂` is empirically ≈ 0.3 bits/step at
  `Q = 8` and 0 at shallow depth, not the ≥ 1 that a useful theorem needs); "27 is a pumpable motif".
* OPEN: unchanged — `L₁(m) < Cm` for some `C < 3 ln 2`, equivalently `r_min(2^k,1) ≥ 2^k`.
* Collatz not proved.  LEVEL 1.
