# OddDarkPressure: are the adversarial local units realizable? (round of 2026-09-16, part 18b)

Nothing committed or pushed; no Lean file touched.  Scripts: `step1_unit.py` … `step6d_certificate.py`,
`common.py`, `adv_copy.py`; raw outputs `UNIT.txt`, `SIEVE.txt`, `LAMBDA3.txt`, `SCAN_*.txt`,
`DEPTH.txt`, `CYCLE.txt`, `CONCAT*.txt`, `CERT.txt`, `REFINE.txt`, `*.json`.
Main-session cross-check: the λ = 1 and λ = 5 values below reproduce `cw2_2026-09-16`'s published
0.099 / 0.119 (J=400, K=32), so the pipeline agrees with the earlier round where they overlap.

## 1. The premise was wrong: the "adversary" is already a 3-adic unit — REFUTED

`oddblack_2026-09-16/adversary.py` never chooses black cells freely: it builds `ξ` one balanced-ternary
digit at a time, so its output **is** a genuine 3-adic unit (`ξ mod 3 = 1`).  Reproduced
byte-identically (`E[N_odd]/R = 0.3016`, max depth 7.99); worst unit at `J=400, K=32` is
`r₀ = 5, S = 15, CW = 0.374218`, driven by one deep triangle at blocks 5–10.

## 2. Exact 3-adic sieve — the pattern is REALIZABLE

Level-by-level exact integer sieve over `b = 12,…,138`, all 2802 cell constraints:
survivors mod `3^138` = **exactly 16 residues (10 of them units)**, density `2.2982·10⁻⁶⁵`; explicit
realizing residue recorded in `SIEVE.txt`.  From `b = 62` on the count is pinned at 16 while `3^b`
grows, i.e. the pattern *forces* every further digit.
**So the adversarial units are not a formal artefact.**

## 3. …but not at low frequency — the gap is ~61 orders of magnitude

2 is a primitive root mod `3^k`, so for *every* unit `λ` there are exactly 10 shifts `δ` mod `2·3^137`
realizing the pattern — the required `δ` has ~66 digits (density `2.15·10⁻⁶⁵`).  At the `m` the window
dictates: exhaustive over `1 ≤ |λ| ≤ 500`, `δ = 0 … 2·10⁶` (776 680 pairs surviving level 1) gives
**zero** realizations; deepest consecutive-level prefix **7 of 64**.  The smallest `λ` realizing it at
`δ = 0` has **64 decimal digits**.

## 4. The true low-frequency environment itself exceeds `θ_max = 0.137` — NEW, and it refutes the fixed-K sup certificate

23 λ values, `J ∈ {200,400,800}`, `K ∈ {16,24,32}`, 9159 windows:

| K | max CW over true windows | where | vs `θ_max = 0.137` |
|---|---|---|---|
| 16 | **0.1835** | λ=11, J=400, r₀=94 | **+34 %**, 103/3373 windows over, 19 different λ |
| 24 | **0.1454** | λ=5, J=400, r₀=133 | +6 %, 3 windows (λ ∈ {5,10,20}) |
| 32 | **0.1414** | λ=7, J=800, r₀=205 | +3 %, 1 window |

Cross-checks: λ=1 → 0.0987/0.0996 and λ=5 → 0.1192/0.1217 at J=400,K=32 (= the earlier round's
0.099 / 0.119); λ ∈ {1,2,4,8,16} give identical values (same ×2-orbit), as they must.
**A sup-over-windows fixed-K certificate therefore fails for the true environment, not only for the
adversary** — robustly at K=16, marginally at K=32.

## 5. Triangle depth is NOT the discriminator — doubly refuted

`P(window max depth ≤ 8) = 0.9811` in the true environment: depth ≤ 8 is the norm, and the adversary's
record unit sits at depth 7.99.  At the same depth cap the adversary gets **2.04×** the best true
window.  The exact separator found is a **configuration**, not a size:

> longest run of consecutive blocks whose readable row begins with an all-black prefix of length ≥ 6

adversary: 6 blocks in a row (max prefix 12); **every tested λ (1,5,7,11,101,1025): 0 blocks**.

## 6. Concatenation, refractory period, cycle means

* **Exact sieve:** the 6-block driver **cannot repeat at period 6, 7, 8 or 9** (empty at level
  `b = 24,26,28,38`); first feasible period is **10**.
* **PROVED (MATH), period 6:** lifting `ξ` by one digit pair `c` moves `y(x,b+2) = y(x,b) + 3^b d_x`.
  The driver forces `|y(x,22)| < 3²²/54`; a repeat needs x = 23…28 black and x = 29 white at level 24,
  but black at level 24 means `|y| < 3²²/6`, while any `d_x ≠ 0` moves `y` by `≥ 3²² = 6×` that
  threshold ⇒ `d_x = 0` for x = 23…28 ⇒ `c = 0` ⇒ cell (29,24) is black.  Contradiction; 0 of 9 digit
  pairs admissible.  *(This is why the adversary's own block 11 is the all-white row.)*
  **A deep triangle forces the next pair block to be either a continuation or entirely white on the
  overlap** — a deterministic balanced-ternary statement with no environment hypothesis.
* **Cycle means (`Λ(r₀,L) = (1/2L) log₂ max_S M_L`)** at J=400:

| environment | L=16 | L=64 | L=128 | L=190 |
|---|---|---|---|---|
| adversary (depth ≤ 8) | 0.5132 | 0.3937 | 0.3434 | **0.3281** (0.3359 at r₀=1) |
| true λ=1 | −0.0011 | 0.0205 | 0.0328 | **0.0382** |
| λ=5 | 0.0391 | 0.0391 | 0.0455 | **0.0432** |
| λ=1025 | 0.0940 | 0.0693 | 0.0576 | **0.0541** |

  * Repeated-driver cycles (periods 10, 12, 16) **contract**: `Λ = 0.0919 / 0.0810 / 0.0612 < 0.137`.
  * **But a genuine depth-≤8 3-adic unit sustains 0.328–0.336 over 190 blocks** — so there is **no
    general contraction theorem**; the record unit is a small-`r₀` / short-row effect, while the full
    greedy adversary scales its triangles to the growing rows.
  * **For the true low-frequency environments the long products contract with a factor 2.5–4 of
    margin** (0.033–0.054 vs 0.137), even though single K=16 windows reach 0.1835.

## 7. Consequences for the programme

1. Triangle-depth control is dead at the CW level (98.1 % of true windows are already in the
   adversary's depth range).
2. A fixed-K sup certificate is refuted **for the true environment** (K ≤ 32).  Either K grows with J,
   or `θ_max` is re-derived, or the certificate becomes **window-averaged** — the last has margin.
3. The residual gap is explicitly arithmetic and now quantified: the exceptional set of one window is
   **16 balls of radius `3^{-138}`**, and what is needed is that `λ2^{-m}` with small `λ` misses them.
   Equivalently: *`λ2^{-m}` never produces ≥ 6 consecutive blocks each beginning with an all-black
   prefix of length ≥ 6*.
4. New Lean-able lemma: the §6 refractory certificate.

Genericity is **not** claimed: the true-environment numbers *match the generic benchmark
computationally*.  Rigorous `γ` still 0.  **LEVEL 1.**

## Known discrepancy

The agent's prose summary quoted "J=800, λ=1 and λ=5 both 0.1044"; `SCAN_800.txt` records 0.0973 and
0.0940 for those (stride-sampled).  The file values are the ones used above.
