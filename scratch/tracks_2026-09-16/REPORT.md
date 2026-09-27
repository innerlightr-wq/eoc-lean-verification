# Track A (covering) vs Track B (ratio extremizer) — round of 2026-09-16, part 16

Nothing committed or pushed.  Lean: `EOC/DirectDescent.lean` extended
(`confined_thirteen_ninths_of_nondescent`, `descent_of_L1_lt_thirteen_ninths`); `lake build` 8792 jobs,
standard axioms, no sorry.  Data: `tracks.py` → `TRACKS_2e7.txt`.

## Shared infrastructure
`R_new(N) = min{m odd : L₁(m) > N} = r_min(N+1,1)`, and at a record depth `R_new(N_i) = m_{i+1}`;
`M(X) = max_{odd m ≤ X} L₁(m)` is the inverse staircase.  The record-only reduction
(`linearFloor_of_minimal`, part 15) is PROVED (LEAN), as is the part-8 chain to Collatz.  **New this round:**
`descent_of_L1_lt_thirteen_ninths` — `L₁(M) < ⌊13M/9⌋` for all large odd `M` ⇒ eventual strict descent ⇒
Collatz (using `13/9 = 1.4444 < 3 ln 2 = 2.0794`).  The base check is odd `m ≤ 31` (part 9).

## TRACK A — initial-interval covering: **no mechanism, and not compressible**
Exact structure: each escaping prefix `D` (confined up to its last step, violating at it) is a residue class
mod `2^{S(D)}`; every seed in it escapes by step `|D|`, and `S_j = ⋃_{j' ≤ j} E_{j'}` sieves the odd seeds.
The first survivor at depth `N` is `r_min(N,1)` — the **leftmost surviving branch** of the binary prefix tree.
**Certificate complexity (COMPUTATIONAL).**  A class with `2^S ≤ X` covers several members of `[1,X]`
("shared"); one with `2^S > X` pins a single seed.  Fractions needing a private class:
| X | 3·10⁵ | 2·10⁷ |
|---|---|---|
| private-class fraction | 0.159 | 0.103 |
| escape-modulus tail | `P(S ≤ 16) = 0.804` | `P(S ≤ 24) = 0.897`, `P(S ≤ 30) = 0.938` |
The fraction decays only like `X^{−0.04}` (the survivor density at depth `≈0.63 log₂X` is `2^{−0.06N}`), so a
covering certificate for `[1,X]` needs `≈ X^{0.96}` residue classes: **linear-order, not compressible**.  Hence
no finite/inductive covering object exists, no Jacobsthal-type maximal-gap structure was found (the classes are
nested dyadic, but their union is not of covering type), and **Track A produced no non-circular lemma**.

## TRACK B — seed 27 as global extremizer: **huge margin, target formalized**
Exhaustive to `2·10⁷`:
* **Ratio records are only `3, 7, 27`** — the sequence terminates at 27 with `L₁(27)/27 = 13/9 = 1.44444`.
* **Only two seeds ever have `L₁(m) > m`: 27 (39) and 31 (37)**; only **8** seeds have `L₁(m) > m/2`.
* Shellwise maxima `M_k = max_{2^k ≤ m < 2^{k+1}} L₁(m)` and `M_k/k`:
  | k | 4 | 8 | 12 | 16 | 19 | 20 | 22 | 24 |
  |---|---|---|---|---|---|---|---|---|
  | `M_k` | 39 | 26 | 53 | 94 | 134 | 144 | 190 | 190 |
  | `M_k/k` | 9.75 | 3.25 | 4.42 | 5.88 | 7.05 | 7.20 | 8.64 | 7.92 |
  so `M_k ≈ (5–9)·k`, i.e. **`L₁(m) ≈ 8 log₂ m`**, and `H_k = max L₁/m ≈ M_k·2^{−k}` collapses like `k·2^{−k}`
  (1.44 at k = 4 down to 1.1·10⁻⁵ at k = 24).
* **Margin:** the target needs `M_k < (13/9)·2^k`; the data give `M_k ≤ 190` against `(13/9)2^{22} = 6·10⁶`.
* Relation to stopping time (PROVED (MATH)): for `j < σ(m)` non-descent gives `R_j ≤ j/(3m ln2) ≤ 1` whenever
  `j ≤ 2.07m`, so **`L₁(m) ≥ σ(m) − 1`**: `L₁` dominates the stopping time and the `L₁`-record list refines the
  classical stopping-time record list (it contains 27, 703, 2223, 10087, 35655, 270271, 381727, 626331,
  837799, 1126015, 6649279, 63728127 plus extra entries such as 937, 1249, 13449, 60975).  *(The identification
  with the literature's record sequence is recalled, not verified in-session.)*
Track B needs only **`L₁(m) = o(m)`** — any sublinear bound closes it — and the truth is logarithmic.

## Comparison (Part B39)
| | Track A | Track B |
|---|---|---|
| non-circular lemma this round | none | none |
| computational evidence | certificate size `X^{0.96}` (negative) | `M_k ≈ 8k` vs needed `1.44·2^k` (enormous margin) |
| target formalized in Lean | reduction only | **yes** (`descent_of_L1_lt_thirteen_ninths`) |
| plausible mechanism | not found; covering not compressible | unknown, but the statement needed is merely sublinear |
**Track B is the better route**; Track A is effectively refuted as a proof mechanism (its certificates cannot be
compressed, so it can only re-verify finitely).

## Status
* PROVED (LEAN): `confined_thirteen_ninths_of_nondescent`, `descent_of_L1_lt_thirteen_ninths` (Track B target
  ⇒ Collatz); record-only reduction (part 15); lift gap (part 14).
* PROVED (MATH): `L₁(m) ≥ σ(m) − 1`; the escape-class sieve description.
* COMPUTATIONAL: ratio records `{3,7,27}`; only 27, 31 exceed ratio 1; `M_k ≈ (5–9)k`; certificate complexity
  `≈ X^{0.96}`.
* REFUTED this round: Track A's compressible-covering programme.
* OPEN: `L₁(m) < 13m/9` for `m ≥ 27` (equivalently any sublinear `L₁(m) = o(m)`).
* Collatz not proved.  LEVEL 1.
