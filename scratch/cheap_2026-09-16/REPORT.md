# Cheap words are statistically generic; the record-only reduction (round of 2026-09-16, part 14)

Nothing committed or pushed.  New Lean: `EOC/LiftGap.lean` (`leastRealizer_mono`, `liftDigit_eq_zero_of_gap`,
`leastRealizer_eq_of_gap`); `lake build` 8792 jobs, standard axioms, no sorry.  Data: `cheap.py`.

## 1. Lift gap and stabilization — PROVED (LEAN)
`LiftDigits.leastRealizer_succ` gives `r_{j+1} = r_j + 2^{S_j+1}·τ_j`, so one nonzero lift costs a full
`2^{S_j+1}`.  Hence (new, formalized):
* `leastRealizer_mono`: prefix least realizers are nondecreasing;
* `liftDigit_eq_zero_of_gap`: `r_N ≤ B < 2^{S_j+1}`, `j < N` ⇒ `τ_j = 0`;
* `leastRealizer_eq_of_gap`: therefore `r_j = r_N` for all such `j` — **the representative stabilizes**.
So an ε-cheap word of length `N` is, after `O(log r_N)` letters, literally the orbit word of the single integer
`r_N`.  This proves the Parts XLI–XLVII proposal — and confirms the Part XLVIII audit: it is exactly the
record-frontier identity `r_min(N,c) = min{m : L_c(m) ≥ N}`, hence **no new consequence** (searching cheap words
= searching small seeds).

## 2. Cheap words are statistically generic — REFUTES the rigidity programme (COMPUTATIONAL, exact)
By §1 the cheap-word dataset is exactly the set of `L₁`-record seeds' words.  For all 21 records up to 2·10⁷:
| m | L₁ | log₂m/L₁ | freq(d=1,2,3,≥4) | p(2) | p(4) | p(8) | longest repeat | border |
|---|---|---|---|---|---|---|---|---|
| 27 | 39 | 0.122 | .615 .256 .077 .051 | 11 | 26 | 32 | 6 | 1 |
| 703 | 50 | 0.189 | .660 .220 .060 .060 | 14 | 27 | 43 | 6 | 0 |
| 35 655 | 85 | 0.178 | .624 .271 .047 .059 | 15 | 39 | 77 | 8 | 0 |
| 270 271 | 102 | 0.177 | .637 .235 .078 .049 | 16 | 47 | 91 | 9 | 0 |
| 1 859 241 | 144 | 0.145 | .618 .236 .097 .049 | 16 | 60 | 125 | 11 | 3 |
| 10 507 503 | 194 | 0.120 | .660 .180 .098 .062 | 19 | 74 | 168 | 11 | 0 |
Tilted-geometric reference (the generic confined law): `.631 .233 .086 .050`.
* **Digit frequencies match the generic law** across every record (d=1: 0.618–0.693 vs 0.631).
* **Factor complexity is near-maximal**: at N = 194, `p(8) = 168` against the ceiling `N−7 = 187`; `p(k)` grows
  essentially linearly in the window count, nowhere near `p(k) ≤ k`.  So Morse–Hedlund/periodicity rigidity is
  **inapplicable**: cheap words are *high*-complexity.
* **Longest repeated factor is 6–12 ≈ 2log N/h**, exactly the random-word value; longest border ≤ 4.
So there is **no structural signature** distinguishing cheap words from generic confined words, and the
dichotomy of Part XII ("repetitive ⇒ periodic machinery, or complex ⇒ separation") has no repetitive branch.
Consistent with part 13: the explicit periodic families cost ≥ 1 bit/step, while these generic-looking words
cost only 0.12–0.21 bits/step.

## 3. Record-only reduction — PROVED (MATH)
`r_min(N,1)` is a step function that changes only at record seeds, and `r_min(N,1) = min{m : L₁(m) ≥ N}`.
Therefore the floor `r_min(N,1) ≥ AN` for all large `N` is **equivalent** to
  **`L₁(m) ≤ m/A` for every sufficiently large record seed `m`**,
the binding case being `N = L₁(m)`.  The required floor per record (`A = m/L₁(m)`):
| m | 27 | 703 | 937 | 2 223 | 35 655 | 270 271 | 837 799 | 1 126 015 |
|---|---|---|---|---|---|---|---|---|
| `m/L₁` | **0.692** | 14.06 | 18.37 | 41.17 | 419.5 | 2 650 | 6 252 | 8 043 |
So the constraint binds **only at m = 27** (margin 1.44× over `A_crit = 0.4809`); every later record has margin
≥ 29×, growing to 10⁴.  Record jumps `m_{i+1}/m_i` are small (1.06–4.5 after the first, 26 at 27→703) and
plateaus are short, so the staircase is dense — the quantifier shrinks to ~21 seeds up to 2·10⁷ but the
mathematics is unchanged.

## 4. Status
* PROVED (LEAN): lift gap, monotonicity, stabilization (`EOC/LiftGap.lean`).
* PROVED (MATH): the record-only reduction (floor ⟺ `L₁(m) ≤ m/A` on records).
* COMPUTATIONAL: cheap words are generic in digit law, factor complexity, repeats and borders; the record
  staircase and its per-record required floor.
* REFUTED this round: cheap-word rigidity/low-complexity (and with it the repetitive branch of the dichotomy);
  "stabilization gives a new consequence" (it is the record identity).
* OPEN: unchanged — `L₁(m) < Cm` for some `C < 3 ln 2`, now equivalently *on record seeds only*.
* Collatz not proved.  LEVEL 1.
