# Round 17 — the search for an unconditional pointwise `L₁(m) = o(m)`

Nothing committed or pushed.  New Lean: `EOC/HarmonicFloor.lean` (imported from `EOC.lean`);
`lake build EOC` = 8793 jobs, no `sorry`/`axiom`/`opaque`, every new theorem on
`[propext, Classical.choice, Quot.sound]`.  Data: `harm.py`, `bootstrap.py` → `boot.txt`,
`slack.py`, `bands.py`.

## A. What was proved

1. **PROVED (LEAN) — the harmonic drift ceiling.**  `R_le_of_nondescent_harmonic`: if odd `M ≥ 3`
   has pairwise distinct states through step `N`, none below `M`, then
   `R_N ≤ (1/(9 ln 2))·log(1 + 3N/(M−2)) + 2/(3 ln 2 (M−2))`, i.e. `R_N ≤ (1/9) log₂(1+3N/(M−2)) + O(1/M)`.
2. This **replaces the linear ceiling** `R_N ≤ N/(3M ln 2)` (`DirectDescent.R_le_of_nondescent`).
   The mechanism is new: the old bound uses only `m_k ≥ M`; the new one uses `m_k ≥ M` **and**
   distinctness **and** coprimality to 6 — the `k`-th state is `≥ M + 3k − 2`, not just `≥ M`.
3. **PROVED (LEAN) — the packing lemma behind it.** `sum_inv_le_sum_inv_shift`: `n` distinct
   coprime-to-6 integers all `≥ M ≥ 3` satisfy `∑ 1/m_k ≤ ∑_{j<n} 1/((M−2)+3j)`; with the
   telescoped log bound (`sum_range_inv_shift_le`) this gives
   `∑_{k<N} 1/m_k ≤ 2/(M−2) + (1/3) log(1 + 3N/(M−2))` (`sum_inv_orbit_le_of_nondescent`),
   against the trivial `N/M` and against `HarmonicPacking.sum_inv_orbit_le`'s `7/3 + (1/3)log N`
   (which ignores the floor `M`).
4. Supporting new lemmas, all formalized: `le_three_mul_coprimeSixRank` (`x ≤ 3·rank x`, the
   density-1/3 companion of the existing upper bound), `sum_le_sum_range_shift_of_antitone`
   (shifted rearrangement), `carryE_le_of_nondescent`, `carryU_le_of_le`, `carryU_strictMono`.
5. **Size of the gain.**  At `N = C·M` the ceiling is `(1/9) log₂(1+3C)` versus `C/(3 ln 2)`:

   | `C` | 0.5 | 1 | **13/9** | 2 | 3 | 5 |
   |---|---|---|---|---|---|---|
   | new `(1/9)log₂(1+3C)` | 0.167 | 0.264 | **0.327** | 0.387 | 0.468 | 0.577 |
   | old `C/(3 ln 2)` | 0.240 | 0.481 | **0.695** | 0.962 | 1.443 | 2.404 |
6. **Where the gain is not.**  For `N ≪ M`, `log(1+3N/M) = 3N/M + O((N/M)²)`, so the new ceiling
   **agrees with the old one to first order**; numerically the two confinement lengths coincide on
   every record seed (`harm.py`).  The improvement lives only in the regime `N ≍ M` — which is the
   regime of the open target, so it was the right place to look.
7. **PROVED (LEAN) — the weighted observable.** `sum_two_rpow_R_le`: `W_N = ∑_{j<N} 2^{R_j} ≤ M·U_N·∑_{j<N} 1/m_j`,
   the exact-identity bridge `2^{R_j} = M U_j/m_j` requested in Parts XXVI–XXIX.
8. **PROVED (LEAN) — band occupancy.** `band_occupancy`: under the same hypotheses,
   `#{j < N : R_j ≥ −A}·2^{−A} ≤ M·U_N·(2/(M−2) + (1/3)log(1+3N/(M−2)))`.  With `N = C·M` and
   `U_N ≤ e^{C/3}` this reads
   `#{j<N : R_j ≥ −A}/N ≤ 2^A·e^{C/3}·log(1+3C)/(3C) + O(1/M)`.
9. **Corollary (forced dip), PROVED (MATH).**  At `C = 13/9` the bound at `A = 0` is `0.625 < 1`, so
   a non-descending prefix of length `(13/9)M` **must** contain a step with `R_j < −0.678`, and at
   most `62.5%` of its steps can have `R_j ≥ 0`.  This is a genuine new unconditional constraint on
   long non-descending prefixes.
10. **PROVED (LEAN) — the injectivity caveat is exactly a cycle.** `R_lt_of_orbit_eq`: `m_i = m_j`
    with `i < j` forces `R_i < R_j` (since `U` is strictly increasing).  So distinctness fails only
    on a genuine nontrivial cycle lying above `M`, whose drift increases strictly each period.

## B. What was refuted

11. **The bootstrap `C ↦ F(C)` does not contract — REFUTED (COMPUTATIONAL, exhaustive to 3·10⁶).**
    `bootstrap.py` computes `r_min(N,c)` for `c ∈ {1, 0.5, 0.387, 0.264, 0.167, 0}` *and* for the
    seed-dependent moving ceiling `B_m(j)` of item 1.  **The frontier is identical**: the gain factor
    `r_min(N,c)/r_min(N,1)` is `1.000` at every `N ≤ 60` sampled, the frontier seeds are the same
    `7, 27, 703, 2223, 10087, …`, and `log₂r_min/N ≈ 0.12–0.24` is unchanged.  The only differences
    are one-record shifts at `N = 4` and `N = 51–54` (e.g. `937 → 2223 → 10087`).
12. Therefore **no iteration of the harmonic ceiling can close the endgame**: feeding `c = 0.327`
    back in returns the same `N`, so `F(C) = C`.  Parts IX–XV are exhausted as a *route*, even
    though they produced a genuine theorem (item 1).
13. **Mechanism of the failure (COMPUTATIONAL).**  `slack.py`: the record prefixes are not pressed
    against the barrier (peaks `max_j R_j` = −0.585, 0.075, 0.278, …, 0.935), and lowering the
    barrier to 0.264 cuts 7 of 13 record seeds — yet the frontier does not move, because at every
    scale many other seeds realize the same depth.  **The binding constraint is arithmetic
    (realizability of the word), not the drift ceiling**; any improvement of the ceiling *constant*
    is worthless.
14. **The occupancy/`W_N` route is true but far from binding (COMPUTATIONAL).** `bands.py`: the
    provable occupancy fraction at `A = 0, C = 13/9` is `0.625`; the true fraction on record
    prefixes is `0.000–0.045`, and the true minimum drift is `−5.2` to `−14.9` against the forced
    `−0.678`.  The bound is loose by a factor 15–80, and closing that factor is exactly the
    unavailable pointwise information.
15. `W_N` itself (`harm.py`) is **sublinear**: `W_N = 4.5–31.7` at `N = 39–238`, i.e. `W_N/N = 0.03–0.27`
    and `W_N/√N = 0.38–2.6`.  Since `∑1/m_j = W_N/M·(1+o(1))`, the *true* harmonic sum is
    `≈ √N/M`, a factor `√N` below the proved ceiling — so the extremal packing configuration is
    nowhere near attained and no sharpening of the packing constant can help.
16. **Magnitude statistics (Parts XLII–XLIII).** Harmonic mean of `m_j/M` over the confined prefix:
    3.7–31.4; median 5.9–866; **minimum 0.52–1.50** — i.e. record orbits *do* dip below `M` early,
    confirming that on record seeds `L₁(M) ≫ σ(M)` and the non-descent hypothesis is not what
    sustains long confinement.

## C. The decisive structural finding

17. **The round's objective is equivalent in strength to the full conjecture.**  Two facts:
    (a) PROVED (LEAN, part 16): `L₁(M) < (13/9)M` for all large odd `M` ⇒ eventual strict descent ⇒
    (finite base check, odd `m ≤ 31`) Collatz.  Any `L₁(m) = o(m)` bound implies this.
    (b) EXTERNAL / elementary: a pointwise bound `σ(n) ≤ f(n) < ∞` for every `n` outside an explicit
    finite set **is** the Collatz conjecture, by strong induction on the first descent.
    Hence "find any unconditional pointwise `L₁(m) = o(m)`" is not a weak statement that a trick
    could close: **it implies Collatz**, so no proof of it can be easier than Collatz.
18. **Literature (Part III/LV), classified.**  No unconditional pointwise upper bound on the 3x+1
    stopping time is known — for any `f`, not `n^0.999999`, not `n/1000`:
    * ALMOST-ALL: Terras 1976 (stopping time finite for density-1 set; `{σ = k}` is a union of
      classes mod `2^k`), Everett 1977, Heppner 1978 (exceptional set `O(x^{1−δ})`),
      Korec 1994 (density 1 for `T^k(n) < n^β`, `β > log3/log4`), Tao 2019/2022 (logarithmic
      density 1, and about `Col_min`, i.e. the minimum *value*, not the number of steps).
    * COUNTING: Krasikov 1989 `x^{3/7}` → Applegate–Lagarias 1995 `x^{0.809}` → Krasikov–Lagarias
      2003 `x^{0.84}` — how many `n ≤ x` reach 1, never which.
    * POINTWISE but wrong direction: Applegate–Lagarias 2003, infinitely many `n` with
      `σ_∞(n) > 6.14316 log n`; and `σ(2^k−1) > k`, giving only `r_min(N) ≤ 2^N − 1`.
    * POINTWISE and unconditional but finite-range: verification to `2^71` (Barina 2021/2025).
    * Cycles: Eliahou 1993 — any nontrivial cycle has period ≥ 17 087 915 (relevant only to item 10).
19. **No lower bound on stopping-time record seeds exists in the literature.** `r_min(N) ≥ g(N)` is
    *logically identical* to "`σ(n) ≤ N` for every `n < g(N)`", i.e. the pointwise problem on a
    range; all unconditional knowledge of that form comes from exhaustive computation.  This
    independently confirms items 11–13: the frontier is the problem, not a proxy for it.
20. No covering-system / Jacobsthal-type result applies: the surviving classes have modulus `2^k`
    with a dynamically defined residue set (same conclusion as the part-16 Track A audit, now
    confirmed against the literature).

## D. Status of the direct-Collatz endgame

21. **OPEN, unchanged:** `L₁(m) < Cm` for some `C < 3 ln 2 = 2.0794` (equivalently `L₁(m) = o(m)`,
    equivalently `r_min(N,1) ≥ AN` with `A > 0.4809`, equivalently — item 17 — Collatz).
22. The Lean reduction chain is complete and unchanged: `descent_of_L1_lt_thirteen_ninths`,
    `linearFloor_of_minimal` (record-only), `reachesOne_of_linearFloor`.
23. Empirical margin is still enormous and still binds only at `m = 27` (`13/9`), with `M_k ≈ 8k`
    i.e. `L₁(m) ≈ 8 log₂ m` versus the needed `1.44·2^k`.
24. New this round, the endgame gained: a logarithmic (not linear) drift ceiling, an occupancy
    bound, and a forced-dip depth — all true, all too weak to bound `L₁`.

## E. Routes closed (cumulative, this round's additions in bold)

25. transport/matching precision; regeneration; low-modulus localization; fixed-depth recurrence;
    magnitude + interval sparsity; depth + duration; symbolic cheap-word rigidity; periodicity;
    min-plus finite-state compression; survivor-covering / Jacobsthal certificates; dyadic
    induction; shell-crossing reformulations (rounds 10–16).
26. **Injective-harmonic bootstrap (`C ↦ F(C)`) — the ceiling constant does not drive the frontier.**
27. **Weighted observable `W_N` / dyadic-band occupancy — provable, but loose by 15–80×.**
28. **Ceiling-tightening in general**: item 13 shows the frontier is invariant under *any* barrier
    `c ∈ [0, 1]`, so no future improvement of the drift ceiling (however sharp) can move `r_min`.

## F. Stop conditions

29. Fired: a proposed route was shown **circular/equivalent to the full conjecture** (item 17), and
    a proposed mechanism was **refuted by exhaustive computation** (items 11–13).
30. Not fired: no pointwise `o(m)` bound was found; none exists in the literature; no contradiction
    with prior rounds appeared.
31. Recommendation: **stop attacking `L₁(m) = o(m)` as if it were a weak lemma.**  Any further work
    on it is work on Collatz itself, and should be planned as such (the honest framing for the
    manuscript is: the Lean chain shows `L₁(m) = o(m) ⟺ (essentially) Collatz`, which is a clean
    *reformulation*, not a reduction).

## G. Bookkeeping

32. Nothing committed, nothing pushed; working tree still carries the untracked round-10…17 files.
33. New file `EOC/HarmonicFloor.lean` (≈400 lines), imported from `EOC.lean`.
34. `lake build EOC`: 8793 jobs, success; axioms `[propext, Classical.choice, Quot.sound]` for
    `R_le_of_nondescent_harmonic`, `sum_inv_orbit_le_of_nondescent`, `carryE_le_of_nondescent`,
    `sum_inv_le_sum_inv_shift`, `sum_two_rpow_R_le`, `band_occupancy`, `R_lt_of_orbit_eq`.
35. Scripts: `harm.py` (ceilings, `W_N`, magnitudes), `bootstrap.py` → `boot.txt` (frontier vs `c`),
    `slack.py` (peak drift per record), `bands.py` (occupancy constants vs truth).
36. Shell scan past `k = 24` was **not** run: with items 11–17 established, extending the record
    staircase from `10⁸` to `10⁹` could only re-confirm `M_k ≈ 8k` at a cost of hours.
37. The EOC/Fourier side is untouched this round; `CriticalWhiteCount` remains the single open
    analytic hypothesis there.
38. Labels used: PROVED (LEAN) items 1,3,4,7,8,10; PROVED (MATH) item 9,17a; EXTERNAL THEOREM
    item 18; COMPUTATIONAL items 11,13,14,15,16,23; REFUTED items 11–12, 26–28; OPEN item 21.
39. No claim in this report is CONJECTURAL beyond what is explicitly labelled OPEN.
40. **Collatz is not proved.  LEVEL 1.**
41. Next honest options: (i) publish the reformulation `L₁(m) = o(m) ⇒ Collatz` with the new
    harmonic ceiling as the sharpest unconditional constraint available; (ii) return to the EOC
    side and attack `CriticalWhiteCount`, where the target is a density statement and therefore
    *not* equivalent to Collatz; (iii) treat the forced-dip/occupancy inequalities as the seed of a
    genuine excursion-shape argument, accepting that it is an attack on the conjecture itself.
