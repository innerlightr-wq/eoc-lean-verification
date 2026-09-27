# Round 4: crediting several white pairs per block (2026-09-17)

Nothing committed or pushed. Branch `research-sparse-visits-2026-09-16`, HEAD `14dea46`, working tree dirty
(new modules untracked).

Labels: PROVED (LEAN) · PROVED (MATH) · EXTERNAL THEOREM · COMPUTATIONAL · HEURISTIC · CONJECTURAL ·
REFUTED · OPEN.

**One line:** the single-white-pair contraction has been replaced by a contraction that counts every white
pair in the block. The new bound needs no `N₀`, uses the exact `1−cos πd`, and needs **no new
arithmetic input**. The explicit Lean family's exponent saving grows from `I₀/(2·10⁹) ≈ 3.97e−11` to
`I₀/(2·10⁶) ≈ 3.97e−8`, a factor of 1000. The result is still **conditional on the same arithmetic
frontier**. It is not a proof of Collatz.

---

## A. Repository and build

1. Repo: `~/GitHub/eoc-lean-verification`, Lean 4 + Mathlib; the build uses the pinned toolchain.
2. Build at the start of the round: `lake build EOC` passed with 8810 jobs.
3. Build at the end of the round: `lake build EOC` passed with **8813 jobs** (3 new modules).
4. New modules (untracked): `EOC/MultiWhiteContraction.lean` (542 lines), `EOC/MultiWhiteChain.lean`
   (146), `EOC/FrontierFamilyMulti.lean` (552).
5. `EOC.lean` now also imports these three modules, placed after `EOC.FrontierFamily` (uncommitted
   change).
6. The new files contain no `sorry`, `admit`, `axiom`, `opaque` or `native_decide`; grep confirms this.
7. Earlier-round modules (ShapeRegion, FrontierRegion, ConditionalChain, ShellCounts, FinalChain,
   BinomialTail, FrontierFamily) are unchanged.

## B. How the old one-pair contraction worked

8. A block `B = pairB` is an interval of pair indices. Its factor is `W = ‖Σ_{z∈B} e(φ_z)‖/|B|`.
9. The old argument used a single white pair `z, z+1` with `distZ(φ_z − φ_{z+1}) ≥ d`. That pair gives
   `‖e(φ_z)+e(φ_{z+1})‖ = 2|cos(π·Δ)| ≤ 2 − 2(1−cos πd)`. So `W ≤ κ = 1 − 2(1−cos πd)/|B|`, with
   `|B| ≤ N₀` on shape-good blocks.
10. It then used `1 − cos πd ≥ 2d²`, which loses a factor `(1−cos πd)/(2d²) = 2.467` at `d = 1/108`, to
    get `κ^{2k} ≤ exp(−8kd²/N₀)` over `k` contracting blocks.
11. Bad blocks were handled with the Markov base `(1+3)/2`, which uses `n` blocks at rate
    `ν·log₂2 ≥ θ'+γ`. What remained was `k` blocks, with `k + n ≤ K_b`.
12. Scalar constraint (`FinalChain.ExplicitPairData`): `γ j ln2 ≤ 8 k d²/N₀`, and
    `K_b + 0.31j + σ/(N₀+2) ≤ j/2`.
13. The old family had `N₀ = 133`, `k/j = 0.00652`, and `n/j = 0.1687`. This gives
    `γ ≤ 4.85e−8`; the family used `γ = 4e−8`. Then `hnum` needs `γP ≥ 27`, which forces
    `P = 6.75·10⁸`.
14. The limit came from two sources at once:
    * the `1/N₀` factor: each contracting block gains only `8d²/N₀ ≈ 5.2e−6`;
    * the budget: small `N₀` inflates `σ/(N₀+2)`, and Markov uses up almost all of `K_b`.

## C. Multi-pair math

15. **Disjoint-pair lemma** — PROVED (MATH), PROVED (LEAN) `MultiWhite.norm_sum_le_pairs`. Let `S` be a
    set of white pairs whose members are separated (`z∈S ⇒ z+1∉S`). Then
    `‖Σ_B e(φ)‖ ≤ |B| − 2|S|(1−cos πd)`. Proof: apply the triangle inequality to each disjoint pair
    separately.
16. Pairs of the same parity are automatically separated. So with `M = max(#white even, #white odd)`,
    `W ≤ 1 − 2c₀M/|B|`, where `c₀ = 1−cos πd`
    (`wfac_le_parity`, `wfac_le_multi`) — PROVED (LEAN).
17. Squaring gives `W² ≤ exp(−4c₀M/|B|)` (`wfac_sq_le_exp`) — PROVED (LEAN).
18. Taking pairs of both parities, i.e. all white edges, would need a norm bound for overlapping pairs:
    OPEN (see item 26). Using one parity loses at most a factor 2 in `M`.
19. q-pair or longer runs: a run of `q` consecutive white edges could give more than `q` separate
    pairs. Not pursued, because the one-parity count already removes the `N₀` loss. Status: OPEN,
    and the likely gain is only a constant factor.

## D. White density from the dark count (no new hypothesis)

20. On eligible pairs, white and dark are exact complements: `#white + D = #Elig`
    (`card_white_add_dark`) — PROVED (LEAN).
21. `|B| ≤ 2M + D + 1` (`two_mul_M_ge`) and, for `|B| ≥ 2`, **`|B| ≤ 3M + 2D`**
    (`three_M_add_two_D_ge`) — PROVED (LEAN).
22. Key per-block inequality: `exp(ln2·([|B|≥2] − 3M/|B|)) ≤ 1 + 2D/|B|` (`exp_block_le`) —
    PROVED (LEAN). Many dark pairs are paid for by the pressure moment. Few dark pairs force at least
    `(|B|−2D)/3` white pairs of one parity.
23. `1 + 2D/|B|` is exactly the per-block factor of the odd-dark pressure moment:
    `Σ_c nCls·∏(1+2D/|B|) = ∏(|B|+2D) = Σ_P 3^{N_odd}` (`block_sum_eq`, `class_moment_eq`) —
    PROVED (LEAN).
24. So white density follows deterministically from the quantity the existing frontier already
    bounds (`SummedOddDarkPressure`, θ = 1/6). **No "white fraction" assumption was added.** The
    arithmetic hypothesis is still `FrontierRegion.PowerOfTwoDangerousWindowSparsityAt`, with the
    same `K_win`, `d = 1/108` and `a = b = 2` as the round-3 family.
25. Each class splits three ways (`class_split`, PROVED (LEAN)):
    * shape-bad (fewer than `K_b` shape-good blocks): `ShapeTail`, with any `N₀`;
    * pressure-heavy (`Σ 3M/|B| < K_b − Λ` over good blocks): Markov with weight `2^{Λ}` against the
      moment;
    * the rest: contracts by `exp(−(4c₀/3)(K_b − Λ))`.

## E. Locality, clusters, spectral

26. Locality/cluster lemma (dark pairs cluster, so white runs are long): **not attempted**, OPEN. The
    proved bound does not need it.
27. Spectral/Gram version, crediting all white edges including overlapping ones, e.g. through
    `‖Σe(φ)‖² = |B| + 2Σ_{z<z'} cos(2π(φ_z−φ_{z'}))`: HEURISTIC. It gains at most a factor about 2 over
    item 16; OPEN.
28. Safe-block white matching: same-parity edges form a matching by construction, so item 16 is
    already this. No extra structure used.
29. No new computational experiments this round. The per-block inequalities are proved in Lean, so no
    COMPUTATIONAL claim is made.

## F. Averaging audit

30. The old proof already averaged over classes (Σ_c nCls·∏W²), not over the worst path. Confirmed
    by rereading `avg_prod_sq_le` and `FinalChain`.
31. The new proof keeps the averaging (`avg_prod_sq_le_multi`). Only the pressure-heavy classes pay
    a Markov factor, and it is paid against the averaged moment `Σ_P 3^{N_odd}`, which the frontier
    bounds per frequency shell.
32. No worst-path step was introduced.

## G. Lean chain (all PROVED (LEAN); axioms: `propext, Classical.choice, Quot.sound` only)

33. `MultiWhite.avg_prod_sq_le_multi (hshape : ShapeTail …)`:
    `Σ_c w∏W² ≤ ρ₁|T| + 2^{−Λ}Σ_P 3^{N_odd} + |T|·exp(−(4c₀/3)(K−Λ))`.
34. `MultiWhite.lowFreqDecay_multi` gives `LowFreqDecay` from `hshape`, the pressure bound
    `≤ 2^{u+1}M|T|` per shell, and `ρ₁ + M2^{−Λ} + exp(−(4c₀/3)(K−Λ)) ≤ C2^{−γj}`.
35. `MultiWhiteChain.lowFreqDecay_of_sparsityAt_multi` connects the frontier to `LowFreqDecay`
    (constant 4, `M = 2^{θ'j}`, `Λ = (θ'+γ)j`).
36. `MultiWhiteChain.ExplicitPairDataMulti` is the explicit per-pair data. Compared with
    `ExplicitPairData`: no `k, n, ν`, no `2 ≤ N₀`, no `d ≤ 1/2`. The rate condition becomes
    `γ j ln2 ≤ (4(1−cos πd)/3)(K_b − (θ'+γ)j)`.
37. `MultiWhiteChain.weightedFourier_of_explicitMulti` and
    `MultiWhiteChain.exceptional_bound_of_frontier_and_scalar_multi`: same conclusion as the `FinalChain`
    version.
38. `FrontierFamilyMulti.one_sub_cos_ge : 4226/10⁷ ≤ 1 − cos(π/108)`, via `Real.cos_bound`.
39. `FrontierFamilyMulti.pairData_fam`, `exceptional_bound_of_frontier_family`, `A_ge`.
40. **`FrontierFamilyMulti.exceptional_bound_family_exponent`**: for every `m ≥ 1000`, if the frontier holds
    on the good pairs,
    `#(E₀ ∩ [0,2^K)) ≤ (3/2)·(2^K)^{H₂(1/α) − I₀/(2·10⁶)}`,
    that is, exponent `binEntropy(α⁻¹)/log 2 − I₀/2000000`.
41. `#print axioms` for items 33–40: `[propext, Classical.choice, Quot.sound]` only.

## H. Quantitative payoff

42. New family: `P = 1 080 000`, `j₀ = Pm`, `N = (P+1)m`, `x* = 4m`, `K = b₀(j₀)+1`,
    `N₀ = P−2` (only enters the budget term), `K_b = 205198m` (≈ 0.18999j), `θ' = 1/6 + 1/1000`,
    `γ = 1/60000`, `d = 1/108`, `ε = κ = 1`, `m ≥ 1000`.
43. Per-block contraction exponent:
    * old: `8d²/N₀ = 5.16e−6` for each of `k` blocks;
    * new: `4c₀/3 = 5.64e−4` for each of `K_b − Λ` excess units. That is 109× per unit.
44. Contraction factor: old `κ = 1 − 2c₀/N₀` with `N₀ = 133`. New effective factor per unit:
    `exp(−4c₀/3) ≈ 1 − 5.64e−4`, independent of block size.
45. γ cap:
    * old ≈ `4.85e−8` (used `4e−8`);
    * new ≈ `1.82e−5` (used `1.667e−5`);
    * ratio ≈ 374.
    Breakdown: `(c₀/2d²)=2.47` × `N₀=133` × `((K_b−Λ)/j = 0.0223)/(k/j = 0.0065) = 3.4` × `1/3`.
46. `hnum` exponent: the old family needed `γP ≥ 27` (poly `2^{15m}` + `4^t`); the new one needs
    `γP ≥ 18` (poly `2^{6m}` + `4^t`, with `32P²m³ ≤ 2^{6m}` for `m ≥ 10`).
47. **ε** (exponent saving below `H₂(1/α) = 0.9499555`):
    * old `I₀/(2·10⁹) = 3.97e−11`;
    * **new `I₀/(2·10⁶) = 3.97e−8`**.
    This meets the targets `ε > 1e−10`, `ε > 1e−9` and `ε > 1e−8`. PROVED (LEAN), conditionally.
48. The structural ceiling with this engine is `ε ≈ I₀/(Pα)` with `P ≳ 18/γ_max`, so
    `ε_max ≈ 5.3e−8`. The family is at about 75% of it.
49. New bottlenecks, in order:
    1. the shape budget margin `K_b/j − θ' ≈ 0.19 − 0.1677 = 0.023`;
    2. the tiny `c₀ = 1−cos(π/108) ≈ 4.2e−4`, which is set by the frontier's `d`;
    3. the counting cost `4^t` together with `2^{6m}` in `hnum` (`γP ≥ 18`).
    Pushing θ' toward 1/6 or improving the shape budget (0.31j) would give linear gains. Increasing
    `d` requires a stronger frontier.

## I. Logic

50. Implication proved in Lean: the frontier `PowerOfTwoDangerousWindowSparsityAt` on all good pairs
    of the family implies the exceptional-set bound with exponent `H₂(1/α) − I₀/(2·10⁶)`. The frontier
    is still **OPEN**. The external inputs (Tao-style `λ*`, `I₀`) are the same as in round 3,
    EXTERNAL THEOREM as before.
51. The white-contraction improvement is unconditional math (PROVED (LEAN)). It changes only the
    constants of the conditional chain, not its hypotheses.
52. Not claimed: any unconditional bound on `E₀`, any statement about all Collatz orbits, or that
    `ε` is optimal.

## J. Verdict

53. **The white-contraction bottleneck is resolved at the level of constants.** The `1/N₀` loss and
    the `2d²` trig loss are gone, and the Markov/contraction split no longer fights over a tiny `k`.
    `γ` is 374× larger and `ε` is 1000× larger, and the round-4 target `ε > 1e−8` is reached in Lean.
    The dominant remaining losses are the shape budget margin and `d`, which comes from the frontier.
    The main open problem is still the arithmetic frontier.
54. **EOC LEVEL:** conditional exceptional-set power saving, formalized end to end in Lean, with
    explicit `ε = I₀/(2·10⁶) ≈ 4·10⁻⁸`, conditional on the power-of-two dangerous-window sparsity
    frontier (OPEN). Not a proof of Collatz.
