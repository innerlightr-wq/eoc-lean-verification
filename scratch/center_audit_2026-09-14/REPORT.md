# Algebraic balance vs. statistical center vs. dynamical equilibrium — audit report

Repository: `/Users/eliasdejesus/EOC` (`origin` = `github.com/innerlightr-wq/eoc-lean-verification`, branch `main`). All new work is under `scratch/center_audit_2026-09-14/` (this report plus four Python scripts). The only change to a tracked file is a one-line sign correction in `README.md`'s exact drift identity (§1, below) — no other tracked file, and no Lean source, was modified.

**Scope discipline followed:** no `lake build` was run (frozen files and existing Lean theorems untouched, and none added); no broad seed search, model training, or long-running computation (worst case here: ~8,200 seeds × ≤65 steps, 0.3s). This is a bounded research investigation, not a proof attempt.

**Status of results in this report — read the labels, not just the numbers.** Two categories of claim appear below and should not be conflated:

- **Exact / closed-form** (the cylinder reference law of §2, its exact `Geom(2)` next-digit distribution, the finite-horizon DP of §4.0–4.1, and the coordinate identities of §1 and §3): these are either algebraic derivations checked against the repo's own exact definitions, or deterministic computations with explicitly bounded, stated truncation error (e.g. §4's `EMAX=80`, `DMAX=90` tails). They hold **as stated**, independent of sample size.
- **Finite real-orbit observations** (§4.2–4.3, and the seed-by-seed checks in §1): these are empirical statistics over a specific, modest, explicitly-recorded sample (odd seeds `1..16383` for §4; five named seeds elsewhere), with sparsity flagged wherever a cell has few observations. They are **evidence at this sample size**, not asymptotic or pointwise claims, and are never asserted to hold for all seeds or in any limit.

**Lean formalization is explicitly deferred to a later session on a Linux machine** (this session's environment is macOS; no `lake build` was attempted here for that reason as well as the scope reasons above). Nothing in this audit is claimed as a Lean theorem, and no proposed identity (§5, "Next steps") has been formalized. **This audit does not resolve, and does not claim to move, the repository's actual open pointwise frontier** — `CriticalCrossing`, any tier of EOC, or the almost-all-to-pointwise amplification gap all remain exactly as OPEN as before this session; see §5's closing paragraph.

## Files inspected

- `README.md`, `RESEARCH_CHECKPOINT_2026-09-05.md`, `docs/RESEARCH_CHECKPOINT_2026-09.md`, `CHANG_CYLINDER_SCRATCHPAD.md` (first ~150 lines)
- `EOC/Basic.lean`, `EOC/ValuationWord.lean`, `EOC/Carry.lean`, `EOC/Confinement.lean` (first ~120 lines), `EOC/RealizerLift.lean` (first ~200 lines)
- Headers of `scratch/audit_round.py`, `scratch/discrepancy_identity.py`, `scratch/m37b_lift_audit.py`, `scratch/m37c_relational_audit.py`, `scratch/transport_audit.py`, `scratch/transport_audit2.py`, `scratch/induced_burst_map.py`, `scratch/memory_and_bridges.py`, `scratch/tcc2.py` (topic check only, to avoid duplicating M37/Chang-burst work — no overlap found: those concern realizer-lift circularity and Chang burst-map structure, orthogonal to this audit's drift/confinement question)
- `git log --oneline -40`, `git log -3 --stat`

No `AGENTS.md` exists anywhere under `/Users/eliasdejesus` (checked at every repo root and two levels down); proceeded without it.

## Files created

All under `scratch/center_audit_2026-09-14/` (this repo does not track `scratch/` in a way that requires cleanup instructions; left in place per the other M37 scratch files' precedent, and **not deleted**, unlike the M33–M36 scripts which had their own explicit deletion instruction — no such instruction applies here):

- `part1_identity.py` — exact orbital coordinate `A_N`
- `part2_cylinder.py` — cylinder reference ensemble
- `part3_phase.py` — depth/phase coordinate change
- `part4_compare.py` — small reproducible comparison (DP reference vs. real orbits)
- `REPORT.md` — this file

Commands: `python3 part{1,2,3,4}_identity_or_topic.py` (Python 3, stdlib + `mpmath` for part 3's high-precision floor checks). All four run in well under one second combined.

---

## 1. The exact orbital coordinate `A_N`

**Repo conventions confirmed exactly** (`EOC/Basic.lean`, `EOC/ValuationWord.lean`, `EOC/Confinement.lean`):
`a(m) = v2(3m+1)`, `T(m) = (3m+1)/2^a(m)`, `S_N = Σ_{j<N} d_j`, `alpha = log2 3`, `R_N := S_N − alpha·N` (`EOC/Confinement.lean:12`, `R d j = s d j - j*alpha`).

**Derived here** (hand derivation, cross-checked by exact float computation and by exact bigint carry identity — `part1_identity.py`):

```
m_{j+1}/m_j = 3/2^{d_j} · (1 + 1/(3 m_j))
=> log2(m_N/m0) = N·alpha − S_N + E_N = −R_N + E_N        (exact)
=> A_N := R_N − E_N = log2(m0/m_N)
```

This matches the task's stated identity and `Confinement.lean`'s own sign convention for `R`.

**Negative/corrective finding (documentation only, no Lean claim affected):** README.md's prose states *"log₂(m₀/m_N) = N·alpha + E_N − S_N"*. Algebraically the right-hand side equals `−R_N + E_N`, but the derivation above shows `−R_N+E_N` is `log2(m_N/m0)`, not `log2(m0/m_N)` — the README sentence has the ratio inverted relative to its own stated RHS. `part1_identity.py`, §1a asserts this mismatch explicitly for five real seeds (3, 7, 27, 703, 10087) and it holds every time. **This is PROSE ONLY** — no Lean theorem states this identity (the README itself says so: "not currently packaged as a single named Lean theorem"), so nothing formally verified is affected. It is exactly the kind of coordinate-sign slip the task warns about. **Corrected in this commit**: `README.md` line 78 now reads `log₂(m_N / m₀) = N·alpha + E_N − S_N` (RHS unchanged, only the named ratio flipped) — a one-line prose fix with zero Lean risk; no Lean theorem, build, or dependency was touched.

**Exact certification, integers only:** `A_N`'s sign (descent/return/growth) was certified using the exact bigint carry identity from `Carry.lean` (`2^{S_N}·m_N = 3^N·m0 + C_N`, `q_eq_C`/`iter_carry_eq`), never a float log test — `part1_identity.py` §1b. All five test seeds through N=60: seeds 3, 7, 27, 703 have already hit the accelerated map's fixed point `T(1)=1` (`m_N=1 < m0` ⇒ exact `A_N>0`, certified by plain integer comparison); seed 10087 is still growing (`m_N=43193 > m0` ⇒ exact `A_N<0`). No seed returned to its exact starting magnitude (`A_N=0`) in this window — expected, since that requires a genuine cycle return.

**One-step recursion** `ΔA_N = d_N − alpha − log2(1+1/(3m_N))` verified exactly (to float precision) for all five seeds, every step (`part1_identity.py` §1c).

**Elementary fact worth stating explicitly (no code needed):** `R_N = 0` is *unreachable* for any `N ≥ 1`, for any word: `S_N` is a nonnegative integer, `alpha·N` is irrational for integer `N ≥ 1` (else `alpha` would be rational), so `S_N = alpha·N` is impossible. **`R_N = 0` is a coordinate reference line that no orbit, real or idealized, can ever exactly sit on** — this is already implicit in the README's "critical Sturmian boundary" discussion but is worth stating plainly here: *"multiplicative balance" `R_N=0` is a normalization artifact, not an attainable dynamical state.* By contrast `R_N = E_N` (i.e. `A_N=0`, exact return to the starting magnitude) is attainable in principle — it is exactly what a nontrivial cycle, or arrival at the trivial fixed point, would produce — but it depends on the entire orbit history through `E_N`, not on a fixed threshold independent of the trajectory. **This is the cleanest form of the requested distinction: algebraic balance (`R_N=0`) is a fixed coordinate fact independent of dynamics and never attained; the actual return condition (`R_N=E_N`) is dynamically meaningful but seed-and-history-dependent, not a fixed "center."**

**What this coordinate clarifies / cannot add:** `A_N` is confirmed to be exactly `log2(m0/m_N)` — a re-expression of the orbit's own magnitude ratio, nothing more. It is **not** an independent predictive variable: computing `A_N` at step `N` requires already knowing `E_N`, which requires already knowing `m_0,...,m_{N-1}` exactly, i.e. the entire realized orbit. It adds no leverage beyond what tracking `m_N` itself already gives.

---

## 2. The reference ensemble (cylinder next-digit law)

**Repo claim** (README "Exact next-digit law from cylinder lifting" / `TaoLike/Cylinder.lean`'s `cylinder_restart`, FORMALLY VERIFIED for the transport identity itself, next-digit law PROVED MATHEMATICALLY but not Lean-packaged): for a seed `m` realizing a length-`t` prefix, `orbit(m + 2^{S_t+1}·k, t) = orbit(m,t) + 2·3^t·k` for every `k`; varying `k` uniformly gives `P(next digit=q | prefix) = 2^{-q}` exactly, independent of the prefix.

**Reproduced here** by direct cylinder-lift brute force, `k` up to `2^14` (modest, as instructed — the repo's own prior audit already went to `2^20`; this is a from-scratch, smaller-scale, independently-coded sanity check, not a re-derivation): confirmed to sampling resolution for two unrelated prefixes (seeds 27 and 703), max deviation between the two prefixes' empirical laws for `q=1..11` was exactly 0 at this resolution.

**Negative result worth recording (methodological pitfall, caught and fixed in-session):** the first version of this script used the *wrong* cylinder step. `cylinder_restart` lifts the **seed** by `2^{S_t+1}·k` but moves the **state at time `t`** by `2·3^t·k` (2-adic valuation exactly 1) — these are two different exponents that are easy to conflate because both appear in the same theorem statement. Using `2^{S_t+1}` as the *state*-space step (valuation `S_t+1`, generically much larger than the actual next digit) makes every lift reproduce the seed's own fixed next digit unchanged — i.e. it silently destroys the very randomization the law depends on. This is recorded because it is exactly the sort of "coordinate confusion masquerading as a dynamical finding" the task is probing for, just one level down in the implementation rather than in the mathematics.

**Derived:** `E[d] = Σ_q q·2^{-q} = 2` (exact series and empirical cylinder-lift mean agree to 4 decimal places), hence `E[ΔR] = 2 − alpha ≈ 0.415037 > 0`. **This is positive, not zero** — the unconditional cylinder-lift law pushes `R` upward (away from confinement), on average, at every step. The reference ensemble is explicitly a law across cylinder lifts of one fixed prefix (a spatial average over the free lift parameter `k`), not a claim about temporal independence along one fixed natural orbit — the natural orbit corresponds to `k=0` at every step, and `RealizerLift.lean`'s `liftDigit_eq_zero_iff` already formally shows that asking whether a given candidate digit is the real one is exactly as hard as computing it (the "M37B circularity" the repo's own audit trail already flags).

**Conditioning separated explicitly (`part4_compare.py`, all four requested ensembles built from the one base law):**

| Ensemble | Definition | Result |
|---|---|---|
| unrestricted | plain cylinder-lift next digit | `E[ΔR] = 2−alpha ≈ +0.415` (§2 above) |
| PAST | prefixes selected by past survival only, next digit's outcome **not** further conditioned | `E[ΔR_n \| PAST] = 2−alpha` **exactly, at every `n`**, by construction (DP, §4.0) and confirmed on real orbit data to 4 decimals at `n=0` (§4.2) |
| next-step survival (myopic) | additionally require the very next step also stays confined | biases the mean digit down, but only locally (checked qualitatively, not separately tabulated — see §4.3's `h(Delta,b)` cells, which *are* exactly this one-step conditioning) |
| TILT (survive to fixed horizon `H`) | full future conditioning via exact finite-horizon Doob h-transform | `E[ΔR_n \| TILT]` moves from unconditional `+0.415` down through **negative** values near the start, crosses toward `0` in the interior, and rises again near the horizon boundary (§4.1) |

**This directly answers the task's central question for Part 2:** the apparent "restoring tendency" visible in confinement-conditioned samples is **not** present in the unconditional law (mean `+0.415`, confirmed both analytically and on 8,192 real odd seeds) and **not** produced by past-survival conditioning alone (mean stays at `+0.415` in both the DP and the real-orbit sample). It **only** appears once paths are conditioned on **surviving into the future**, i.e. it is a selection/conditioning artifact of which continuations get kept, not a property of the one-step law or of "confinement" as a past-only filter. This reproduces, in a self-contained way, the repo's own M33 Cramér-tilt finding (`docs`/`CHANG_CYLINDER_SCRATCHPAD.md` region — `E_* e = beta` under the tilt, i.e. exact zero drift) without depending on the now-deleted M33 scripts.

---

## 3. Depth and arithmetic phase

**Repo conventions confirmed:** `beta = alpha−1`, `K_n = S_n − n`, `Delta_n = floor(beta·n) − K_n`, `b_n = floor(beta(n+1)) − floor(beta·n) ∈ {0,1}`, and the first-crossing hazard `h(Delta,b) = 2^{-(b+1+Delta)}`.

**Derived and verified exactly (`part3_phase.py`, 60-digit `mpmath` precision):**

1. `b_n` is a **deterministic function of `n` alone** — no orbit/word data enters it (it is the Sturmian mechanical sequence of `beta`). Frequency of `b_n=1` over `n=0..199` is `0.58`, trending toward `beta≈0.585` as expected.
2. `R_n = −Delta_n − {beta·n}` holds exactly (checked against five real seeds' true `S_n`, `n ≤ 80`).
3. **`(n, Delta_n, b_n)` and `(n, R_n)` carry exactly the same information** — a coordinate change, not new data: `b_n` is recoverable from `n` alone, and `Delta_n` is then recoverable from `(n, R_n)` (or from `(n, S_n)` directly) by simple algebra, and vice versa.
4. `h(Delta,b) = 2^{-(b+1+Delta)}` is **exactly** the Geom(2) tail probability `P(d ≥ b+2+Delta)` from the first-crossing terminal-digit law — checked for `Delta=0..3`, `b∈{0,1}`, exact match to `1e-12`.

**Answers the task's central question for Part 3:** the "phase changes the hazard by a factor of two at matched integer deficit" observation is **not** additional predictive information beyond `(n, R_n)`. It is exactly the information an **integer-only** summary of the exact real drift (`Delta_n` alone, without its fractional remainder `{beta n}`) *discards* — and `b_n` is precisely the one bit needed to recover it, no more. Since `b_n` is a fixed, non-random function of `n`, there is no sense in which two orbits could differ only in `b_n` while agreeing on `Delta_n` and `n` — matching `Delta_n` at a different `n` necessarily changes `b_n` too (unless `n` is also matched, in which case `b_n` is already determined). So this is **information loss corrected by phase-tracking, not new structure discovered by it** — precisely what the task instructed not to claim without proof, and here it is proved (an exact coordinate-change identity, not a heuristic).

---

## 4. Small reproducible comparison (full output: `part4_compare.py`)

**Setup:** confinement level `c=0` (matches the repo's own `CriticalCrossing`/`rmin(0,·)` framing); verified `Confined 0 ⟺ Delta_n ≥ 0 ∀n` follows from `R_n=−Delta_n−{beta n}` and `{beta n}∈[0,1)`. Reference ensemble: exact finite DP over `Delta_n` (deficit truncated at 90, jump digit truncated at 80 — both negligible-tail, confirmed by a zero spill check) with the deterministic `b_n` sequence, horizon `H=150`. Real-orbit ensemble: **odd seeds 1..16383 (8,192 seeds)**, horizon 200 steps, **first-exit retained, one observation per seed** (no pooling of repeated visits to the accelerated map's fixed point `T(1)=1`, which a locked-in seed exits from in a handful of steps anyway since `d=2>alpha` there always).

- **§4.0 — validated the DP against its own generating assumptions first**, per task instruction: reproduces `E[ΔR|PAST]=2−alpha` exactly at every `n`, confirming past-only conditioning induces no bias in the reference model.
- **§4.1 — TILT (survive-to-H):** martingale identity `Σ_δ f(δ,n)h(δ,n) = const` checked exactly across `n=0,30,60,100,150` (all equal to `1.28×10⁻⁶`, the total survival probability). `E[ΔR_n|TILT]` sweeps from negative through ≈0 back to positive near the horizon — the discrete analogue of the repo's own **M34** "finite-horizon original conditioning is excursion/bridge-like" finding.
- **§4.2 — real orbits, PAST ensemble** (bug found and fixed in-session: an earlier version of this cell excluded the crossing digit itself from the aggregate, which silently substituted the *myopic next-step-survives* ensemble for the intended *past-only* one — corrected before recording results below): `E[ΔR_n|ORBIT]` at `n=0` is `0.4149`, matching the unconditional `2−alpha=0.4150` to 3 decimals (exactly as expected: the first digit of any odd seed already realizes Geom(2), an elementary and unrelated-to-cylinders fact). At `n=5,10,20` it stays near `0.41–0.45`, i.e. **does not drift toward 0** under past-only conditioning, consistent with §4.0's DP prediction. At `n=40` the cell is explicitly flagged sparse (23 seeds) and not over-interpreted.
- **§4.3 — crossing frequency at matched `(Delta,b)`:** empirical `P(cross)` vs. `h(Delta,b)` agree well for the well-populated small-`Delta` cells (`Delta=0,1,2`: within ~0.01 of prediction, thousands of observations); cells at `Delta≥4` are increasingly sparse (`n_obs` down to 49–186) and reported as such rather than smoothed — deep confinement is intrinsically rare among small odd seeds, matching the repo's existing "long-confined record seed" observations (27, 703, 10087, 35655, 381727).

**Failed/ruled-out hypothesis, explicitly:** "confinement (past survival) itself produces a restoring/centering bias toward `R≈0`." Both the exact reference DP (§4.0) and 8,192 real orbits (§4.2, after the off-by-one fix) show this is false — the mean one-step drift among confined-so-far paths stays at the full unconditional `+0.415`, not 0. Centering only appears under **explicit future-horizon conditioning** (§4.1), which is a fact about the conditioning/selection procedure, not about confinement as a filter on the past.

---

## 5. What survives, what doesn't

**FORMALLY VERIFIED (pre-existing, unchanged by this audit):** `R d j = s d j − j·alpha` (`Confinement.lean`), the carry identity `q_eq_C`/`iter_carry_eq` (`Carry.lean`), `cylinder_restart`/`cylinder_additivity` (`TaoLike/Cylinder.lean`), `RealizerLift.lean`'s lift-digit uniqueness/circularity results. None of this audit touched or extended any of these.

**MATHEMATICALLY DERIVED (this audit, hand derivation + exact/float cross-checks, not Lean-packaged):**
- `A_N = R_N − E_N = log2(m0/m_N)` exactly, with the corrected sign relative to the README's literal (but non-load-bearing) prose statement.
- `ΔA_N = d_N − alpha − log2(1+1/(3m_N))`.
- `R_N=0` is unattainable for `N≥1` (irrationality of `alpha`) — the "algebraic balance" line is a coordinate fact, never a reachable orbit state.
- `(n,Delta_n,b_n) ↔ (n,R_n)` is an exact bijection; `h(Delta,b)` is exactly the Geom(2) tail law composed with this bijection — the "phase" carries no information beyond `(n,R_n)`.

**COMPUTATIONAL (this audit):**
- Cylinder next-digit law reproduced by brute force at `k<2^14` for two prefixes (confirms existing claim; does not extend it).
- DP reference ensemble (§4.0–4.1) and real-orbit ensemble (§4.2–4.3, 8,192 seeds) both show: unconditional and past-only-conditioned mean drift `≈2−alpha>0`; only full-future-horizon conditioning drives the mean toward 0; crossing-frequency vs. `h(Delta,b)` agreement in well-populated cells, explicit sparsity flags elsewhere.

**CONDITIONAL:** none introduced (no `TaoMixingHypothesis`-style external dependency was used).

**OPEN (unchanged; this audit does not move the needle on any of these, and does not claim to):** `CriticalCrossing`, EOC (any tier), the almost-all-to-pointwise amplification mechanism, nontrivial-cycle exclusion, Collatz itself. This audit is entirely at the level the repo itself already labels "ensemble vs. pointwise gap" — it sharpens *which* ensemble/coordinate effects are real vs. artifactual, and adds no pointwise leverage.

### The requested three-way (four-way) distinction, as it actually cashes out here

- **Algebraic/coordinate balance** (`R_N=0`): a normalization reference line fixed by the choice of `alpha` as the rescaling constant. Never attained (`N≥1`), by an elementary irrationality argument. Carries no dynamical content by itself.
- **Statistical center under a specified sampling law**: `E[ΔR]=2−alpha>0` under the *unconditional* cylinder law — not centered at all. A statistical center *at* `R≈0` only emerges under an explicit, stated future-survival conditioning (the Doob/Cramér tilt), and is a property of *that conditioning*, confirmed exactly reproducible from the base law with no extra assumptions (§4.1).
- **Trajectory symmetry / restoring drift for a generic orbit**: not observed. Past-survival-conditioned real orbits (§4.2) track the *unconditional* mean, not a centered one. The historically observed "shallow" long-confined record seeds are exactly that — rare records, i.e. instances of the tilted/conditioned ensemble by definition of being the seeds selected for surviving long — not evidence of a restoring force present in typical dynamics.
- **A threshold for growth vs. descent**: `A_N` gives an exact, non-heuristic, integer-certifiable sign test (§1b) for descent/return/growth relative to the *starting seed specifically* — but it is a re-expression of `m_N` itself, not an independently predictive threshold, since `E_N` requires the whole realized history.

**Relevance to realizer placement:** none of the above adds pointwise leverage on realizer placement (the repo's actual open frontier per `RESEARCH_CHECKPOINT_2026-09-05.md`'s "persistent-bit / triangular defect separation"). This audit's contribution is entirely at the ensemble/coordinate-hygiene level: it certifies that the *specific* apparent "centering" phenomena a reader might be tempted to read into `R_N=0`, into confinement, or into the `(Delta,b)` phase are exactly explained by (a) an irrationality fact, (b) future-conditioning selection bias, and (c) a lossless coordinate change — none of which are new arithmetic obstructions, and none of which should be mistaken for one.

## Next steps (ranked)

1. **Done in this pass:** the one-sentence sign inversion in README.md's exact drift identity (§1a) is corrected (`log₂(m₀ / m_N) = ...` → `log₂(m_N / m₀) = ...`, RHS unchanged) — pure prose, zero Lean risk, matches this report's §1a derivation and the already-consistent restatement `R_N = log₂(m₀/m_N) + E_N` elsewhere in the README (that line needed no change).
2. **Candidate small Lean identity, if ever formalized:** `A_N = R_N − E_N = log2(m0/m_N)`, packaged as an exact real-valued lemma parallel to the existing (unpackaged) drift identity, with `A_N`'s sign characterized via the *existing* carry identity (`Carry.lean`) rather than via `Real.log` directly — i.e. state the integer-comparison corollary (`m_N < m0 ↔ A_N > 0`) as the primary exported fact, since that is what is actually usable without floating-point/transcendental reasoning in Lean. Dependencies: `EOC.Carry`, `EOC.Confinement`. Left for a subsequent round, as instructed.
3. **Lower priority / exploratory:** extend §4's DP to a genuine Doob h-transform *coupled* to real-orbit conditioning (i.e. weight real seeds by how deep their record actually is, rather than only bucketing by first-exit step) to see whether the small residual "shallow-survivor" signature the repo already flagged (M34) can be attributed quantitatively to horizon length alone, or needs an extra factor — this only re-confirms/refines an existing COMPUTATION-level finding, not a new direction.
