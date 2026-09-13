# Read-only mathematical audit — `innerlightr-wq/eoc-lean-verification`

Date of audit: 2026-09-12. Read-only: no commits, branches, issues, PRs, or edits were made.

Label key (used for every claim below): **FV** = formally verified (declaration in tracked Lean, no `sorry`/custom axiom); **PM** = proved mathematically (complete paper argument here, not Lean-checked); **COMP** = computationally verified (finite exact computation only); **COND** = conditional on a named unproved hypothesis; **CONJ** = conjectural; **REF** = refuted; **PA** = prior art.

One qualification applies to every **FV** label in this report: see §2 (build status could not be independently confirmed).

---

## 1. Executive verdict

* The tracked Lean library (29 modules, ≈12,300 lines) contains **no `sorry`, `admit`, or custom `axiom`**; every module is imported by `EOC.lean`, so all are in the default build target. The only external mathematical input is Tao's Proposition 1.9, packaged as an explicit structure field (`TaoMixingHypothesis`), never as an axiom.
* **The disputed name `EOC.CompositionCounting.valuationShell_card` does not exist** anywhere in the tracked source or documentation (`grep` over all `.lean` and `.md` files at HEAD returns nothing). Neither does `EOC.valuationShell_card`. Neither may be cited.
* **No new EOC consequence (level 5) emerged.** The finite-word → natural-orbit bridge is exactly where the repository's own documentation says it is: the injective, forever-confined orbit with unbounded negative excursions.
* Three findings rise above restatement:
  1. **Strongest new deduction (PM, level 3–4):** the finite-prefix drift-floor exponent of row V can be raised unconditionally from `2 − log₂3 ≈ 0.415` to `8/9`, by replacing the dyadic-packing bound on `E_N` with a harmonic-sum bound over distinct integers coprime to 6. The exact drift identity does all the work.
  2. **Strongest computational finding (COMP, level 2):** for the irrational barrier `S_j ≤ jα + c` with endpoint on the barrier, `N·|W_c(N,s_N)|/C(s_N−1,N−1) = (c+1)·g({Nα}) + o(1)` with `g` bounded in `[≈1.1, ≈2.5]` and discontinuous at `{Nα} = α−1`. So `γ_conf = 1` exactly (phase-controlled fits give `1.000 ± 0.001` at `c = 0`), `γ_total = 3/2`, and the "`c = 3` discrepancy" is Sturmian-phase aliasing plus a slow finite-size drift — not a change of exponent. The lower bound `|W_c|/shell ≥ 1/N` is **PM** by Spitzer's cyclic lemma.
  3. **Collision rate (COMP):** `I₂(θ) := −log₂P_{N,⌊θN⌋}/N` is strictly convex and superadditive with local slope rising from ≈0.45 (boundary layer at `c = 0`) to ≈1.9 near `θ = 1`; a stationary collision rate `R₂` is **REF** on the confined ensemble.
* One documentation error propagated from the supplementary Catalan script: the limit of `log₂C_n − [2n − (3/2)log₂n]` is `−½log₂π ≈ −0.8257`, not `−0.9624`.

---

## 2. Public commit and files examined

* Repository: `https://github.com/innerlightr-wq/eoc-lean-verification`, branch `main`.
* HEAD examined: **`c6bc9297febb26c8cb5aeeb5ebb4c5dd1a2811a0`** (2026-09-07 14:19:14 −0400, "correct EOC documentation after mathematical audit"). 44 tracked files.
* Toolchain: `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned at `de5ce8a9…` (`lake-manifest.json`).
* **Build status caveat.** The GitHub check-run `build` for this exact commit (workflow `lean_action_ci.yml`, which runs `leanprover/lean-action@v1` followed by `docgen-action@v1`) reports `status: completed, conclusion: failure` (started 2026-09-07 18:19Z). I could not retrieve the annotations (API rate-limited from a shared sandbox address), so I cannot tell whether the Lean build or the docgen step failed. I could not build Mathlib locally either. Consequently every **FV** label in this report means: *tracked, sorry-free, axiom-free Lean source, statement read directly; compilation at HEAD not independently confirmed by me.* The README's assertion that `lake build` succeeds should be re-checked against that CI run.
* Tracked files read: `README.md`, `EOC.lean`, all 14 `EOC/*.lean`, all 15 `EOC/TaoLike/*.lean`, `docs/RESEARCH_CHECKPOINT_2026-09.md`, `CHANG_CYLINDER_SCRATCHPAD.md`, `scratch/{chang_eoc_experiment,supp_long,supp_negatives}.py`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, CI workflows.
* **Supplementary, untracked material supplied separately in this conversation** (not in the public commit; never to be cited as repository content): `catalan_barrier_control.py`, its 13-test suite, and the audit brief. No other "uploaded audit files" (the `γ_conf`/`γ_total` tables, the `c = 3` numbers) were provided to me; where the brief refers to them I recomputed from scratch and say so.
* The scratchpad's own inventory (§10) lists three `scratch/transport_*`/`tcc2.py` scripts and `EOC/PeriodicRealizer.lean` as unavailable; confirmed absent from the working tree at HEAD.

---

## 3. Formal theorem inventory

Columns: principal definitions · strongest theorem · hypotheses · downstream dependents · unconditional? · converse? · underused outputs.

| Module | Principal definitions | Strongest theorem | Hypotheses | Dependents | Uncond. | Converse | Underused |
|---|---|---|---|---|---|---|---|
| `Basic` | `a m = v₂(3m+1)`, `T` | `affineClosure_T : T(4m+1) = T m` | none | everything | yes | n/a | — |
| `ValuationWord` | `s`, `S`, `orbit`, `iter`, `Realizes` | `realizes_iff_iter_valuation` | none | Realizer, Cylinder | yes | it *is* an iff | — |
| `Carry` | `q`, `C` | `q_eq_C`; `iter_carry_eq` | per-step exact divisibility | Realizer, Periodic | yes | — | `iter_carry_eq` is the whole drift identity in disguise (§11, §17) |
| `Realizer` (frozen) | `coarseAnchor`, `leastRealizer` | `realizerCongruence : Realizes d N m ↔ 3^N m + q_N ≡ 2^{S_N} (mod 2^{S_N+1})`; `residue_pinning` | `Odd m`, `d_i ≥ 1` | all | yes | iff | `coarseAnchor` = the "moving anchor" (§10) |
| `RealizerLift` | `liftDigit`, `extendDigit` | `existsUnique_zero_lift_digit`; `liftDigit_extendDigit_injective`; `q_succ_extendDigit_eq` | `d_i ≥ 1`, `N ≥ 1` | none in-repo | yes | — | zero-lift uniqueness never combined with confinement (§6) |
| `Confinement` | `alpha`, `R`, `Confined`, `L` (unused), `rmin` | `record_chronology`; `rmin_mono`; `single_window_equiv`; `coarse_depth_window` | `hne`, `N ≥ 1`; `L` uncertified | Periodic, BoundedDrift | yes | `single_window_equiv` is an iff | `coarse_depth_window` unused downstream |
| `PeriodicCore` | `sr`, `qr`, `EvPeriodic`, `blockSum` | `three_pow_lt_two_pow_of_block_return`; `exists_exit_of_block_growth` | `0 < C`, `S ≥ 1` | Periodic, BoundedDriftCore | yes | — | — |
| `Periodic` | — | `not_confined_forever_of_evPeriodic_orbit`; `realizes_all_of_leastRealizer_const`; `leastRealizer_unbounded_of_confined_evPeriodic` | odd seed, `L ≥ 1`, ev.-periodic word | BoundedDrift | yes | `realizes_all_of_leastRealizer_const` is the converse of `residue_pinning` (§14-E) | this equivalence is never stated as one theorem |
| `BoundedDriftCore` | `pr`, `prf`, `cnt` | `no_injective_orbit_of_lower_drift` (packing) | injectivity, `3^j ≤ 2^G 2^{s_j}` ∀j | BoundedDrift, FinitePrefixPacking | yes | — | `packing_bound` loses `(3/2)^{L+1}` (§7) |
| `BoundedDrift` | — | `leastRealizer_unbounded_of_two_sided_drift` | `d_i ≥ 1`, two-sided drift ∀N | README Sturmian corollary | yes | — | — |
| `FinitePrefixPacking` | `coprimeSixRank` | `finite_prefix_injective_drift_depth_bound : (3·2^L−2)·2^{L+1} ≤ 2^g M 3^{L+1}` | injective through `2^L`, floor `−g` through `2^L` | none | yes | — | `coprime_six_packing` (3N ≤ B+2) is sharper than what the drift bound uses (§7) |
| `SignedBlock` | — | `minus_block_return_rigid` | `0 < C`, positivity | SignedRealizer | yes | — | not connected to Confinement |
| `SignedRealizer` | `leastRealizerMinus`, `am` | `realizer_complement : r⁺ + r⁻ = 2^{S_N+1}`; `joint_val_two_min` | `N ≥ 1`, `d_i ≥ 1` | none | yes | — | complement identity unused |
| `ChangHistory` | `changWord`, `changSeed` | `every_finite_history_is_a_consecutive_chang_history` | `ys ≠ []` | none | yes | no (and false, §14-E) | `changSeed_lt'` is the only quantitative output |
| `TaoLike/Cylinder` | — | `cylinder_restart : Realizes d t m → Realizes d t (m+2^{S_t+1}k) ∧ orbit(…,t) = orbit m t + 2·3^t k` | none | ResidueTV, ConditionalMixing | yes | — | — |
| `TaoLike/CylinderAppend` | `wordAppend` | `realizes_wordAppend_iff`; `cylinder_additivity` | none | none | yes | iff | additivity never composed with `record_chronology` (§6) |
| `TaoLike/PrefixPartition` | `prefixMass`, `prefixConditionalWeight` | `realizes_iff_modEq` (realizer set = odd residue class); `good_prefix_event_bound_of_conditional_bound` | `d_i ≥ 1`, some realizer | LateShiftPersistence | yes | iff | `realizes_iff_modEq` is the clean AP characterization; underused outside Tao chain |
| `TaoLike/HarmonicAP` | — | `harmonic_ap_discrepancy` | `A₀ > 0`, `D ≥ 0` | ResidueTV | yes | — | — |
| `TaoLike/ResidueTV` | — | `restart_residue_iff`; `conditional_residue_tv_eta_bound` | `Q ≥ 1`, odd base | ConditionalMixing | yes | — | — |
| `TaoLike/TaoInterface` | `geom2`, `atomWeight`, `iidGeom2VectorProb`, `taoL1TV`, `IsProbabilityLaw`, `TaoMixingHypothesis` | `atomWeight_tsum_eq_one` (FV); interface field `finite_valuation_mixing` (**external**) | — | all later Tao modules | interface is COND | — | — |
| `TaoLike/ConditionalMixing` | `conditionalIndexWeight`, `conditionalRestartLaw` | `conditional_future_valuation_mixing` | `tao : TaoMixingHypothesis`, thickness, `Q ≥ (2+c₀)n` | ShiftedPersistence | **COND** | — | — |
| `TaoLike/PersistenceModel` | `centeredSum`, `geomPersistenceEvent`, `I0`, `lambdaStar` | `geometric_persistence_upper_bound : P ≤ e^{λ*c}·2^{−I₀ n}` | iid model only | ShiftedPersistence | yes | — | only exponential rate; no polynomial prefactor (§13) |
| `TaoLike/ShiftedPersistence` … `AllShiftsAveragedPersistence` | events, windows | one-restart → fixed-shift → all-shifts persistence bounds | Tao witnesses + residue-closeness hypotheses | next module | **COND** | — | — |
| `TaoLike/NormalizedHarmonicLaw` | `harmonicWindowMass`, `normalizedHarmonicWindowWeight` | normalization (FV) + normalized transfers (COND) | as above | Summability | split | — | — |
| `TaoLike/HarmonicExceptionalSetSummability` | `dyadicPersistenceExceptionalEvent`, `I0`, `I0_pos` | `harmonic_exceptional_summability` | 3 Tao witnesses, growth hypotheses, `hresidue_prefix`, `hresidue_early`, `hbudget_param`, `hbad_rate` | none | **COND** | — | Part 6 soft-EOC audit is a negative result, correctly stated |

Mapping into the ten requested areas: (1) `Basic`, `ValuationWord`; (2) `ValuationWord`, `PeriodicCore`; (3) `Carry`, `Periodic.orbit_block_identity`, `BoundedDriftCore.orbit_product_identity`; (4) `Realizer`, `RealizerLift`, `SignedRealizer`; (5) `Confinement`; (6) `TaoLike/Cylinder`, `CylinderAppend`, `PrefixPartition.realizes_iff_modEq`; (7) `PeriodicCore`, `Periodic`, `BoundedDriftCore`, `BoundedDrift`, `FinitePrefixPacking`, `SignedBlock`; (8) `TaoInterface` through `HarmonicExceptionalSetSummability`; (9) `ChangHistory`; (10) `PrefixPartition`, `RestartLawAlignment`, `PersistenceModel` — **no prefix-counting, shell-counting, or collision theorem exists in tracked Lean.**

Documentation vs source: every row A–V of the README table was checked against source; the row descriptions are accurate. The README's derived claim `G(N) ≥ (2−log₂3)log₂N − O_M(1)` follows correctly from row V (§7). The README's Sturmian corollary (instantiating `leastRealizer_unbounded_of_two_sided_drift` with `c = 0`, `G = 1`) is a valid instantiation (`−1 < R*_N ≤ 0`).

---

## 4. Logical dependency map

```
finite formal word (d_0..d_{N-1}, d_i ≥ 1)
  │ PROVED  realizerCongruence / realizes_iff_modEq: realizer set = one odd class mod 2^{S_N+1}
  ▼
exact residue-class realizer  (leastRealizer d N < 2^{S_N+1}; coarseAnchor = it mod 2^{S_N})
  │ PROVED  leastRealizer_odd, leastRealizer_realizes (need d_i ≥ 1, N ≥ 1)
  ▼
least positive realizer r(D)
  │ PROVED (trivial direction)  r(D) realizes D as a genuine orbit prefix
  │ PROVED (residue_pinning)   if m realizes D and m < 2^{S_N+1} then m = r(D)
  ▼
natural orbit prefix
  │ OPEN (compatibility)  extension of D by one digit keeps the SAME seed iff liftDigit = 0
  │      (existsUnique_zero_lift_digit: exactly one next digit does; whether it is
  │       a confined digit is the whole question)
  ▼
extendable infinite word realized by a fixed seed
  │ PROVED both ways: realized by fixed m  ⟺  leastRealizer(D|N) eventually constant
  │      (⇒ residue_pinning; ⇐ realizes_all_of_leastRealizer_const)
  │ FALSE that every infinite 0-confined word is realizable (Sturmian word: BoundedDrift)
  ▼
confined infinite orbit  (exists?)
  │ PROVED for non-injective orbits: impossible (not_confined_forever_of_evPeriodic_orbit)
  │ OPEN for injective orbits with unbounded negative excursions  ← THE FRONTIER
  ▼
CriticalCrossing (∀ odd M ∃ N, R_N(M) > 0)
  │ OPEN; equivalent to rmin(0,N) → ∞ (checkpoint §1, paper proof, not Lean)
  ▼
finite occupation O_c(m) < ∞          OPEN (strictly weaker than EOC rate)
  ▼
quantitative EOC O_c(m) = O(log m)    OPEN
  ▼
Collatz-related consequences          OPEN, and requires a separate no-cycle input
```

First unproved arrow on every route: **natural orbit prefix → extendable infinite word for a *confined* extension**, i.e. whether the unique zero-lift next digit can stay ≤ the barrier indefinitely for some seed. All named blockers are the same problem (§5).

---

## 5. Exact current frontier

Four names in the documentation — "moving-anchor anti-concentration", "injective bounded-drift case", "companion-seed amplification gap", "fresh-bit / natural-tail argument" — are one problem, stated in four coordinate systems:

* **2-adic form (PM, assembled from `leastRealizer_succ_modEq` + `residue_pinning`):** for an infinite word `w` with `d_i ≥ 1`, the least realizers `r_N := leastRealizer(w|N)` form a compatible tower (`r_{N+1} ≡ r_N mod 2^{S_N+1}`), hence converge to a 2-adic integer `ξ(w) = −lim_N C_N 3^{−N} ∈ ℤ₂`. **`w` is the valuation word of a natural orbit iff `ξ(w) ∈ ℕ`** (equivalently, iff `(r_N)` is eventually constant). `CriticalCrossing ⟺ ξ(w) ∉ ℕ for every infinite 0-confined w.`
* **Anchor form:** `ξ(w)` is the moving anchor. It is *word-dependent* (not fixed, not orbit-dependent); for a natural orbit it equals the seed. Residue pinning fixes `ξ(w) mod 2^{S_N}` from the prefix — it gives *no separation* between distinct words (two words can have arbitrarily close anchors), and gives no size information beyond `r_N < 2^{S_N+1}`.
* **Drift form:** by the exact identity `R_N = log₂(m₀/m_N) + E_N` (§17), a forever-0-confined orbit has `m_N ≥ m₀ 2^{E_N} ≥ m₀`, and by row V/§7 must have `R_N ≤ −(8/9)log₂N + log₂m₀ + O(1)` infinitely often (unboundedly deep excursions). The observed record seeds have excursion depth `Δ_n ∈ [0,8]` growing roughly logarithmically — inside what packing allows, so packing cannot close it.
* **Ensemble form:** the Tao chain controls the harmonic mass of persistent seeds at scale `2^{−I₀ N}`, a single cylinder has mass `2^{−αN}`; `α − I₀ = αH₂(1/α) = 1.5056` bits/step is exactly the shell entropy (§11). Nothing in the chain is pointwise.

Blockers are therefore equivalent, not several.

---

## 6. Underused theorem combinations (Phase 3)

Tested pairs/chains; only those producing something are listed.

1. **`iter_carry_eq` + `orbit_product_identity` + `Real.logb` algebra ⇒ exact drift identity** (§17). New named statement: yes. Removes hypotheses: no. Quantitative: it *is* the quantity. Transfers through cylinder restart: yes (identity is per-orbit). Collatz-independent: yes (any `(3m+1)/2^v` recursion). **Level 1.**
2. **Drift identity + `coprime_six_packing` + harmonic-sum bound ⇒ improved drift-floor exponent 8/9** (§7). **Level 3–4.**
3. **`residue_pinning` + `realizes_all_of_leastRealizer_const` ⇒ realizability criterion `ξ(w) ∈ ℕ`** (§5, §14-E). Both directions FV; the iff is not stated. **Level 1.**
4. **`three_pow_lt_two_pow_of_evPeriodic_orbit` + `changWord` ⇒ the infinite all-zeros Chang history `(2,1,1)^∞` is realized by no natural orbit** (blockSum 4, `2^4 = 16 < 27 = 3^3`). Instantiation, FV content. **Level 1**, but it sharpens the README's "finite only" remark into a theorem-backed obstruction (§14-E).
5. **`existsUnique_zero_lift_digit` + `Confined`:** the unique confined-continuation question. `q_succ_extendDigit_eq` shows the carry at `N+1` is independent of the candidate digit, so the zero-lift digit `e₀(N)` is a function of `(r_N, S_N, q_{N+1})` only. The natural orbit continues with `e₀` iff `a(orbit r_N N) = e₀`. Combining with `coarse_depth_window`: confinement/exit at step `N+1` is decided by `2^{S_N}` (one bit less). **No new theorem** — but this is the cleanest formal statement of the frontier: `CriticalCrossing ⟺ ∀ 0-confined finite D with r(D) < 2^{S_N}` (i.e. seed already pinned), the zero-lift digit eventually exceeds the barrier.` Level 0/1.
6. **`cylinder_additivity` + `record_chronology`:** gives `rmin(c, t+u) ≤ rmin(c,t) + 2^{S_t + S_u + 1}·k` type bounds only when a confined suffix `e` is realized *from `orbit m t`*, which is again the open compatibility. Nothing new.
7. **`realizer_complement` (`r⁺ + r⁻ = 2^{S_N+1}`) + confinement:** the minus-map realizer of a word is the mirror of the plus-map realizer; no consequence for confinement of the plus map. Dead end (recorded).
8. **`coarse_depth_window` + `first-crossing law` (checkpoint §2):** consistent (both say the terminal digit only needs a ≥), no strengthening.

---

## 7. Strongest new deduction — improved unconditional drift-floor exponent

**Theorem candidate (PM).** Let `M` be odd, `N ≥ 2`, `orbit M` injective on `{0,…,N}`, and `R_j(M) ≥ −g` for all `j ≤ N`. Then
```
g ≥ (8/9)·log₂N − log₂M − 3.
```
Equivalently: any injective orbit stretch of length `N` with drift floor `−g` forces `N ≤ (8·M·2^{g})^{9/8}`-scale bounds. (Constants not optimized.)

**Proof.** (i) Exact identity (§17): `m_j = m₀·2^{−R_j}·2^{E_j}`, `E_j = Σ_{i<j} log₂(1+1/(3m_i))`. (ii) `R_j ≥ −g` gives `m_j ≤ m₀ 2^{g} 2^{E_j}`. (iii) `E_j ≤ (1/(3 ln 2)) Σ_{i<j} 1/m_i`. For `i ≥ 1`, `m_i` is odd and `3 ∤ m_i` (`orbit_succ_coprime_six`, FV) and the `m_i` are distinct; the sum of reciprocals of `j` distinct positive integers coprime to 6 is at most `Σ_{k≤j} 1/x_k` with `x_k` the k-th such integer (`x_k ≥ 3k − 2`), which is `≤ (1/3)ln j + 2`. Hence `E_j ≤ (1/9)log₂j + 1.5` (this absorbs the `i = 0` term, at most `log₂(4/3)`). (iv) All `m_j`, `1 ≤ j ≤ N`, are distinct, odd, coprime to 6, and `≤ B := m₀2^{g}·2·N^{1/9}`; `coprime_six_packing` (FV) gives `3N ≤ B + 2`. Rearranging gives the claim. ∎

**Why not already in the repository.** Row V bounds `∏(1+1/(3m_i))` by dyadic packing (`packing_bound`: `≤ (3/2)^{L+1}` over `2^L` terms), i.e. `E_N ≤ log₂(3/2)·log₂N ≈ 0.585 log₂N`, which is where `2 − log₂3 = 1 − log₂(3/2)` comes from. The harmonic bound gives `E_N ≤ (1/9)log₂N + O(1)`. **COMP check:** the worst case over distinct odd values is `E_N = (1/6)log₂N + 0.39` (N = 2¹⁴: 2.72 vs. row V's 8.77); over integers coprime to 6, `(1/9)log₂N + 0.4`.

**Relation to Curry.** Curry's threshold `B < 1/β* ≈ 1.036` is stronger but uses collision-free windowed sparsity (`Σ 1/m_n < ∞`). This bound is elementary, unconditional, and sits strictly between row V (`0.415`) and Curry (`1.036`). It still does not touch the observed record-seed depth (§5). **PA risk: moderate** — harmonic-sum bounds along Collatz orbits are standard; the specific exponent statement is not, to my knowledge, in the cited literature.

**Lean difficulty:** low–moderate (real logs of finite products; a harmonic-sum lemma over a finite set of distinct naturals coprime to 6 — Mathlib has `Finset.sum_le_sum` + `Nat` counting; no analysis beyond `Real.logb`). See §19.

---

## 8. Strongest standalone theorem candidate — two-sided bounds for the confined shell

**Setting.** `α = log₂3`, integer `c ≥ 0`, `N ≥ 1`, `s_N := ⌊Nα⌋ + c` (endpoint on the barrier), `W_c(N,s) := #{d ∈ ℕ_{≥1}^N : S_j ≤ ⌊jα⌋ + c ∀j ≤ N, S_N = s}`, `shell := C(s−1, N−1)`.

**(a) Lower bound, PM.** `W_c(N, s_N) ≥ shell/N` for all `N, c`.
*Proof.* For a composition `d` of `s_N`, let `f(j) := S_j − j·s_N/N` (chord deviation, cyclically extended). Rotating `d` to start after an argmax of `f` (Spitzer's combinatorial lemma; valid for arbitrary real increments, nothing about boundedness is used) gives a composition with `S'_j ≤ j·s_N/N` for all `j`. Since `j·s_N/N = jα + j(c − {Nα})/N ≤ jα + c`, the rotated word is barrier-confined. Each confined word arises from at most `N` compositions this way, so `W_c ≥ shell/N`. ∎
*Exactness case (PM, classical cycle lemma):* if `gcd(s_N, N) = 1` and `⌊j s_N/N⌋ = ⌊jα⌋ + c` for `1 ≤ j < N`, then `W_c(N,s_N) = shell/N` exactly (verified: `N = 7, c = 0, s = 11` gives 30 = 210/7; every composition has exactly one confined rotation). This is the "rational approximant" mechanism of Phase 5.

**(b) Upper bound, CONJ (route: fluctuation theory).** `W_c(N,s_N) ≤ C(c)·shell/N` with `C(c) = O(c+1)`. Barrier-confined implies `f(j) ≤ c + 1` for all `j`, i.e. the exchangeable-increment bridge stays within `c+1` of its chord and ends on the chord. For i.i.d.-increment lattice bridges this probability is `~ V(c)·V̂(0)/N` with `V` the ascending-ladder renewal function; here the integer distance to the ceiling changes by at most `−1` per step (digits ≥ 1, barrier increments ≤ 2), so `V(c) = c+1`, predicting the linear-in-`(c+1)` prefactor seen computationally. **PA:** Kaigh (1976), Bolthausen (1976), Caravenna–Chaumont (2008) for bridges conditioned to stay positive; Takács's ballot theorems for exchangeable increments (rational slope only). The genuinely new part is the Sturmian offset `⌊jα⌋ − j s_N/N`, which is what makes the limit oscillate.

**(c) Conjecture (COMP, strongly supported).** `N·W_c(N,s_N)/shell = (c+1)·g({Nα}) + o(1)` with `g` bounded, increasing on `[0,1)` with a jump at `{Nα} = α − 1 ≈ 0.585` (the phase at which the last Sturmian digit `d*_{N−1}` switches from 2 to 1). Evidence: at `N ∈ [1200,1600]`, `N·W/shell` averages 1.126 (`{Nα} < 0.3`) vs 2.501 (`{Nα} > 0.7`) for `c = 0`, and 4.426 vs 9.813 for `c = 3` — ratios 3.93 and 3.92 ≈ `(3+1)/(0+1)`.

Levels: (a) 4 (proved standalone; elementary); (b) 3; (c) 2.

---

## 9. Strongest computational experiment

Two, both reproducible from the definitions (exact integer/rational arithmetic, scripts written during this audit; they are not repository files):

1. **Phase-controlled exponent fit** (`c = 0,…,4`, `N ≤ 1600`, exact DP over `(j, S_j)` states): regress `log(W/shell)` on `log N` with `{Nα}` binned. Results: `γ_conf = 0.9985 (c=0), 0.990, 0.982, 0.974, 0.967 (c=4)` over `N ∈ [40,800]`; restricting to `N ∈ [600,1600]`: `1.0001 (c=0)`, `0.9966 (c=3)`. Against the entropy line `N·αH₂(1/α)`: `γ_total = 1.500 (c=0)`, `1.488 (c=3)`; shell alone `γ_shell = 0.500`.
2. **Moving-anchor equidistribution test** (all odd seeds `≤ 2²⁰`, `c = 0`): actual `#{m ≤ X : 0-confined through N}` vs prediction `X·P_iid(C_{0,N})/2` (anchor uniform in its class). Ratio is exactly 1.000 while `2^{S_N} ≤ X` (`N ≤ 12`, as it must be), then decreases: 0.955 (N=30), 0.929 (50), 0.797 (65), 0.769 (84), 0.629 (102, 10 seeds vs 15.9), 0.460 (108), 0.141 (114, 1 seed vs 7.1). Small realizers of confined words are **under**-represented relative to uniform, increasingly with `N`. Poisson-significance at `N=114` is `p ≈ 0.007`; at `N = 102`, `p ≈ 0.08`. Ensemble evidence only.

---

## 10. Moving-anchor findings (Phase 4A)

* **Quantity whose concentration must be bounded:** `A(X,N) := #{c-confined words D of length N : leastRealizer(D) ≤ X}` (equivalently, the number of odd seeds `≤ X` confined through `N`). EOC (`O_c(m) = O(log m)`) implies `Σ_N A(X,N) = O(X log X)`; the uniform-anchor heuristic gives `A(X,N) ≈ X·P_iid(C_{c,N})/2 = X·2^{−I₀N}N^{−3/2}·O(1)`, hence `Σ_N A(X,N) = O(X)`.
* **Anchor type:** word-dependent (`ξ(D) = −C_N 3^{−N} mod 2^{S_N+1}`); fixed only in the periodic sector (`Periodic.lean`, rational 2-adic limit); for a natural orbit it is the seed itself (scratchpad §8.2, `ξ_j → m₀` in ℤ₂ — confirmed as an exact corollary of `iter_carry_eq`).
* **Does residue pinning give deterministic separation?** No. `coarseAnchor` determines `r(D) mod 2^{S_N}` exactly, but the map `D ↦ r(D)` on confined words of fixed length has no proven injectivity-at-scale or spacing property; distinct words can have anchors differing by any residue. The one deterministic fact is `r(D) ∈ {coarseAnchor, coarseAnchor + 2^{S_N}}` (`leastRealizer_eq_or_eq_add`) — one bit, not separation.
* **What the computation says:** no favorable concentration of small realizers is visible; if anything the opposite (§9). This is consistent with EOC and with the heuristic, but is an ensemble statement about `A(X,N)`, not about any `m₀`.

---

## 11. Confined-composition findings (Phase 4B)

* **Unrestricted shell entropy (PA, Stirling/Cramér):** `log₂C(s_N−1,N−1) = N·αH₂(1/α) − ½log₂N + O(1)` with `αH₂(1/α) = 1.50564…` bits/step. **Cross-check:** this equals `α − I₀` (since `I₀ = α(1 − H₂(1/α))`, `PersistenceModel.lean`), which is exactly the README's "1.506 bits/step" gap. So the shell count and the Chernoff exponent are the same number seen from two sides (Cramér's theorem for the Geom(2) endpoint LDP). The `O(1)` term depends on `{Nα}` through `s_N − Nα = c − {Nα}`.
* **`|W_c(N,s_N)|/shell ~ N^{−1}` (COMP, now with a PM lower bound and a fluctuation-theory upper-bound route):** confirmed as `(c+1)g({Nα})/N`; see §8. Status of the exponent: `γ_conf = 1` is COMP + PM-lower-bound; the limit `N·W/shell` does **not** exist (oscillates), only limits along `{Nα} → φ` subsequences.
* **`γ` means `γ_conf`.** The brief's `N^{−1}` refers to the ratio against the endpoint-fixed shell, i.e. `γ_conf`. `γ_total = γ_conf + ½ = 3/2` is the exponent against the entropy line and includes the bridge (endpoint) cost `½`; both fitted to three decimals (§9). The two must not be conflated: a fit of `log₂W` against `N` alone (no shell normalization) measures `γ_total`.
* **`c = 3` discrepancy:** with the uploaded numbers unavailable, I recomputed. Two effects: (i) **Sturmian phase**: the prefactor varies by a factor ≈2.2–2.5 with `{Nα}`; sampling a handful of `N` values with different phases produces apparent exponent errors of order `±0.1` — this is aliasing, not a change of `γ`; (ii) **finite size**: the effective exponent approaches 1 from below more slowly as `c` grows (`0.936–0.961` on `N ∈ [50,200]` at `c = 3` vs `0.991–0.993` at `c = 0`; both `≥ 0.9936` on `N ∈ [600,1600]`). A "`c = 3` exponent ≈ 0.93–0.96" is therefore what one sees at `N ≲ 200`; it is not asymptotic.
* **Catalan comparison, transferable vs superficial:** see §13–§14.

---

## 12. Collision-rate findings (Phase 4C)

Definition: two independent uniform samples from `W_c(N,s_N)`; `P_{N,k} = Σ_S F_k(S)·(B_k(S)/W)²` with forward counts `F_k` and backward completion counts `B_k` (state `(k,S_k)` suffices, as in the Catalan script). Exact rationals, `N ≤ 600`.

* **Stationary rate `R₂` — REF.** `−log₂P_{N,k}` is not linear in `k`: the per-step increment at `c = 0` starts at `0` (first digit forced), `0.45, 0.51, 0.66, 0.71, 0.78, 0.82, 0.85` for `k = 2..8`, and the 0.1-window slopes at `N = 400` rise monotonically `1.16, 1.25, 1.33, 1.42, 1.51, 1.61, 1.72, 1.84, 1.93`.
* **Rate function `I₂(θ)`** — better supported: `I₂(θ) := lim −log₂P_{N,⌊θN⌋}/N` appears to exist (values at `N = 200, 400` differ by `≤ 0.03`, converging like `log N/N`), with `I₂(0) = 0`, `I₂(1) = αH₂(1/α) = 1.5056` (the full word is uniform, so all Rényi entropies coincide), and **strict convexity** (increasing slopes) hence **superadditivity** (`I₂(θ₁+θ₂) ≥ I₂(θ₁)+I₂(θ₂)`: 765/765 sampled pairs at `N = 400`, both `c = 0, 2`) and monotonicity (0 violations).
* **Structure from forward/backward counts:** `P_{N,k+1} ≤ P_{N,k}` exactly (nested cylinders) — monotone, FV-able. Superadditivity of `−log₂P` is *not* a general identity of the forward/backward decomposition; it is a property of this ensemble (a confined bridge's prefix marginals are far from uniform early — Rényi-2 < Shannon — and become uniform only at `θ = 1`). No subadditivity, so no Fekete-type existence argument; existence of the limit is COMP/CONJ.
* **Boundary layer:** at `c = 0` the walk starts on the ceiling, so early digits are nearly forced (`d_0 = 1`), giving `I₂'(0⁺) ≈ 0.45–0.5`, below the free tilted-Geom Rényi-2 value `−log₂((1−r)/(1+r)) = 1.1176` (`r = 1 − 1/α`) that would hold if the barrier were far away. For `c = 2` the boundary layer is shallower (`I₂(0.1) = 0.1016` vs `0.0946`).

---

## 13. Catalan comparison: what transfers

Using the supplementary script's decomposition (all COMP there; classical facts PA), and my irrational-barrier computations:

| Feature | Dyck/Catalan | Confined valuation shell | Status |
|---|---|---|---|
| Forward/backward DP; `B` depends only on state `(k,S)` | yes | yes (identical architecture) | FV-able, generic |
| Exact monotonicity `P_{N,k+1} ≤ P_{N,k}` | yes | yes | PM (nested cylinders) |
| `P_{N,N} = 1/W` | yes | yes | PM |
| Bridge (endpoint) cost `N^{−1/2}` | `C(2n,n)/4^n` | `C(s_N−1,N−1)/2^{N αH₂(1/α)}`, `γ_shell = 0.500` (COMP), local limit (PA) | transfers |
| Positivity/confinement cost `N^{−1}` | exact `1/(n+1)` | `(c+1)g({Nα})/N` (COMP), `≥ 1/N` (PM) | transfers as an order, not as an identity |
| Total `N^{−3/2}` | exact | `γ_total = 1.500` (COMP) | transfers as an order |
| Rotation lemma gives a confined representative | cycle lemma (unique) | Spitzer rotation (existence, always; uniqueness fails) | lower bound transfers |
| Rényi-2 rate of prefixes convex | (not computed here) | yes | — |

The Catalan logarithmic-correction constant: correct limit is `log₂(1/√π) = −½log₂π = −0.825748`; the script's docstring/banner value `−0.9624` is wrong (the code computes the right quantity). My earlier reply repeated the wrong constant; corrected here.

---

## 14. Catalan comparison: what fails

* **Exact counting formula.** Catalan has `C_n = C(2n,n)/(n+1)` exactly; the confined shell has no closed form: the number of confined rotations of a shell composition varies (histogram at `c=1, N=8`: `{2:240, 3:240, 4:168, 5:96, 6:40, 7:8}`), so `W ≠ shell/N` in general, and `N·W/shell` oscillates with `{Nα}` without converging.
* **Reflection principle.** Requires ±1 steps or a symmetric lattice; valuation digits are unbounded above and the barrier slope is irrational. No reflection-type identity; only asymptotic fluctuation theory.
* **Boundedness of the constant.** Catalan's `1/(n+1)` is uniform; the confined prefactor depends on `c` (linearly) and on the Sturmian phase.
* **Cycle-lemma claim from the brief, corrected.** The word `(1,3,1)` at `c = 0` has `S₃ = 5 > ⌊3α⌋ = 4`: it lies **outside the shell**, so it is not a counterexample to the rotation construction (which presupposes `S_N ≤ Nα + c`); no rotation of it is confined, as expected. What genuinely fails for unbounded digits is *uniqueness* of the good rotation, hence exact division by `N` — not existence. Spitzer's rotation succeeded for 100% of shell compositions in every tested `(N ≤ 8, c ≤ 1)`. **REF** (as a counterexample to existence); **confirmed** (as a warning about ceiling-endpoint conventions).
* **Stationary collision rate.** Fails (§12).
* **Nothing in the Catalan control touches realizability**; it is pure word counting and cannot rise above level 2 for EOC.

---

## 15. Counterexamples and killed ideas

1. `(1,3,1)`, `c = 0`: outside the shell; see §14.
2. Stationary `R₂`: REF by convexity of `I₂` (§12).
3. "`N·W_c/shell → const`": REF; oscillates between ≈1.1(c+1) and ≈2.5(c+1) (§8c).
4. "Exponent depends on `c`": REF at large `N` (phase-controlled `γ_conf → 1` for `c = 0` and `c = 3`); the drift is finite-size.
5. Infinite all-ones Chang history `(2,1,2)^∞`: no natural orbit realizes it (PM: the block map `y ↦ (27y+29)/32` strictly decreases positive integers and has no integer fixed point since `29/5 ∉ ℤ`; the sequence of integers would have to be infinite and decreasing). Least realizers of `(2,1,2)^k` have bit-length `S_N + 1` (maximal): 6, 10, 14, 21, 30, 41, 61, 81, 121 for `k = 1,…,24` (COMP). The infinite all-zeros history `(2,1,1)^∞` is excluded by FV `three_pow_lt_two_pow_of_evPeriodic_orbit` (`16 < 27`). So `ChangHistory`'s finite universality is sharp: **both** constant infinite histories are unrealizable.
6. Residue pinning as a separation mechanism: dead (§10).
7. `realizer_complement` as a confinement tool: dead (§6-7).
8. `cylinder_additivity` + `record_chronology` as a growth bound: reduces to the open compatibility (§6-6).
9. "Free tilted-geometric Rényi rate at `θ = 0`": REF at `c = 0` (boundary layer, §12).

---

## 16. Prior-art risks

* Drift identity `R_N = log₂(m₀/m_N) + E_N`: standard (Terras/Everett/Lagarias-era "telescoping"); the repository correctly labels it PM, not new.
* Shell entropy `αH₂(1/α)` and its equality with `α − I₀`: Cramér/Sanov; PA.
* `1/N` lower bound via Spitzer rotation: Spitzer (1956), Dwass, Takács; the barrier-vs-chord comparison step is trivial. PA for the lemma; the application is routine.
* `O(1/N)` upper bound for bridges conditioned to stay near their chord: Kaigh, Bolthausen, Caravenna–Chaumont, Vatutin–Wachtel; **the irrational Sturmian offset is not covered by those statements** and would need to be handled (bounded offset, so likely a perturbation argument).
* Improved drift-floor exponent (§7): harmonic-sum bounds along orbits appear in many Collatz papers (e.g., Eliahou's cycle bounds use `Σ 1/m`); the packaged inequality with `8/9` is not in the cited literature but may exist in unpublished form. Moderate risk.
* Convex Rényi-2 rate for conditioned bridges: I know of no published statement; low risk but also low priority for EOC.

---

## 17. Five-item Lean roadmap (no code written)

Ordered by value; all unconditional; each has a complete informal proof unless noted.

1. **Exact drift identity.** Path `EOC/DriftIdentity.lean`; imports `EOC.Confinement`, `EOC.BoundedDriftCore`, `Mathlib.Analysis.SpecialFunctions.Log.Base`; namespace `EOC`.
   `theorem drift_identity (m0 N : ℕ) (hm0 : Odd m0) : R (fun i => a (orbit m0 i)) N = Real.logb 2 (m0 / orbit m0 N) + ∑ i ∈ range N, Real.logb 2 (1 + 1/(3 * orbit m0 i))`
   plus `theorem E_nonneg`. Dependencies: `orbit_product_identity` (all factors positive by `odd_orbit`), `Real.logb_mul/div`, `logb2_two_pow`. Informal proof complete (take `log₂` of `2^{s_j} m_j ∏(3m_i) = 3^j m₀ ∏(3m_i+1)`). Difficulty: low.
2. **Harmonic-sum bound and improved floor exponent.** Path `EOC/HarmonicPacking.lean`; imports `EOC.DriftIdentity`, `EOC.FinitePrefixPacking`.
   `theorem sum_inv_distinct_coprime_six_le (m : ℕ → ℕ) (N) (hinj) (hodd) (hthree) : ∑ i ∈ range N, (1:ℝ)/m i ≤ (1/3) * Real.log N + 1` (or with `Real.log (N+1)`), then
   `theorem finite_prefix_injective_drift_depth_bound' (M N g) (hM) (hinj through N) (hlow through N) : (8/9 : ℝ) * Real.logb 2 N ≤ g + Real.logb 2 M + 3`.
   Informal proof complete (§7). Difficulty: moderate (the harmonic-sum lemma needs an injection of the `m_i` into `{x : x ≡ ±1 mod 6}` sorted; `coprimeSixRank_injective_on` already exists).
3. **Realizability criterion.** Path `EOC/RealizabilityCriterion.lean`; imports `EOC.Periodic`, `EOC.RealizerLift`.
   `theorem realized_iff_leastRealizer_eventually_const (d) (hd : ∀ i, 1 ≤ d i) : (∃ m, Odd m ∧ ∀ j, a (orbit m j) = d j) ↔ ∃ N0 m, 1 ≤ N0 ∧ ∀ N, N0 ≤ N → leastRealizer d N = m`, and `leastRealizer_tower : leastRealizer d (N+1) ≡ leastRealizer d N [MOD 2^(S d N + 1)]` (already `leastRealizer_succ_modEq`, restate). Both directions exist; packaging only. Difficulty: low.
4. **Generic confined-shell counting (Collatz-independent).** Path `EOC/Combinatorics/ConfinedShell.lean`; imports `Mathlib.Combinatorics.Enumerative.Composition` (or `Finset.Nat.antidiagonal`), no `EOC` imports.
   `def shellCount (N s : ℕ) : ℕ := Nat.choose (s-1) (N-1)` with `theorem card_compositions_eq_shellCount`; `def confinedShell (b : ℕ → ℕ) (N s : ℕ) : Finset (Fin N → ℕ)` (barrier `b` an arbitrary function); `theorem confinedShell_card_ge_div_N : shellCount N s ≤ N * (confinedShell b N s).card` under `∀ j ≤ N, j*s ≤ N*b j` (chord below barrier). Informal proof complete (Spitzer rotation, §8a); Lean difficulty: high-moderate (cyclic rotations, argmax over reals, fibre counting). Also `collision_monotone : P_{N,k+1} ≤ P_{N,k}` and `collision_terminal : P_{N,N} = 1/W` as `ℚ`-valued statements over the same finset. This is the honest replacement for the non-existent `valuationShell_card`.
5. **Chang infinite-history obstructions.** Path `EOC/ChangHistoryInfinite.lean`; imports `EOC.ChangHistory`, `EOC.Periodic`, `EOC.SignedBlock`.
   `theorem no_orbit_realizes_zero_history : ¬ ∃ m, Odd m ∧ ∀ j, a (orbit m j) = changWord (List.replicate k false) j` (instantiate `three_pow_lt_two_pow_of_evPeriodic_orbit`; complete), and `theorem no_orbit_realizes_one_history` (block map `y ↦ (27y+29)/32` decreasing; complete but needs a small well-foundedness argument). Difficulty: low/moderate.

Deliberately **not** proposed: an `N^{−1}` upper bound (needs fluctuation theory not in Mathlib), anything conditional on Tao, and any "EOC consequence".

---

## 18. Three highest-value next actions

1. **Resolve the CI failure at `c6bc929`** (or confirm it is docgen-only). Until then, "FORMALLY VERIFIED … compiles with `lake build`" in the README is unverified for HEAD.
2. **Package items 1–2 of §17** (drift identity + `8/9` exponent). This converts the README's strongest derived quantitative claim into Lean and strictly improves it.
3. **Exhibit a concrete parameter region for `harmonic_exceptional_summability`.** The theorem's residue-closeness hypotheses (`hresidue_prefix`, `hresidue_early`: TV of the harmonic window's residues mod `2^{Qpre}` within `Cres·2^{−Qpre}` of uniform) appear (by a heuristic discrepancy estimate, not proved here) to be satisfiable only if `Qpre ≲ L/2` (the harmonic AP discrepancy of a `2^{L−1}`-point window is of order `2^{Q−L}`, so `2^{2Q} ≲ Cres 2^{L}`), which forces `Ttotal ≲ L/(2(2+cPrefix))`. Whether this coexists with `hbad_rate`, `hbudget_param`, and `hthick` has not been shown; the README already notes no closed-form choice is exhibited. Until it is, row U is conditional on hypotheses of unknown joint satisfiability — a stronger caveat than "conditional on Tao".

---

## 19. Explicit non-claims

* No proof, partial proof, or new evidence bearing on the Collatz conjecture, EOC (any tier), `CriticalCrossing`, finite occupation, or Tao's Proposition 1.9.
* No Lean declaration is claimed to compile beyond what is stated in §2.
* `EOC.CompositionCounting.valuationShell_card` and `EOC.valuationShell_card` are not cited and do not exist at HEAD.
* The 13 passing tests of the supplementary Catalan script verify finite instances (`n ≤ 100`; collision at `n = 10`) only; they prove neither the Catalan identity nor any asymptotic.
* All `N^{−1}`, `N^{−3/2}`, `I₂(θ)` statements about the irrational barrier are COMP except the `1/N` lower bound (PM) and the classical shell asymptotic (PA).
* The `8/9` bound is PM (paper proof in §7), not Lean-checked.
* Nothing here infers infinite-orbit behavior from finite words; the only infinite statements are the two Chang-history obstructions and the `ξ(w) ∈ ℕ` criterion, each with its own proof.
* Supplementary script observations: `collision_probability_exact` should raise `ValueError` outside `0 ≤ k ≤ 2n` rather than clamp (no documentation defines constant continuation past terminal depth); `log2_bridge_only` in `decomposition_costs` is computed but unused — code quality, not a mathematical defect.

---

## 20. Final classification (levels 0–5)

| Item | Level |
|---|---|
| Drift identity packaging | 1 (organizational; PM, PA) |
| Realizability criterion `ξ(w) ∈ ℕ` / eventual constancy | 1 (both directions FV, iff not stated) |
| Infinite Chang histories `(2,1,1)^∞`, `(2,1,2)^∞` unrealizable | 1 / 3 (FV instantiation / PM) |
| `N·W_c/shell = (c+1)g({Nα})`, phase jump at `α−1`, `γ_conf = 1`, `γ_total = 3/2` | 2 (COMP) |
| Convex, superadditive collision rate `I₂(θ)`; stationary `R₂` refuted | 2 (COMP/REF) |
| Anchor equidistribution deficit at `X = 2²⁰` | 2 (COMP, ensemble) |
| Confined-shell lower bound `W_c ≥ shell/N` (Spitzer) and exact rational-approximant case | 4 (PM; elementary; PA for the lemma) |
| Confined-shell `O((c+1)/N)` upper bound | 3 (CONJ with a named route; PA-adjacent) |
| Improved unconditional drift-floor exponent `8/9` | 4 (PM; not yet Lean) |
| Any EOC consequence | **none at level 5** — no logical bridge to natural-orbit behavior was found; the frontier is unchanged (§5). |
