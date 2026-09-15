# Proposed documentation ledger (draft, 2026-09-14 — nothing moved or committed)

## Ensemble (paper: *Three Scales of Confinement*, `~/Downloads/ScalesConfinement (1).pdf`)

| PDF item | Lean status | Computational confirmation |
|---|---|---|
| Prop 4.1 terminal count `C(s_N,N)` | PROVED (LEAN) `CapacityBounds.card_feasibleWords` | — |
| Lemma 5.1 chord rotation | PROVED (LEAN) `ChordRotation.chord_rotation_nat` | — |
| Thm 5.2 shell bound | PROVED (LEAN) `CapacityBounds.collatz_shell_lower` (lower), `shellWords` ⊆ (upper) | exact DP |
| Cor 6.1 capacity sandwich | PROVED (LEAN) `CapacityBounds.collatz_capacity_sandwich` | — |
| Thm 6.2 entropy `αH₂(1/α)` | PROVED (LEAN) `EntropyBounds.tendsto_log_card_confined`, `alpha_entropy_eq` | — |
| Thm 7.1 upper bound | PROVED (LEAN) `TaoExternal.geometric_persistence_upper_bound_bits`; mass identity `SurvivorDensity.sum_half_pow_confined_eq` | — |
| Thms 8.20–8.23 (N^{-3/2}, renewal phase) | paper-level (PROVED MATH, external fluctuation theory) | phase constants to ≤2e-3 at N≈4000 (`scales_reconciliation_2026-09-14`) |
| Obs 8.26 `U(β)=α` | PROVED (MATH) this project (last-step identity + Blackwell) | 7 digits |

## Realizer geometry

| Module | Content |
|---|---|
| `PairValuation` | `v₂(r(E)−r(D)) = S_k + min(a,b)` |
| `SuffixTransport` | orbit values realize suffixes; pair split-depth shift |
| `TransportCollapse`, `PrescribedMatching` | transport-deficit identities, prescribed matching = split depth |
| `SurvivorClusters.confined_iff_of_modEq` | congruence mod `2^{S_k+1}` ⇒ same first `k` digits ⇒ same survival through `k` |

## Orbit classification / EOC

| Module | Content |
|---|---|
| `LogCorridor` | forced exit of log corridors (8/9 unconditional) |
| `UpperEscape` | orbit dichotomy, upper exit of returning anchors, exceptional class |
| `UpperCertificates` | divergence ⇔ log upper wall anchor; block/run certificates |

## Seed statistics and dependence

| Item | Status |
|---|---|
| `SurvivorCounting.card_seeds_le_sum` | PROVED (LEAN) |
| `SurvivorDensity.survivor_count_le` | PROVED (LEAN): `#{μ<X confined N} ≤ (X/2)e^{λ*c}2^{-I₀N} + C(s_N,N)` |
| `(log X)^{-3/2}` improvement | PROVED (MATH) via PDF Lemma 8.9 |
| split-depth survival law (Haar) | PROVED (MATH) in the 2-adic model; COMPUTATIONAL agreement with integer pairs to ~0.3% (N≤150) |
| orbit clusters: survivors/clusters ≈ 2.92 (c=0), 4.75 (c=1), 6.35 (c=2) | COMPUTATIONAL (X ∈ [2^30,2^38], N ∈ [60,250]) |
| on-orbit multiplicity `Σ W₀(i)/3^i = 1.071` | HEURISTIC derivation, COMPUTATIONAL match 1.066 |
| `SurvivorClusters.confined_predecessor` | PROVED (LEAN) |
| extremal index: θ=1 short blocks, θ≈1/2.92 prefix intervals | COMPUTATIONAL (block maxima 32768 samples; records to 2^40) |
| no phase signature in placement/covariance/records | COMPUTATIONAL (slopes 0±0.003 vs −1) |

## Stale statements to mark superseded (eventually)

* `EOC_repository_audit_2026-09-12.md` §8(b), §13, §19 — N^{-3/2} labelled COMP/CONJ (proved in the Sept 8 PDF).
* `explorations/confined_shell_consolidation/PAUSE_CHECKPOINT_2026-09-12.md` §6–§7 — "missing upper lemma".
* `~/Research-Archive/.../SNAPSHOT_ENTROPY_CONFINEMENT_EXPLORATION_2026-09-13.md` §5 ("do not promote"), §6 clustering `κ̄≈4.6` (different definition from the Palm size 5.9 / ratio 2.92 measured here).
* `docs/CONSTRAINED_WORD_THEOREM_AUDIT.md` §14 (confinement-exponent conjecture).
* `EOC/TaoLike/PersistenceModel.lean` header: still correct for Lean ("not claimed"), should cite the paper proof.
* `scratch/pair_valuation_2026-09-14` exponent audit ("status C") — superseded by `scratch/scales_reconciliation_2026-09-14/REPORT.md`.
