# Errata for the recovered September 2026 research

*Written 2026-09-13.*

This document records corrections to the research material recovered from the Mac working copy
on 2026-09-12.

## How the material was preserved

The recovered files are committed **exactly as recovered**. Each one is byte-identical to the
Mac copy.

| Commit | Contents |
|---|---|
| `e76e81c` | `explorations/hypercuboid_transfer/**` |
| `7e83079` | `experiments/`, `tests/`, `results/constrained_word_asymptotics/`, `docs/CATALAN_CONTROL_AND_LIMITS.md`, `docs/COLLISION_RATE_PROOF_OBLIGATIONS.md`, `docs/CONSTRAINED_WORD_THEOREM_AUDIT.md`, `docs/PROMISING_LEMMAS.md` |
| `6315520` | `EOC_repository_audit_2026-09-12.md`, `explorations/confined_shell_consolidation/PAUSE_CHECKPOINT_2026-09-12.md` |

None of those files has been edited to hide the errors below. The historical record stands as
written, and this document supplies the corrections.

Each entry gives:

- **Original claim:** what the recovered file says.
- **Finding:** what is wrong.
- **Corrected interpretation:** what should be believed instead.
- **Verification:** how the correction was checked.

Unless stated otherwise, checks were re-run while preparing this document, against the committed
files.

---

## E1. `count_padicValNat_affine` needs the hypothesis `q ≤ K`

**Where.** `explorations/hypercuboid_transfer/ROUND3_DEFERRED_THEOREMS.md`, item D1: the
statement at lines 14–18 and the base case at line 41.

**Original claim.** For odd `C` and `0 < B`, the number of `k ∈ Finset.range (2^K)` with
`padicValNat 2 (B + 2*C*k) = q` is:

- for odd `B`: `2^K` if `q = 0`, and `0` otherwise;
- for even `B`: `2^(K-q)` if `1 ≤ q ≤ K`, and `0` otherwise.

The base case claims that for `K = 0` "only `q = 0` can occur".

**Finding.** The "otherwise `0`" branch is false when `q > K` and `B` is even, and so is the
stated base case.

- **Counterexample:** take `K = 0`, `B = 2`, `C = 1`, `q = 1`. Then `k = 0` gives
  `v₂(2) = 1`, so the true count is `1`, but the formula gives `0`.

**Corrected interpretation.**

- The statement becomes correct once `q ≤ K` is added as a hypothesis.
- The proof sketch, induction on `K` splitting `k` into `2j` and `2j+1`, is sound in the range
  `1 ≤ q ≤ K`.
- The corollary `cylinder_next_digit_card` stated in the same file already assumes
  `hqK : q ≤ K`, so it is unaffected.
- Only the `q = 1` case is formalized, as `EOC.CylinderCounting.cylinder_next_digit_eq_one_card`
  in `EOC/TaoLike/CylinderDigitCounting.lean`. The general-`q` law is not formalized.

**Verification.** Brute force, with even `B ∈ [2, 38]`, odd `C ∈ [1, 11]`, `K ≤ 6`, `q ≤ 9`,
and `padicValNat 2 0 = 0`:

- the formula matches in all 2394 cases with `1 ≤ q ≤ K`;
- it fails in 794 cases with `q > K`.

---

## E2. The cyclic-rotation "refutation" came from testing words outside the feasible shell

**Where.**

- `docs/PROMISING_LEMMAS.md`, "Lemma 3 (REFUTED …)" (lines 41–56)
- `docs/CONSTRAINED_WORD_THEOREM_AUDIT.md`, lines 165–173 and 237
- `experiments/cyclic_rotation_audit.py`, lines 238–262
- `results/constrained_word_asymptotics/cyclic_rotation_audit.json` and `rotation_run.log`

**Original claim.** Rotating a word to start right after the (unique) maximizer of `R_j` should
give a confined rotation. This is recorded as **refuted**:

- the construction "succeeds only 435 times (1.34%)" out of 32,518 tested words;
- the minimal counterexample given is `(1,3,1)` at `c = 0`;
- the diagnosis given is that unbounded digits break the cycle-lemma mechanism.

**Finding.** The test set was `N ∈ {3,4,5,6}`, `s ∈ [N, 2N+5]`, `c ∈ {0,1}`. It is dominated
by words whose **endpoint is infeasible**, meaning `R_N > c`. No rotation of such a word can be
confined, because every rotation has the same endpoint `R_N`. The construction succeeds on
exactly the words with a feasible endpoint and fails on exactly the others.

- The counterexample `(1,3,1)` has `S₃ = 5 > ⌊3α⌋ = 4`, so it lies outside the shell.
- The recovered audit already records this in `EOC_repository_audit_2026-09-12.md`, line 240.

**Corrected interpretation.** The data support the rotation statement for words in the feasible
shell; they do not refute it. For `c ≥ 0`, the statement has an elementary proof:

> Let `j*` maximize `R_j` (`0 ≤ j ≤ N`) and rotate the word to start at position `j*`.
> - The first `N − j*` partial drifts of the rotated word are `R_{j*+i} − R_{j*} ≤ 0 ≤ c`.
> - The remaining ones are `R_N − R_{j*} + R_i ≤ R_N`.
>
> So the rotation is confined whenever `R_N ≤ c`.

- Unbounded digits do not break **existence** of a confined rotation. Uniqueness and counting
  statements are separate questions.
- Lemma 2's recorded non-constancy of rotation counts is not affected by this entry.
- This is the mechanism behind the rotation lower bound `|W_c(N, s)| ≥ C(s−1, N−1)/N` recorded
  (proved on paper, not in Lean) in the audit and checkpoint.

**Verification.** The committed script's own loop was re-run, using its own functions on its own
test set:

- 32,518 words tested;
- 435 successes;
- 435 words with a feasible endpoint (`confined_exact(s, N, c)`);
- success ⇔ feasible endpoint on **32,518 / 32,518** words.

---

## E3. The collision-rate comparison used a mismatched baseline

**Where.**

- `docs/CONSTRAINED_WORD_THEOREM_AUDIT.md`, lines 18, 184–200 (§10) and 238–239
- `docs/COLLISION_RATE_PROOF_OBLIGATIONS.md`, lines 34–46 and 122

**Original claim.** The naive stationary collision rate is `R₂ = α = log₂ 3`. This is the exact
Rényi-2 entropy of the unconditioned digit law Geom(1/2), which is also recorded in
`ROUND2_REPORT.md` around line 431. Because the measured `−log₂ P_{N,k} / k` stays below `α`,
the docs record `R₂ = α` as "refuted" on the confined, endpoint-conditioned, uniform problem.

**Finding.** Geom(1/2) has mean digit `2`. The uniform measure on the shell has mean digit
`s_N / N ≈ α ≈ 1.585`. The geometric law matched to that mean is Geom(1/α):

| Law | Mean digit | Rényi-2 entropy (bits/digit) | Shannon entropy (bits/digit) |
|---|---|---|---|
| Geom(1/2) | 2 | `α ≈ 1.5850` | 2 |
| Geom(1/α) | `α` | `≈ 1.1176` | `≈ 1.5056` |

Both entropies of the matched law are below `α`. So a measured rate below `α` is what any
endpoint-conditioned uniform measure would show. It says nothing specific about confinement.

**Corrected interpretation.**

- **Still valid:**
  - the exact formula `P_{N,k} = Σ_S F(k,S) · B(k,S)² / A_N²`;
  - its brute-force cross-check;
  - the stored `N = 40`, `c = 0` rate curve, as finite-`N` data.
- **Uninformative:** "refuting `R₂ = α`". The comparison was against the wrong baseline.
- **Remains open:** any statement about a limiting rate function `I₂(θ)` and its relation to
  confinement. The stored data (`N ≤ 50`) are far from any limit.
- **Not re-verified here:** the recovery audit also reported that the θ-dependence persists for
  unconfined uniform compositions at large `N`.

**Verification.** The entropies above come from the closed forms for Geom(p):

- Rényi-2: `−log₂(p / (2 − p))`
- Shannon: `h(p) / p`, where `h` is the binary entropy

---

## E4. The Catalan constant is `−½ log₂ π ≈ −0.8257`

**Where.**

- `experiments/catalan_barrier_control.py`, line 264 (and the approximate remark "~ −0.9" at
  line 191)
- `results/constrained_word_asymptotics/catalan_run.log`, line 46

**Original claim.** The correction term "approaches `log2(1/sqrt(pi)) = −0.9624...` exactly".

**Finding.** The expression `log₂(1/√π)` is the correct constant, since
`C_n ~ 4ⁿ / (n^{3/2} √π)`. Its numerical value was mis-evaluated.

**Corrected interpretation.** `log₂(1/√π) = −½ log₂ π ≈ −0.8257`. The stored data approach this
value; the recorded recovery audit reports `−0.8308` at `n = 320`.

**Verification.** `−0.5 · log₂ π = −0.82574…`, computed directly.

---

## E5. `valuationShell_card` was cited as already Lean-proved, but no such module is in the repository

**Where.** The name is cited as "already proved" or "already Lean-proved" in:

- `explorations/hypercuboid_transfer/ROUND2_REPORT.md` (e.g. lines 95, 198, 722)
- `explorations/hypercuboid_transfer/ROUND2_LEAN_CANDIDATES.md` (lines 34, 42)
- `explorations/hypercuboid_transfer/ROUND3_FORMALIZATION_REPORT.md` (e.g. lines 39, 118, 432)
- `explorations/hypercuboid_transfer/scripts/round2_verification.py` (lines 108, 202)

**Original claim.** `EOC.CompositionCounting.valuationShell_card`, the stars-and-bars count
`C(s−1, N−1)`, is an existing Lean theorem in this repository.

**Finding.** Neither `valuationShell_card` nor any `CompositionCounting` module exists:

- not under `EOC/`;
- not anywhere in this repository's git history.

According to `explorations/confined_shell_consolidation/PAUSE_CHECKPOINT_2026-09-12.md`
(lines 93–99), it lived only in a recovered backup file `EOC/CompositionCounting.lean`. That file:

- was never integrated;
- was never kernel-checked;
- "must not be cited as formally verified";
- is **not present on this machine**.

The recovered audit (line 14) and `docs/CONSTRAINED_WORD_THEOREM_AUDIT.md` (line 50) already
flag the name as nonexistent.

**Corrected interpretation.**

- The combinatorial identity itself is classical and true.
- The claim that it is **formally verified here** is unsupported.
- Any argument that treats it as an available Lean theorem, including the "Low difficulty"
  estimates for Round 2 candidates that depend on it, has an unmet dependency.

**Verification.** A repository-wide search, and `git log --all -S valuationShell_card` over
`*.lean`, both return nothing.

---

## E6. Docstring formula error in `PersistenceRateCramer.lean` (the proofs are unaffected)

**Where.** `EOC/TaoLike/PersistenceRateCramer.lean`, tracked on `main` since `3dfae5c`, docstrings
at lines 47 and 52–53.

**Original claim.**

- The Legendre integrand is described at "parameter `t = 2 * exp(lam)`".
- The critical point `t* = 2(a−1)/a` is described as "matching `2 * Real.exp lambdaStar` at
  `a = collatzAlpha`".

**Finding.** `lambdaStar` is defined in `EOC/TaoLike/PersistenceModel.lean`, line 333, as
`log(α / (2(α−1)))`. Hence:

- `exp(−lambdaStar) = 2(α−1)/α = t*`;
- `t* ≈ 0.7381`, whereas `2 · exp(lambdaStar) ≈ 2.7095`.

The change of variables that matches the integrand to the moment-generating function
`Mfun α λ = e^{λα} / (2e^λ − 1)` (`PersistenceModel.lean`, line 126) is `t = e^{−λ}`:

`(a−1)·ln t + ln(2 − t) = −ln Mfun(a, λ)`, exactly.

**Corrected interpretation.**

- The docstrings should read `t = e^{−λ}` and `t* = exp(−lambdaStar)`.
- This affects comments only. Every theorem statement and proof in the file is correct, and the
  module builds.
- The docstring correction is deliberately **not** made in this preservation branch. It is left
  as separate follow-up work.

**Verification.**

- `tStar(α) = 0.738140 = exp(−lambdaStar)`.
- The identity above holds to 12 significant digits at `λ ∈ {0.1, 0.3, lambdaStar}`.
- The algebra: with `t = e^{−λ}`, `(a−1)(−λ) + ln(2 − e^{−λ}) = −aλ + ln(2e^λ − 1)`.

---

## E7. The `8/9` logarithmic-floor exclusion is not an open theorem

**Where.**

- `EOC_repository_audit_2026-09-12.md`: line 17 ("Strongest new deduction"), §7 (line 143 ff.)
  and the roadmap in §17
- The withdrawal is in `explorations/confined_shell_consolidation/PAUSE_CHECKPOINT_2026-09-12.md`,
  lines 104–110 and 345–346.

**Original claim.** The audit presents raising the drift-floor exponent to `8/9` as its
"strongest new deduction" (proved on paper), and schedules Lean work for it in its roadmap.

**Finding.**

- The later checkpoint already withdrew the novelty claim. The result is Lemma 4.3, Theorem 4.5
  and Remark 4.7 of the EOC manuscript (Revision 5).
- The manuscript's Theorem 4.5 is now **formally verified** in `EOC/HarmonicPacking.lean`,
  merged to `main` in `20fda6e` (PR #2):
  - `EOC.HarmonicPacking.injective_orbit_not_eventually_log_floor`
  - `EOC.HarmonicPacking.injective_orbit_log_floor_fails_infinitely_often`
- Together they state: for an odd seed with an injective accelerated orbit and every real
  `B < 8/9`, the floor `R_k ≥ −B·log₂ k` fails for infinitely many `k`.
- The same module also proves the explicit carry budget
  `E_N ≤ (1/9)·log₂ N + 7/(9 ln 2)` (`carryE_le`).

**Corrected interpretation.** The `8/9` exclusion is part of the flagship EOC development and is
machine-checked. It should not be described as unresolved or as new. Two precise caveats:

- **The audit's finite-prefix packaging** `g ≥ (8/9)·log₂ N − log₂ M − 3` (§7; roadmap §17,
  item 2) is a different formulation. It is not separately formalized.
- **The audit's "exact drift identity"** `R_N = log₂(m₀/m_N) + E_N` (roadmap §17, item 1) is
  formalized only in exponentiated form, as `m_k · 2^{R_k} = m_0 · U_k`
  (`EOC.HarmonicPacking.orbit_mul_two_rpow_R`).

---

## Minor corrections

- **Digit count of `C_100`.** `docs/CATALAN_CONTROL_AND_LIMITS.md`, line 13, calls `C_100` "a
  60-digit integer". It has **57** decimal digits (checked directly).
- **"Monotonically".** `docs/CONSTRAINED_WORD_THEOREM_AUDIT.md`, line 184, says
  `−log₂ P_{N,k} / k` "rises smoothly and monotonically" to `≈ 1.27` at `θ = 1`. The stored data
  (`results/constrained_word_asymptotics/prefix_collision_audit.json`, `N = 40`, `c = 0`) peak at
  `1.2961` at `θ = 0.95`, then fall to `1.2713` at `θ = 1`. So the rise is not monotone at the end.

## Status updates to statements in the recovered files

- **CI failure at `c6bc929`.** The audit and checkpoint report it as unexplained. The step
  results of the 12 most recent push runs on `main` (`79a4892` through `20fda6e`) show:
  - the Lean build step (`leanprover/lean-action`) succeeded in every one;
  - the documentation step (`leanprover-community/docgen-action`) has failed on every push
    since `5a30e9f`, including `c6bc929`.

  It is a documentation-generation failure, not a Lean failure.
- **The two Lean drafts.**
  - `docs/CONSTRAINED_WORD_THEOREM_AUDIT.md` (lines 30–31 and 60) lists
    `EOC/TaoLike/PersistenceRateCramer.lean` and `EOC/TaoLike/CylinderDigitCounting.lean` as
    untracked.
  - `ROUND3_FORMALIZATION_REPORT.md` describes them as "hand-verified, pending compiler
    confirmation" (lines 13–16).
  - Both are now committed and build on `main`: `3dfae5c`, and `5dd38ea` via `960e3ef`.
  - The recovered `CylinderDigitCounting.lean` draft contained a false intermediate identity:
    it used the affine coefficient `2·3^t` where `3·(x + 2·3^t·k) + 1 = (3x + 1) + 2·3^{t+1}·k`
    requires `2·3^{t+1}`.
  - The draft was corrected before commit, and the theorem statement did not change.
  - The Round 3 report's statement that the drafts were hand-verified was therefore wrong for that
    file. The Round 3 prose itself states the restart law `orbit m t + 2·3^t·k` correctly.

## Files referenced by the recovered material but not recovered

None of these files exists in this repository, in the Mac copy transferred to this machine, or in
the local recovery archive. They were **not** recreated.

| File | Referenced in |
|---|---|
| `EOC/CompositionCounting.lean` | Round 2 and Round 3 reports, and the 2026-09-12 checkpoint. Recovered backup, never compiled. See E5. |
| `EOC/FiniteValuationWord.lean` | Round 3 report and the 2026-09-12 checkpoint. Recovered backup, never compiled. |
| `LOWER_BOUND_AUDIT.md`, `lower_bound_check.py`, `phase_resolved.py`, `collision_rate.py` | The 2026-09-12 checkpoint |
| `explorations/hypercuboid_transfer/scripts/round2_output.txt` | Round 2 report and the 2026-09-11 checkpoint. Can be regenerated by re-running `round2_verification.py`. |
| `scratch/extremal_orbit_prefix_audit.py` | `ROUND2_LEAN_CANDIDATES.md`, `ROUND3_DEFERRED_THEOREMS.md`, `round2_verification.py` |

According to the checkpoints, the two Lean files came from the Mac's former working copy
(`~/Desktop/eoc-lean-verification-damaged-backup`). The copy of that directory transferred to
this machine is empty.

## Outside the scope of this errata

- It changes no theorem statement and no recovered file.
- It does not correct the `PersistenceRateCramer.lean` docstrings (E6). That is follow-up work.
- It does not update the README.
