# Pause checkpoint — confined-shell consolidation (2026-09-12)

This file did not previously exist; it is created fresh by this checkpoint.
`explorations/confined_shell_consolidation/` itself did not exist before this
write — it is created now to hold this note. No other file in that directory
exists yet (see §10).

## 1. Repository identity

```
pwd:                 /Users/eliasdejesus/Desktop/eoc-lean-verification
git rev-parse HEAD:  c6bc9297febb26c8cb5aeeb5ebb4c5dd1a2811a0
git branch --show-current: main
git diff --stat HEAD: (empty — no tracked file has been modified)
```

`git status --short`:
```
?? EOC/TaoLike/CylinderDigitCounting.lean
?? EOC/TaoLike/PersistenceRateCramer.lean
?? "EOC_latestRev (4).pdf"
?? EOC_repository_audit_2026-09-12.md
?? docs/CATALAN_CONTROL_AND_LIMITS.md
?? docs/COLLISION_RATE_PROOF_OBLIGATIONS.md
?? docs/CONSTRAINED_WORD_THEOREM_AUDIT.md
?? docs/PROMISING_LEMMAS.md
?? experiments/
?? explorations/
?? results/
?? tests/
```

**State clearly:**
- All tracked files are unchanged (`git diff --stat HEAD` is empty).
- Everything listed above is untracked, not staged, not committed.
- Nothing has been committed or pushed in this session.
- The confined-shell consolidation work exists only under
  `explorations/confined_shell_consolidation/` (this file, newly created).
- `"EOC_latestRev (4).pdf"` and `EOC_repository_audit_2026-09-12.md` are
  present but were not created by this session and their provenance is not
  established here — flagged, not investigated further per this checkpoint's
  read-only scope.

**On iCloud-dataless placeholders:** this Mac's `~/Desktop` is iCloud-synced.
During this session, a large Mathlib precompiled-cache download
(`lake exe cache get`, run against the separate damaged-backup repository,
not this one) drove local disk usage high enough that macOS's storage
optimizer evicted local copies of a number of unrelated Desktop files —
including some inside this active repository (`README.md`, `EOC/Basic.lean`,
`lean-toolchain`, `.git/HEAD`, `.git/config` were observed with the
`dataless` file flag) — into cloud-only placeholders. **These are not
deleted files.** `stat` metadata (size, mtime) remained correct throughout,
and `git show HEAD:README.md` / `git status` / `git diff` all successfully
returned correct content when tested, confirming the underlying data is
intact and recoverable via git/iCloud. Plain shell `cat`/read calls in the
sandboxed tool environment did not reliably re-materialize a dataless file on
their own (one 29-byte file stayed reported as empty on a bare `cat`), but no
git-mediated read failed or returned wrong content. Treat any locally "empty"
read of a tracked file on this Mac as a placeholder-materialization question,
not evidence of data loss, and prefer `git show HEAD:<path>` to check.

## 2. Why the Lean work is paused

- Mathlib's precompiled cache download (`lake exe cache get`, damaged-backup
  repo) completed successfully: **8,323 `.olean` files decompressed**,
  terminating with `Completed successfully!`.
- The cache occupies approximately **6.4 GB** in the damaged-backup
  repository's `.lake/packages`.
- **No `lake build` was run afterward** — building was intentionally not
  attempted once the disk/eviction issue was discovered.
- The Mac reached critically low available disk space (11 GB free of 228 GB,
  95% used) immediately after the cache download, and macOS began evicting
  Desktop files into iCloud placeholders as described in §1.
- Reported free space increased only modestly after this was noticed; no
  cleanup that would materially change that was performed in this session
  (no cache deletion, no file removal).
- The user has decided this Mac is not presently suitable for continued Lean
  builds. Future Lean verification will resume on a Linux machine with more
  storage headroom.

**Build status, recorded honestly:**
- The public repository's GitHub Actions workflow at `c6bc929` is reported
  (by the user) to have failed. This session did not independently inspect
  that CI run, so the failure is recorded as **reported, not confirmed
  in-session**.
- It is unknown whether the failure was in the Lean build itself or in a
  documentation-generation stage — not established this session.
- The tracked source at `c6bc929` is, by textual audit in earlier sessions,
  free of `sorry` and does not textually reference disallowed axioms — but
  **compilation of the current HEAD has not been independently kernel-checked
  in this session** (no working local Mathlib build was reached before the
  disk issue intervened).
- The recovered backup file `EOC/CompositionCounting.lean` (candidate
  `EOC.valuationShell_card`) **remains unintegrated** into the active
  repository and **must not be cited as formally verified** — its own
  isolated kernel-check was blocked by the same disk/build situation (see
  prior session's report: `lake env lean` failed immediately on the first
  import because no `.olean` existed at all prior to this session's cache
  fetch; the cache fetch was completed, but `lake build`/`lake env lean` on
  the recovered files themselves was never subsequently run).

## 3. Corrected provenance finding

- The elementary "(8/9) logarithmic-floor exclusion" result is **already
  present in the latest EOC manuscript** — it appears in **Lemma 4.3,
  Theorem 4.5, and Remark 4.7**.
- The earlier classification of (8/9) as a *new* deduction (made in a prior
  session/round) is **withdrawn**.
- A finite-horizon explicit-constant formulation of it may still be useful as
  a standalone Lean corollary, but it is **not** a new (8/9)-type result and
  should not be reported as one.

## 4. Strongest new proved mathematical result (as reported for consolidation)

Setup:
```
alpha = log_2(3)
s_N   = floor(N * alpha) + c
U(N, s_N) = C(s_N - 1, N - 1)                       [unrestricted shell count]
W_c(N, s_N) = { (d_1,...,d_N) in Z_{>=1}^N :
                  S_N = s_N,
                  S_j <= floor(j * alpha) + c  for all j <= N }
```

**Confined-shell lower bound**, for integer `c >= 0`:

```
|W_c(N, s_N)|  >=  (1/N) * C(s_N - 1, N - 1)
```

**Classification:**
- **PM** (proved mathematically) as a result of this consolidation round.
- **PA** (prior art): Spitzer's rotation lemma is the prior-art tool the
  proof rests on.
- The application of that tool to *this specific irrational prefix barrier*
  (the `floor(j*alpha) + c` boundary) appears **absent** from the current
  manuscript and from the tracked repository — i.e., the combination is
  claimed as newly assembled here, not the underlying lemma.

**Proof summary (as consolidated, not independently re-derived in this
session):**
1. Rotate each shell composition after an index attaining the maximum of its
   chord deviation.
2. Spitzer's lemma places that rotation's partial sums below the chord
   (linear interpolation between the endpoints).
3. The chord itself lies below the irrational barrier `floor(j*alpha) + c`.
4. Each confined word has at most `N` rotational preimages (one per starting
   index).
5. Hence `U(N, s_N) <= N * |W_c(N, s_N)|`, i.e. the boxed bound above.

**Conventions used:** `c` is a nonnegative integer; digits `d_i` are positive
integers; the endpoint sum `s_N` sits exactly on the barrier
`floor(N*alpha) + c`.

## 5. Exact continued-fraction subsequence (as reported)

For lower convergents `p/q < alpha` at which the rational chord floor agrees
exactly with the irrational barrier:

```
|W_0(q, p)|  =  (1/q) * C(p - 1, q - 1)
```

**Tested denominators:** `q = 2, 12, 53, 665, ...` (consistent with known
continued-fraction convergent denominators of `log_2(3)`).

- The equality is stated to follow from the classical cycle lemma together
  with coprimality of `p` and `q`.
- The **general** statement (for an arbitrary qualifying convergent) is
  marked **PM only to the extent justified in `LOWER_BOUND_AUDIT.md`** — that
  file does not exist in this repository's working tree as of this
  checkpoint (see §10); its justification could not be located or checked in
  this session.
- Any unverified universal formulation of this identity should be treated as
  **requiring final proof review**, not as settled.

## 6. Central open upper bound

The matching estimate

```
|W_c(N, s_N)|  <=  (C(c) / N) * C(s_N - 1, N - 1)
```

is **NOT proved**. **Classification: CONJ.**

- Exact computation through `N = 2000`, `c = 0,...,4` is reported to support
  boundedness of `rho_c(N) = N * |W_c| / U`.
- For `c = 0`, the observed range is approximately **1 to 2.708**.
- The strongest proposed route: a conditioned-geometric-bridge survival
  estimate.
- The missing lemma: an `O(1/N)` upper bound for a bridge under a linearly
  closing wedge, plus a bounded Sturmian perturbation.
- Existing constant-barrier bridge theorems **do not apply literally** to
  this linearly-closing/irrational-slope setting.
- **No upper-bound theorem should be claimed until that adaptation is
  proved.**

## 7. Corrected phase conjecture

The earlier model `(c+1) * g({N*alpha})` (fractional-part-driven, rigid form)
is reported to have been **too rigid** and is superseded.

**Current computational conjecture:**

```
rho_c(N) ~ A(phi_N) * c + B(phi_N) + o(1),      phi_N = {N * alpha}  (fractional part)
```

- A persistent **phase jump** is observed near `phi = alpha - 1`.
- The jump is attributed to a switch in the final Sturmian driving digit.
- Lower-convergent denominators (§5) attain `rho_0 = 1` exactly.
- High-phase values approach approximately **2.7**.
- Computation suggests an effective offset around `c + 1.02`; it is
  **unresolved** whether this tends to `c + 1` in the limit.
- `gamma_conf = 1` and `gamma_total = 3/2` remain **computational/
  conjectural** until the matching upper bound (§6) is proved.
- The *ordinary* limit of `rho_c(N)` is computationally disfavored (i.e., it
  likely does not exist as a plain limit); phase-indexed **subsequential**
  limits are what is conjectured instead.

## 8. Collision-rate status

```
I_2(theta) := lim_{N->infty} -(1/N) * log_2( P_{N, floor(theta*N)} )
```

**Proved:**
- `P_{N,k+1} <= P_{N,k}` (monotonicity)
- `P_{N,0} = 1`
- `P_{N,N} = 1 / |W_c|`

**Computational / conjectural:**
- Existence of `I_2(theta)` as an actual limit.
- Increasing and strictly convex behavior in `theta`.
- Asymptotic independence from `c` and from the Sturmian phase.
- A transfer-operator or variational representation for `I_2`.

**Refuted:**
- A single stationary scalar collision rate `R_2` (theta-independent) — this
  matches and reconfirms the refutation already recorded in this session's
  earlier `docs/COLLISION_RATE_PROOF_OBLIGATIONS.md`.

## 9. EOC relevance

**Stated prominently:** counting confined words does **not** control the
natural-number placement of their least realizers.

Logical chain:
```
unrestricted compositions
  -> confined compositions
  -> confined-word counts
  -> exact residue realizers
  -> small least realizers
  -> prefixes of one fixed natural orbit
  -> EOC
```

**The missing arrow** is anti-concentration of the least-realizer /
moving-anchor map — i.e., nothing established so far (in this or prior
rounds) shows that *counting* confined words says anything about how small
their *least realizers* actually are.

- The lower bound (§4) does **not** help EOC directly.
- The matching upper bound (§6), even if proved, would **not** prove EOC by
  itself.
- The necessary missing result remains either:
  - a bound on `A(X, N) = #{ D in W_c(N) : r(D) <= X }`, or
  - a pointwise exponential realizer floor `r(D) >= 2^(epsilon*N - O(1))`.
- **No Collatz consequence emerged from this round.**

## 10. Files and reproducibility

**Actual current contents of `explorations/confined_shell_consolidation/`:**
prior to this write, the directory **did not exist**. This checkpoint file
is the only file present in it as of now. None of the following files
referenced in the dictated reproduction plan were found anywhere in this
repository's working tree and are **not inventoried as present**:
`lower_bound_check.py`, `phase_resolved.py`, `collision_rate.py`,
`LOWER_BOUND_AUDIT.md`. This is recorded as a discrepancy rather than
silently assumed — if these scripts exist elsewhere (another machine,
another session's workspace), they have not been located or copied into this
repository.

Grouped inventory (as currently on disk, this directory only):
- **documentation:** `PAUSE_CHECKPOINT_2026-09-12.md` (this file)
- **experiments:** (none present)
- **tests:** (none present)
- **numerical results:** (none present)
- **logs:** (none present)
- **binary data files:** (none present)

**Recorded (not executed) reproduction commands**, as dictated for the
consolidation record — these were **not run** in this session:
```
python3 lower_bound_check.py
python3 phase_resolved.py
python3 collision_rate.py
```
Approximate runtime and dependencies for these were not independently
confirmed in this session (the scripts themselves are not present here to
inspect).

## 11. Linux resumption plan

Exact first-session plan for the Linux machine:
1. Confirm at least 40–50 GB free disk space.
2. Install Git, `elan`, and required build tools.
3. Clone `innerlightr-wq/eoc-lean-verification`.
4. Confirm the pinned `lean-toolchain` and `lake-manifest.json`; **do not**
   run `lake update`.
5. Fetch the pinned Mathlib cache once (`lake exe cache get`).
6. Run `lake build` on the unchanged public repository.
7. If the build fails, diagnose the first actual error before doing anything
   else.
8. Independently copy and inspect the recovered backup files
   (`EOC/CompositionCounting.lean`, `EOC/FiniteValuationWord.lean`) without
   overwriting any tracked file.
9. Kernel-check `FiniteValuationWord.lean` and `CompositionCounting.lean` in
   isolation.
10. Only after successful compilation, decide whether to integrate them.
11. Resume with a proof attempt for the conditioned-bridge `O(1/N)` upper
    bound (§6) **before** attempting any Lean formalization of it.

**Exact first mathematical task on Linux:** audit and attempt to prove the
missing conditioned-geometric-bridge survival lemma needed for
`|W_c(N, s_N)| <= C(c) * U(N, s_N) / N`. **This task is not begun in this
session.**

## 12. Final status

- **Strongest proved result:** the confined-shell lower bound
  `|W_c(N, s_N)| >= (1/N) * C(s_N - 1, N - 1)` (§4), built on Spitzer's
  rotation lemma applied to this irrational prefix barrier — recorded here
  as PM for this consolidation round, not independently re-derived by this
  session.
- **Strongest computational finding:** boundedness of `rho_c(N)` through
  `N = 2000`, `c = 0..4`, with the phase-indexed structure of §7.
- **Strongest open conjecture:** the matching upper bound
  `|W_c(N, s_N)| <= (C(c)/N) * C(s_N - 1, N - 1)` (§6), CONJ, plus the
  phase-conjecture form of `rho_c(N)` (§7).
- **Hypotheses refuted:** a single stationary scalar collision rate `R_2`
  (§8); the earlier rigid phase model `(c+1) * g({N*alpha})` (§7); the
  earlier claim that the (8/9) logarithmic-floor exclusion was a new
  deduction (§3, now known to already be Lemma 4.3/Theorem 4.5/Remark 4.7 of
  the manuscript).
- **Exact EOC blocker:** anti-concentration of the least-realizer/
  moving-anchor map is missing; neither the proved lower bound nor the
  conjectured upper bound on confined-word counts constrains where least
  realizers actually land among the naturals (§9).
- **Build status:** Mathlib cache fetched successfully in the damaged-backup
  repository (8,323 `.olean` files, ~6.4 GB); `lake build` was never run;
  the public repo's CI at `c6bc929` is reported failed, not independently
  diagnosed this session; the recovered `CompositionCounting.lean` remains
  unintegrated and uncertified.
- **Disk/storage reason for migration:** this Mac reached 95% disk usage
  (11 GB free) immediately after the Mathlib cache download, triggering
  iCloud eviction of local file copies across the synced Desktop (including
  inside this active repository). Lean verification work is moving to a
  Linux machine with more headroom rather than continuing here.
- **Complete git status:** see §1 — `git diff --stat HEAD` is empty (no
  tracked file changed); the untracked list is exactly as printed in §1;
  `HEAD` remains `c6bc9297febb26c8cb5aeeb5ebb4c5dd1a2811a0` on branch `main`.
- **Confirmation:** nothing was committed, staged, or pushed in this session
  or in the making of this checkpoint.
