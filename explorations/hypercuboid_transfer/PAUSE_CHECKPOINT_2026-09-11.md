# EOC Program — Pause Checkpoint (2026-09-11, end of Mac session)

The EOC program is paused here. Work resumes on a Linux machine with a 1 TB
drive, where Lean/Mathlib verification will have substantially more disk
headroom. This checkpoint records only work already completed — no further
research, builds, dependency downloads, file modifications, commits, or
pushes were performed after this file was written.

## Repository state

1. **Canonical repository**: `~/Desktop/eoc-lean-verification`.
2. **Damaged former working copy**: preserved, untouched, at
   `~/Desktop/eoc-lean-verification-damaged-backup` — treat as inert. Not a
   source of anything further; kept only as a fallback.
3. The canonical repository is a fresh `git clone` of
   `https://github.com/innerlightr-wq/eoc-lean-verification.git`, verified
   against GitHub directly (`git ls-remote` and `git log`), with tracked tip
   commit **`c6bc929`** ("correct EOC documentation after mathematical
   audit"), clean tracked tree, correct `origin`, branch `main`.

## Recovered uncommitted work

4. All uncommitted Round 1–3 material under
   `explorations/hypercuboid_transfer/` was recovered and hash-verified
   against this session's own record, **except** `scripts/round2_output.txt`,
   which was corrupted at the source (zero-byte content behind a stale
   directory-size entry) and could not be recovered. It is fully regenerable
   by rerunning `scripts/round2_verification.py` (present and intact) — it
   is saved stdout, not source material, so nothing mathematical was lost.

   Present and verified: `ROUND1_REPORT.md`, `ROUND2_REPORT.md`,
   `ROUND2_LEAN_CANDIDATES.md`, `ROUND3_FORMALIZATION_REPORT.md`,
   `ROUND3_DEFERRED_THEOREMS.md`, `scripts/two_step_law_check.py`,
   `scripts/three_step_law_check.py`, `scripts/round2_verification.py`.

## New Lean work (untracked, uncommitted)

5. Two new Lean files exist, untracked:
   - `EOC/TaoLike/PersistenceRateCramer.lean`
   - `EOC/TaoLike/CylinderDigitCounting.lean`

6. **`PersistenceRateCramer.lean`** contains the general-level
   persistence-rate/Cramér identity for `a ∈ (1,2)`
   (`geom2CramerRate_eq_sSup`), with the repository's own Collatz constant
   `I0` (at `a = collatzAlpha`) as a specialization
   (`I0_eq_geom2_cramer_rate`), not the sole case proved.

7. **`CylinderDigitCounting.lean`** currently formalizes **only the `q = 1`**
   instance of the one-step cylinder-lift digit-counting law
   (`cylinder_next_digit_eq_one_card`). The general-`q` theorem is **not**
   present in this file — it remains an explicitly deferred item, with a
   complete hand-verified proof sketch recorded as item **D1** in
   `ROUND3_DEFERRED_THEOREMS.md`.

8. **Compiler status, stated exactly and not to be altered by inference**:
   neither new Lean file has been kernel-checked by Lean. Both are
   **hand-reviewed only**. No claim of "compiles" or "verified" applies to
   either file at this checkpoint.

9. The most recent verification attempt this session returned
   **LEAN-SAFE-C**: compiler verification was blocked by the total absence
   of any local `.lake`/Mathlib dependency tree in the canonical repo (a
   fresh clone carries no gitignored build state), combined with the unsafe
   disk cost of rebuilding Mathlib from source on this machine's remaining
   headroom. No `lake build`, dependency fetch, or partial compile was run
   as a result — this was a deliberate stop, not a failed attempt.

## Environment notes

10. `lean-toolchain` in this repository is authoritative and currently
    specifies **`leanprover/lean4:v4.34.0-rc1`**. This is the version
    actually installed and confirmed working (`lean --version`,
    `lake --version`) during this session's checks. Do not substitute an
    older remembered version (e.g. 4.33.0) in future sessions — read
    `lean-toolchain` fresh each time.
11. This Mac's disk (`/System/Volumes/Data`) is presently constrained
    (last measured: 16 GiB available, 92% capacity). A prior from-source
    Mathlib build on this machine drove the disk to exhaustion and
    corrupted a broad set of files (since fully recovered, per above). By
    deliberate choice, Mathlib was **not** rebuilt on this Mac after that
    incident, to avoid repeating it. Verification work is intentionally
    deferred to the Linux machine's larger drive.

## Scope discipline for the next session

12. **No mathematical result should be downgraded** on account of the
    environment failure — the two new theorems' mathematical content is
    unaffected by any of this session's disk/build/git incidents, and the
    hand-verification already performed (including catching and fixing
    three real Lean-code issues before this checkpoint) stands as-is.
    **Equally, no result should be upgraded** to "Lean-verified" or
    "compiles" until an actual `lake build` (or targeted `lake env lean`
    single-file check) completes successfully on a machine with adequate
    dependency headroom. The correct next action on the Linux machine is
    to fetch Mathlib (via cache if reachable there, else from source with
    real headroom) and run the single-file checks on
    `PersistenceRateCramer.lean` first, then `CylinderDigitCounting.lean`,
    exactly as attempted (and safely deferred) on the Mac.
