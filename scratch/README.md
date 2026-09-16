# `scratch/` — research computations and round reports

Everything here is **outside the Lean library** (see `lakefile.toml`). Nothing in `scratch/` is a proof. Each dated
folder is one research round. Its `REPORT.md` states what was proved (with Lean module names), what was computed, and
the labels used. The consolidated status is in [`../docs/RESEARCH_STATUS.md`](../docs/RESEARCH_STATUS.md).

A report's header line "Nothing committed or pushed" describes the state at the end of that round. All rounds of
2026-09-14/15 were committed together at the 2026-09-15 checkpoint.

Of the 2026-09-16 rounds, only those behind the ShapeTail milestone are in git: `shapetail_2026-09-16/`,
`pressure_2026-09-16/`, `shapetail_allEven_2026-09-16/` and `avgpressure_2026-09-16/` (threshold arithmetic for
`EOC/AverageOddDark.lean`; `python3 threshold.py`, `python3 lowershells.py`). For the last one, run `python3 residues.py > residues.txt`
(standard library, ~2 s). Its output guided the schedule of `EOC/ShapeUnconditional.lean` but is not part of the proof;
the Lean kernel re-checks every finite fact the proof uses. The other exploratory rounds of that day are not
committed. Some committed module docstrings and reports still cite them (e.g. `rmin_2026-09-16`, `cheap_2026-09-16`,
`transient_2026-09-16`, `oddpressure_2026-09-16`, `whitecount_2026-09-16`, `cw*_2026-09-16`). Those citations are provenance only: nothing
proved in Lean depends on them, and they are not reproducible from this repository.

## Dependencies

* **Python 3** (tested with 3.14), **standard library only**. No NumPy is needed or used by any script in this
  directory.
* **gcc** for the `.c` programs: `gcc -O2 -fopenmp -o prog prog.c -lm`. The programs use GCC's `__int128`. OpenMP is
  optional: without `-fopenmp` the pragmas are ignored and the program runs single-threaded. `tao_2026-09-15/lambda1q.c`
  also needs `-lquadmath`. Usage is in each file's header comment or `argv` parsing; only a few headers carry a
  build line.
* Run every command from inside the round's folder.

## What is not in git (and how to regenerate it)

`scratch/.gitignore` lists the following. They exist only locally and are not needed to check any reported number.

* **Compiled executables.** Rebuild from the `.c` file of the same name.
* **Raw binary dumps `*.bin`** (up to 324 MB each) from `phase_dependence_2026-09-14/survivor_dump.c`,
  `lift_mixing_2026-09-14/word_state.c`, `weyl_2026-09-14/weyl_words.c` and `prefix_states.c`. The scripts that read
  them (e.g. `phase_dependence_2026-09-14/*.py`, `lift_mixing_2026-09-14/*.py`, `horizon_2026-09-14/*.py`,
  `weyl_2026-09-14/*_analyze.c`) need these dumps to be regenerated first, which takes seconds to hours of CPU depending on the run. Those
  rounds are kept for provenance: their committed `REPORT.md` and compact outputs record the results.
* **Large raw text outputs (> 300 KB)**: `phase_dependence_2026-09-14/edges_U0_2p32_N{60,80,100,120}.txt`,
  `interval_2026-09-15/V800.txt`, and the two `pn_table.json` files. The latter are regenerable with
  `phase_dependence_2026-09-14/pn_table.py`.
* **Lean build logs**, empty or timing-only run logs, and two superseded outputs: a float-sampler hop table and a
  partial rerun of the buggy `rmax.py` (see below).
* **Third-party sources downloaded for reading**: Tao's arXiv source (`tao_2026-09-15/src/`, `tao.tgz`) and Evertse's
  lecture notes (`ridout_2026-09-15/src/`). These are copyrighted by their authors; the URLs are in
  [`../docs/LITERATURE_SUBSPACE_TRIANGLES.md`](../docs/LITERATURE_SUBSPACE_TRIANGLES.md).

## Reproducing the main computations of the triangle rounds

Runtimes are single-core wall-clock times measured on the development machine for the commands shown.
"Reproduces exactly" means byte-identical output for the listed rows (the sampling scripts use fixed seeds).

### Triangle statistics — `triangle_2026-09-15/`

| Command | Output | Time |
|---|---|---|
| `python3 triangles.py 100 16 0.0185 corridor` (also `400 66 …`, `1600 266 …`) | `CORRIDOR.txt` (one block per J) | ~1 s at J = 100 (larger J not re-timed) |
| `python3 triangles.py 200 33 0.0185 paths 60` (also `400 66 0.0185 paths 60`) | `PATHS.txt` | ~1 s at J = 200 |
| `python3 sizetail.py 800 0` | size tail P(size ≥ r), quoted in `REPORT.md` | ~1 s |

The J = 100 corridor block, the J = 200 paths block and the J = 800 size tail reproduce exactly.

**`rmax.py` has a known bug, kept only for provenance.** Its random-unit control ξ is not forced coprime to 3. With
seed 41 the draws for J = 800 and J = 6400 are divisible by 3; then U(a,1) = 0 for every a and the apex climb
`while |U(aa+1, bb)| < η` never terminates. `RMAX.txt` holds the J = 200, 400 rows produced before the hang. **Use
`ridout_2026-09-15/rmax_fixed.py` instead.** It applies the `triangles.py` guard (ξ ↦ ξ + 1 when 3 | ξ), adds a loop
cap, and leaves the true (ξ = 1) column unchanged.

### Ridout audit and maximum triangle size — `ridout_2026-09-15/`

| Command | Output | Time |
|---|---|---|
| `python3 check_ridout.py 300 200` | `CHECK_300x200.txt` — exact-integer check of every inequality in the Subspace reduction | ~5 s |
| `python3 rmax_fixed.py 200 400 800 1600 3200 6400` | `RMAX_J200-6400.txt` — R_max, R_max/J, R_max/log J | ~70 s (J = 6400 dominates) |

`check_ridout.py 60 40` (smoke test, 0 failures) and the J = 200, 400, 800 rows of `rmax_fixed.py` reproduce exactly
(the last column is a timing).

### Tao-round low-frequency tests — `tao_2026-09-15/`

| Command | Output | Time |
|---|---|---|
| `python3 envctl.py 60 95`, `python3 envctl.py 120 190` | `ENV_J60.txt`, `ENV_J120.txt` — environment controls | < 1 s / seconds |
| `python3 xiunit.py` | `XIUNIT.txt` — ξ ∈ {1, 2, −1/2, …}: uniform decay fails for small integer ξ | ~1 s |
| `python3 ldtail.py j0 sigma t npaths` (the exact arguments of the recorded runs were not preserved; `REPORT.md` gives j0 = 60/100/150 with 20000/8000/3000 paths) | `LDTAIL.txt` — lower tail of per-path contraction | not re-timed |
| `gcc -O2 -o lambda1q lambda1q.c -lquadmath -lm && ./lambda1q 60 95 10 6` | γ₁ = −log₂\|Φ(1)/P\|/j0 ≈ 0.7056 | ~1 s |

Use `lambda1q` (quad precision) for γ₁: the double-precision `lambda1.c` underflows to |Φ(1)| = 0 at these depths.
The fourth argument U (frequencies λ < 2^U) must be ≥ 1. `ENV_J60.txt` and `XIUNIT.txt` reproduce exactly.

### Hop statistics and the jump threshold — `hop_2026-09-15/`

| Command | Output | Time |
|---|---|---|
| `python3 witness.py 54` (also `20`, `100`, `200`) | `WITNESS.txt` — distinct-triangle hops by digit; minimal-d witnesses | seconds |
| `python3 ld_tables.py` | `LD_TABLES.txt` — p_{d₀}, binary-KL rates, exact DP for N₆ under confined / shell / iid laws, n^{3/2}P*(C_n) | ~20 s |
| `python3 hops.py J npaths [random]` with (J, npaths) = (100,400), (200,300), (400,200), (800,100), (1600,40) | `HOPS.txt` — black fraction, hops, runs, Q(a,b), coarse chain; also checks the exact transfer kernel and the Lean run inequality on every path | ~1 s (J = 100) to several minutes (J = 1600) |

`witness.py 54`, `ld_tables.py` and the J = 100 block of `hops.py` reproduce exactly. The sampler uses a log-space
table: plain floats underflow at J = 1600.

## Other rounds (provenance)

| Folder | Topic (see its `REPORT.md`) | Main programs |
|---|---|---|
| `pair_valuation_2026-09-14/` | pair valuation, suffix transport, upper escape, prescribed matching (Lean: `PairValuation`, `SuffixTransport`, …) | `verify_*.py`, `*_diagnostics.py`, `glide_sieve.c`; outputs `*.out` (no `REPORT.md`; results are summarized in the Lean module docstrings) |
| `scales_reconciliation_2026-09-14/` | ensemble layer vs. the ScalesConfinement note | `renewal_dp.c`, `survivor_bound.py`, `phase_prediction.py` |
| `horizon_2026-09-14/`, `lift_mixing_2026-09-14/`, `phase_dependence_2026-09-14/` | survivors, horizons, lift mixing, phase dependence | dump programs (`survivor_dump.c`, `word_state.c`, …) + analysis scripts (need regenerated dumps) |
| `weyl_2026-09-14/` | Weyl sums of least realizers | `weyl_words.c` (+ analyzers), `bilinear_check.c` |
| `collision_2026-09-15/`, `swap_2026-09-15/`, `weighted_2026-09-15/`, `l3_2026-09-15/` | prefix collisions, swap bound, weighted Fourier target, L = 3 block cubes | `phi_dp.c`, `deep_dp.c`, `phi_weighted.c`, `phi3.c` |
| `interval_2026-09-15/`, `spacing_2026-09-15/`, `orbit_2026-09-15/`, `decay_2026-09-15/` | interval sieve, spacing exponent, power-of-2 orbit, continuation decay | `c3chain*.c`, `spacing.c`, `orbit.c`, `mwindow.c`, `c3gamma.c`, `controls.py` |
