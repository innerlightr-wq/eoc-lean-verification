# Round — unconditional ShapeTail for every even j ≥ 300 (2026-09-16)

**Proof: `EOC/ShapeUnconditional.lean`** (imported by `EOC.lean`). The theorem note is
[`docs/SHAPETAIL_UNCONDITIONAL.md`](../../docs/SHAPETAIL_UNCONDITIONAL.md). Nothing in this folder is part of the
proof; the Lean kernel re-checks every finite fact the proof uses.

## PROVED (LEAN) — axioms `propext`, `Classical.choice`, `Quot.sound`

* `EOC.ShapeUnconditional.shapeTail_cofinal` — j = 300(q+1), K = 12(q+1), ρ₁ = 2^{−(q+1)}.
* `EOC.ShapeUnconditional.shapeTail_allEven` — every even j ≥ 300, K = ⌊j/25⌋, ρ₁ = 2^{−⌊j/300⌋}.
* `EOC.ShapeUnconditional.shapeTail_allEven_rate` — the same with ρ₁ ≤ 2·2^{−j/300}.

All with N₀ = 10, σ = ⌊j log₂ 3⌋ and certificate exponent T = ⌊31j/100⌋.

## COMPUTATIONAL — `residues.py` → `residues.txt`

`python3 residues.py > residues.txt` (Python 3 standard library, ~2 s). Exact integer arithmetic only.

* All 150 even bases j = 300, 302, …, 598 satisfy the certificate and the budget. Worst bit margin: r = 2 (j = 302),
  20 bits. Worst budget slack: r = 0 (j = 300), 6.
* Every even j in [300, 6000] passes. Below 300 the schedule fails for 51 even j, the largest being j = 106; the
  threshold 300 is a convenient choice, not a sharp one.
* Block step: 2·3^150·2^477 ≤ 2^150·3^93·C(475,300) with an exact margin of 27 bits; the Lean proof uses
  C(475,300) ≥ 2^430, leaving 11 bits.

The ShapeTail reduction itself was developed in `../shapetail_2026-09-16/` (bridge and certificate rounds) and
`../pressure_2026-09-16/` (shape-only large deviations).

## Lean engineering notes

* The earlier (Codex) attempt stalled on elaboration, not mathematics: literal powers such as 2^477 exceed Lean's
  exponent-evaluation threshold and were being normalized inside `gcongr`/`ring`/`simpa`. The step lemma
  `step_core` is now proved with abstract exponents and instantiated afterwards.
* A `calc` whose head term restates a literal (e.g. `(475).choose 300`) is elaborated without an expected type;
  the numeral takes a different instance path and the defeq check unfolds `Nat.cast 475`, hitting `maxRecDepth`.
  Chain lemmas with abstract variables avoid it.
* `decide +kernel` evaluates the 150 base certificates (binomials up to C(946, 597) via the factorial formula)
  in about 7 s; no `native_decide` is used anywhere.
