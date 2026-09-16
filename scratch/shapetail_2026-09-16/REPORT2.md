# Round 19, Part A — `ShapeTail`: bridge + certificate, both PROVED (LEAN)

Nothing committed or pushed.  New Lean: `EOC/ShapeBridge.lean`, `EOC/ShapeCertificate.lean` (both
imported from `EOC.lean`).  `lake build EOC` = **8796 jobs**, no `sorry`/`axiom`/`opaque`; every new
theorem on `[propext, Classical.choice, Quot.sound]`.  Data: `certificate.py`, `arith.py`.

## 1. The class-sum ↔ kernel bridge — PROVED (LEAN)

* **`ShapeBridge.sum_prod_le_ker`** — for *any* finite family `C` of paths `Fin (n+1) → S` with
  `c 0 = x`, `c (last n) = z`, and any nonnegative layered weight,
  `∑_{c ∈ C} ∏_r w(l+r, c r, c (r+1)) ≤ ker w l n x z`.
  The key structural point: **no characterization of which sequences are classes is needed** — the
  classes only have to *inject* into the kernel's paths, and the kernel sums over all of them.
* **`ShapeBridge.class_sum_le_ker`** — the tilted class sum of the confined prefix shell is at most
  `ker (blockW b u σ) 0 (j₀/2) 0 σ`, where
  `blockW b u σ l x y = |Bset b l x y| · u^{[|Bset| ≤ 1]}`, `Bset b l x y = (x,y) ∩ [·≤ b(2l+1)]`.
  Requires `j₀` even (`2·(j₀/2) = j₀`), which is free to assume.
* **`ShapeBridge.tightTail_of_superEigen`**, **`shapeTail_of_superEigen`** — chaining with
  `ker_le_of_superEigen` and last round's `tightTail_of_tilted_choose`.

This closes item 1 of the three ShapeTail needs and, as predicted last round, the same bridge is what
`OddDarkPressure` will need.

## 2. The certificate — PROVED (LEAN), and it is *exact*

The numerics pointed to a layer-dependent, periodic-barrier, rational super-eigenvector.  The final
object is much simpler: in state coordinates (rather than headroom) the certificate is

  **`h(l,x) = 2^{σ−x}`,  tilt `u = 3`,  `M = 3/2`** — no layer dependence, no periodic barrier,
  no free parameters.

`ShapeCertificate.blockW_superEigen` proves `∑_y blockW(l,x,y)·h(l+1,y) ≤ (3/2)·h(l,x)` for **every**
layer and state.  The proof is a two-case dyadic computation (`w = b(2l+1) − x` the headroom):

| case | row sum | value |
|---|---|---|
| `w ≤ 1` | every weight `≤ 1`, every tilt `= 3` | `3·∑_{k≥1} 2^{−k−1} = 3/2` |
| `w ≥ 2` | `k=1` term `3·2^{−2}`, rest untilted `≤ k·2^{−k−1}` | `3/4 + 3/4 = 3/2` |

Both cases hit `3/2` exactly, so `λ = 2` is the natural (and tight) choice.  Supporting exact
identities, proved by induction: `∑_{i<n} 2^{−(i+2)} = 1/2 − 2^{−(n+1)}` and
`∑_{i<n} (i+2)·2^{−(i+3)} = 3/4 − (n+3)·2^{−(n+2)}`.
(`card_Bset`: `|Bset b l x y| = min(y−x−1, b(2l+1)−x)` — the choice set is an interval.)

*Note on last round's numerics.*  The earlier "phase-blind geometric `h` fails (4.52 bits/block)"
finding is not contradicted: that scan used headroom coordinates, in which `h(l,x) = 2^{σ−x}` carries
an `l`-dependent factor `2^{−b(2l)}`.  The certificate is layer-dependent in exactly the sense the
numerics demanded; writing it in state coordinates makes the dependence disappear.

## 3. What is left of `ShapeTail`: one arithmetic inequality

**`ShapeCertificate.shapeTail_of_arith`** [PROVED (LEAN)]: with `hchord` (the chord condition the
repo's cycle lemma already needs), `j₀ ≤ σ ≤ b j₀`, `j₀` even, and
`K + T + σ/(N₀+2) ≤ j₀/2`, the shape tail `ShapeTail b j₀ σ N₀ K ρ₁` holds as soon as

  **`j₀ · (3/2)^{j₀/2} · 2^σ  ≤  ρ₁ · 3^T · C(σ−1, j₀−1)`.**

No dynamics, no operator, no certificate — a pure inequality between explicit quantities.

**It is true, with room** (`arith.py`, exact big-int binomials, `σ = ⌊j₀α⌋`, `T = 0.60R`,
`ρ₁ = 2^{−γ j₀}`):

| J | 200 | 300 | 400 | 600 | 800 | 1200 |
|---|---|---|---|---|---|---|
| γ (exact `C`) | +0.0379 | +0.0576 | +0.0670 | +0.0778 | +0.0835 | +0.0895 |
| γ using only `C ≥ 2^{nH(k/n)}/(n+1)` | +0.0185 | +0.0437 | +0.0561 | +0.0700 | +0.0774 | +0.0852 |

At `T/R = 0.62` (still inside the `N₀ = 10` budget) the exact-`C` figures rise to +0.054 … +0.105.
Crucially **the entropy lower bound alone suffices**, so the remaining Lean work is ordinary
analysis with no dynamical content:

1. the binomial entropy bound `C(n,k) ≥ 2^{n H(k/n)}/(n+1)` (standard max-term argument: the
   `j = k` term of `∑_j C(n,j)p^j q^{n−j} = 1` is maximal, via `Nat.choose_succ_right_eq`);
2. the numeric comparison `n H(k/n) − log₂(n+1) ≥ log₂ j₀ + (j₀/2)log₂(3/2) + σ − T log₂3 + γ j₀`
   for `σ = ⌊j₀ α⌋`, `T = 0.6·(j₀/2)`, for all `j₀ ≥ j₀⁰`.

Mathlib has no usable lower bound on `Nat.choose` (only `Nat.pow_le_choose`, far too weak — it gives
129 bits against the true 294.6 at `J = 200`), so item 1 must be proved.

## 4. Status of Part A

* Tier A (PROVED (LEAN)): the bridge, the certificate, `shapeTail_of_arith`, and the whole chain
  down to the EOC exceptional-set count.
* **`ShapeTail` is NOT yet unconditional** — it rests on the arithmetic inequality above.
* Tier D (COMPUTATIONAL): that inequality holds with `γ = +0.018 … +0.105` on the entropy bound.
* Parameters (Part II): `N₀ = 10`, `T/R = 0.60–0.62`, `u = 3`, `λ = 2`, `M = 3/2` — unchanged from
  the round's instructions, not optimized.
* The periodic rational barrier (Parts III–IV) turned out to be **unnecessary**: the exact
  certificate works against the true barrier directly.  Recorded for the record: `65/41` costs
  +0.04 bits, `485/306` +0.000.
