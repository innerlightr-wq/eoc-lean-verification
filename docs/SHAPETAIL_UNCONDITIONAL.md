# Unconditional ShapeTail for the Collatz barrier

**Status: PROVED (LEAN), 2026-09-16.** Source: [`EOC/ShapeUnconditional.lean`](../EOC/ShapeUnconditional.lean),
built by `lake build EOC`. Axioms: `propext`, `Classical.choice`, `Quot.sound` only (checked with `#print axioms`;
no `sorry`, no `native_decide`).

> This is one input of the EOC contraction chain. It is **not** a proof of `OddDarkPressure`,
> `CriticalWhiteCount`, an improved exceptional exponent, or the Collatz conjecture. See §8.

Labels follow [`RESEARCH_STATUS.md`](RESEARCH_STATUS.md): PROVED (LEAN), PROVED (MATH), EXTERNAL THEOREM, COMPUTATIONAL,
HEURISTIC, CONJECTURAL, REFUTED, OPEN.

## 1. Result

Write α = log₂ 3 and let b(j) = ⌊jα⌋ be the zero-offset Collatz barrier, `CapacityBounds.collatzBarrier 0 j`.

### PROVED (LEAN) — `shapeTail_allEven`

Statement as printed by Lean:

```lean
EOC.ShapeUnconditional.shapeTail_allEven : ∀ {j : ℕ},
  300 ≤ j →
    2 ∣ j →
      EOC.OddBlack.ShapeTail (EOC.CapacityBounds.collatzBarrier 0) j (EOC.CapacityBounds.collatzBarrier 0 j) 10 (j / 25)
        (2 ^ (j / 300))⁻¹
```

That is, for every even j ≥ 300, `ShapeTail b j σ N₀ K ρ₁` holds with

| parameter | value | meaning |
|---|---|---|
| barrier b | ⌊iα⌋ | prefix sums must satisfy S_i ≤ b(i) |
| shell σ | b(j) = ⌊jα⌋ | the top shell: words of length j with total exactly σ |
| N₀ | 10 | a shape-good block has at most N₀ internal choices |
| K | ⌊j/25⌋ | the required number of shape-good blocks |
| ρ₁ | 2^{−⌊j/300⌋} | the proved tail fraction |

(Inside the proof the tight-block threshold is T = ⌊31j/100⌋; it does not appear in the statement.)

### PROVED (LEAN) — `shapeTail_allEven_rate`

```lean
EOC.ShapeUnconditional.shapeTail_allEven_rate : ∀ (j : ℕ),
  300 ≤ j →
    2 ∣ j →
      ∃ ρ₁ ≤ 2 * 2 ^ (-↑j / 300),
        EOC.OddBlack.ShapeTail (EOC.CapacityBounds.collatzBarrier 0) j (EOC.CapacityBounds.collatzBarrier 0 j) 10
          (j / 25) ρ₁
```

The power 2^{−j/300} is a real power. **The factor 2 is part of the theorem.** It comes from the floor:
⌊j/300⌋ > j/300 − 1, so 2^{−⌊j/300⌋} < 2·2^{−j/300} (`rho_le_rate`). On the cofinal family j = 300(q+1) the floor is
exact and ρ₁ = 2^{−j/300} (§5). In either form the rate is exponential with exponent γ = 1/300 bits per unit of j.

### Definition being proved

```lean
def EOC.OddBlack.ShapeTail : (ℕ → ℕ) → ℕ → ℕ → ℕ → ℕ → ℝ → Prop :=
fun b j0 σ N0 K ρ₁ =>
  ∑ c ∈ Finset.image (EOC.BlockCubeInstance.pairκ j0) (EOC.PrefixCollision.shellP b j0 σ) with
      (Finset.filter (EOC.OddBlack.ShapeGood b N0 c) (Finset.range (j0 / 2))).card < K,
      EOC.BlockCubeInstance.nCls (EOC.PrefixCollision.shellP b j0 σ) (EOC.BlockCubeInstance.pairκ j0) c ≤
    ρ₁ * ↑(EOC.PrefixCollision.shellP b j0 σ).card
```

* `shellP b j σ` — the confined prefix shell: positive valuation words (d₁,…,d_j) with prefix sums S_i ≤ b(i) for
  1 ≤ i ≤ j and total S_j = σ.
* `pairκ j P` — the coarse class of a word: its even-indexed prefix sums S₀, S₂, S₄, ….
* `pairB b c r` — block r of class c: the admissible odd prefix sums S_{2r+1}, i.e. S_{2r} < x < S_{2r+2} with
  x ≤ b(2r+1). A class is exactly a product of these choice sets.
* `ShapeGood b N₀ c r` — |pairB c r| ≤ N₀, and some x with x, x+1 both admissible exists.
* `nCls` — the number of shell words in a class.

## 2. Plain-language meaning

Split a confined valuation word of even length j into j/2 consecutive digit pairs. Fixing the even prefix sums
leaves each pair with an interval of internal choices. A pair block is *shape-good* when that interval is neither
tiny (it must hold two adjacent choices) nor large (at most 10 choices). These are the blocks in which the
pair-block Fourier factor can later contract (`WhiteContraction`).

Shape-goodness depends only on the class, so the left side of `ShapeTail` counts the shell words whose class has
fewer than K shape-good blocks. The theorem says:

> badly shaped confined words occupy an exponentially decaying weighted share of the relevant shell.

More precisely: among all confined words of length j on the top shell σ = ⌊jα⌋, the fraction with fewer than ⌊j/25⌋
shape-good pair blocks is at most 2^{−⌊j/300⌋}.

This is an **exponential tail in the word length j** for a uniformly weighted finite ensemble of words. It is a
counting statement about valuation words, **not a pointwise statement about any individual Collatz orbit**. It also
says nothing about the arithmetic phases attached to those blocks; that is the pressure side (§8).

## 3. Proof architecture

```
coarse classes ──► layered block kernel ──► super-eigenvector ──► TightTail ──► ShapeTail
 (ShapeBridge)          (LocalWindow)        (ShapeCertificate)   (ShapeTail)   (ShapeTail)
```

All arrows are PROVED (LEAN).

### Big and tight blocks — `EOC/ShapeTail.lean`

A block that is not shape-good is **tight** (|B_r| ≤ 1) or **big** (|B_r| > N₀). Big blocks are deterministically
rare: ∑_r (|B_r| + 1) ≤ σ (`sum_card_pairB_add_le`), so one word has at most σ/(N₀+2) big blocks. Hence
(`shapeTail_of_tightTail`) if K + T + ⌊σ/(N₀+2)⌋ ≤ j/2, `ShapeTail` follows from `TightTail`: at most a ρ₁ fraction
of the shell has ≥ T tight blocks. By a Chernoff/Markov bound with tilt u ≥ 1 (`tightTail_of_tilted`), `TightTail`
follows from a bound on the tilted class sum ∑_c (∏_r |B_r(c)|)·u^{#tight(c)}.

### Shape bridge — `ShapeBridge.class_sum_le_ker`

The tilted class sum is at most the pinned layered kernel `ker (blockW b u σ) 0 (j/2) 0 σ`, where

  blockW(l, x, y) = |{z : x < z < y, z ≤ b(2l+1)}| · u^{[that count ≤ 1]}

is the one-block weight from even prefix sum x to y. No characterization of which sequences of even prefix sums are
realizable classes is needed. Realizable classes **inject** into kernel paths, and all weights are nonnegative, so
the path sum over classes is at most the full kernel (`sum_prod_le_ker`).

### Exact certificate — `ShapeCertificate.blockW_superEigen`

With

  h(l, x) = 2^{σ−x},  u = 3,  M = 3/2,

the kernel satisfies ∑_y blockW(l,x,y)·h(l+1,y) ≤ M·h(l,x) at every layer l and state x. **PROVED (LEAN)**. The
verification is a dyadic identity. With headroom w = b(2l+1) − x, the row sum is 3·∑_{k≥1} 2^{−k−1} = 3/2 when
w ≤ 1, and 3/4 + ∑_{k≥2} k·2^{−k−1} = 3/4 + 3/4 when w ≥ 2. These are the untruncated sums; the finite sums in the
kernel are smaller. Both limits equal 3/2, so M = 3/2 is the sharp constant for this h as σ − x grows.
`LocalWindow.ker_le_of_superEigen` then gives

  ker ≤ M^{j/2}·h(0,0)/h(j/2,σ) = (3/2)^{j/2}·2^σ.

### Denominator

The shell is large. By the chord-rotation (cycle-lemma) argument, C(σ−1, j−1) ≤ j·|shellP|
(`CapacityBounds.shell_choose_le_mul_card`), for any barrier dominating its chords. For the Collatz barrier the chord
condition is `CapacityBounds.collatz_chord`.

### Arithmetic closure — `ShapeCertificate.shapeTail_of_arith`

Combining the above:

```lean
EOC.ShapeCertificate.shapeTail_of_arith : ∀ (b : ℕ → ℕ) {j0 σ : ℕ} {t : ℕ} {N0 K T : ℕ} {ρ₁ : ℝ},
  1 ≤ j0 → 0 ≤ ρ₁ → 2 * (j0 / 2) = j0 →
  (∀ j ≤ j0, ∀ (p : ℕ), j0 * p ≤ j * b j0 → p ≤ b j) →      -- chord
  j0 ≤ σ → σ ≤ b j0 →                                        -- shell
  K + T + σ / (N0 + 2) ≤ j0 / 2 →                            -- budget
  ↑j0 * ((3 / 2) ^ (j0 / 2) * 2 ^ σ) ≤ ρ₁ * 3 ^ T * ↑((σ - 1).choose (j0 - 1)) →   -- arithmetic
  EOC.OddBlack.ShapeTail b j0 σ N0 K ρ₁
```

(line comments added here; `t` is an unused implicit and is set to 0.) Everything that remains is the single explicit
inequality

  j·(3/2)^{j/2}·2^σ ≤ ρ₁·3^T·C(σ−1, j−1)

plus the side conditions. `EOC/ShapeUnconditional.lean` discharges all of them for the Collatz barrier.

| hypothesis | discharged by |
|---|---|
| 1 ≤ j, 2·(j/2) = j | `omega` from 300 ≤ j and 2 ∣ j |
| 0 ≤ ρ₁ | `positivity` |
| chord | `CapacityBounds.collatz_chord 0` |
| j ≤ σ ≤ b(j) | `CapacityBounds.le_collatzBarrier`, `le_rfl` |
| budget ⌊j/25⌋ + ⌊31j/100⌋ + ⌊σ/12⌋ ≤ j/2 | `budget`, from 200σ < 317j (`barrier_lt`, via 3²⁰⁰ < 2³¹⁷) |
| arithmetic | `arith_allEven` + `real_of_nat` (§4–§6) |

## 4. Exact block arithmetic

All facts in this section are **kernel-checked Lean theorems** (`decide +kernel` on natural numbers, or proofs from
such facts), not floating-point estimates.

**Barrier increments.** `collatzBarrier 0 j = Nat.log 2 (3^j)` (`barrier_eq_log`), so 2^{b(j)} ≤ 3^j < 2^{b(j)+1}.
With

  2⁴⁷⁵ < 3³⁰⁰ < 2⁴⁷⁶   (`pow_475_lt`, `pow_476_gt`)

this gives, for every j,

  475 ≤ ⌊(j+300)α⌋ − ⌊jα⌋ ≤ 476   (`barrier_add_lower`, `barrier_add_upper`).

**Binomial blocks** (Vandermonde, C(n,k)·C(m,l) ≤ C(n+m, k+l)):

  2⁸⁶ ≤ C(95, 60)   (`choose95_lower`)
  2⁸⁵ ≤ C(94, 59)   (`choose94_lower`)
  C(95, 60)⁵ ≤ C(475, 300)   (`choose475_ge`)
  C(95, 60)⁴·C(94, 59) ≤ C(474, 299)   (`choose474_ge`)

The two small binomials are evaluated by the kernel through the factorial formula; the large ones are never
evaluated.

**Block inequality used in the induction** (`block_constant`):

  2·3¹⁵⁰·2⁴⁷⁷ ≤ 2¹⁵⁰·3⁹³·C(475, 300).

Via C(475,300) ≥ 2⁴³⁰ this has about 11 bits of slack; the exact slack is 27 bits (COMPUTATIONAL, not needed).

**The +300 step** (`arith_step`). Let Arith(j, σ, e) be the cleared-denominator certificate

  j·3^{⌊j/2⌋}·2^{σ+e} ≤ 2^{⌊j/2⌋}·3^{⌊31j/100⌋}·C(σ−1, j−1).

For every j ≥ 300 and every e, Arith(j, b(j), e) implies Arith(j+300, b(j+300), e+1). The ingredients:

* the multiplier j+300 ≤ 2j costs one bit, and ⌊(j+300)/2⌋ = ⌊j/2⌋ + 150;
* ⌊31(j+300)/100⌋ = ⌊31j/100⌋ + 93;
* the upper barrier increment and the extra rate bit give at most 2⁴⁷⁷;
* the lower barrier increment gives C(b(j)−1, j−1)·C(475, 300) ≤ C(b(j+300)−1, j+299) (`choose_step`).

Then `block_constant` closes the step. The step does not depend on j mod 300.

## 5. Cofinal proof

Intermediate schedule:

  j = 300(q+1), σ = ⌊jα⌋, T = 93(q+1), K = 12(q+1), N₀ = 10, ρ₁ = 2^{−(q+1)}.

```lean
EOC.ShapeUnconditional.shapeTail_cofinal : ∀ (q : ℕ),
  EOC.OddBlack.ShapeTail (EOC.CapacityBounds.collatzBarrier 0) (300 * (q + 1))
    (EOC.CapacityBounds.collatzBarrier 0 (300 * (q + 1))) 10 (12 * (q + 1)) (2 ^ (q + 1))⁻¹
```

**PROVED (LEAN).** The base j = 300 uses b(300) = 475 (`barrier_300`) and

  300·3¹⁵⁰·2⁴⁷⁶ ≤ 2¹⁵⁰·3⁹³·(2⁸⁶)⁴·2⁸⁵ ≤ 2¹⁵⁰·3⁹³·C(474, 299)   (`arith_base_300`),

and the +300 step supplies every q. Here ρ₁ = 2^{−(q+1)} = 2^{−j/300} exactly, so γ = 1/300.

## 6. Extension to every even j

Every even j ≥ 300 can be written uniquely as

  j = (300 + 2i) + 300q,  0 ≤ i < 150, q ≥ 0,

with ⌊j/300⌋ = q + 1. So it suffices to have:

1. **150 base certificates** Arith(300+2i, b(300+2i), 1) for i < 150, i.e. j = 300, 302, …, 598;
2. **one +300 induction**, `arith_step`, which is uniform in the residue (§4).

`arith_of_base` iterates the step q times from base 300 + 2i, which gives Arith(j, b(j), ⌊j/300⌋) (`arith_allEven`).

The 150 bases are **one** finite statement:

```lean
theorem bases_ok : ∀ i < 150, baseOK (300 + 2 * i) = true := by decide +kernel
```

`baseOK j` proposes a floor s by a fuel-bounded bit-length and then **checks**, as part of the Boolean:

* 1 ≤ j ≤ s;
* 2^s ≤ 3^j < 2^{s+1};
* the certificate, with C(s−1, j−1) written as (s−1)!/((j−1)!(s−j)!).

`arith_of_checkAt` turns the Boolean into Arith, using `barrier_eq_of_pow` to identify s with b(j). So the helper
needs no specification. The kernel evaluates all 150 cases (binomials up to C(946, 597)) in about 7 seconds;
`bases_ok` depends on `propext` only.

**Role of Python.** `scratch/shapetail_allEven_2026-09-16/residues.py` (exact integer arithmetic) was used to find the
schedule and to see that one global threshold works for every residue. It found: worst base margin 20 bits at
j = 302, all even j ∈ [300, 6000] passing, and failures below 300 up to j = 106. This is COMPUTATIONAL guidance only.
**The theorem does not depend on Python;** every number used is re-checked by the Lean kernel.

## 7. Proof engineering

An earlier attempt at the cofinal case stalled in elaboration, not in mathematics. Lessons for contributors:

* **Literal large powers inside broad tactics are the main cost.** Terms such as 2⁴⁷⁷ exceed Lean's
  exponent-evaluation threshold (256). `gcongr`, `ring`, `simpa` and unification then try to normalize them and hit
  heartbeat limits. The generic step `step_core` is stated with **abstract exponents** (variables a, c, d for 150, 477,
  93); the concrete constants are substituted only when it is applied.
* **Stay in ℕ.** `collatzBarrier 0 j = Nat.log 2 (3^j)` (`barrier_eq_log`) is the only lemma that touches ℝ. Every
  barrier recurrence is then an integer power comparison.
* **Isolate ℕ → ℝ.** `real_of_nat` converts the cleared-denominator ℕ inequality into the real `harith` hypothesis once,
  with all quantities abstract.
* **Use the kernel for finite facts.** `decide +kernel` uses GMP arithmetic and bypasses elaborator normalization. It
  is cheap even for 900-digit factorials. No `native_decide` (and so no `Lean.ofReduceBool`) is needed.
* **Do not restate literals in `calc` heads.** A head like `(475).choose 300` is elaborated without an expected type.
  The numeral then takes a different instance path, and the defeq check unfolds `Nat.cast 475` until `maxRecDepth`.
  Abstract chain lemmas (`pow5_le_of_chain`) plus term-mode `trans` avoid this.

The whole file builds in about 14 s.

## 8. Scope and non-claims

This theorem does **not** prove:

* `OddBlack.OddDarkPressure` — the exponential-moment bound for the word's own dark odd cells (OPEN for the true
  environment);
* any averaged form of that pressure bound (OPEN);
* `WhiteContraction.CriticalWhiteCount` unconditionally. `OddBlack.criticalWhiteCount_of_shape_and_oddPressure`
  derives it from `ShapeTail` (now available at K = k + n) **together with** `OddDarkPressure` and a numerical
  compatibility condition;
* `LowFreqDecay`, `WeightedFourier`, or any improvement of the exceptional-set exponent H₂(1/α) ≈ 0.949956 by itself;
* the Collatz conjecture, or the Global Occupation Conjecture.

It also does not cover odd j, even j < 300, shells σ < b(j), nonzero barrier offsets, or other N₀.

`EOC/AverageOddDark.lean` removes the `ShapeTail` hypothesis from that implication. It proves
`AverageOddDarkPressure ⇒ CriticalWhiteCount ⇒ LowFreqDecay`, using the fact that this ShapeTail holds for any
N₀ and K within the block budget K + ⌊31j/100⌋ + ⌊σ/(N₀+2)⌋ ≤ j/2 (`shapeTail_allEven_budget`).

ShapeTail is purely combinatorial: it concerns interval sizes of block choice sets, not the 3-adic phases attached to
them. The **dominant remaining analytic obstruction is the pressure side**: showing that confined words cannot keep
most of their shape-good blocks dark, which is a 3-adic pattern problem for powers of 2 sampled along confined paths.

**ShapeTail is now unconditional in Lean for every even j ≥ 300. The pressure side remains open; this is not a proof
of Collatz.**
