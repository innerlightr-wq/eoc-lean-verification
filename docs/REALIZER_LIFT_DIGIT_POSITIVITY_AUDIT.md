# Successive realizer lift-digit / positivity boundary audit

Follow-up to [`docs/W2_REALIZER_SELECTOR_BRIDGE_AUDIT.md`](W2_REALIZER_SELECTOR_BRIDGE_AUDIT.md),
which closed the W=2 Fourier bridge and established that *complete compatible lift fibres are
balanced, while the least-positive representative selector is where the Archimedean information
enters*.

**Question.** Does the successive lift digit `t_N = (r_{N+1} − r_N)/2^{S_N+1}` contain new
arithmetic information about positive-integer realization, or is it merely the next block of binary
digits of the 2-adic realizer?

**Answer: it is exactly the grouped binary expansion, and the carry/peeling machinery *computes*
the lift digits rather than *restricting* them.**

All five of Gate 34's stop conditions hold:

| # | condition | status |
|---|---|---|
| 1 | `t_N` is the variable-block binary expansion of the realizer | **yes** — §E, formalized |
| 2 | eventual `t_N = 0` is exactly ZCRE / eventual realizer constancy | **yes** — §G, formalized |
| 3 | peeling / master-difference become ordinary prefix separation of that expansion | **yes** — §W |
| 4 | zero confinement imposes only known population/entropy restrictions | **yes** — §O, §Q |
| 5 | no independent theorem forces nonzero `t_N` infinitely often | **yes** — §N, §AB |

The audit is not empty, though. It **identifies the exact coordinate** any future positivity
argument must act on, and it produces one calibration that sharpens the frontier statement:
`−1` and `−5` realize **zero-confined** words. So zero confinement plus *ordinary integer*
realization does not imply positivity — the sign boundary is visible only in the tail bits.

---

## A. Starting state

| | |
|---|---|
| branch point | `w2-realizer-selector-bridge-audit` = `29e969693887564522276c1ff544af2c818e7843`, **fetched and verified**, not taken from prose |
| new branch | `realizer-lift-digit-positivity-audit` |
| worktree | isolated; Mathlib shared by read-only symlink |

Ordinary checkout on `research-sparse-visits-2026-09-16`, 53 dirty files, untouched. `main`
(`1c4d6700`) unmodified.

## B. Source inventory

| | source |
|---|---|
| **PL** | `~/Downloads/peeling_theorem_ledger.md` — *The Peeling Reconstruction Theorem: Formal Audit and Ledger*, 91 lines, sha256 `54a6d958286a793e…`. **Read in full.** |
| **HC** | `~/Downloads/halfcylinderv2.pdf`, 356 163 bytes, sha256 `9dde423a50e5fbf9…`, extracted to 749 lines of text |
| repo | `EOC/ZCRERealizerGrowth.lean`, `EOC/Realizer.lean`, `EOC/ChangZeroCorridor.lean`, `EOC/ChangInfiniteCompatibility.lean`, `EOC/ChangFullShift.lean`, `EOC/W2SelectorBridge.lean` |
| **P1** | EOC Rev 5 — Prop 5.2 (exact realizer congruence), Def 5.4 (coarse anchor vs exact lift), §6, §8 |

PL's own tier table is preserved: T1–T4, T6, T7 **proved**; T5 proved in the corrected 1-Lipschitz
class; supra-frontier tail entropy and erosion-prevention **computational/conditional on fresh-bit
anti-concentration**; the "defect stratum = distortion sector" reading **heuristic**.

## C. Exact realizer convention

Verified against `EOC/Realizer.lean` and P1 Prop 5.2, not assumed.

- **Modulus is `2^{S_N+1}`, not `2^{S_N}`.** P1 Prop 5.2: "the exact realizers of `D` form a single
  residue class modulo `2^{S_N(D)+1}`, not `2^{S_N(D)}`."
- **Representatives:** `leastRealizer d N` is the least *positive* representative, so it lies in
  `[1, 2^{S_N+1}]`. Every realizer is odd (`leastRealizer_odd`), so `0` never occurs and the
  half-open/closed ambiguity at the ends is vacuous.
- **Nesting.** `r_{N+1} ≡ r_N (mod 2^{S_N+1})`. Verified on **4317** one-letter extensions of
  zero-confined words with `N ≤ 10`: **0 violations**. (Proof: the exact cylinder of the extension
  refines that of the prefix — `Realizer.realizerCongruence` at both depths.)

## D. Lift-digit definition

```
t_N  :=  (r_{N+1} − r_N) / 2^{S_N+1}
```

Range: `0 ≤ t_N < 2^{d_N}`. Formalized as `RealizerLiftDigit.liftDigit_lt`, from
`r_{N+1} < 2^{S_{N+1}+1}` and `S_{N+1} = S_N + d_N`.

Verified on the same 4317 extensions: **0 range violations**, and the bound is attained —
max observed `t` for `d = 1,2,3,4` is `1, 3, 7, 15`, exactly `2^d − 1`.

**No boundary exception arises.** Because realizers are odd and the least positive representative is
used, `r_{N+1} ≥ r_N` always (the nesting class representative can only move up within the refined
modulus), so `t_N` is a genuine natural number with no wraparound case to hide.

## E. Variable-block binary expansion

**Proved, and this is the decisive gate.**

If a fixed `m` realizes every prefix then `r_N = m mod 2^{S_N+1}`
(`ZCRERealizerGrowth.leastRealizer_eq_mod_of_realizes`), hence

```
t_N = ( (m mod 2^{S_{N+1}+1}) − (m mod 2^{S_N+1}) ) / 2^{S_N+1}
    = ⌊ m / 2^{S_N+1} ⌋  mod  2^{d_N}
```

which is precisely the block of binary digits of `m` at positions `S_N+1, …, S_{N+1}`.

Formalized as `RealizerLiftDigit.liftDigit_eq_bitBlock` (pure arithmetic:
`(m % 2^{a+d} − m % 2^a)/2^a = (m / 2^a) % 2^d`) and `liftDigit_of_fixed`.

Verified numerically on real positive seeds `7, 27, 703, 26623, 159487`: **48 (word, N) pairs,
0 mismatches**, checking both `r_N = m mod 2^{S_N+1}` and the block identity.

> **SUCCESSIVE LIFT DIGITS ARE THE VARIABLE-LENGTH BINARY DIGITS OF THE 2-ADIC REALIZER.**

The blocks are cut at the valuation sums; that is the only thing the Collatz structure contributes.

## F. Positive/negative integer tails

Standard 2-adic behaviour, transported to blocks:

| `x ∈ ℤ ⊂ ℤ₂` | binary tail | lift-digit tail |
|---|---|---|
| `x ≥ 0` | eventually `0` | `t_N = 0` eventually |
| `x < 0` | eventually `1` | `t_N = 2^{d_N} − 1` eventually |

**Calibration computed** (§T): `−1` gives `t_N = 1 = 2^1 − 1` throughout; `−5` gives
`t_N = 2, 1, 3, 1, 3, …` against max blocks `3, 1, 3, 1, 3, …` — *eventually* maximal with one
transient at `N = 1`, because `−5 = …11111011` has a `0` at bit position 2. The "eventually" is
therefore load-bearing and is stated as such.

## G. ZCRE equivalence

Exact repo statement:

```
ZCRERealizerGrowth.boundedPrefixRealizers_iff_positiveRealizer (d) (hd_pos : ∀ i, 1 ≤ d i) :
  (∃ M, ∀ N, leastRealizer d N ≤ M) ↔ (∃ m₀, Odd m₀ ∧ ∀ i, a (orbit m₀ i) = d i)
```

plus `leastRealizer_eventually_constant_of_bounded`.

Formalized here: `RealizerLiftDigit.liftDigit_eq_zero_iff` (`t_N = 0 ↔ r_{N+1} = r_N`, given
nesting) and `eventuallyZero_iff_eventuallyConstant`:

```
(∃ N₀, ∀ N ≥ N₀, t_N = 0)  ↔  (∃ N₀, ∀ N ≥ N₀, r_N = r_{N₀})
```

Chaining: eventual lift-zero ⟺ eventual realizer constancy ⟺ bounded prefix realizers ⟺
positive-integer realizer.

> **NEW COORDINATE, NOT NEW INFORMATION.** The lift-digit criterion is *exactly* ZCRE.

## H. Normalized carry / moving-anchor identity

PL uses `−Z_n = Σ_{i<n} 3^{−(i+1)} 2^{S_i}`. Multiplying by `−3^n`:

```
−3^n Z_n = Σ_{i<n} 3^{n−1−i} 2^{S_i} = C_n          so   q_n = C_n exactly,
Z_N = −3^{−N} C_N.
```

Hence `ξ_N = −C_N·3^{−N} mod 2^{S_N} = Z_N mod 2^{S_N}` — the peeling normalized carry and the EOC
moving anchor are the same object at different precision. And at one more bit:

```
r_N = (Z_N + 2^{S_N})  mod  2^{S_N+1}.
```

Both identities verified numerically across zero-confined words with `N ≤ 9`: **0 mismatches**.

## I. Half-cylinder selector

The coarse anchor `ξ_N` lives mod `2^{S_N}` and has two lifts mod `2^{S_N+1}`, namely `ξ_N` and
`ξ_N + 2^{S_N}` (P1 Def 5.4). HC's half-cylinder theorem says exactly one has odd terminal quotient.

By §H the selected one is determined by **bit `S_N` of `Z_N`**. Worked example `D = (1,2,1,1,2)`:
`Z_N mod 2^8 = 219`, `ξ_N = 91`, the two lifts are `91` and `219`, and `r_N = 91` — recovered by
`(Z_N + 2^{S_N}) mod 2^{S_N+1} = (219+128) mod 256 = 91`.

> **THE TERMINAL TOP-BIT CHARACTER IS THE FIRST EXACT-REALIZER LIFT BIT** — the single bit taking
> `ξ_N (mod 2^{S_N})` to `r_N (mod 2^{S_N+1})`.

This is **not** `t_N`: it is one bit *within the current depth*, whereas `t_N` carries `d_N` bits of
the *next* refinement (§J).

## J. Lift-block bit decomposition

Extending by `d_N` raises the modulus by `d_N` bits, so `t_N` is exactly `d_N` binary digits at
positions `S_N+1, …, S_N+d_N`:

```
bit position:   0        1 … S_N    S_N+1  …  S_N+d_N     S_N+d_N+1 …
                │        │           └──────  t_N  ──────┘
            always 1   r_N's bits        the new block        not yet determined
          (r odd)    (already fixed)
```

- The **terminal-selector bit** of §I is bit `S_N`, i.e. the *top* bit of the current `r_N` — it
  belongs to the previous refinement, not to `t_N`.
- **None** of `t_N`'s bits is forced by integrality: all `2^{d_N}` values occur (§D, bound attained).
- All `d_N` bits are genuinely new higher bits of the realizer.

## K. Frontier erosion reinterpretation

HC proves a `K`-bit parent frontier window retains `K − d` bits after a step of cost `d`. In
lift-digit language that is the statement that a step consumes `d_N` bits of look-ahead — exactly
the `d_N` bits constituting `t_N` (§J).

So erosion and lift blocks are the **same bookkeeping**: the bits lost from the window are the bits
gained by `t_N`. This unifies the two older formulations, and it also explains why neither
constrains anything: both describe *where* the new bits sit, not *what* they are.

**Quantified:** erosion controls the *number* of fresh bits per step (`d_N`), and zero of their
values.

## L. Minimum precision

PL T3: recovery of the visible data from `Z_n mod 2^Q` succeeds iff `Q ≥ S_{n−1}+1`, with **silent
truncation** below threshold.

For the lift digit the requirement is strictly higher: `t_N` lives at bit positions up to
`S_N + d_N`, so determining it needs `Z` to precision at least `2^{S_{N+1}+1}` — i.e.
**`t_N` requires precision beyond what determines `r_N`**, and in particular beyond the truncation
threshold that reconstructs the visible word.

This is the Gate 9 outcome: `Z_N mod 2^{S_N+1}` determines the current exact realizer, but `t_N`
needs genuinely new bits above that precision. Connected to silent truncation (T3): a peeler at
precision `S_N+1` returns a valid shorter word and cannot see the next block at all.

## M. Exact `t_N` recurrence

From `r_N ≡ 2^{S_N} − C_N·3^{−N} (mod 2^{S_N+1})` and the carry recursion
`C_{N+1} = 3C_N + 2^{S_N}`:

```
r_{N+1} ≡ 2^{S_{N+1}} − C_{N+1}·3^{−(N+1)}
        ≡ 2^{S_N+d_N} − (3C_N + 2^{S_N})·3^{−(N+1)}
        ≡ 2^{S_N+d_N} − C_N·3^{−N} − 2^{S_N}·3^{−(N+1)}     (mod 2^{S_{N+1}+1})
```

so, subtracting the same expression for `r_N` truncated at the coarser modulus,

```
t_N = ⌊ ( 2^{S_N+d_N} − 2^{S_N} − 2^{S_N}·3^{−(N+1)} + 2^{S_N}·(3^{−N} − 3^{−N}) + … ) / 2^{S_N+1} ⌋
```

— and the point is what this collapses to: every term carries `C_N·3^{−N}` at a precision **higher
than `2^{S_N+1}`**. So the minimal state determining `t_N` is

```
F( N, S_N, d_N, C_N mod 2^{S_{N+1}+1} )
```

i.e. it needs the carry to the *next* precision. No smaller state suffices, because by §J all
`2^{d_N}` values of `t_N` occur and they are separated only by those higher carry bits.

**This is not a shortcut.** It is the exact-realizer formula evaluated one step deeper — §N.

## N. Anti-tautology audit

**Coordinate change.** The recurrence of §M is "compute `r_{N+1}` from the carry at higher
precision, then subtract" with the subtraction pushed inside. It restricts nothing.

The decisive question the brief poses — *does the carry/peeling structure restrict the lift digits,
or merely compute them?* — is answered by PL's own T1:

> "`Z_n` alone determines the visible data `(S_0,…,S_{n−1})`, hence `(d_0,…,d_{n−2})` and `n`."

The carry is a **faithful encoding** of the word (one-bit deficient). An encoding cannot restrict
what it encodes. Every peeling theorem is a statement about *recovering* `D` from `Z`, i.e. about
computation and access cost, not about which `D` occur.

None of the useful restriction types the gate lists — forbidden long zero blocks, mandatory
infinitely many nonzero `t_N`, lower density of nonzero `t_N`, a recurrence incompatible with
eventual zero, a monotonic or Diophantine restriction — was found, and none is claimed.

## O. Zero-corridor lift language

Enumerating zero-confined words and their lift data:

| `N` | #words | #distinct `r` | #distinct `λ`-prefix | bijective? |
|---|---|---|---|---|
| 8 | 173 | 173 | 173 | **yes** |
| 10 | 961 | 961 | 961 | **yes** |
| 12 | 8045 | 8045 | 8045 | **yes** |

**No collisions, no branching freedom, no forbidden local pattern beyond what the word already
encodes.** The image size *equals* the number of valuation words, by shell injectivity (P1 §6).

## P. Flattened binary lift stream

Flatten the blocks: `λ_0, λ_1, …` with `t_N` occupying positions `S_N+1, …, S_{N+1}`. Then
`λ_b` is simply **bit `b` of the realizer**, with `λ_0 = 1` always (realizers are odd).

In this representation positivity is transparent: `x ∈ ℤ_{≥0}` ⟺ `λ` is eventually `0`;
`x < 0` ⟺ `λ` is eventually `1`. The block structure contributes nothing except where the cuts fall.

## Q. Entropy-rate comparison

| quantity | value |
|---|---|
| zero-confined words of depth `N` | `≈ 2^{1.12 N}` (measured, `N ≤ 15`) |
| residue bits available | `S_N + 1 ≈ 1.585 N + 1` |
| possible `λ`-streams to that scale | `2^{S_N}` (bit 0 fixed) |
| entropy deficit | `I_Collatz = α(1 − H₂(1/α)) = 0.0793186…` |

So the zero-corridor image occupies an exponentially thin subset of lift-bit space — which is the
old entropy-deficit identity read in these coordinates. **Thin population is not pointwise
exclusion**, and this audit does not treat it as such; it is the same population statement the
Curry-window round already located (`X^{H₂(1/α)}`).

## R. Eventually-zero zero-corridor words

Combining §E, §G and §P:

> An infinite zero-confined valuation word has an eventually-zero lift stream **iff** it has a
> positive-integer realizer.

So the Collatz Type-II question is: *does there exist an infinite zero-confined word, satisfying the
divergence/non-periodicity conditions, whose lift stream is eventually zero?* Cycles and
terminating orbits are excluded separately — a terminating orbit reaches `1` and its word is finite;
a cycle gives an eventually periodic word with a fixed anchor (P1 Thm 5.8/5.9).

This is a clean restatement, and **exactly** the existing problem.

## S. Periodic-sector calibration

For periodic and eventually periodic words, P1 Thm 5.8/5.9 give exponential realizer floors via the
fixed 2-adic anchor `ξ_X`. In lift coordinates that reads: the lift stream of `X^n` is the binary
expansion of `ξ_X`, which is eventually zero **iff** `ξ_X ∈ ℤ_{>0}` — the theorem's excluded case.

So the known floors say "the anchor's binary expansion is not eventually zero", which is the
positivity statement again. **The lift-digit viewpoint rephrases the existing fixed-anchor proofs
and does not extend them.**

## T. Negative-integer calibration

| `x` | valuation word | zero-confined? | `r_N` (N=1..5) | `t_N` | max block |
|---|---|---|---|---|---|
| `−1` | `(1,1,1,1,…)` | **yes** | 3, 7, 15, 31, 63 | 1,1,1,1,1,1,1 | 1,1,1,1,1,1,1 ✓ |
| `−5` | `(1,2,1,2,…)` | **yes** | 3, 11, 27, 123, 251 | 2,1,3,1,3,1,3 | 3,1,3,1,3,1,3 (eventually ✓) |
| `−7` | `(2,1,2,1,…)` | no | 1, 9, 57, 121, 505 | 1,3,1,3,1,3,1 | 1,3,1,3,1,3,1 ✓ |

**This is the audit's sharpest calibration.** `−1` and `−5` realize **zero-confined** words. So:

> Zero confinement together with **ordinary integer** realization does **not** imply positivity.

The corridor cannot see the sign; only the tail bits can. This is worth recording because it rules
out any hope that the corridor alone forces `λ` to be eventually zero — the corridor is satisfied by
words whose `λ` is eventually *maximal*.

## U. Curry translation

The already-proved Curry consequences (`R_N → −∞`, `Δ_N → ∞`, `m_N = Θ(2^{Δ_N})`) transport
directly. **Does `Δ_N → ∞` force anything about `t_N`? No.**

`Δ_N → ∞` constrains the *valuation word* (the drift below the Beatty line); `t_N` records bits of
the *realizer*. §T is the counterexample in miniature: the word of `−1` has `Δ_N = ⌊αN⌋ − N → ∞`,
yet its lift digits are constantly maximal, never zero. Curry's conclusions are word-level and
`q`-blind in exactly the sense the W=2 audit identified.

No re-audit of Curry was performed.

## V. Chang calibration

Using `ChangFullShift.changSeq`, arbitrary symbolic histories give arbitrary zero-confined words,
hence (by §O's bijection) arbitrary distinct realizers and lift streams within the image. The
symbolic freedom transports to lift-stream freedom **within the image**, and the image is exactly
the set of words — no more.

Calibration only; no Chang route reopened.

## W. Master-difference translation

PL T2: `v₂(Z(D) − Z(D')) = min(V(D) △ V(D'))`.

In lift coordinates: `Z` and `r` differ by the known affine relation of §H, so two words' realizers
first differ at bit `min(V △ V')` (up to the `+1` of T2's specialization (i)). Since `λ` *is* the
binary expansion of `r`, this says: **the first differing lift bit is at the first differing visible
valuation.**

> That is uniqueness of binary expansion plus T1's injectivity, not new information.

PL says as much itself — the master law is a statement about *separation* of encodings.

## X. Cost-metric geometry

PL T4/T7: in the cost metric the embedding is an exact similarity of ratio `1/2`; the image is a
strongly separated IFS attractor with `dim_H = log₂ φ`.

In lift coordinates this is the statement that `λ` realizes the symbolic space as a self-similar
subset of `ℤ₂` with the natural 2-adic metric. Elegant, and **geometric separation is not an
Archimedean lower bound**: the ultrametric distance `|r − r'|₂` measures agreement of *low* bits,
while `r`'s *size* is governed by its *high* bits. Two realizers can be 2-adically very close and
Archimedean-ly far apart, and conversely. Stated explicitly because the two notions are easy to
conflate.

## Y. Carry/Diophantine interface

The candidate would be "high bits of `3^{−N} C_N`". By §M that is precisely what `t_N` is. So the
candidate **reduces to the binary digits of a general 2-adic number**, and the gate's own stop
condition applies.

For an interface to be valid it would need increasing precision with `N` (yes), the actual moving
carry (yes), more than bounded local residues (yes) — but also *a statement capable of excluding
eventual zero*, and there is none: no Diophantine property of `−C_N 3^{−N}` is known that forbids
its residues from eventually agreeing with a fixed integer, and asserting one is the problem itself
(§R).

**Surviving candidate: NONE.**

## Z. Open Problems C/D/E in lift coordinates

| problem | lift-coordinate translation |
|---|---|
| **C** — `r(D) ≥ 2^{εN−O(1)}` | the **highest nonzero `λ` bit below `S_N+1`** sits at position `≥ εN − O(1)`; equivalently the terminal run of zero lift bits is **shorter** than `S_N + 1 − εN` |
| **D** — moving-anchor anti-concentration | prefixes of `λ` (equivalently `ξ_N`'s low bits) are not exceptionally often the low bits of a small integer |
| **E** — `E(D) ≤ H₂(ρ_c)S + Φ(N)` | `E(D) = S − log₂ r(D)` is exactly the **length of the terminal zero-run in `λ` below `S_N+1`**, up to `O(1)`; E bounds that run by `H₂(ρ_c)S + Φ(N)` |

The translation of **E** is the cleanest gain of the audit: *the frontier-defect variable is the
terminal zero-run length of the lift stream*. It does not prove anything, but it makes C and E
visibly the same kind of statement about one bit string.

## AA. Record-frontier computation

| seed | `N` | `S_N` | `log₂ r_N` | highest `1` bit | terminal zero-run below `S_N` |
|---|---|---|---|---|---|
| 27 | 6 | 7 | 4.75 | 4 | 3 |
| 27 | 10 | 14 | 4.75 | 4 | **10** |
| 703 | 10 | 12 | 9.46 | 9 | 3 |
| 26623 | 10 | 10 | 11.00 | 10 | 0 |
| 1017667 | 10 | 20 | 19.96 | 19 | 1 |

The seed `27` shows the phenomenon cleanly: once `2^{S_N+1} > 27` the realizer stops moving, and the
zero-run grows one bit per unit of valuation. **`log₂ r_min ≈ I_Collatz·N + O(1)` is exactly the
statement that the terminal zero-run is `≈ (α − I_Collatz)N` bits long.** Used to sharpen the
formulation only.

## AB. Weakest genuinely new missing lemma

The natural candidate is:

> *Every genuinely irregular zero-confined infinite valuation word has infinitely many nonzero lift
> digits.*

**This is exactly equivalent to "no positive-integer realizer"** by §G, so it is the problem, not
progress. Stated and rejected as the gate requires.

A *weaker, non-equivalent* statement that would still imply a realizer floor would have to bound the
**terminal zero-run length** at each finite `N` — e.g.

> *for every zero-confined `D` of depth `N`, the terminal run of zero lift bits below `S_N+1` has
> length `≤ (α − ε)N`*

which is Open Problem C restated (§Z) and is strictly weaker than eventual non-vanishing, since it
is a finite-`N` statement. **No proof of it, or of anything implying it, was found**, and the
translation does not suggest one: the terminal zero-run is not controlled by any identity in the
carry recursion, only *computed* by it (§N).

## AC. Lean formalization

**New module `EOC/RealizerLiftDigit.lean`**, 5 theorems + 1 definition, no
`sorry`/`admit`/`axiom`/`opaque`.

| declaration | statement |
|---|---|
| `liftDigit r S N` | `(r (N+1) − r N) / 2^(S N + 1)` |
| `liftDigit_lt` | `r (N+1) < 2^(S (N+1)+1) → S (N+1) = S N + d → liftDigit < 2^d` |
| `liftDigit_eq_zero_iff` | with nesting divisibility: `liftDigit = 0 ↔ r (N+1) = r N` |
| `eventuallyZero_iff_eventuallyConstant` | `(∃N₀ ∀N≥N₀, t_N = 0) ↔ (∃N₀ ∀N≥N₀, r N = r N₀)` — **the ZCRE bridge** |
| `liftDigit_eq_bitBlock` | `(m % 2^{a+d} − m % 2^a)/2^a = (m / 2^a) % 2^d` — **the deflationary theorem** |
| `liftDigit_of_fixed` | the same in lift-digit shape for a fixed realizer |

Stated for an abstract nested `r : ℕ → ℕ` rather than for `leastRealizer`, which is the generality
in which they hold. **No 2-adic API was built** (Gate 33): every statement is a finite-residue
statement, and the `ℤ₂` reading is given in this report only.

## AD. Tests/build

| command | result |
|---|---|
| `lake build EOC.RealizerLiftDigit` | **success, 2050 jobs, 0 errors** |
| `lake build EOC.ZCRERealizerGrowth` | success, 2049 jobs (no regression) |
| `lake build EOC.W2SelectorBridge` | success, 2041 jobs |
| `lake build EOC.ChangFullShift` | success, 2042 jobs |
| `python3 scratch/realizer_lift_digit.py` | exit 0 |
| forbidden-token grep | clean |

Numerical: nesting **0/4317** violations; range **0/4317** violations with bound attained;
block identity **0/48** mismatches; `ξ_N = Z_N mod 2^{S_N}` and `r_N = (Z_N + 2^{S_N}) mod 2^{S_N+1}`
**0 mismatches**; bijectivity `D ↔ r ↔ λ` exact for `N ≤ 12`.

## AE. Axiom audit

```
liftDigit_lt                          : [propext]
liftDigit_eq_zero_iff                 : [propext, Quot.sound]
eventuallyZero_iff_eventuallyConstant : [propext, Quot.sound]
liftDigit_eq_bitBlock                 : [propext, Classical.choice, Quot.sound]
liftDigit_of_fixed                    : [propext, Classical.choice, Quot.sound]
```

Standard Mathlib axioms only.

## AF. Files changed

```
new:  EOC/RealizerLiftDigit.lean                        5 theorems + 1 definition
new:  scratch/realizer_lift_digit.py                    reproducible checks
new:  docs/REALIZER_LIFT_DIGIT_POSITIVITY_AUDIT.md      this report
```

No existing Lean file modified; no theorem statement changed; neither source document edited.

## AG. Commits

Branch `realizer-lift-digit-positivity-audit`, from `29e9696`.

| commit | contents |
|---|---|
| `43d42af` | `EOC/RealizerLiftDigit.lean` + `scratch/realizer_lift_digit.py` |
| (this file) | this report |

## AH. Push status

Branch pushed to `origin/realizer-lift-digit-positivity-audit`. **No pull request opened.** `main`
unmodified; dirty ordinary checkout untouched.

## AI. Research verdict

**`POSITIVITY COORDINATE IDENTIFIED, BUT NO NEW CONSTRAINT`**

This is the deepest rigorously supported verdict, and it strictly contains the two shallower ones
that are also true: `LIFT DIGITS ARE EXACTLY GROUPED 2-ADIC REALIZER BITS` (§E, formalized) and
`EVENTUAL ZERO IS EXACTLY EXISTING ZCRE` (§G, formalized). It is chosen over both because those
record only the deflationary half, whereas the positive half — that a genuinely positivity-sensitive
coordinate has now been isolated and formalized — is the reason the audit was worth running.

It is **not** `ZERO CORRIDOR IMPOSES A NEW LIFT-DIGIT RESTRICTION`: §T exhibits zero-confined words
(`−1`, `−5`) whose lift streams are eventually *maximal*, so the corridor does not push `λ` toward
zero at all. It is **not** `PEELING GIVES A NEW CONSTRAINT`: PL's own T1 says the carry *determines*
the word, and an encoding cannot restrict what it encodes (§N, §W). And it is **not** a new
interface or consequence: §Y finds no surviving Diophantine candidate, and §AB shows the obvious
missing lemma is equivalent to the problem.

**The answer to the central anti-tautology question is: the carry/peeling structure merely computes
the lift digits.** Every arrow in the hierarchy

```
valuation word → moving anchor ξ_N → exact realizer r_N → lift blocks t_N → binary stream λ
```

is a coordinate change — each is a bijection onto its image (§O), with `ξ_N → r_N` the single
half-cylinder selector bit (§I) and `t_N → λ` pure regrouping (§P). The only non-coordinate arrow is
the last one:

```
λ eventually zero  ⟺  positive ordinary integer
```

and that equivalence is ZCRE.

**What the audit delivers.** The exact coordinate on which any future positivity argument must act:
the terminal zero-run of the lift stream below `S_N+1`. Open Problem E is *literally* a bound on
that run length (§Z), and Open Problem C is its asymptotic form. A future mechanism must bound how
long the realizer's high bits can stay zero — and §T warns that the corridor alone cannot do it,
because the corridor is satisfied by words whose high bits stay *one*.
