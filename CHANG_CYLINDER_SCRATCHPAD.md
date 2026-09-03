# CHANG_CYLINDER_SCRATCHPAD

> **Research scratchpad — not a manuscript.** This file contains exploratory
> derivations, computational experiments, literature connections, negative
> results, and open questions. Statements labeled "Derived here" have not
> necessarily been checked for novelty against the full literature. External
> results should be verified against their primary sources before publication.

Session date: 2026-09-03. Repo: `EOC` (Lean 4 / Mathlib formalization of
Pillar-3 realizer/confinement results). No Lean source files were modified in
this round. Scratch code sits in `scratch/` as untracked files (see §10).

Provenance labels used throughout:

- **External source** — already appears in Chang or another cited source.
- **Derived here** — derived independently during this session.
- **Computational confirmation** — tested here, but already known/implied externally.
- **Computational observation** — found experimentally here; not established as a theorem.
- **Interpretation** — conceptual reformulation/synthesis, not a new result.
- **Open question** — unresolved.

---

## 1. External sources

### 1.1 Chang — one-bit orbit-mixing reduction

1. **Author(s):** Edward Y. Chang (Stanford University — affiliation per web
   search summary, *SOURCE TO VERIFY* against the paper).
2. **Title:** *A Structural Reduction of the Collatz Conjecture to One-Bit
   Orbit Mixing.*
3. **Identifier:** arXiv:2603.25753 (v1, submitted 2026-03-24). Also
   ResearchGate publication 403070918. URLs seen:
   `arxiv.org/abs/2603.25753`, `.../pdf/2603.25753`, `.../html/2603.25753v1`.
   *The arXiv number is consistent across search hits but should be
   re-confirmed directly.*
4. **Theorem/section numbers:** Definitions of `X_t`, burst/gap/run; the
   burst–gap block decomposition `1^{L_1}0^{G_1}1^{L_2}0^{G_2}…`; **Lemma 4.1**
   (gap length ↔ mod-8 residue of the gap start); **eqs (8)–(9)** (bit 4 ↔
   `9`/`25 mod 32` ↔ gap outcome for `n ≡ 1 mod 8`); **Propositions 3.1, 3.2,
   3.6** (exact low-depth decomposition at `K = 3, 4, 5`); a **"Map Balance
   Theorem"** (burst residues mod `2^K` initiating gaps: counts to gap starts
   `≡ 3` vs `≡ 7 (mod 8)` differ by exactly 1 for every `K ≥ 5`).
   *All specific numberings here were read from the arXiv HTML via an
   automated summarizer, not verified line-by-line against the PDF —
   **SOURCE TO VERIFY**.*
5. **What the source actually proves (as understood):** Working with the
   compressed odd map `T(n) = (3n+1)/2^{v2(3n+1)}`, Chang gives exact
   finite-depth decomposition formulas (`K = 3,4,5`) for block/run
   frequencies, and reduces the Collatz conjecture to a single statement:
   along the sparse subsequence of *burst-ending times* with `n_t ≡ 1 (mod 8)`,
   the orbit must visit the two residue classes `9 mod 32` and `25 mod 32`
   ("bit 4 = 0/1") with sufficient balance. Lemma 4.1 / eqs (8–9) establish
   the *local* dictionary bit4 ↔ gap length; the residual hard target is the
   *pointwise* balance of that bit along one deterministic orbit. The Map
   Balance Theorem establishes the corresponding *ensemble* balance exactly.
6. **How we used it:** as the definition of the observable `Y` (bit 4 at
   burst-ending times), the selection rule for the sparse subsequence, and the
   local rule `Y = 0 ⇔ G ≥ 2`, `Y = 1 ⇔ G = 1` that our derivation (§3) and
   experiments (§6) check against.
7. **Reproduce or add?** Our §3 derivation **reproduces** the content of
   Lemma 4.1 / eqs (8–9) in the `n ≡ 9 (mod 16)` channel by an independent
   route (explicit affine chain + one parity split). It adds no new
   classification. Everything downstream (EOC-carry reformulation, finite-state
   audits) is **different in framing** from Chang but produced **no new
   mathematical content** and, per §6–§7, no predictive improvement.

### 1.2 The EOC repository (pre-existing formal machinery)

1. **Author:** Elias De Jesús (repo `EOC`; commits by `innerlightr-wq`).
2. **Title:** companion Lean artifact to *"A Global Occupation Conjecture for
   the Accelerated 3x+1 Map: Drift-Axis Progress, the Corrected Residue-Axis
   Reformulation, and the Least-Realizer Floor"* (Zenodo).
3. **Identifier:** Zenodo `doi:10.5281/zenodo.21895060` (all-versions
   `10.5281/zenodo.20569293`). Repo `github.com/innerlightr-wq/eoc-lean-verification`.
4. **Key items used this round:**
   - `EOC/Carry.lean` — `q` (carry recursion `q_0=0`, `q_{j+1}=3q_j+2^{s_j}`),
     `C` (closed form `C_N = Σ_{j<N} 3^{N-1-j} 2^{s_j}`), `q_eq_C`,
     `iter_carry_eq`.
   - `EOC/Realizer.lean` — `realizerCongruence` (Prop 5.2),
     `coarseAnchor` (`= −q_N·3^{−N} mod 2^S`), `leastRealizer`,
     `leastRealizer_eq_or_eq_add`, `residue_pinning`.
   - `EOC/ValuationWord.lean` — `orbit`, `iter`, `s`, `S`, the identity
     `2^{S_N}·iter d m0 N = 3^N·m0 + q d N` (under exact per-step divisibility).
5. **What it proves:** the exact realizer congruence and the confinement /
   least-realizer-floor apparatus (Props 5.2, 5.5–5.9), plus later periodic-
   and bounded-drift-sector escape theorems. It is *size*-oriented (floors,
   magnitudes), never residue-distributional.
6. **How we used it:** the identity `2^{S_N} m_N = 3^N m_0 + C_N` is the sole
   ingredient of the "mod-32 realizer identity" (§2); `coarseAnchor` is the
   `−C_N 3^{−N} mod 2^{S_N}` "moving anchor".
7. **Reproduce or add?** We only *instantiated* existing identities mod 32/64
   and re-expressed them; nothing was proved about the repo's objects.

### 1.3 Tao — almost-all Collatz orbits

1. **Author:** Terence Tao.
2. **Title:** *Almost all Collatz orbits attain almost bounded values.*
3. **Identifier:** arXiv:1909.03562; blog post
   `terrytao.wordpress.com/2019/09/10/…`.
4. **Section:** main theorem.
5. **What it proves:** density-1 (not "all") statement about Collatz orbits
   attaining almost-bounded values, via a logarithmic-density / measure
   argument on the 3-adic (Syracuse) distribution.
6. **How we used it:** only as the canonical reference for the epistemic gap
   "ensemble/measure balance ⇏ pointwise balance along a fixed orbit" (§7.4).
7. **Reproduce or add?** Not used mathematically; cited for the principle.

---

## 2. The mod-32 realizer identity

**Statement.** For the accelerated orbit `m_0, m_1, …` with valuation word
`d_j = v2(3m_j+1)`, prefix sums `S_j`, and carry `C_N = Σ_{j<N} 3^{N-1-j}2^{S_j}`
(equivalently `C_0=0`, `C_{n+1}=3C_n+2^{S_n}`):

```
2^{S_N} · m_N  =  3^N · m_0  +  C_N            (exact, in ℤ)
```

and hence, whenever `S_N ≥ 5` (so `2^{S_N} ≡ 0 mod 32`),

```
m_0  ≡  −C_N · 3^{−N}   (mod 32),      3^{−1} ≡ 11 (mod 32).
```

The shifted/tail form: with `D^{(k)}` the valuation word from time `k` and
`C_N(D^{(k)})` its carry,

```
m_k  ≡  −C_N(D^{(k)}) · 3^{−N}   (mod 32)     whenever  S_N(D^{(k)}) ≥ 5.
```

- **Provenance:** the exact `ℤ` identity is **External source** (EOC
  `Carry.lean`: `q_eq_C` + `iter_carry_eq`; it is also standard "carry
  telescoping" for the compressed map). Reducing it mod 32 and solving for
  `m_0` is **Derived here** but entirely routine (`3` is a unit mod `2^k`).
- **Relation to `coarseAnchor`:** `−C_N·3^{−N} mod 2^{S_N}` is exactly
  `EOC/Realizer.lean`'s `coarseAnchor d N (S d N)`, and
  `leastRealizer ∈ {coarseAnchor, coarseAnchor + 2^{S_N}}`. **Interpretation.**
- **Computational confirmation:** §6, Test 1 — 0 exceptions in 640,510 mod-32
  checks + 106,494 exact big-integer checks + 2,706 checks along one
  433,166-step orbit.

---

## 3. The cylinder derivation `m_0 = 16j+9`, `m_1 = 12j+7`, `m_2 = 18j+11`

### 3.1 Independent derivation performed here — **Derived here**

Let `m_0 ≡ 9 (mod 16)`, i.e. `m_0 = 16j + 9`, `j ≥ 0`.

**Step 0 → 1.**
`3m_0 + 1 = 48j + 28 = 4·(12j + 7)`. Since `12j + 7` is odd,
`v2(3m_0+1) = 2`, so `d_0 = 2` and

```
m_1 = (3m_0 + 1)/4 = 12j + 7.
```

**Step 1 → 2.**
`3m_1 + 1 = 36j + 22 = 2·(18j + 11)`. Since `18j + 11` is odd,
`v2(3m_1+1) = 1`, so `d_1 = 1` and

```
m_2 = (3m_1 + 1)/2 = 18j + 11.
```

**Step 2 → 3 (the split).**
`3m_2 + 1 = 54j + 34 = 2·(27j + 17)`, and the parity of `27j + 17` depends on `j`:

| `j` | `27j + 17` | `v2(3m_2+1) = d_2` |
|-----|------------|--------------------|
| even | odd | `1` |
| odd  | even | `≥ 2` |

**Bit-4 identification.** `m_0 = 16j + 9`, so

- `j` even ⇔ `m_0 ≡ 9 (mod 32)` ⇔ bit 4 of `m_0` is `0` ⇔ (Chang) `Y = 0`;
- `j` odd  ⇔ `m_0 ≡ 25 (mod 32)` ⇔ bit 4 of `m_0` is `1` ⇔ (Chang) `Y = 1`.

**Conclusion (Derived here).** The length-3 forward valuation cylinder at `m_0`:

```
(d_0, d_1, d_2) = (2, 1, 1)    ⇔   m_0 ≡ 9  (mod 32)
(d_0, d_1, d_2) = (2, 1, ≥2)   ⇔   m_0 ≡ 25 (mod 32)
```

### 3.2 Gap-length reading — **Derived here**, then matched to Chang

With `X_t = 𝟙[d_t ≥ 2]`, the chain reads `X = (1, 0, ?)` at `(m_0, m_1, m_2)`:
`m_0` is a burst step, `m_1` opens a gap run. Then

- `d_2 = 1` ⇒ `m_2` is still a gap step ⇒ the gap run has length **`G ≥ 2`**;
- `d_2 ≥ 2` ⇒ `m_2` is a burst step ⇒ the gap run had length **`G = 1`**.

So

```
(2,1,1)   ⇔  G ≥ 2  ⇔  m_0 ≡ 9  (mod 32)   ⇔  Y = 0
(2,1,≥2)  ⇔  G = 1   ⇔  m_0 ≡ 25 (mod 32)  ⇔  Y = 1
```

**Cross-check via the gap-start residue.** Gap start `m_1 = 12j + 7 ≡ 4j + 7
(mod 8)`: `j` even ⇒ `m_1 ≡ 7 (mod 8)`; `j` odd ⇒ `m_1 ≡ 3 (mod 8)`. Chang's
Lemma 4.1 (as read): `G = 1 ⇔ gap-start ≡ 3 (mod 8)`, `G ≥ 2 ⇔ gap-start ≡ 7
(mod 8)`. Both branches agree with §3.1. **Computational confirmation** in §6
Test 4 (0 violations / 2.6M events).

### 3.3 Relationship of this to Chang's existing lemma — **Interpretation**

- The `(2,1,1)` vs `(2,1,≥2)` cylinder split found here **is the same
  distinction** as Chang's `G ≥ 2` vs `G = 1` (Lemma 4.1 / eqs 8–9),
  specialized to the `n ≡ 9 (mod 16)` channel.
- Our contribution is a re-derivation by explicit affine substitution and a
  single parity split on `j`, plus the observation that the dichotomy can be
  phrased through `d_2` (the third forward valuation) instead of through the
  gap-start residue mod 8. These are **equivalent statements** — `d_2 = 1` is
  by definition "the gap continues past `m_1`."
- **This classification is NOT presented as a new theorem.** It reproduces
  Chang.

### 3.4 Independent vs. verified vs. related — explicit separation

| Aspect | Status |
|---|---|
| Affine chain `16j+9 → 12j+7 → 18j+11` and the parity split | **Derived here** (elementary; independent of reading Chang's proof) |
| Values checked on real orbits | **Computational confirmation** (§6 Test 3, Test 4) |
| Conclusion `bit4 ↔ G` | **External source** (Chang Lemma 4.1 / eqs 8–9); our derivation only re-proves it in this channel |

---

## 4. Bijection: `m mod 32` ↔ forward valuation prefix

**Statement (Derived here; elementary).** For odd `m`, let `A(m)` be the set of
partial sums `S_j < 5` of the forward valuation word of `m` (equivalently: run
the accelerated map, recording cumulative valuation, until it first reaches
`≥ 5`). The map `m mod 32 ↦ A(m)` is a **bijection** between the 16 odd
residues mod 32 and the 16 subsets of `{0,1,2,3,4}` containing `0`.

Full table (**Computational confirmation**, §6 Test 3; also reproduced by the
`−C_r·3^{−r}` formula):

```
 m%32 : A(m)                m%32 : A(m)
   1  : {0,2,4}              17  : {0,2}
   3  : {0,1}                19  : {0,1,4}
   5  : {0,4}                21  : {0}
   7  : {0,1,2,4}            23  : {0,1,2}
   9  : {0,2,3,4}  (Y=0)     25  : {0,2,3}   (Y=1)
  11  : {0,1,3}              27  : {0,1,3,4}
  13  : {0,3}                29  : {0,3,4}
  15  : {0,1,2,3}            31  : {0,1,2,3,4}
```

- **Interpretation.** The "forward valuation prefix" carries **exactly** the
  information in `m mod 32` — no more, no less. Any finite-state coordinate
  built from it is a *relabeling* of `m mod 32`, not a compression or an
  enrichment.
- Chang's channel: `9 ↔ {0,2,3,4} ↔ (d_0,d_1,d_2,…) = (2,1,1,2,…)`;
  `25 ↔ {0,2,3} ↔ (2,1,3,…)`. Distinguishing quantity: `d_2` (equivalently
  `m_2 mod 4`, equivalently — §3 — `27j+17` parity).

---

## 5. `C_N mod 64` as a 512-state finite coordinate

**Statement (Derived here; the reduction is elementary).**

```
C_N mod 64  =  f( N mod 16 ,  A ),
```

where `A` is the set of partial sums `S_j < 6` of the tail word.

**Modular reason (Derived here):**

1. A term `3^{N-1-j} 2^{S_j} ≡ 0 (mod 64)` iff `S_j ≥ 6`.
2. `S_j` is strictly increasing (`d_i ≥ 1`) and `S_j ≥ j`, so the first `r`
   with `S_r ≥ 6` satisfies `r ≤ 6`; only `j < r` contribute.
3. `ord_64(3) = 16`, so `3^{N-1-j} mod 64` depends only on `(N-1-j) mod 16`.
4. The contributing partial sums form a subset `A ⊆ {0,…,5}` with `0 ∈ A`:
   `2^5 = 32` such subsets.
5. Hence `≤ 16 · 32 = 512` finite states.

- **Computational confirmation (§6 Test 2):** 2,925,036 full-vs-prefix checks,
  0 mismatches; all **512** states realized; they map onto **32** distinct
  `C_N mod 64` values (the odd residues — `C_N` is always odd); the map is
  single-valued.
- **Interpretation.** This is a genuine finite-state coordinate for the
  *carry*, but by §4 it collapses, for predicting `m mod 32` / `Y`, to the
  forward prefix, i.e. to `m mod 32` itself. The extra ingredient `N mod 16`
  is nearly irrelevant to `Y` (§6 Test 5: `H(Y | N mod 16) = 0.88` bits).

---

## 6. Computational experiments

All code: `scratchpad/chang_eoc_experiment.py`, `scratchpad/supp_long.py`,
`scratchpad/supp_negatives.py` (Python 3.12, exact integer arithmetic).
Seed sets: `SMALL` = odd `3 … 1,000,001` (500,000 seeds), all trajectories run
to `1`; `BIG` = 40 random odds in `[2^220, 2^260)`; one seed in
`[2^180000, 2^180050)`; 4,000,000 iid geometric valuation words for N2.

### Test 1 — mod-32 realizer identity

- **Question:** does `m_k ≡ −C_N(D^{(k)})·3^{−N} (mod 32)` hold exactly for
  `S_N ≥ 5`, head and tail?
- **Method:** grow `N`, track `C_N mod 32` by the recurrence and `S_N`; compare
  `(−C_N·pow(3,−N,32)) mod 32` to `m_k mod 32`. Separately, for small seeds,
  check the exact `ℤ` identity `2^{S_N} m_{k+N} = 3^N m_k + C_N` with big ints.
- **Parameters:** 4,000 small seeds (head + up to 40 tail offsets, up to 6
  hits each) + 40 big seeds; plus one 433,166-step orbit (2,706 sampled
  checks).
- **Result:** mod-32 checks **640,510**, exceptions **0**. Exact `ℤ` checks
  **106,494**, exceptions **0**. Long-orbit checks **2,706**, exceptions **0**.
- **Conclusion:** the algebraic interface is translated correctly.
- **Limitations:** it is an identity, so 0 exceptions is expected; this tests
  transcription, not anything about balance. Longest single orbit still finite
  and still terminates at `1`.

### Test 2 — `C_N mod 64` reduction

- **Question:** is `C_N mod 64` a function of `(N mod 16, prefix pattern A)`,
  and how many states?
- **Method:** for many tail words and `N ∈ {r, r+1, r+3, r+7, r+16, T−k}`,
  compare the full recurrence `C_N mod 64` with the prefix-only formula;
  accumulate the state → value map and check single-valuedness.
- **Parameters:** 20,000 small seeds + 40 big seeds, `k = 0..29`.
- **Result:** **2,925,036** checks, **0** mismatches; **512/512** states seen;
  **32** distinct `C_N mod 64` values; map single-valued.
- **Conclusion:** the finite-state reduction (§5) is exact; 512 states.
- **Limitations:** none material — this is a modular-arithmetic fact.

### Test 3 — `Y` as a finite-state observable

- **Question:** is the map `m mod 32 ↔ forward prefix A` a bijection, and does
  the `−C_r·3^{−r}` formula reproduce it?
- **Method:** enumerate all 16 odd residues; compute `A` by forward simulation
  mod 32; independently compute `−C_r·3^{−r} mod 32` from `A`.
- **Parameters:** exhaustive over the 16 residues.
- **Result:** bijection **confirmed** (16 ↔ 16); formula reproduces **16/16**.
- **Conclusion:** the forward prefix ≡ `m mod 32` informationally (§4).
- **Limitations:** none — exhaustive.

### Test 4 — Chang burst-ending selection

- **Question:** (a) do selected events (`n_t ≡ 1 mod 8`, burst-ends) all land
  in `{9,25} mod 32`? (b) does `Y = 0 ⇔ G ≥ 2`, `Y = 1 ⇔ G = 1` hold? (c) what
  is the raw 9/25 split, overall and by burst length `L`?
- **Method:** for each trajectory build `X_j = 𝟙[d_j ≥ 2]`, find burst runs and
  the following gap runs, select burst-ends with `n_t ≡ 1 mod 8`, record
  `m%32, m%64, L, G, N mod 16, Y`, forward prefix, backward valuation suffix.
- **Parameters:** all 500,000 small seeds → **2,606,319** selected events.
- **Result:**
  - events with `n_t mod 32 ∉ {9,25}`: **0**.
  - `Y ↔ G` rule violations: **0**.
  - 9/25 split (raw counts on this seed set):

| channel | #events | #9 | #25 | P(25) | #9 − #25 |
|---|---|---|---|---|---|
| ALL   | 2,606,319 | 1,397,102 | 1,209,217 | 0.4640 | +187,885 |
| L = 1 | 1,588,237 |   920,867 |   667,370 | 0.4202 | +253,497 |
| L ≥ 2 | 1,018,082 |   476,235 |   541,847 | 0.5322 | −65,612 |

- **Conclusion:** the residue confinement (`→ 9 mod 16`) and the local rule
  `Y ↔ G` hold exactly; the split is non-degenerate and **channel-dependent**
  (L=1 leans to `9`, L≥2 leans to `25`).
- **Limitations (important):** every trajectory here terminates at `1`; the
  sample is transient-dominated and small-number-biased. These counts are
  **not** a sparse subsequence of one infinite aperiodic orbit and say
  **nothing** about asymptotic densities or Chang's pointwise-balance target.
  Reported as raw finite-sample counts only.

### Test 5 — does the EOC coordinate improve prediction of `Y`? (L ≥ 2)

- **Question:** among `L ≥ 2` selected events, how much does each state
  description determine `Y`? (Conditional entropy `H(Y | state)`.)
- **Method:** plug-in conditional entropy over the empirical joint
  distribution; no model fitting.
- **Parameters:** 1,018,082 events; baseline `H(Y) = 0.9970` bits.

| description | #states | `H(Y | state)` (bits) |
|---|---|---|
| A. `m mod 64` | 4 | **0.0000** |
| B. `N mod 16` alone | 16 | 0.8841 |
| C. forward prefix (sums < 5) | 2 | **0.0000** |
| C′. forward prefix (sums < 6) | 4 | **0.0000** |
| C″. forward valuation tuple | 57 | **0.0000** |
| D. `(N mod 16, forward prefix<5)` | 32 | **0.0000** |
| E1–E4. backward valuation suffix, len 1–4 | 1 / 16 / 124 / 645 | 0.9970 / 0.9866 / 0.9554 / 0.8848 |
| `m mod 32` (reference) | 2 | **0.0000** |

- **Conclusion:** every **forward** coordinate determines `Y` exactly
  (`H = 0`), the smallest doing so with **2 states** — identical to `m mod 32`
  on this channel. `N mod 16` alone and the backward suffixes are nearly
  uninformative. The EOC/carry coordinate does **not** compress below
  `m mod 32` and adds no predictive structure.
- **Limitations:** plug-in entropy is biased for rare states, but the salient
  values are exact `0` (structural determinism), not statistical estimates.
  L ≥ 2 sample still from terminating orbits.

### N1 — do burst-end → next-burst-end return maps close mod `2^k`?

- **Question:** is `m_{t_i} mod 2^k ↦ m_{t_{i+1}} mod 2^k` (consecutive
  burst-ending times) a well-defined function for fixed `k`?
- **Method:** within each trajectory, list consecutive selected burst-ends;
  accumulate the residue → {residues} relation; count inputs with fan-out > 1.
- **Parameters:** odd seeds `3 … 2,000,001`; **4,555,113** consecutive pairs;
  `k ∈ {5,6,7,8,10,12}`.
- **Result:** for **every** tested `k`, **every** input residue maps to the
  maximum possible number of outputs (fan-out `2, 4, 8, 16, 64, 256` for
  `k = 5..12`). No closure at any tested modulus.
- **Conclusion (Computational observation):** the burst-ending subsequence is
  **not** governed by a finite-state deterministic dynamical system on
  `ℤ/2^k` for any tested `k`. Higher bits of `m_t` (and the intervening gap
  length) determine where the next burst ends.
- **Limitations:** finite `k` tested; terminating-orbit sample; does not rule
  out closure at some untested modulus or with additional coordinates (though
  the full-fan-out pattern makes that look unlikely).

### N2 — ensemble `Y`-balance under the geometric valuation measure

- **Question:** under `d_j` iid with `P(d = k) = 2^{-k}` (`k ≥ 1`), is the
  realizer residue `−C_N·3^{−N} mod 32` equidistributed, and is Chang's channel
  balanced?
- **Method:** sample random words until `S_N ≥ 5`; histogram `−C_N·3^{−N} mod
  32`; condition on words starting `(2,1,…)`.
- **Parameters:** **4,000,000** samples.
- **Result:** all 16 odd residues hit with counts in **[249,374 , 250,727]**
  (uniform expectation 250,000). Channel `(2,1,…)`: `#9 = 250,201`,
  `#25 = 250,727`, `P(25) = 0.5005`, `#9 − #25 = −526`.
- **Conclusion (Computational confirmation):** under this measure the residue
  is equidistributed and the `9/25` channel is balanced to within sampling
  noise — consistent with Chang's Map Balance Theorem (**External source**;
  exact difference `±1` for `K ≥ 5`).
- **Limitations:** the geometric measure is a heuristic model; it is **not**
  the empirical distribution of any single deterministic orbit's
  burst-ending subsequence (cf. §7.4).

---

## 7. Negative findings (preserved deliberately)

### 7.1 The EOC carry representation is exact but does not improve prediction of `Y`

- **Computational observation** + **Interpretation.**
- Test 1: `m_k ≡ −C_N·3^{−N} (mod 32)` — exact, 0 exceptions.
- Test 5: the forward-prefix / carry coordinate determines `Y` with `H = 0` —
  but so does `m mod 32` (2 states), and by §4 the forward prefix **is**
  `m mod 32` relabeled. `N mod 16`, the one genuinely new ingredient the carry
  picture contributes, gives `H(Y | N mod 16) = 0.88` bits (near-useless).
- Net: the carry identity is a **change of variables**, not a reduction. It
  relocates "distribution of `m_t mod 32` along the subsequence" to
  "distribution of `(N mod 16`, first ≈5 forward valuations) along the
  subsequence" — the same difficulty.

### 7.2 The apparent `m ↦ m + 16` pairing is tautological

- **Derived here** (elementary) + **Interpretation.**
- `m_0 = 16j + 9 ↦ 16(j+1) + 9` flips the parity of `j`, i.e. swaps
  `9 ↔ 25 (mod 32)`, i.e. flips `Y`. It "pairs" a `Y = 0` state with a
  `Y = 1` state **by construction** — it is literally "toggle bit 4."
- It is **not** a dynamical symmetry: one accelerated step sends
  `m_1 = 12j + 7 ↦ 12j + 19 = m_1 + 12` (not `+16`), and the two orbits then
  have different `d_2` and diverge. `m ↦ m + 16` does not commute with `T`.
- Consequently the pairing carries **no information** about how often `Y = 0`
  vs `Y = 1` occurs along a given orbit — which is the entire question.

### 7.3 The tested finite-state return maps do not close mod the tested powers of two

- **Computational observation** (N1). No closure at `2^5, 2^6, 2^7, 2^8,
  2^10, 2^12`; full fan-out at every modulus. There is (empirically) no
  finite-state Markov/automaton description of the burst-ending subsequence on
  `ℤ/2^k` alone.

### 7.4 Exact ensemble balance does not establish pointwise balance

- **External source** (Chang frames exactly this as the residual target;
  Tao 2019 is the canonical instance of the gap) + **Interpretation**.
- N2 shows exact `9/25` balance under the iid geometric valuation measure;
  Chang's Map Balance Theorem gives it exactly in the combinatorial ensemble.
- Neither implies that a **single deterministic orbit**'s burst-ending
  subsequence is balanced. A fixed orbit is one trajectory, not a measure;
  the valuation word it produces is not iid geometric and its empirical
  burst-ending residue distribution is exactly the unknown Chang needs.
- This is the standard "almost all ≠ all" barrier; nothing in this session
  narrows it.

---

## 8. Transport Audit: Genuine-Orbit Degeneracy and Failure of the GT/C Bridge

Audit performed 2026-09-03 (same session, later round). Question asked: does the
transport-deficit / matching-precision / regeneration framework provide a new
dynamical bridge between Garcia–Tal/Curry value-space sparsity and the EOC
moving-anchor / pointwise realizer-placement problem? **Verdict: no** (§8.9).

Indexing note: the transport paper uses `d_1..d_j`, `S_j = Σ_{i=1}^j d_i`;
scratchpad §2 uses `d_0..d_{N-1}`. Same objects; transport notation below.

### 8.1 External source record

**External source.** `SOURCE TO VERIFY` — no arXiv/DOI identifier located; local
copy only (`~/Downloads/transportDeficits (1) (4).pdf`, 26 pp., header "August
2026 — Technical Note"). Not checked against published literature.

> Elias De Jesús, *Transport Deficits and 2-Adic Survival Budgets in
> Accelerated Collatz Words: Equality Cylinders, Past–Future Matching, and
> First-Failure Structure*, August 2026 technical note.

Core exact **abstract-word** results used here (verified against the paper and
re-checked computationally; **not** invalidated by the audit below):

- **Mismatch recurrence** (Prop 29, Eq 39), every step, perfect or failed:
  ```
  X_{j+1} = ( X_j − K_j(d_{j+1}) ) / 2^{d_{j+1}}
  ```
- **Perfect-transport law** (Prop 32 Eq 52; Thm 18 Eq 25); a step with
  `δ_{j+1} = 0` (⟺ `K_j(d_{j+1}) = 0`):
  ```
  F_{j+1} = F_j + d_{j+1},        M_{j+1} = M_j − d_{j+1}
  ```
  hence `H^tr_j := F_j + M_j` is **conserved on perfect steps**.
- **First-failure regeneration** (Prop 30, Eq 46), with `X_j = 2^{M_j} a`,
  `K_j = 2^{M_j} u`, `a,u` odd:
  ```
  M_{j+1} = M_j − d_{j+1} + v2(a − u)
  ```
- **Failure budget map** (Prop 33, Eq 56):
  ```
  ΔH^tr = v2(a − u) − δ_fail
  ```
- **Depth reset** (Cor 34, Eqs 59–60): at a failure with `F_j > 0`,
  `δ_fail > F_j`, hence `F_{j+1} < d_{j+1}`.

Supporting definitions: `ξ_j := −C_j·3^{−j} ∈ ℤ₂` with
`ξ_j = χ_j + 2^{S_j} T_j` (Eq 2); `χ_j := ξ_j mod 2^{S_j}` (the "exposed coarse
anchor" = scratchpad §2's `coarseAnchor`); `A_{j,∞} := Σ_{r≥0} 2^{D_r}·3^{−(j+1+r)}`
(Prop 14, Eq 18); `X_j := T_j − A_{j,∞}` (Eq 36); `M_j := v2(X_j)` (Def 15,
Eq 20); matching criterion `δ_{j+1}=…=δ_{j+m}=0 ⟺ M_j ≥ D_m` (Thm 16, Eq 21).

**These abstract-word theorems are correct and stand.** The audit below
concerns only their specialization to genuine positive-integer orbits.

### 8.2 Decisive genuine-orbit identity

**Derived here — exact algebraic corollary of the EOC carry identity.**
`SOURCE TO VERIFY` — whether this exact ℤ₂ limiting formulation already appears
explicitly in the EOC manuscript or elsewhere (it is `iter_carry_eq` /
`residue_pinning` taken to the 2-adic limit).

For a genuine accelerated orbit from odd seed `m_0` (EOC `Carry.lean`
`q_eq_C` + `iter_carry_eq`):
```
2^{S_j} m_j = 3^j m_0 + C_j            (exact, in ℤ)
```
Therefore
```
ξ_j = −C_j·3^{−j} = m_0 − m_j·2^{S_j}·3^{−j}       (in ℤ₂)
```
Since `m_j` and `3^{−j}` are 2-adic units, `v2(ξ_j − m_0) = S_j`, hence
```
    ξ_j → m_0   in ℤ₂          (ξ_∞ := lim_j ξ_j = m_0)
```
Combining with `ξ_j = χ_j + 2^{S_j} T_j` (Eq 2) and the telescoping identity
`ξ_{j+m} = ξ_j − 2^{S_j} A_{j,m}` (iterate the paper's App. A.2
`ξ_{j+1} = ξ_j − 2^{S_j}·3^{−(j+1)}`), so that `A_{j,∞} = (ξ_j − ξ_∞)/2^{S_j}`:
```
    X_j = T_j − A_{j,∞} = ⌊ m_0 / 2^{S_j} ⌋
    M_j = v2( ⌊ m_0 / 2^{S_j} ⌋ )
    χ_j = m_0 mod 2^{S_j}
```

For a genuine orbit the transport mismatch `X_j` is **not** an independent
past–future dynamical degree of freedom. It is exactly the high-bit tail of the
original seed `m_0` above binary position `S_j`; `M_j` reads those seed bits and
the running total `S_j`, nothing else.

### 8.3 Permanent perfect transport past the seed bit-depth

**Derived here.** If `2^{S_j} > m_0` then `⌊m_0/2^{S_j}⌋ = 0`, so
```
M_j = ∞ ,    and therefore    δ_{j+1} = δ_{j+2} = … = 0.
```
Transport becomes **permanently perfect** once the cumulative valuation depth
`S_j` passes `⌊log₂ m_0⌋`.

This is the transport-coordinate form of **residue pinning**: once
`2^{S_j} > m_0`, `χ_j = m_0` (the exposed anchor equals the seed), so the
paper's `A_{j,∞}` target is met exactly. **Not** a new Collatz theorem — it is
the least-realizer / `residue_pinning` regime (scratchpad §2, EOC
`Realizer.lean`) re-expressed 2-adically.

### 8.4 Computational confirmation

**Computational confirmation** — scripts `scratch/tcc2.py`,
`scratch/transport_audit2.py`, `scratch/transport_audit.py`; exact integer /
2-adic arithmetic. These confirm the implementation and illustrate §8.2–§8.3;
they are **not** the proof.

- `X_j = ⌊m_0/2^{S_j}⌋` (checked mod 2⁴⁸): **0 mismatches / 3128 rows**, 13
  seeds including Mersenne primes up to `2¹²⁷−1`.
- `χ_j = m_0 mod 2^{S_j}`: confirmed on every tested row.
- `r(D_j) = m_0` for all post-transient `j`: confirmed on every tested seed.
- Across **6,000 genuine trajectories**, **43,814** transport failures
  (`K_j ≠ 0`) observed; **0 / 43,814** occurred after `S_j > bitlen(m_0)`.
  Every failure lies in the initial transient.
- Max `F_j` at any observed failure ≈ 13–16. Positive-regeneration events
  (`v2(a−u) > δ_fail`) present at `H_before ≈ 4` (≈ 6% of failures), **absent
  at `H_before ≥ 8`** in this sample. Consistent with the transport paper's own
  §D.9 scan (40,000 trajectories, 380,078 failures with `H^tr ≥ 8`, 267 with
  `v2(a−u) > H^tr`, up to `H^tr ≈ 13`) — and here shown to be **entirely a
  transient phenomenon** (`S_j ≤ bitlen(m_0)`).

Limitations: seeds `< 5×10⁶` (plus a few Mersenne primes for the `X_j`
identity); all orbits terminate at 1; no divergent orbit accessible; `X_j`
checked to 2⁴⁸, not exactly; finite `H` only.

### 8.5 Negative result — transport → Garcia–Tal/Curry bridge

**Negative result — deterministic.** The proposed bridge
```
transport failures / regeneration
  → recurrent dynamical events
  → Garcia–Tal/Curry window-count sparsity
```
does **not** exist in this form for genuine finite seeds. Reason: `ξ_j → m_0`
(§8.2) forces `M_j = ∞`, `K_j = 0`, `δ_{j+1} = 0` for every `j` with
`S_j > bitlen(m_0)`. A genuine orbit therefore has **only finitely many**
transport failure / reset / regeneration events — all inside a transient of
length `≈ (log₂ m_0)/α` — and thereafter **one** transport excursion lasting
forever, with matching precision `∞` because the target is the seed itself.

There is no infinite sequence of excursion-start events to localize into an
Archimedean window, so no GT/C window-count argument can be attached.

This is **stronger than "one quantitative lemma is missing."** The bridge is
**structurally blocked** by the exact identity `ξ_∞ = m_0`. The statement that
would be needed — *"a genuine divergent orbit has infinitely many `j` with
`δ_{j+1} > 0`"* — is **false**, refuted by `χ_j = m_0` frozen (§8.3).

### 8.6 Relation to collapse / moving anchor

**Interpretation.** For genuine orbits, `F_j = S_j − log₂ χ_j` is the same
coarse-collapse / moving-anchor depth already present in EOC (scratchpad §2;
`E_j = S_j − log₂ r(D_j)` differs from `F_j` by `≤ 1`, transport Cor 3).
Post-transient, `χ_j = m_0`, so `F_j = S_j − log₂ m_0` — a deterministic linear
ramp, no new content.

The transport decomposition `H^tr = F + M` (§D.3, Eq 50) is a meaningful
**abstract-word** bookkeeping identity ("perfect transport converts stored
precision into realized depth one-for-one"), but after the genuine-orbit
transient `M = ∞`, so it is **not** a useful finite asymptotic Lyapunov
variable. Every scalar combination examined in this audit (`H^tr ± λR`,
`F ± λR`, `M − λ log₂ m`, `F + M + λR`) is either `∞` or an unbounded ramp on
genuine orbits — recorded as a failed Lyapunov search.

**Transport introduces no independent asymptotic obstruction beyond the
existing moving-anchor / collapse problem.**

### 8.7 Negative result — Chang cylinder comparison

**Negative result — Chang comparison.** The transport variables give no useful
bridge to the Chang bit-4 / cylinder-discrepancy problem (§7.1, OQ1).

- Chang's `Y` is determined by a short **forward** valuation prefix / low
  2-adic residue of `m_t` (scratchpad §4).
- `M_j = v2(⌊m_0/2^{S_j}⌋)` reads **high bits of the original seed** during a
  bounded initial transient.

These read different bits. Scan (`scratch/transport_audit2.py`, 113,647
burst-ending events): mean `M_before` = 0.779 (`Y=0`, `n=13,531`) vs 0.750
(`Y=1`, `n=13,368`); transient fraction 0.233 vs 0.265 — no meaningful
difference between the two Chang outcomes.

```
Task 10 verdict:  D — no meaningful interaction.
```

### 8.8 Interpretive consequence for the transport paper's open problems

**Interpretation.** The transport paper's Open Problems 23 (§11) and 26–27
(§C.4), insofar as they ask whether a genuine positive-integer orbit can
achieve arbitrarily large or infinite matching precision `M_j(n)` with its own
actual future, should be re-examined in light of
```
M_j(n) = v2( ⌊ n / 2^{S_j} ⌋ ) ,    hence    M_j(n) = ∞  ⟺  n < 2^{S_j}.
```
For every finite positive seed, `M_j = ∞` once `2^{S_j} > m_0`.

**The paper is not wrong.** The abstract transport theorems (§8.1) remain
valid. But the genuine-orbit interpretation of "matching precision" appears to
collapse to residue pinning, and the open-problem statements should be revised
(or explicitly restricted to non-realizable / adversarial future
continuations) before further circulation. `SOURCE TO VERIFY` against the
paper's own qualifier "outside already-understood trivial or periodic
behavior" — the mechanism here (`ξ_∞ = seed`) is arguably exactly that
qualifier.

### 8.9 Final status

```
Transport is useful abstract-word structure, but NOT a new asymptotic
genuine-orbit dynamical coordinate.

No transport → Garcia–Tal/Curry bridge.
No transport → Chang cylinder-discrepancy bridge.
```

Audit verdict (of the five options A–E offered): **D — transport is mostly a
reparameterization of the existing moving-anchor / collapse obstruction**,
sharpened by the observation that its distinctive quantity `M_j` / `H^tr` is
**degenerate (`= ∞`) on every genuine orbit after a bounded transient**. Not
verdict E: no transport theorem is false.

The unresolved pointwise problem remains the same one already identified
elsewhere in this scratchpad (OQ1, §7.4): how a single deterministic orbit
samples arithmetic states over long times.

---

## 9. Open questions

- **OQ1 (Open question).** Along a single infinite aperiodic accelerated
  orbit, does the burst-ending subsequence (`n_t ≡ 1 mod 8`) visit `9 mod 32`
  and `25 mod 32` with `#9 − #25 = o(K)` over the first `K` events? (Chang's
  reduced target; unresolved.)
- **OQ2 (Open question).** Is there *any* finite set of coordinates
  (beyond `m_t mod 2^k`) closing the burst-end return map to a finite-state
  system? N1 tested only `m_t mod 2^k`.
- **OQ3 (Open question).** Does a windowed-sparsity bound
  (`#(O ∩ [a,a+X)) ≤ C_β X^β log 2X`, `β < 1`; Garcia–Tal/Curry, **not** in
  the EOC repo, **SOURCE TO VERIFY** for exact statement/authorship) refine
  per residue class mod 32 with the same exponent? Needed for GT/C to touch
  Chang's split; no evidence either way here. *(Update, §8: the transport
  framework was tested as a route to attach GT/C and found structurally
  blocked on genuine orbits — this OQ is untouched by that negative result.)*
- **OQ4 (Open question).** Can `EOC/PeriodicRealizer.lean`'s `ξ_X` /
  `delta_X` apparatus be given a residue-mod-32 reading that constrains the
  *distribution* (not just the value) of bit 4 over an ensemble of blocks?
  §4 suggests the value is determined but the distribution is not addressed.
- **OQ5 (Open question).** Is the channel dependence in Test 4
  (`P(25) ≈ 0.42` for `L = 1`, `≈ 0.53` for `L ≥ 2`) a genuine asymptotic
  feature or a small-number artifact of terminating orbits?
- **OQ6 (Open question).** The transport-audit identity `M_j = v2(⌊m_0/2^{S_j}⌋)`
  (§8.2) gives the *value* of matching precision explicitly; its *distribution*
  over dynamically-selected `n` (e.g. along burst-ending times, or over
  realizers of a fixed prefix) is unaddressed — and that distributional
  question is the same ergodic-mixing / Collatz-level obstacle as OQ1 / §7.4.

---

## 10. Reproducibility / file inventory

Scratch code, copied into the repo working tree as **untracked** files
(`scratch/`, gitignored-by-intent; delete freely, not part of the build):

| file | contents |
|---|---|
| `scratch/chang_eoc_experiment.py` | §6 Tests 1–5 |
| `scratch/supp_long.py` | §6 Test 1 on one 433,166-step orbit |
| `scratch/supp_negatives.py` | §6 N1 (return-map closure), N2 (ensemble balance) |
| `scratch/transport_audit.py` | §8 first-pass transport audit on genuine orbits |
| `scratch/transport_audit2.py` | §8 `X_j`/`χ_j` identity, failure stats, Chang connection |
| `scratch/tcc2.py` | §8 minimal exact check `X_j = ⌊m_0/2^{S_j}⌋` (mod 2⁴⁸) |

Runtimes: §6 scripts ~32 s / ~6 s / ~22 s; §8 scripts ~5 min / ~17 s / <1 s
(single core, CPython 3.12). Determinism: `random.seed(20260903)` (main §6),
`random.seed(1)` (supp_long), `random.seed(7)` (supp_negatives),
`random.seed(3)` / `random.seed(5)` (transport_audit2).

**Verdict — Chang round (from §6–§7):** the EOC carry coordinate is
**C — essentially a relabeling of the raw residue state; adds no useful
predictive structure**. Smallest state space capturing all deterministic
information about `Y`: **2 states** (`m_t mod 32 ∈ {9, 25}`, i.e. `Y` itself;
equivalently `d_2 ∈ {1, ≥2}`, equivalently `m_2 mod 4`).

**Verdict — Transport round (from §8):** **D — transport is mostly a
reparameterization of the existing moving-anchor / collapse obstruction**, and
its distinctive quantity `M_j` / `H^tr` is degenerate (`= ∞`) on every genuine
orbit after a bounded transient. No transport → Garcia–Tal/Curry bridge; no
transport → Chang-discrepancy bridge. No transport theorem is false.

No Lean sources, README, or imports were modified. No exploratory finding in
this file is a theorem claim.
