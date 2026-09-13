# Round 3 — Deferred Theorems

Items examined this round but not implemented in Lean, each with an exact statement, the missing
dependency, a difficulty estimate, and a recommendation. None of these were left as `sorry` in any
committed file — they simply were not attempted in Lean, only derived and verified by hand (and,
where noted, computationally in Round 1/2's Python scripts).

---

## D1. General-`q` joint/marginal cylinder counting law (`cylinder_digits_joint`, full form)

**Statement**:
```
theorem count_padicValNat_affine (C : ℕ) (hC : Odd C) :
    ∀ K B q, 0 < B →
      ((Finset.range (2 ^ K)).filter (fun k => padicValNat 2 (B + 2 * C * k) = q)).card
        = if Odd B then (if q = 0 then 2 ^ K else 0)
          else (if 1 ≤ q ∧ q ≤ K then 2 ^ (K - q) else 0)
```
with the corollary, applying `cylinder_restart` exactly as
`EOC.CylinderCounting.cylinder_next_digit_eq_one_card` does for `q = 1`:
```
theorem cylinder_next_digit_card (d : ℕ → ℕ) (t m K q : ℕ) (h : Realizes d t m)
    (hq : 1 ≤ q) (hqK : q ≤ K) :
    ((Finset.range (2 ^ K)).filter
        (fun k => a (orbit (m + 2 ^ (S d t + 1) * k) t) = q)).card
      = 2 ^ (K - q)
```
and, by re-applying this at every subsequent depth (see D2 below), the full `k`-step joint law.

**Missing dependency**: the general count lemma itself — nothing else in the repository is
missing; `cylinder_restart` already supplies everything needed to transfer it to the real
`a`/`T`/`orbit` objects, exactly as done for `q=1` in `EOC/TaoLike/CylinderDigitCounting.lean`.

**Complete proof sketch** (verified by hand; this is the derivation `ROUND3_FORMALIZATION_REPORT.md`
Part II summarizes; two independent lines of derivation were checked against each other and against
Round 1/2's Python scripts before being written down here):

Induct on `K`.

- **`K = 0`**: only `q = 0` can occur (`q ≤ K = 0`); direct unfold, no recursion.
- **`K → K+1`**: write `B = 2B'` when `B` is even (`Even B ↔ ∃ B', B = 2B'`; when `B` is odd the
  whole count is `0` for `q ≥ 1`, immediate since `B + 2Ck` is always odd, and `q=0` gives
  `2^(K+1)` immediately since it holds for every `k`, no recursion needed — both are one-line
  parity facts, no induction).

  For `B` even (`B = 2B'`), split `k ∈ range(2^{K+1})` into `k = 2j` and `k = 2j+1`
  (`j < 2^K`), via the *same* image-bijection technique already used for
  `card_filter_mod_two` in `CylinderDigitCounting.lean` (that lemma's proof pattern — `Finset.ext`
  + `Finset.card_image_of_injective` — generalizes directly to a 3-way split
  `range(2^{K+1}) = image(2·) (range 2^K) ⊔ image(2·+1) (range 2^K)`, disjoint union, each part in
  bijection with `range(2^K)`).

  - `k = 2j`: `B + 2C(2j) = 2(B' + 2Cj)`, so
    `padicValNat 2 (B+2C·2j) = 1 + padicValNat 2 (B' + 2Cj)` — an instance of the *same* count
    problem one level down, base `B'`, **same** `C`, at depth `K` (not `K+1`) — apply the
    induction hypothesis with `(B, q) ↦ (B', q-1)`.
  - `k = 2j+1`: `B + 2C(2j+1) = 2((B'+C) + 2Cj)`, so similarly
    `padicValNat 2 (B+2C·(2j+1)) = 1 + padicValNat 2 ((B'+C) + 2Cj)` — apply the IH with
    `(B,q) ↦ (B'+C, q-1)`.

  Since `C` is odd, exactly one of `B'`, `B'+C` is odd (they differ by an odd number). This gives
  the `q=1` case directly (matching `CylinderDigitCounting.lean`'s existing proof, not needing the
  IH at all): whichever of the two branches has the odd base contributes all `2^K` of its `j`'s to
  `q=1` (constant, no dependence on `j`), the other contributes `0`. Total: `2^K = 2^{(K+1)-1}`. ✓.

  For `q ≥ 2` (so the inner target is `q' := q-1 ≥ 1`, and `q ≤ K+1 ⟺ q' ≤ K`, matching the IH's
  domain exactly): apply IH to both branches at `q'`. Exactly one of `B', B'+C` is odd (contributing
  `0` at `q' ≥ 1` by the IH's own odd-base clause) and the other is even (contributing
  `2^{K-q'} = 2^{(K+1)-q}` by the IH's even-base clause). Sum: `0 + 2^{(K+1)-q} = 2^{(K+1)-q}`. ✓.

This closes the induction. Both branches were checked against each other and against the K=0..2
cases by hand (matching Round 1's Method B script's residue-class construction exactly, which is
the same argument in un-formalized form), and the resulting formula was independently confirmed —
by two separate computational methods, at multiple real Collatz seeds — in
`ROUND1_REPORT.md`/`scripts/two_step_law_check.py` and `three_step_law_check.py`.

**Estimated difficulty**: **D (substantial new formalization)**. The mathematics is fully
resolved and the induction is standard in shape, but implementing the 3-way `range` split as a
reusable Lean lemma, correctly threading the `Even`/`Odd` case dispatch through nested `if`s, and
managing the index bookkeeping (`K-q` vs `K+1-q` arithmetic under `omega`) across ~4 real branches
realistically requires substantially more Lean engineering than the `q=1` case implemented this
round (which itself required several rounds of lemma-name correction against the actual Mathlib
API). A rough estimate, based on the `q=1` case's actual size (~90 lines after debugging) and the
roughly 2x branching factor of the general induction: 250–400 lines, likely 15–30 compile-and-fix
iterations even for a careful implementer with live compiler feedback.

**Worth formalizing now?** Not this round — correctly scoped as the single highest-value Lean
target for a **dedicated** future round (not a sub-task squeezed into a broader exploration round),
since the mathematics is completely settled and only the engineering remains.

---

## D2. The `k`-step extension (arbitrary window, not just one digit ahead)

**Statement**: iterating D1's one-step corollary via `cylinder_additivity` (already in
`EOC/TaoLike/CylinderAppend.lean`) gives, for any finite word `e` of length `u` with all digits
`≥ 1`:
```
theorem cylinder_word_count (d : ℕ → ℕ) (t m K : ℕ) (h : Realizes d t m)
    (e : ℕ → ℕ) (u : ℕ) (he_pos : ∀ i < u, 1 ≤ e i) (hSK : S e u ≤ K) :
    ((Finset.range (2 ^ K)).filter
        (fun k => ∀ i < u, a (orbit (m + 2 ^ (S d t + 1) * k) (t + i)) = e i)).card
      = 2 ^ (K - S e u)
```
i.e. the exact multi-digit analogue of D1, matching Round 1's full product law
`P(d_t=q_1,…,d_{t+k-1}=q_k) = ∏2^{-q_i}` in finite-counting form (mass `2^{-S e u}` exactly).

**Missing dependency**: D1 (the general-`q` one-step case) — this is a genuinely short corollary
once D1 exists, by induction on `u` using `cylinder_additivity` to peel one further digit at each
step (the *same* pattern already used by Round 1/2's informal derivation, and structurally
identical to how `cylinder_additivity` itself is proved from `cylinder_restart` in
`CylinderAppend.lean`).

**Estimated difficulty**: **C (small new lemma), conditional on D1**. Genuinely easy once D1
exists; not attempted since D1 itself was not completed.

**Worth formalizing now?** Only after D1.

---

## D3. Doob h-transform for the conditioned next-digit law

**Statement** (finite-count form, matching `ROUND2_REPORT.md` Part V exactly, translated out of
probability language into raw cylinder-mass/counting language to avoid needing a new measure-
theory layer):
```
def survivalCount (c : ℤ) (j S N : ℕ) : ℕ :=  -- recursive, mirrors scratch/extremal_orbit_prefix_audit.py's confined_count_dp / survival_count
  ...

theorem conditioned_next_digit_count (c : ℤ) (j S N r : ℕ) (hr : confined_exact (S+r) (j+1) c) :
    -- among confined-surviving completions from (j,S) to depth N with first digit r,
    -- the EXACT relation to survivalCount at (j+1, S+r) vs (j, S)
    ...
```

**Missing dependency**: (a) D1/D2 (to have the exact mass of each individual completion), and
(b) a NEW recursive definition `survivalCount`/`confinedCountDP` — the exact confinement predicate
`Confined`/`R`/`alpha` from `EOC/Confinement.lean` used directly, translated into the *integer*
form `2^(Sj-c) ≤ 3^j` already used (as a proof *technique*, not yet a named `def`) in
`scratch/extremal_orbit_prefix_audit.py`'s `confined_exact`. This integer-comparison device would
need to be lifted from an informal Python pattern into an actual Lean `def` with a proven
equivalence to `Confined`/`R` — not itself hard, but is additional, currently nonexistent,
plumbing.

**Estimated difficulty**: **D (substantial new formalization)**. Requires D1/D2 first, then a new
recursive DP definition with a termination proof (recursion on `N - j`), then the Doob-transform
identity itself (which, as shown in `ROUND2_REPORT.md` Part V, is a one-line Bayes computation
*given* the DP — the real work is entirely in standing up the DP as a well-founded Lean
definition with the right recursive equations available as rewrite lemmas).

**Worth formalizing now?** No — explicitly flagged in the round's own instructions as something to
defer rather than force; this assessment concurs. It is a reasonable Round 4+ target *after* D1/D2.

---

## D4. Conditioned two-step correlations (exact sign pattern)

**Statement**: a Lean formalization of `ROUND2_REPORT.md` Part VI's finding (the exact,
reproducible mixed-sign correlation structure under survival conditioning).

**Missing dependency**: D3 (the conditioned kernel itself must exist first — correlations are a
second-order property of it).

**Estimated difficulty**: **D**, strictly harder than D3 since it requires reasoning about *pairs*
of conditioned digits and comparing against a product, likely needing real inequalities over the
DP's values (not just an identity) — genuinely more delicate than D3's clean Bayes identity.

**Worth formalizing now?** No. Lowest priority of the deferred items — Round 2 already established
this numerically to a satisfying level of rigor (exact rational arithmetic, multiple states,
reproducible sign pattern), and a Lean proof would mostly re-confirm rather than extend that
finding, at high engineering cost.

---

## D5. Exact first-passage/first-crossing law

**Statement**: a Lean version of `ROUND2_REPORT.md` Part VII's `P(τ = j)` recursion.

**Assessment, per the round's own instruction to check equivalence-vs-novelty first**: Round 2
Part VII already determined this is **the existing forward DP re-expressed in probabilistic
language**, not a new identity. Per the round's explicit instruction ("If equivalent to existing
DP: document the equivalence; do not duplicate it") — **this should NOT be formalized as a
separate theorem**. If D3's DP-in-Lean (`survivalCount`) is ever built, the first-crossing law
falls out of it as a trivial corollary (`escaped mass at step j = total mass − mass surviving to
step j`, a one-line telescoping fact), not worth a dedicated theorem statement of its own.

**Worth formalizing now?** No, and arguably not ever as a *separate* theorem — fold it into D3's
statement as a remark/corollary if D3 is ever built.

---

## D6. Exponential martingale / optional stopping

**Statement**: a Lean version of `ROUND2_REPORT.md` Part XII's canonical exponential martingale
`M_j = exp(θD_j - jΛ(θ))` and its optional-stopping consequence.

**Assessment**: Round 2 found this **reproduces, rather than strengthens**, the existing
`geom_persistence_pointwise_chernoff`/`iid_geom_chernoff_bound` machinery already fully formalized
in `PersistenceModel.lean`. Formalizing it as a *separate* Lean theorem would be almost entirely
redundant with what `tiltedDigitWeight`/`Mfun`/`geometric_persistence_upper_bound` already prove
(those definitions **are** the discrete-time analogue of this martingale's increments, just not
packaged with explicit martingale/optional-stopping vocabulary).

**Estimated difficulty**: **B (follows immediately from existing lemmas)** if attempted — but see
below.

**Worth formalizing now?** No — this is the one deferred item that isn't really "too hard," it's
"not worth doing," since it would be a restatement of existing content in fancier probabilistic
vocabulary with zero new mathematical or Lean-formal content. Explicitly **not recommended**, ever,
unless a future direction specifically needs the martingale *packaging* (e.g. to invoke a generic
Mathlib optional-stopping theorem rather than the repository's own bespoke Chernoff argument) —
no such need has been identified.

---

## Summary table

| Item | Difficulty | Depends on | Recommended now? |
|---|---|---|---|
| D1: general-`q` one-step count | D | — | Dedicated future round |
| D2: `k`-step extension | C | D1 | After D1 |
| D3: Doob h-transform (Lean) | D | D1, D2 | No — explicitly deferred per round instructions |
| D4: conditioned correlations (Lean) | D | D3 | No — lowest priority |
| D5: first-crossing law (Lean) | — (not novel) | D3 | No — fold into D3 if ever built, not separate |
| D6: exponential martingale (Lean) | B | none | No — purely redundant, not worth it regardless of ease |
