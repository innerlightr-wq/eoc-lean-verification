# Formalization plan — the repetition-surplus cap

**Planning note only. No theorem is implemented in this update, and no Lean file is changed.**

Recorded 2026-09-29 from the EOC × Periodicity handoff audit. The route-closure itself is
documented in `eoc-divergence`:
[`notes/PERIODICITY_HANDOFF_ROUTE_CLOSED.md`](https://github.com/innerlightr-wq/eoc-divergence/blob/main/notes/PERIODICITY_HANDOFF_ROUTE_CLOSED.md).

**Novelty discipline.** The qualitative closure of the periodic-approximation route was already
on record (EOC Revision 7 §5.3 / Observation 5.9, and the bridge repository's `LADDER.md`
closing section). The audit supplies the exact identity, the quantified obstruction, and
certified verification — not the original qualitative observation. What follows is a plan to
make one elementary consequence machine-checked.

---

## Target lemma

```lean
/-- An initial square of half-length `L` in the parity word of `n` forces `(4/3)^L ≤ n+1`. -/
theorem initial_square_bound (L n : ℕ) (hn : 0 < n)
    (hsq : ∀ j < L, U^[j] n % 2 = U^[L + j] n % 2)
    (hne : U^[L] n ≠ n) :
    4 ^ L ≤ 3 ^ L * (n + 1)
```

`U` is the raw (standard) `3x+1` step `U(x) = x/2` for even `x`, `(3x+1)/2` for odd `x` — the
map already defined in `eoc-divergence`'s `Divergence/RawMap.lean`. The hypothesis `hsq` says
the length-`L` parity prefix of `n` equals that of `U^[L] n`, i.e. the parity word of `n` begins
in a square of half-length `L`.

The `ℕ`-form `4^L ≤ 3^L (n+1)` is preferred over its real-valued reading
`L ≤ log₂(n+1)/(2 − log₂ 3) = 2.4094 log₂(n+1)`: no casts, no `rpow`, and it is what a caller
actually wants.

## Why this cap formally blocks the surplus-based handoff

The Periodicity Bridge's most general sufficient condition is *"arbitrarily long initial squares
suffice, unconditionally"* — a word with initial squares of unbounded half-length has
`Φ(s) ∉ ℚ`. A divergent `3x+1` orbit has `Φ(s) = m₀ ∈ ℚ`, so the bridge would exclude it if its
parity word had long initial squares.

`initial_square_bound` says no positive integer's parity word has an initial square of
half-length beyond `2.4094 log₂(n+1)` — divergent or not, confined or not. Consequently the
implication the handoff needs,

> "zero confinement ⟹ initial squares of unbounded half-length",

holds **iff** no zero-confined positive odd integer exists, i.e. iff `(DE)` holds. The
intermediate step is the conclusion restated: the route is circular, and
`initial_square_bound` is the exact statement that makes that formal.

The same cap is what pins the bridge's surplus on the confined sector: with
`W = s[0:ℓ]`, `F(W) = |2^ℓ − 3^k| + c_W`, one has (audit Theorem H1, verified exactly at 1 862
confined checkpoints, 0 failures)

```
    lcp(s, W^∞) = ℓ + v₂(m₀ − T^ℓ m₀),
    S(W)        = log₂ h_eff − log₂ oddpart(T^ℓ m₀ − m₀)  ≤  log₂ m₀,
```

which is this programme's aggregate identity plus "a nonzero integer is at least `2^{v₂}`".
Formalizing `initial_square_bound` captures the load-bearing half of that in one short lemma.

## Dependencies already available

All in `eoc-divergence`'s `Divergence/RawMap.lean` (self-contained, Mathlib only):

| needed | name | status |
|---|---|---|
| the raw map and its two branches | `U`, `U_of_even`, `U_of_odd` | proved |
| doubled forms, the growth step's source | `two_mul_U_of_even : 2 * U n = n`, `two_mul_U_of_odd : 2 * U n = 3 * n + 1` | proved |
| **equal parity prefixes ⟹ congruence** | `modEq_of_parity_prefix (N) : (∀ j < N, U^[j] n % 2 = U^[j] n' % 2) → n ≡ n' [MOD 2^N]` | proved, no bound on `n, n'` |
| its `Finset` form | `modEq_of_parityPrefix_eq` | proved |
| shift invariance (the converse direction, if wanted) | `U_iter_shift`, `U_iter_shift_endpoint` | proved |
| parity-prefix bookkeeping | `parityPrefix`, `oddCount`, `oddCount_eq_card` | proved |
| accelerated ↔ standard link | `bridge : orbit M n = U^[S M n] M` | proved |
| aggregate identity (accelerated) | `Divergence.aggregate_identity` (Lemma 2.4) | proved |

Mathlib: `Nat.le_of_dvd`, `Nat.ModEq`, `Function.iterate_add_apply`, `pow_le_pow_left`.

## Missing ingredients

Three, all elementary:

1. **The archimedean growth bound in exact `ℕ` form**
   ```lean
   theorem two_pow_mul_succ_le (N n : ℕ) : 2 ^ N * (U^[N] n + 1) ≤ 3 ^ N * (n + 1)
   ```
   Base case trivial; step from `2 * U n ≤ 3 * n + 1` (immediate from `two_mul_U_of_even` /
   `two_mul_U_of_odd`), hence `2 * (U n + 1) ≤ 3 * (n + 1)`.

   **This must be added, not reused.** `RawMap.lean`'s existing `E_lt` / `contraction` prove a
   *different* estimate, `2^N · U^[N] n < 3^m · (n + 2^N)`, which carries an additive `3^m` and
   is not strong enough for the target.

2. **Natural-number subtraction handling** in the step "a nonzero difference divisible by `2^L`
   is at least `2^L`, so `2^L ≤ max n (U^[L] n)`". `Nat.le_of_dvd` gives the divisibility half;
   the bookkeeping is easiest either by a `max`/`min` case split or by moving that step to `ℤ`
   and casting back.

3. **The `⟸` half of the dictionary**, only if the `iff` form is wanted:
   `n ≡ n' [MOD 2^N] → ∀ j < N, U^[j] n % 2 = U^[j] n' % 2`, from `U_iter_shift` (the
   `2^(N−j)` factor is even for `j < N`). Not needed by `initial_square_bound` itself, which
   uses only the already-proved forward direction.

## Proof outline for the target

1. `U^[L + j] n = U^[j] (U^[L] n)` by `Function.iterate_add_apply`; so `hsq` says `n` and
   `U^[L] n` have equal length-`L` parity prefixes.
2. `modEq_of_parity_prefix L n (U^[L] n)` gives `n ≡ U^[L] n [MOD 2^L]`.
3. With `hne`, the difference is nonzero and divisible by `2^L`, so `2^L ≤ max n (U^[L] n)`.
4. `two_pow_mul_succ_le` gives `2^L * (U^[L] n + 1) ≤ 3^L * (n + 1)`; with `2^L ≤ 3^L` the same
   bound covers `2^L * (n + 1)`.
5. Combining, `2^L * 2^L ≤ 3^L * (n + 1)`, i.e. `4^L ≤ 3^L * (n + 1)`.

## Likely module location

This belongs in **`eoc-divergence`**, not here: every dependency is in that repository's
`Divergence/RawMap.lean`, and this repository's `EOC` library targets the residue /
arithmetic-placement axis. Suggested home there: a new `Divergence/Repetition.lean` importing
`Divergence.RawMap` only.

Note for whoever implements it: a new module must be added to the root `Divergence.lean` to be
built, since CI only reaches modules imported from the root. It need not be imported by
`Divergence/Main.lean`, so `divergent_iff_zeroConfined`'s axiom audit is unaffected.

## Estimated effort

**Estimate, not a measurement.** L1 (`⟸` half) 2–4 h; the growth bound 1–2 h; the target lemma
4–8 h, dominated by step 3's `ℕ`-subtraction bookkeeping; a one-line restatement of the surplus
identity from `aggregate_identity` under 1 h. **Total: 1–2 focused days.** No Mathlib gaps are
expected.

## Scope

No theorem implementation in this update. Nothing here bears on the Collatz conjecture, on EOC,
or on this repository's open arithmetic hypothesis
(`PowerOfTwoDangerousWindowSparsity`, `docs/ARITHMETIC_FRONTIER.md`), which is unaffected.
