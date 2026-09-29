# Formalization targets for the closed EOC routes

**Documentation only. No Lean is implemented in this note, and no new mathematical claim is
made.** It records which parts of three audited route-closures would be worth machine-checking,
and which would not.

Consolidated 2026-09-29. The closures themselves are recorded in `eoc-divergence`:
[`notes/CLOSED_POINTWISE_ROUTES_2026-09-29.md`](https://github.com/innerlightr-wq/eoc-divergence/blob/main/notes/CLOSED_POINTWISE_ROUTES_2026-09-29.md).
The earlier, more detailed plan for target A is
[`docs/PERIODICITY_HANDOFF_FORMALIZATION.md`](PERIODICITY_HANDOFF_FORMALIZATION.md); this file
supersedes it as the index and does not repeat its derivation.

Classification used: **ALREADY FORMALIZED** · **SMALL MISSING LEMMA** · **DOCUMENTATION ONLY** ·
**NOT A SEPARATOR** (the last is orthogonal — it says what the statement is *for*, never that it
is false).

---

## A. Initial-square / surplus cap

> `initial_square_bound (L n : ℕ) (hn : 0 < n) (hsq : ∀ j < L, U^[j] n % 2 = U^[L + j] n % 2)`
> `(hne : U^[L] n ≠ n) : 4 ^ L ≤ 3 ^ L * (n + 1)`

An initial square of half-length `L` in the parity word of a positive integer forces
`(4/3)^L ≤ n+1`. This is why the periodic-approximation handoff is circular: the implication it
would need is equivalent to `(DE)`.

| aspect | status |
|---|---|
| `modEq_of_parity_prefix`, `two_mul_U_of_even/odd`, `U_iter_shift`, `bridge`, `aggregate_identity` | **ALREADY FORMALIZED** (in `eoc-divergence`, `Divergence/RawMap.lean` and `Basic.lean`) |
| `2^N * (U^[N] n + 1) ≤ 3^N * (n + 1)` — the exact-`ℕ` growth bound | **SMALL MISSING LEMMA**. Must be *added*, not reused: the existing `E_lt`/`contraction` prove `2^N·U^[N] n < 3^m·(n + 2^N)`, which carries an additive `3^m` and is not strong enough |
| the `ℕ`-subtraction step ("a nonzero difference divisible by `2^L` is at least `2^L`") | **SMALL MISSING LEMMA** (bookkeeping; `Nat.le_of_dvd` plus a `max` case split, or a detour through `ℤ`) |
| the target itself | **SMALL MISSING LEMMA** once the two above are in place |
| purpose | **NOT A SEPARATOR** — it records a closure |

**Home:** `eoc-divergence`, a new `Divergence/Repetition.lean` importing `Divergence.RawMap`
only — not this repository, since every dependency lives there. Estimated 1–2 focused days
(*an estimate, not a measurement*). Full detail:
[`docs/PERIODICITY_HANDOFF_FORMALIZATION.md`](PERIODICITY_HANDOFF_FORMALIZATION.md).

## B. Finite-height / realizer-deficit reduction

> For `N ≥ B − 1`: an odd `m < 2^B` realizes a confined word iff it **is** that word's least
> realizer, i.e. `#{odd m < 2^B : N-confined} = #{w confined : δ(w) > S(w)+1−B}` with
> `δ(w) = (S+1) − log₂ r(w)`.

This identity is what makes every `δ`-based claim a restatement of Terras–Everett plus the
aggregate identity — the reason the realizer-deficit route is closed as a separator.

| aspect | status |
|---|---|
| `realizerCongruence`, `leastRealizer`, `leastRealizer_lt`, `leastRealizer_unique`, `leastRealizer_odd`, `leastRealizer_modEq`, `residue_pinning`, `coarseAnchor_unique` (`EOC/Realizer.lean`) | **ALREADY FORMALIZED** |
| `q_eq_C` — the carry's recurrence and closed forms agree (`EOC/Carry.lean`) | **ALREADY FORMALIZED** |
| the bijection form, stated without logarithms: `∀ m, Odd m → m < 2^B → (Realizes d N m ↔ leastRealizer d N = m ∧ leastRealizer d N < 2^B)` | **SMALL MISSING LEMMA**; the work is the side condition `B ≤ N+1 ≤ S+1` (from `∀ i < N, 1 ≤ d i`, hence `S ≥ N`), which must hold for *every* confined word including the all-ones word — the off-by-one that `eoc-divergence/audits/pointwise_discovery/PHASE0.md` caught and corrected (the condition is `n ≥ B−1`, **not** `A[n]+1 ≥ B`), and which should be reproduced as an explicit hypothesis |
| the counting identity `= 2^{B−1} p_N(0)` over `ℚ` | **SMALL MISSING LEMMA**, heavier: needs the confined-word set as a `Finset` with rational weights; would connect to the already-formalized `Occupation.confined_mass_rate` |
| `δ` itself as a Lean definition | **DOCUMENTATION ONLY** — deliberately not worth adding: it is `S+1 − log₂ r` of an already formalized integer, so it would introduce real analysis and a second name for existing data |
| purpose | **NOT A SEPARATOR** |

**Home:** this repository, e.g. `EOC/FiniteHeight.lean` importing `EOC.Realizer` and `EOC.Carry`.
Estimated 3–6 h for the bijection form, 1–2 days for the counting identity (*estimates*). Note
that a new module must be added to the root `EOC.lean` or CI will not build it.

## C. Carry-integral identities

> `C_{n+1} = 3C_n + 2^{S_n}` (definition); `C_n = Σ_{j<n} 3^{n−1−j} 2^{S_j}`;
> `C_n/3^n = (1/3) Σ_{j<n} 2^{−R_j}`; `U_n = 3 m₀ (Q_n − 1)`; `ρ_n m_n = m₀ Q_n`;
> `3^n − 2^n ≤ C_n ≤ 3^{n−1} Σ_{j<n} 2^{−{jα}}`.

| aspect | status |
|---|---|
| the recurrence, and the closed sum form | **ALREADY FORMALIZED** — `Divergence/Basic.lean` `C`, `C_succ` (by `rfl`); `EOC/Carry.lean` `q_eq_C` |
| `aggregate_identity`, `rho`, `Q`, `rho_mul_orbit`, `Q_le_exp`, `rho_tendsto_zero`, `summable_inv_orbit` | **ALREADY FORMALIZED** (`eoc-divergence`) |
| `C_n/3^n = (1/3)Σ 2^{−R_j}` and `U_n = 3m₀(Q_n−1)` | **DOCUMENTATION ONLY** — one-line rearrangements of the two rows above; formalizing them would add real-valued restatements of existing `ℕ`/`ℝ` theorems |
| `3^n ≤ C m n + 2^n` (the sharpened lower bound) | **SMALL MISSING LEMMA** — induction on `C_succ` using `2^{S_n} ≥ 2^n`; needs `S m n ≥ n` for odd `m`, a two-line induction not currently stated. ≈ 1–2 h |
| `#{j < n : 3^j ≤ 2^{S_j+c}} · 3^n ≤ 2^c · 3 · C m n` (the occupation bound, pure `ℕ`) | **SMALL MISSING LEMMA** — ≈ 4–8 h, dominated by the `ℕ`-division bookkeeping |
| the sharp upper envelope with the constant `1/(2 ln 2)` | **DOCUMENTATION ONLY** — needs effective equidistribution of `{jα}` for `α = log₂3`, i.e. real analytic number theory, for a `0.47`-bit improvement |
| purpose | **NOT A SEPARATOR** |

**Home:** `eoc-divergence`, a new `Divergence/CarryBounds.lean` importing `Divergence.Basic`.

## D. Which closures would actually be useful to machine-check

In priority order, with the reason:

1. **B, the bijection form** (≈ 3–6 h, this repository). Cheapest, purely `ℕ`, and it is the
   statement that makes the entire realizer-deficit coordinate a restatement. It also pins the
   `n ≥ B−1` side condition that was got wrong once already.
2. **A, `initial_square_bound`** (≈ 1–2 days, `eoc-divergence`). Converts the periodicity
   route-closure from "verified on 1 862 checkpoints and 400 random seeds" to machine-checked
   for all `n` and all `L`, so the route is never re-litigated.
3. **C, the two `ℕ` carry bounds** (≈ half a day). Records the exact strength of the
   amortization channel.

**What would NOT be useful:** any `δ`-envelope (they are false, refuted by the `3x−1` control,
or circular); the amortization identities as such (rearrangements of formalized theorems); and
anything asymptotic in `α`'s equidistribution.

## Scope

None of these targets bears on the Collatz conjecture, on `(DE)`, on `(PosPC)`, or on this
repository's open arithmetic hypothesis `PowerOfTwoDangerousWindowSparsity`
([`docs/ARITHMETIC_FRONTIER.md`](ARITHMETIC_FRONTIER.md)), which is unaffected. They record
closures; they do not open anything. Effort figures throughout are **estimates**, not
measurements.
