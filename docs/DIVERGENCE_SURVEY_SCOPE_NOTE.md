# Scope corrections to the divergence-exclusion survey

*Four logical distinctions that `docs/DIVERGENCE_EXCLUSION_SURVEY.md` (commit `76afebb`) got
wrong. Each is re-derived here against Curry's source text (audited in
`docs/CURRY_INDEPENDENT_AUDIT.md`). Branch `curry-audit-and-scope-correction`.*

The survey's **verdict** — no new exclusion mechanism found — is unaffected. What is corrected is
the characterisation of what remains open, and in one case the correction makes the live frontier
*better* than the survey described.

---

## A. Divergence does not imply linear negative drift

**What the survey said.** "Divergent orbits have `R_n ≍ −δn`", and therefore "the gap is `log n`
vs `n` — a functional-form gap, not a constant."

**Wrong.** What is established, under reciprocal summability and the exact orbit identity
`y_n = y_0 2^{g_n}Q_n` with `Q_n ↗ Q_∞ < ∞`, is exactly

```
y_n → ∞        and        g_n = −R_n → +∞ ,     i.e.     R_n → −∞ .
```

Nothing more. Curry's Corollary 4.3 adds only a **limsup**: for every `B < 1/β* = 1.0358567…` and
every `K`, `g_n > B log₂ n + K` infinitely often, i.e.

```
limsup_n  g_n / log₂ n  ≥  1/β* .
```

That is not a slope, not a limit, and gives no asymptotic valuation mean. No theorem in the
repository or in Curry's note supplies one.

**The regimes actually left open.** Writing `y_n ≍ n^c` gives `g_n ≍ c log₂ n`; summability needs
`c > 1` and Corollary 4.3 needs `c ≥ 1/β*`. So:

| regime | `g_n` | status |
|---|---|---|
| `y_n = O(n)` | `g_n ≤ log₂n + O(1)` | **excluded** (Thm 4.1) |
| `y_n ≍ n^c`, `1 < c < 1/β*` | `g_n ≍ c log₂n` | **excluded** (Cor 4.3) |
| `y_n ≍ n^c`, `c ≥ 1/β* = 1.0359` | `g_n ≍ c log₂n` — **logarithmic** | **open** |
| `y_n ≍ 2^{n^θ}`, `0<θ<1` | `g_n ≍ n^θ` — sublinear | **open** |
| `y_n ≍ 2^{δn}` | `g_n ≍ δn` — linear | **open** |

So **sublinear and even logarithmic drift regimes remain open**, and the survey's "log n vs n"
framing picked one end of an open range and presented it as the truth. The logarithmic-versus-linear
comparison in survey §5 illustrates a limitation of *one particular packing estimate*; it does not
classify divergent orbits.

---

## B. Summability is not eventual superlinear growth

**What `Σ_n 1/y_n < ∞` gives, exactly:**

* **`y_n = O(n)` is impossible.** If `y_n ≤ Cn` then `Σ1/y_n ≥ C^{-1}Σ1/n = ∞`.
* **`y_n/n` is unbounded**, i.e. `limsup y_n/n = ∞` — immediately from the previous line.

**What it does not give: `y_n/n → ∞`.** Counterexample (as an implication between sequences):
`m_n = n` for `n ∈ {2^k}` and `m_n = 2^n` otherwise. Then `Σ1/m_n = Σ_k 2^{-k} + Σ 2^{-n} < ∞`
while `m_n/n = 1` at every `n = 2^k`, so `liminf m_n/n = 1`. The survey's phrase "Curry already
forces `m_n` to grow faster than `n¹`" is therefore too strong; the correct statement is the
`O(n)`-impossibility plus the unbounded `limsup`.

**Improved constants do exclude more.** The survey said "improving the constant enlarges no
exclusion". That is wrong, and Curry's note is itself the counterexample: Theorem 4.1 reaches
`B ≤ 1` and **Corollary 4.3 reaches `B < 1/β* = 1.0358567…`**, past the harmonic barrier `B = 1`
and past the repository's earlier `8/9`. Each improvement removes a genuinely new family of
hypothetical behaviours (polynomial growth `y_n ≍ n^c` with `c` in the newly covered range).

What remains true, and is the distinction that must be kept: **removing additional hypothetical
behaviours is not excluding divergence.** No finite `B` touches super-polynomial growth, where
`g_n ≤ B log₂n + K` fails vacuously. So pushing `1/β*` upward is real progress on the open range
of §A and simultaneously can never, by itself, finish the problem.

The survey's claim that the repository's `8/9` result is superseded *for this application* stands:
Theorem 4.1 already covers `B ≤ 1 > 8/9` from summability alone.

---

## C. The survey does not rule out future counting arguments

**What the survey said.** The missing mechanism "must **not** route through value-counting".

**Unsupported as a universal claim.** What the audit supports is the narrower statement:

> The particular counting mechanisms audited do not close the gap — the repository's packing engine
> (`BoundedDriftCore.state_bound`, which caps at `O(log n)` drift floors, survey §5) and Curry's
> windowed parity-class pigeonhole (which caps at `β*`, by his own §5).

A future argument combining counting with **additional residue restrictions** remains entirely
possible, and Curry says as much: improving `1/β*` needs "either deeper iteration than
`N ≈ log₂X` inside the window argument, which breaks Lemma 2.1's modulus bookkeeping, or an input
beyond parity counting."

**Which information the existing estimates discard.** Naming it precisely is the useful part:

* **Curry's Theorem 2.3** holds for *any* collision-free set `A`. It never uses that `A` is a single
  trajectory beyond collision-freeness, and it classifies residues mod `2^N` **only by the weight
  `m_N` of the parity prefix** — the entropy bound `Σ_{i≥γN}C(N,i)` counts classes by their number
  of ones and discards which classes they are.
* **The repository's packing engine** discards residues entirely: it uses only distinctness of orbit
  values (pigeonhole `max ≥ N`).
* **What neither uses:** the exact realizer congruence `3^N m₀ + q_N ≡ 2^{S_N} (mod 2^{S_N+1})`,
  which pins the seed to a *single* residue class — the sharpest arithmetic fact the repository has,
  and the one both counting arguments throw away.

So the honest open problem is not "avoid counting" but "**combine counting with the residue
information both current arguments discard**".

---

## D. The restricted target is equivalent, not strictly weaker

**What the survey said.** Target 4 ("exclusion restricted to words satisfying the necessary
divergent-orbit conditions") is "strictly weaker — the only genuinely easier target".

**Wrong.** Under the background inputs, it is **equivalent** to the universal target.

Let (U) be *no positive odd seed has an infinite zero-confined word*, and (R) the same restricted to
words that additionally satisfy any list `P` of properties possessed by every divergent orbit's
restarted word.

* **(U) ⟹ (R):** trivial, (R) quantifies over fewer words.
* **(R) ⟹ (U):** let `m₀` be odd with `Confined 0 (orbWord m₀) N` for all `N`. Then its orbit is
  **injective** — a repeat makes the word eventually periodic and forces positive drift
  (`noninjective_orbit_not_upper_confined` at `c = 0`) — hence **divergent**
  (`injective_iff_divergent`), hence by Curry it satisfies reciprocal summability and every
  consequence in `P`. So `m₀` is already in the restricted class, and (R) excludes it.

Both steps are now formalized: `CurryInterface.injective_of_zero_confined`,
`CurryInterface.divergent_of_zero_confined`, `CurryInterface.injective_iff_divergent`.

**Background assumptions made visible.** (R) ⟹ (U) uses: the elementary orbit classification
(injective or eventually periodic) and the positive-period-drift lemma — both formalized and
unconditional — plus, for any `P` that mentions summability or its consequences, **Curry's
Proposition 3.1**, which is external and unformalized.

**Why this matters, stated correctly.** Restricting the word class by properties all divergence
candidates have does **not** weaken the theorem to be proved. What it does is make more hypotheses
available *inside* a proof. That can make a proof easier without making the statement weaker, and
the two must not be confused. A statement should be called "weaker" only when it is implied by, and
does not imply, the original.

---

## D'. A qualification on the deficit result

The deficit computation (audit §9) rules out the proposed inference **from the upper cap alone**:
`leastRealizer(d,N) < 2^{S_N+1}` and `Δ_N = ⌊Nα⌋ − S_N` mean a larger deficit lowers the cap, while
unboundedness needs a lower bound.

It does **not** rule out using the deficit *together with additional residue information*. The
all-ones word illustrates exactly this: it has maximal deficit and yet its least realizer is
`2^{N+1} − 1`, exponentially large. So at that extreme the cap is not what decides the size, and a
finer invariant does. The deficit is dropped as a *standalone mechanism*, not as a possible
*ingredient*.

## E. What the survey got right, and still stands

* The verdict: no new exclusion mechanism was found.
* The packing-engine cap: `BoundedDriftCore.state_bound` converts a drift floor `G` into a ceiling
  `2^G m₀ N^{log₂(3/2)}`, against an injectivity floor of `N`, so a contradiction needs
  `G < 0.4150375·log₂N − O(1)`. That derivation is correct **as a statement about that estimate**.
* The `8/9` logarithmic-floor result is superseded for the divergence application (§B).
* Targets 1, 2, 3 (drift exit / zero-confined exclusion / unbounded least realizers) are one
  statement in three vocabularies.
* Link (5) was a genuine gap and is closed; links (1) and (6) remain as recorded.

## F. Corrected files

| File | Change |
|---|---|
| `docs/DIVERGENCE_EXCLUSION_SURVEY.md` | §5 and §9 rewritten; scope banner added pointing here |
| `EOC/OscillatingEscape.lean` | module docstring said "Curry ⟹ bounded carry ⟹ **linear** negative drift" — corrected to `R_n → −∞` |
| memory `eoc-divergence-exclusion-cap.md` | linear-drift claim, "log n vs n", "improving constants excludes nothing", "must not use value-counting", "strictly weaker" — all corrected |
