# Dynamic deficit-feedback audit

*Does combining eventual realizer stabilization with the dynamic feedback
`Δ_N → m_N → d_N = ν₂(3m_N+1) → Δ_{N+1}` produce any genuinely new obstruction to a
Curry-normalized Type-II divergent orbit?*

**Verdict reached at Gate 0: no. The feedback system is an exact change of coordinates for a
Type-II divergent orbit — and the repository already contains the Lean proof that says so.** The
route is documented and closed here rather than developed.

---

## A. Starting commit

Branch `zcre-realizer-growth`, tip **`9435bca06456087648492c5620e2335dda1f3100`**
("Add computational cross-checks for the realizer-growth equivalence").

Ancestry verified before starting: `70a4d4a`, `fe9a6eb`, `9435bca` (ZCRE realizer growth);
`2c6e790`, `9cb8540`, `5db34a5` (Curry foundation). All six present.

Work done on a new branch **`dynamic-deficit-feedback`** cut from that tip, in a separate git
worktree so that the 53 uncommitted files of in-progress work on
`research-sparse-visits-2026-09-16` were left untouched. `main` not modified.

## B. Frozen assumptions

**Unconditional** (true for every accelerated orbit of an odd `m₀`, no hypothesis):

| | fact | where |
|---|---|---|
| U1 | `m_{N+1} = (3m_N+1)/2^{d_N}`, `d_N = ν₂(3m_N+1)`, `d_N ≥ 1` | definition of the accelerated map |
| U2 | `S_N = Σ_{j<N} d_j`, `R_N = S_N − αN`, `α = log₂3` | repo conventions |
| U3 | `m_N = m₀ · Q_N · 2^{−R_N}`, `Q_N = Π_{j<N}(1+1/(3m_j))` | Eliahou–Rozier; `orbit_mul_two_rpow_R`, `two_rpow_R_eq` |
| U4 | `Δ_N := ⌊αN⌋ − S_N`; `b_{N+1} := ⌊α(N+1)⌋ − ⌊αN⌋ ∈ {1,2}` | `deficit`, `beatty_gap_mem` |
| U5 | `Δ_{N+1} = Δ_N + b_{N+1} − d_N` | `deficit_succ` |
| U6 | `R_N = −Δ_N − {αN}` | inside `deficit_tendsto_atTop_iff` |

**Type-II conditional** (normalization at the last global drift maximum): `R₀ = 0`, `R_N < 0` for
`N ≥ 1`, hence `S_N ≤ ⌊αN⌋` and `Δ_N ≥ 0` (`zero_corridor_tail`, `deficit_nonneg`).

**Curry conditional**: `ReciprocalSummable M` ⟹ `Q_N → Q_∞ < ∞` (`carryU_tendsto`) and
`R_N → −∞` (`R_tendsto_atBot`), hence `Δ_N → ∞` (`deficit_tendsto_atTop_iff`).

**Asymptotic only**: `m_N ≍ C·2^{Δ_N}`. The bracketing constants are recorded in §C.

## C. Feedback identities

All four verified exactly, symbolically and by exact-arithmetic computation on real orbits
(§L). Written in repo conventions:

```
Δ_N      = ⌊αN⌋ − S_N                                   (U4, definition)
Δ_{N+1}  = Δ_N + b_{N+1} − d_N                          (U5)
R_N      = −Δ_N − {αN}                                  (U6)
m_N      = m₀ Q_N 2^{−R_N} = m₀ Q_N 2^{Δ_N + {αN}}      (U3 + U6)
d_N      = ν₂(3m_N + 1)                                 (U1)
```

**Explicit bracketing under Curry.** `Q_N` is increasing with `Q_N → Q_∞ < ∞`, and
`{αN} ∈ [0,1)`, so for every `N`

```
m₀ · 2^{Δ_N}  ≤  m_N  <  2 m₀ Q_∞ · 2^{Δ_N},
```

i.e. `c₁ = m₀` and `c₂ = 2 m₀ Q_∞`, both unconditional given `Q_N ↑ Q_∞`. The dependence is
entirely on `m₀` and `Q_∞`; no further constant is available, because `{αN}` is equidistributed
and `Q_N` is monotone.

## D. Tautology gate

**Category 1 — exact algebraic equivalence. The feedback system is Type-II divergence rewritten
in `(m_N, Δ_N)` coordinates.**

Each arrow of the proposed loop is a definition or an identity already proved:

| arrow | status |
|---|---|
| `Δ_N → S_N` | definition, and invertible: `S_N = ⌊αN⌋ − Δ_N` |
| `S_N → m_N` | U3, the Eliahou–Rozier identity — unconditional |
| `m_N → d_N` | U1, the definition of the map |
| `d_N → Δ_{N+1}` | U5 — and its Lean proof is literally `unfold deficit; push_cast; ring` |

The decisive point is that **`deficit_succ` already exists in the repository with the docstring
"Pure algebra from the definitions"**. A recurrence whose proof is `ring` transports no
information: it is a restatement of `S_{N+1} = S_N + d_N` after subtracting the Beatty sequence.
The loop therefore reads, in full:

> given the digits so far, the state is determined; given the state, the next digit is
> determined; appending it gives the digits so far, one step on.

That is the orbit. Nothing in the loop is a compatibility condition *between* two independently
specified objects, because `Δ_N` is not independent of the digits — it is a function of them.

The only non-definitional inputs are the Curry hypotheses (`Q_N → Q_∞`, hence `Δ_N → ∞`), which
are the frozen conditional setting and not a product of the feedback formulation.

**Classical confirmation.** This is the Bernstein–Lagarias conjugacy `Φ` on `ℤ₂` with
`Φ ∘ S ∘ Φ⁻¹ = T` (see `docs/LITERATURE_CONTEXT.md` §"The 2-adic realizer formula and the
conjugacy map", already cited in this repository). A conjugacy is by definition a change of
coordinates; the feedback loop is that conjugacy read in the state→word direction. The
repository had the reference before this audit began.

Per the governing brief, the route closes here. Gates 1–8 below are reported at the depth needed
to make the closure checkable, not developed further.

## E. Valuation congruence structure

Exact, elementary, and verified computationally for `k ≤ 8` (§L):

- **`ν₂(3m+1) ≥ k` ⟺ `m ≡ −3⁻¹ (mod 2^k)`** — a *single* residue class mod `2^k`, for odd `m`.
  The class values are `1, 1, 5, 5, 21, 21, 85, 85, …` for `k = 1,…,8`.
- **`ν₂(3m+1) = k` ⟺ `m ≡ −3⁻¹ (mod 2^k)` and `m ≢ −3⁻¹ (mod 2^{k+1})`.**
- **Densities among odd residues mod `2^K` (`K > k`):** `ν₂ = k` has density exactly `2^{−k}`,
  `ν₂ ≥ k` exactly `2^{−(k−1)}`; the mean of `d` over the ensemble is `2` (computed:
  `65535/32768` at `K = 16`).

These are **ensemble facts only**. No inference is drawn that an individual orbit samples them.
The relevant asymmetry — mean digit `2` versus the Beatty slope `α ≈ 1.585` — is the classical
heuristic for why divergence is atypical, not an argument.

**Already in the repository in the form that matters**: `SplitPrefix.dvd_state_diff` proves that
two states with `2^g ∣ 3m+1` are congruent mod `2^g`, which is the relative form of the
single-class statement. No new congruence lemma was added.

## F. Deficit increment structure

From U5 with `b ∈ {1,2}` and `d ≥ 1`, the increment `Δ_{N+1} − Δ_N = b_{N+1} − d_N` is classified
completely:

| increment | requires |
|---|---|
| `+1` | `b = 2` **and** `d = 1` — the only way the deficit grows |
| `0` | `(b,d) = (1,1)` or `(2,2)` |
| `−j`, `j ≥ 1` | `(b,d) = (1, 1+j)` or `(2, 2+j)` |

Hence **`Δ_{N+1} ≤ Δ_N + 1`**: the deficit cannot jump, and `Δ_N → ∞` requires infinitely many
steps carrying Beatty gap `2` *and* digit `1`, each buying one unit. This is the one structural
fact this audit produced that is not an immediate instance of `deficit_succ`, and it is now in
Lean as `deficit_succ_le` (§O).

It is not an obstruction. `d = 1` has ensemble density `1/2` and `b = 2` occurs with density
`α − 1 ≈ 0.585`; nothing prevents their co-occurrence infinitely often.

## G. State-size versus valuation audit

Every proposed deterministic inequality, with status:

| # | proposed | status |
|---|---|---|
| G1 | `d_N ≤ log₂(3m_N+1)` | **TRUE but vacuous** — immediate from `2^{d_N} ∣ 3m_N+1`. See below. |
| G2 | `d_N ≤ f(Δ_N)` strong enough to bite | **SUBSUMED** — see below |
| G3 | large `Δ_N` restricts the *next* digit beyond the corridor | **FALSE** |
| G4 | large `Δ_N` forces a small-seed or strong-congruence structure | **NOT ESTABLISHED**; reduces to G5 |
| G5 | a congruence mod `2^K` with `K ≫ Δ_N` is incompatible with `m_N ≍ 2^{Δ_N}` | **FALSE** — see §H |

**G1/G2 in detail — the sharpest negative result of this audit.** The state-size ceiling is
*never* tighter than the zero-corridor constraint that is already assumed. The corridor
`Δ_{N+1} ≥ 0` gives directly

```
d_N ≤ Δ_N + b_{N+1}   ≤ Δ_N + 2.
```

The state-size ceiling gives `d_N ≤ log₂(3m_N+1)`, and by §C `m_N ≥ m₀ 2^{Δ_N}`, so

```
log₂(3m_N + 1) > log₂(3 m₀ 2^{Δ_N}) = Δ_N + α + log₂ m₀ ≥ Δ_N + 1.58 + log₂ m₀ .
```

For any `m₀ ≥ 2` — in particular for any Type-II divergent seed — this exceeds `Δ_N + 2`, so the
state-size ceiling is strictly weaker. **Knowing the state is huge tells you less about the next
digit than the corridor hypothesis already does.** Verified computationally: the state ceiling
was tighter in `0` of `2000` steps across five seeds (§L).

This kills the naive intuition motivating the round. Largeness of `m_N` is not a constraint on
`d_N`; it is the *same* information as `Δ_N`, one exponential away.

## H. Recovery-cost audit

Fix `Δ_N = G` and suppose `Δ_{N+L} ≤ G − H`. By telescoping U5,

```
Σ_{j=N}^{N+L−1} d_j  =  G − Δ_{N+L} + Σ_{j=N}^{N+L−1} b_{j+1}  ≥  H + (⌊α(N+L)⌋ − ⌊αN⌋).
```

So recovering `H` units over `L` steps costs exactly `H` digits above the Beatty budget — an
identity, not a constraint.

Does the corresponding valuation block force a strong residue condition on `m_N`? Yes, and it is
harmless. Prescribing `d_N, …, d_{N+L−1}` pins `m_N` in one residue class modulo `2^{K}` with
`K = Σd_j + O(1)` (this is the realizer congruence, `leastRealizer_eq_mod_of_realizes`). Combined
with the corridor, `K ≤ G + Σb ≤ G + 2L`. Meanwhile `m_N ≍ 2^{G}`. So the modulus may exceed the
state, but by at most a factor `4^L`.

**That is not a contradiction.** A residue class mod `2^K` contains integers of every size above
`2^K`, and containing exactly one integer below `2^K` is not an obstruction — it just means the
block *determines* `m_N`, which is the conjugacy again. Any useful statement here would have to
exploit more than size, and the audit found nothing that does. This is genuinely weaker than the
existing periodic/realizer recovery analysis, which at least carries an explicit modulus.

## I. Monotone-escape audit

Can `Δ_N → ∞` proceed with few or no recoveries? **Yes, as far as the feedback system is
concerned.** The system imposes only `Δ_{N+1} = Δ_N + b − d` with `d ≥ 1`, `b ∈ {1,2}`; the word
`d = 1` repeated on every step with `b = 2` gives `Δ` increasing by one per such step
indefinitely. Nothing in the feedback loop forbids it.

What forbids it, if anything, is the *arithmetic* realizability of that word — which is exactly
the ZCRE question resolved in the previous round, not a new one. The previous Curry audit
already indicated recovery-free escape is consistent with the symbolic constraints; this audit
confirms the feedback formulation adds no further symbolic restriction.

## J. Realizer-stabilization interaction

Testing the five directions in the brief against `r_N = m₀` eventually (previous round):

1. *Fixed prefix realizer + growing modulus ⟹ useful congruence on `m_N`?* **No.** `r_N = m₀` says
   `m₀ ≡ m₀ (mod 2^{S_N+1})` once `2^{S_N+1} > m₀` — a tautology. It constrains the *seed*, not
   the tail state.
2. *Does `2^{S_N+1} ≫ m₀` add anything dynamically?* **No.** It says the prefix determines the
   seed exactly, which is the conjugacy being injective. Already known.
3. *Two-scale contradiction from suffix realizers?* **No.** The suffix state `m_N` is itself a
   realizer of the suffix word; `m_N ≍ 2^{Δ_N}` grows while `m₀` is fixed. Two different words
   having realizers of different sizes is not a contradiction — it is the generic situation.
4. *Can the seed stay fixed while suffix states grow like `2^{Δ_N}`?* **Yes, necessarily.** This
   is U3: `m_N = m₀ Q_N 2^{Δ_N+{αN}}` with `m₀` fixed. The growth is a *consequence* of the fixed
   seed plus the digits, not in tension with it.
5. *Least-realizer stabilization versus injectivity?* **No new interaction.** Both are aspects of
   Bernstein–Lagarias conjugacy injectivity.

Every statement reduced immediately to the exact recurrence or the existing affine-cylinder
identities. **This route is closed.**

## K. Minimal-seed variant

Not invoked. Gate 5 is conditional on there being leverage at Gates 3–4, and there is none. For
the record: `m_N ≥ m₀` would follow from minimality, but §C already gives the stronger
`m_N ≥ m₀ 2^{Δ_N}` unconditionally, so minimality supplies no independent inequality here — the
same redundancy earlier audits found (minimality recreating Chain B).

## L. Computational findings

Script: `scratch/dynamic_deficit_feedback_2026-09-21/feedback_audit.py`; output in `output.txt`.
Exact integer and `Fraction` arithmetic throughout; `⌊Nα⌋` computed as `(3**N).bit_length()-1`,
never by floating point. Finite computation is used **only** to falsify and calibrate.

| test | parameters | result |
|---|---|---|
| U3, U4, U5 identities on real orbits | `m₀ ∈ {7, 27, 703, 10087}`, 60 steps each | **PASS**, exact |
| `ν₂(3m+1) ≥ k` is one class `= −3⁻¹ mod 2^k` | `k ≤ 8` | **confirmed**, classes `1,1,5,5,21,21,85,85` |
| density of `ν₂ = k` | odd residues mod `2^16` | **exactly `2^{−k}`**; mean `65535/32768` |
| **is the state ceiling ever tighter than the corridor?** | `m₀ ∈ {7,27,703,10087,106239}`, 400 steps each | **0 of 2000** — never |
| `Δ` increment classification | `m₀ ∈ {27,703,10087}`, 400 steps | increments `≤ +1` always; every `+1` had `b=2, d=1` |

**Limitations.** These are convergent orbits; no finite computation can exhibit Type-II
behaviour, and none of the above is offered as evidence about divergent orbits. The identity
checks are the point: they confirm the algebra is what §C says it is.

## M. Literature classification

No broad search was run — correctly, since nothing here is claimed as new. The one reference
that bears directly on the tautology gate was already in the repository:

| source | classification |
|---|---|
| **Bernstein–Lagarias [BL96]** — conjugacy `Φ` on `ℤ₂`, `Φ∘S∘Φ⁻¹ = T` | **exact theorem, decisive here**: the feedback loop *is* this conjugacy in coordinates |
| **Bernstein [Be94]** — noniterative 2-adic realizer formula | exact theorem; the state/word correspondence in closed form |
| **Terras [Te76] / Everett [Ev77]** — accelerated map, parity-prefix facts | background; source of the `ν₂` ensemble statistics |
| **Eliahou / Rozier** — the `orbit · 2^{R}` identity, critical ones-ratio | exact theorem, already formalized as U3 |

Nothing in §E–§I is claimed to be new; §E is classical, §F is a two-line corollary of repo
lemmas, §G is a negative result about a proposal rather than a theorem about Collatz.

## N. New theorem candidate

**NONE — feedback is currently only an exact reformulation.**

The audit did produce one small structural fact worth keeping, but it is a corollary of existing
repository lemmas rather than a new obstruction: `Δ_{N+1} ≤ Δ_N + 1`, with growth possible only
on steps carrying Beatty gap `2` and digit `1` (§F). It restricts nothing that was not already
restricted; it makes the shape of deficit growth explicit.

## O. Lean formalization

Checked first, per policy: three of the four candidate formalizations **already existed** and were
not duplicated.

| candidate | status |
|---|---|
| exact deficit recursion | **exists** — `CurryFoundation.deficit_succ` |
| `R_N = −Δ_N − {αN}` | **exists** — inside `CurryFoundation.deficit_tendsto_atTop_iff` |
| state/deficit formula | **exists** — `CurryFoundation.two_rpow_R_eq`, `orbit_mul_two_rpow_R` |
| `ν₂` congruence class | **exists in the operative form** — `SplitPrefix.dvd_state_diff` |
| new dynamic obstruction | **none found** |

One theorem added, to the existing module rather than a new one (a single corollary does not
justify `EOC/DeficitFeedback.lean`):

```
EOC/CurryFoundation.lean
  theorem deficit_succ_le (S : ℕ → ℤ) (k : ℕ) (hd : 1 ≤ S (k + 1) - S k) :
      deficit S (k + 1) ≤ deficit S k + 1
```

**Build status.** `lake build EOC.CurryFoundation` — **completed successfully, 2037 jobs.** Two
warnings, both pre-existing and outside the added lines (a header-length style lint and an unused
binder at line 113). No `sorry`, no `admit`, no new axiom, no `opaque`. Axiom audit:

```
'EOC.CurryFoundation.deficit_succ_le' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## P. Files changed

```
docs/DYNAMIC_DEFICIT_FEEDBACK_AUDIT.md                              (new)
EOC/CurryFoundation.lean                                            (+1 theorem)
scratch/dynamic_deficit_feedback_2026-09-21/feedback_audit.py       (new)
scratch/dynamic_deficit_feedback_2026-09-21/output.txt              (new)
```

## Q. Commits

Recorded in the commit trailer of this branch; see `git log dynamic-deficit-feedback`.

## R. Push status

Branch `dynamic-deficit-feedback` pushed to `origin`. No pull request opened. `main` untouched.

## S. Research verdict

**`EQUIVALENT TO TYPE-II DIVERGENCE`.**

The `Δ → m → d → Δ` loop is the Bernstein–Lagarias 2-adic conjugacy written in deficit
coordinates. Every arrow is a definition or an identity the repository had already proved, and
the key one — `deficit_succ` — is proved by `ring`. No arrow imposes a compatibility condition
between independently specified data, because `Δ_N` is a function of the digits.

The one candidate with a plausible mechanism, "a huge state constrains the next valuation", is not
merely unproved but **strictly subsumed**: the state-size ceiling `d_N ≤ log₂(3m_N+1)` is weaker
than the corridor ceiling `d_N ≤ Δ_N + b_{N+1}` for every seed `m₀ ≥ 2`, provably and in 2000 of
2000 computed steps. Largeness of `m_N` carries the same information as `Δ_N`, one exponential
away, and so cannot constrain what `Δ_N` does not already constrain.

Answering the target question directly:

> **Curry-normalized deficit growth creates no new deterministic arithmetic pressure on future
> valuations.** The pressure it appears to create is the zero-corridor constraint, already
> assumed.

This closes the dynamic-feedback route, as the realizer-growth round closed the
unbounded-realizer route. Both closures are of the same kind: a proposal that looked like a
weaker target turned out to be the same target in new letters. The remaining frontier is
unchanged.
