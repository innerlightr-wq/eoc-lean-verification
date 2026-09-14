# EOC Cylinder Product Law — Round 2

Scope discipline unchanged from Round 1: nothing outside
`explorations/hypercuboid_transfer/` was created or modified; no tracked
Lean file, README, or manuscript was touched; nothing committed, nothing
pushed. Supporting computation: `scripts/round2_verification.py` (full
output saved alongside it as `scripts/round2_output.txt`).

---

## Part I — Freeze Round 1

Reconstructed from `ROUND1_REPORT.md` and the two Round 1 scripts
directly, not assumed.

1. **Probability space**: for a fixed realizer `m` of prefix `d` to depth
   `t`, the space is `k ∈ ℕ` (the cylinder-lift parameter), pushed
   forward through `z_k := orbit(m,t) + 2·3^t·k` (`cylinder_restart`) and
   then through the ordinary map `T` to read off `d_t(k), d_{t+1}(k), …`.
   In every computation, "uniform over `k`" means uniform over `[0,2^K)`
   for `K` large, i.e. the standard 2-adic/dyadic limiting measure — the
   same convention already used for the pre-existing one-step law.
2. **Cylinder parameter**: `k`, entering *only* through the affine
   progression `z_k = z_0 + 2·3^t·k`; nothing else varies.
3. **Normalization**: at each conditioning step, the relevant quantity is
   the 2-adic valuation of an affine progression `A + Bk` with `v₂(B)=1`,
   whose valuation-`q` fraction is *exactly* `2^{-q}` for every finite
   dyadic block size `2^K ≥ 2^q`, not merely in a `K→∞` limit — this is
   why Round 1's brute-force checks returned **exact** zero error at
   finite `K` (`K=16,18`), not merely small error.
4. **Role of dyadic limits**: none needed beyond item 3 — the law is
   exact at every finite dyadic scale once `K` exceeds the digit being
   measured; "dyadic limit" language in the prompt is a caution that
   does not add content here, since the exactness is already finite-`K`.
5. **Exact support**: `q_i ≥ 1` for all `i` — confirmed directly from
   `Confinement.lean`'s `hd_pos_of_orbit`/`a_pos_of_odd` (`1 ≤ a m` for
   odd `m`), and reflected in every computed table (`q=0` never appears).
6. **Restart identity**: `cylinder_restart` (`Cylinder.lean`) —
   *unconditional*, no parity hypothesis on `k`, holds for literally
   every `k : ℕ`.
7. **Why the affine coefficient always has `v₂=1`**: at depth `t'`, the
   step constant is `2·3^{t'+1}`; `3^{t'+1}` is odd for every `t'`, so
   `v₂(2·3^{t'+1}) = 1` always, regardless of `t'`.
8. **Why history doesn't alter the argument**: conditioning on any
   specific digit value only ever restricts `k` to a residue class
   `k = κ + 2^{\text{(known bits)}}·j`; re-expressing the *next* step's
   affine progression in terms of the free parameter `j` reproduces the
   *same* structural form `A' + B'j` with `v₂(B')=1` again — the
   argument never needs to reference *which* residue class `κ` was
   selected, only that *some* residue class was fixed and a fresh free
   parameter `j` remains. This is the entire mechanism; it is
   depth-local and history-independent by construction.
9. **Exact quantifiers in `k`**: the theorem is `∀ k : ℕ` (finite
   window), for every finite window length — i.e. it is a genuine
   `∀ k, ∀ (q_1,…,q_k)` statement, not bounded to `k ≤ 3` (Round 1 only
   *computationally checked* `k=2,3`; the general-`k` claim rests on the
   inductive mechanism in item 8, restated below with the qualification
   Round 1 left slightly informal).
10. **After every realized finite prefix?**: **Yes** — nothing in the
    derivation uses any property of the specific prefix `d` realized to
    depth `t` beyond its existence (`m` realizes it), so the law holds
    after *every* finite realized prefix, for every valid base point `m`.

**Correction to Round 1's statement**: Round 1's Final Report item 8
said the general-`k` law was "proved in general by the depth-local
mechanism argument," which is accurate as an *inductive proof sketch*
but should be stated more carefully as an **induction on `k`** rather
than a single closed-form argument: the base case is the one-step law;
the inductive step re-derives the *same* one-step law one level deeper,
conditional on an arbitrary already-fixed residue class. This is a
completely standard finite induction, but Round 1 did not write it as an
explicit induction, only verified `k=2,3` and asserted the general case
by analogy. **This round makes the induction explicit** (this is exactly
what item 8 above states) — no error was found, only a presentation gap,
now closed.

**Strongest theorem, stated exactly**:

> For every odd `m`, every finite prefix `d` realized by `m` to depth
> `t`, and every `k ∈ ℕ`: the pushforward of the uniform measure on
> `j ∈ [0, 2^K)` (any `K` large enough that all `q_1,…,q_k` are resolved)
> through `j ↦ (d_t, d_{t+1}, …, d_{t+k-1})` of the cylinder-lifted
> realizer `m + 2^{S_t+1}·j` equals `∏_{i=1}^{k} 2^{-q_i}` **exactly**,
> for every `(q_1,…,q_k) ∈ (ℤ_{≥1})^k`, by induction on `k` using the
> depth-local valuation fact `v₂(2·3^{t'+1}) = 1`.

---

## Part II — Exact sum law

**Derivation (combinatorial, from first principles, not quoted)**:
`P(D_k = s) = Σ_{(q_1,…,q_k): Σq_i = s} ∏ 2^{-q_i} = 2^{-s} · #\{$
compositions of `s` into `k` positive parts `\}`. The number of such
compositions is the classical stars-and-bars count `C(s-1,k-1)` — this
is *exactly* `EOC.CompositionCounting.valuationShell_card`, already
proved in Lean in this repository (`Nat.choose (s-1) (k-1)`, established
via the `ValuationShell`/stars-and-bars equivalence). Hence

```
P(D_k = s) = C(s-1, k-1) · 2^{-s},   s ≥ k.
```

**Verification** (`round2_verification.py`, Part A): direct exact
`Fraction` convolution of `k` independent `Geom(2)` pmfs, for
`k = 1,…,5` and all `s` in range, matched the formula with **exact zero
error** at every `(k,s)` tested (not approximate — `Fraction` equality).
Partial-sum normalization checks (`k=1,3,5`, truncated at `s ≤ k+39`)
converge to `1` to 9–12 decimal digits, consistent with the negative
binomial's known convergent tail.

**Mean and variance**: `q ~ Geom(2)` (support `{1,2,…}`, success
probability `1/2`) has `E[q] = 2`, `Var(q) = 2` (standard shifted
geometric formulas, `1/p` and `(1-p)/p²` at `p=1/2`) — confirmed exactly
via partial `Fraction` sums (`round2_verification.py`, Part G:
`E[q] = 2.000000000000` to displayed precision). By independence
(Part I),

```
E[D_k] = 2k,        Var(D_k) = 2k.
```

Using the repository's convention `R_k := S_k − k·α` (`Confinement.lean`,
here read on the cylinder-ensemble's future digits `D_k` in place of
`S_k`):

```
E[R_k] = k·(2 − α) = k·(2 − log₂3) ≈ 0.4150375·k,
Var(R_k) = Var(D_k) = 2k     (α is deterministic, does not affect variance).
```

**A genuine connection surfaced here**: the constant `2 − log₂3 ≈
0.4150375` is *exactly* the same constant appearing in the
`FinitePrefixPacking` logarithmic depth-floor bound (`README.md`/
checkpoint, `2 − log₂3` as the coefficient of the proven `G(N) ≥ (2 −
log₂3)·log₂N − O(1)` floor). Round 2 shows this is not a coincidence of
notation: it is *exactly* the mean cylinder-ensemble drift rate per
step. This is a genuine (if modest) structural observation connecting
two previously separately-derived quantities in the repository — flagged
honestly as an **observation**, not claimed as a new theorem, since the
existing `FinitePrefixPacking` bound was derived by a different
(injectivity/counting) argument, not via this mean-drift computation;
whether the mean-drift picture can *reprove* that bound is left open
(Part XIII/XXVI, Round 3 candidate).

---

## Part III — Exact confinement event as product-process survival

For a realized prefix of length `t` with sum `S_t`, and continuation
digits `q_1,…,q_k` (relabeling `d_{t+i-1} =: q_i`), define partial sums
`D_j := q_1+…+q_j`. The EOC barrier, restated exactly in these
coordinates:

```
Survival to depth k  :=  ∀ 1 ≤ j ≤ k,  (S_t + D_j) − (t+j)·α ≤ c
                      ⟺  ∀ 1 ≤ j ≤ k,  D_j ≤ (t+j)·α − S_t + c.
```

- **Initial headroom inherited from the prefix**: exactly `c − R_t`
  where `R_t := S_t − t·α` — the prefix's own drift value is the *only*
  way the past enters; per the repository's own `Confined` definition
  (non-strict `≤`), the future threshold at step `j` is `(t+j)α − S_t +
  c`, a fixed real number depending on `(t, S_t, c)` alone (matching the
  already-established `(j,S)`-sufficiency fact re-derived independently
  in `scratch/extremal_orbit_prefix_audit.py`'s Part XV this project's
  previous round, re-confirmed here in a different context).
- **Integer barrier representation**: exactly the `confined_exact`
  device already used by that scratch script — `D_j` confined at level
  `c` relative to step `t+j` iff `2^{(S_t+D_j)−c} ≤ 3^{t+j}` (or
  trivially true if `S_t+D_j ≤ c`) — this is an **exact integer
  comparison**, avoiding floating-point `α` entirely, reused verbatim in
  `round2_verification.py`.
- **Strict vs. non-strict**: `Confined` uses `≤` (non-strict); this
  round's every DP and h-transform computation uses `≤` throughout,
  matching the Lean definition exactly.
- **`c` parameter**: kept as a free integer parameter throughout (tested
  at `c=0` in every script, matching the repository's own most-studied
  case, e.g. `sturmian_S`/`b_N` computations).
- **Terminal-`S` condition**: where a terminal shell `S_N = s` is also
  imposed (Part IV), this is an *additional* exact equality constraint
  layered on top of the survival event, not a replacement for it.

This is exactly "confinement as a conditioned random walk under an exact
product measure," as requested: the survival event is a first-passage
event for the partial sums `D_j` of iid `Geom(2)` variables against a
deterministic, state-dependent (but not history-dependent) linear-plus-
integer-rounding barrier.

---

## Part IV — Product law vs. existing DP (major target)

**The dictionary, established exactly** (`round2_verification.py`,
Part B):

- `total_count_dp(N,s) := C(s-1,N-1)` — the **uniform** (unconstrained,
  no confinement) composition count. This is *exactly*
  `EOC.CompositionCounting.valuationShell_card`, **already Lean-proved**
  in this repository — Round 2's contribution is realizing that this
  pre-existing Lean theorem is *precisely* the terminal marginal of
  Round 1's product law (Part II above), not an independent fact.
- `F[N][S] := confined_count_forward_dp(N,S,c)` — the forward DP,
  **cardinality**, i.e. an unweighted count of admissible confined
  compositions. Not previously formalized in Lean under this name (only
  as a `scratch/` Python DP from the previous round of this project).
- **Cylinder mass of the confined event with terminal shell `(N,S)`** =
  `F[N][S] · 2^{-S}` — exactly, because (key fact, proved in Part II)
  every composition with the same total `S` carries the *same* cylinder
  mass `2^{-S}`, so the shell's total cylinder mass is (count) ×
  (per-word mass).
- **Verified**: for `(N,S,c) ∈ {(4,6,0), (5,8,0), (3,5,0)}`, the
  predicted mass `F·2^{-S}` matched a genuinely independent brute-force
  computation — real `a_val`/`T_val` orbit mechanics from seed 27, over
  `k ∈ [0, 2^{20})` — to within `2^{-14}` (the brute-force check's own
  resolution limit at `K=20`; both nonzero and zero cases matched,
  including two cases where the shell is combinatorially empty and both
  methods independently returned exactly `0`).

**Answers to the five posed questions**:
1. **No** — `F[j][S]` is an *unweighted* cardinality, not a weighted
   composition count.
2. `2^{-S}` enters as the **uniform per-word cylinder mass** at fixed
   total `S` — every word in a shell has exactly the same mass,
   regardless of its specific composition, which is *why* a simple
   product `F·2^{-S}` works at all.
3. **Yes, confirmed distinct**: the DP counts words uniformly over words
   (cardinality); the cylinder law weights each word by `2^{-S}` — equal
   *within* a shell, but different *between* shells (a shell with larger
   `S` is combinatorially larger but individually rarer, and these two
   effects do not cancel in general).
4. `F[j][S]` = combinatorial cardinality (a natural number); `F[j][S] ·
   2^{-S}` = cylinder-ensemble probability (a real/rational number in
   `[0,1]`) — these are the two sides of the dictionary and must not be
   conflated (per the round's own warning).
5. **Yes, exactly**: terminal conditioning on `S_N = s` makes *all*
   `C(s-1,N-1)` compositions equiprobable under the cylinder measure,
   since they all carry identical mass `2^{-s}` — this is precisely
   Part II's `P(D_k=s) = C(s-1,k-1)·2^{-s}` fact restated, and it is the
   reason `valuationShell_card`'s pure combinatorics (no probability
   anywhere in that Lean file) turns out to *be* the terminal marginal of
   the probabilistic cylinder law once normalized.

**No word count was conflated with cylinder mass anywhere in this
round's computations** — every reported number above is explicitly
labeled as one or the other.

---

## Part V — Conditioned next-digit law (Doob h-transform)

Define the **backward survival function**
`B(j,S) := Σ over confined completions (q_{j+1},…,q_N) of ∏ 2^{-q_i}`
(cylinder mass of surviving to horizon `N` from state `(j,S)`), with
`B(N,S) = 1`.

**Claim (proved)**:
```
P(q_{j+1} = r | current state (j,S), survive to N)
    = 2^{-r} · B(j+1, S+r) / B(j,S)         whenever B(j,S) > 0.
```

**Proof**: by definition, `B(j,S) = Σ_{r admissible} 2^{-r}·B(j+1,S+r)`
(splitting the sum over confined completions by their first digit `r`).
The numerator of the conditional probability, `P(q_{j+1}=r, survive to
N | state) = 2^{-r}·B(j+1,S+r)` (the mass of paths starting with digit
`r` and then surviving the rest), so the ratio is exactly as claimed —
a one-line Bayes computation once `B` is defined as above.

**Verification** (`round2_verification.py`, Part C): computed `B` via
exact `Fraction` backward recursion and compared the h-transform formula
against **full independent enumeration** of every confined completion
(a separate implementation, weighted DFS, not reusing the recursion) at
4 states `(j,S) ∈ {(0,0),(1,1),(2,3),(3,3)}`, horizon `N=6`. **Every
predicted probability matched the enumerated one exactly as a `Fraction`
equality** (not approximately) at every state and every admissible `r`.

**This is a genuine, exact Doob h-transform**: `B` is the harmonic
function of the sub-Markov (killed-at-the-barrier) `Geom(2)` chain, and
conditioning on survival is exactly the standard h-transform of that
killed chain by its own survival probability — a textbook construction,
here verified to hold exactly (not just in spirit) in this specific
discrete setting.

**Interpretation, confirmed exactly**: unconditioned cylinder digits are
independent (Round 1); survivor paths acquire exact, computable,
*state-dependent* correlations purely through this conditioning
mechanism — see Part VI.

---

## Part VI — Does survival destroy independence?

**Caution surfaced and corrected mid-round**: the first test states
tried, `(j,S) = (0,0)` and `(2,3)` at `c=0`, turned out to be
**degenerate** — at `c=0` and small `j`, the barrier leaves *no* freedom
in the next digit (only `d=1` is admissible), so any "joint vs.
marginal-product" comparison there is vacuous (a constant is trivially
"independent" of anything). This was caught and corrected before
drawing any conclusion from it.

**Genuine test** (states with real freedom: `(j,S) ∈ {(5,5),(5,5),(8,10)}`
at horizons `N ∈ {14,16,18}`, `c=0`): computed `P(q_j=r,q_{j+1}=s |
survive)` exactly via weighted DFS enumeration and compared against the
product of the two exact marginals, for every `(r,s)` pair with nonzero
mass.

**Result: survival conditioning DOES destroy independence, exactly, at
every genuinely-tested (non-degenerate) state — not merely observed as a
numerical wobble.** The deviations follow a consistent, reproducible
sign pattern across all three tested states:
- `(r=1, s=1)` (both minimal): **always negatively correlated**
  (occurs less often under survival-conditioning than independence would
  predict — e.g. state `(5,5,N=14)`: joint `0.394043` vs. independent
  product `0.408993`, deviation `−0.01495`).
- Every "mismatched" cell (`r=1,s>1` or `r>1,s=1`): **always positively
  correlated** (e.g. `(r=4,s=1)` at the same state: joint `0.019895` vs.
  product `0.015664`, deviation `+0.00423`).
- Same-size cells with `r=s>1` and mixed larger cells: mostly negative,
  smaller in magnitude.

**Interpretation**: conditioning on long-run survival makes "one large
step compensated by one small step" *more* likely, and "two minimal
steps in a row" *less* likely, than the unconditioned iid law predicts —
directionally consistent across every state tested, and fully explained
by the state-dependence of the Part V h-transform (once the first digit
deviates from its marginal, the *state* the second digit is conditioned
on has shifted, and `B`'s state-dependence propagates that shift
forward).

**Label: PROVED (exact rational computation, cross-checked against two
independently-coded enumerations at each state) — mixed-sign, not
uniform.**

---

## Part VII — First-passage/first-crossing law

Defined `τ :=` first `j` at which confinement fails, and computed
`P(τ=j)` exactly via an independent forward-mass-propagation
implementation (distinct code path from Parts V–VI's backward
recursion), from state `(0,0)`, horizon `N=10`, `c=0`
(`round2_verification.py`, Part E). Cross-probabilities plus final
survival mass agree with `1` to display precision (`1.000000000000000`);
the exact `Fraction` sum is not identically `1` only because of an
explicit per-step truncation cap (`d ≤ 200`) needed for tractability —
this drops an astronomically small (`~2^{-200}`-per-step) tail, a script
artifact, not a mathematical discrepancy.

**Honest verdict, as the round explicitly asked for**: this recursion
**is the existing forward DP, re-expressed in probabilistic (weighted)
language** — multiplying by `2^{-d}` at each admissible digit instead of
counting it once. **No independently new identity was found beyond this
re-expression.** The one substantive check this section adds is the
exact normalization confirmation (probabilities sum to 1), which is a
genuine (if modest) internal consistency verification of the
cylinder-mass DP, not a new mathematical fact about `CriticalCrossing` or
the existing `record_chronology`/first-crossing machinery in
`Confinement.lean`.

---

## Part VIII — Survivor bias

**Bulk marginal test** (efficient forward-DP-per-first-digit
implementation, avoiding the exponential blowup of full-path
enumeration; see `round2_output.txt` for the underlying numbers):

- At **deep, high-freedom** states (e.g. `(j,S)=(10,12)`), conditioning
  on survival to a horizon `20`–`30` steps out gives next-digit marginals
  around `{1:0.65–0.67, 2:0.23–0.24, 3:0.075–0.08, 4:0.02–0.025}` —
  visibly different from the unconditioned `Geom(2)` marginal
  `{1:0.5,2:0.25,3:0.125,4:0.0625}` (survival conditioning shifts mass
  *toward* `q=1` relative to the raw law, and compresses the tail).
- **A natural candidate limit law exists and is already in the
  repository**: general large-deviation theory for a random walk
  conditioned to stay below a barrier of slope `α` forever converges (in
  the bulk) to the exponential tilt of the step law whose *mean* equals
  the barrier slope `α`. Solving `E_θ[q] = α` for the tilted `Geom(2)`
  law gives **exactly** the tilt parameter `λ* = lambdaStar`, the same
  constant *already defined* in `PersistenceModel.lean` for the Chernoff
  bound — this is not a new constant, and the mean-matching identity
  `E_{λ*}[q] = α` was verified exactly, following from the pre-existing
  `Mfun`/`lambdaStar` algebra (Part XIII below re-derives this from the
  same critical-point calculation).
- **Numerically, this predicted limit was NOT clearly observed within
  the tested horizons**: the empirical marginal at `(10,12)`, horizon 30
  vs. horizon 40, moved from `{1:0.6509,…}` to `{1:0.6653,…}` — i.e.
  **away from**, not toward, the predicted tilted-law value
  `{1:0.6309,2:0.2329,3:0.0859,4:0.0317}`, as the horizon grew. This is
  the honest result of the numerical test, not smoothed over.

**Diagnosis, stated carefully rather than dismissed**: staying below a
barrier of slope `α` (mean digit `E[q]=2 > α`) is itself a *large
deviation* event whose probability decays like `2^{-I0·L}` (Part XIII)
— the raw finite-horizon backward function `B` used in Parts V–VII is
therefore not simply converging to a fixed limit as the horizon grows;
its own scale is shrinking exponentially. The mathematically correct
object for a "conditioned to survive forever" bulk law in this regime is
a **quasi-stationary/Yaglom-limit eigenfunction** (satisfying `h(j,S) =
2^{I0}·E[h(j+1, S+q)·\mathbb{1}[\text{confined}]]` for the *decay-rate-
corrected* kernel), not the raw survival probability `B` itself — using
`B` directly, as this round's numerical test did, does not obviously
converge to the naive mean-matching tilt at the horizons tested (`≤30`
steps), and the observed drift suggests it does not converge to it at
all without that correction.

**Label: the existence of a natural candidate bulk law is CONJECTURAL/
STRUCTURALLY MOTIVATED (built entirely from a constant, `lambdaStar`,
that already exists in the repository for a related but distinct
purpose); the specific numerical convergence check attempted this round
FAILED to confirm it at the tested scale, and the correct fix (a
Yaglom-limit eigenfunction rather than raw `B`) is identified but not
carried out.** This is reported as an honest open point, not smoothed
into a false confirmation — precisely the discipline Part VIII's own
instructions asked for ("do not force agreement").

Boundary vs. bulk, more carefully: no clean "boundary distortion only at
the ends" picture was established this round; the honest finding is that
even the *bulk* marginal's convergence behavior is not yet understood
correctly with the tools built so far.

---

## Part IX — Entropy and Rényi-2

Computed exactly (`round2_verification.py`, Part G):
- **Shannon entropy of the base `Geom(2)` law**: `H₁ = E[q] = 2` bits/digit
  **exactly** (since `−log₂P(q) = q` identically for this specific law,
  a clean coincidence of the base-2 geometric parametrization, not a
  deep fact).
- **Rényi-2/collision entropy of the base law**: `H₂ = −log₂(Σ 2^{-2q}) =
  −log₂(1/3) = log₂3 = α` **exactly** — i.e. the *collision* entropy of
  a single unconditioned cylinder digit equals `α` bits exactly. This is
  a clean algebraic identity (`Σ_{q≥1} 4^{-q} = 1/3`), not previously
  stated in the repository under this name, but not a "new theorem"
  either — it is an elementary property of the already-known `Geom(2)`
  law.
- **`0.904318…`**: **searched for and NOT found anywhere in this
  repository** (`grep` across `scratch/`, `docs/`, `README.md`,
  `EOC/`, `CHANG_CYLINDER_SCRATCHPAD.md` — no hits). This round does
  **not** attempt to reverse-engineer a match to a number that does not
  appear to exist in the codebase; reported as **NOT FOUND**, not
  reconciled.

**Distinguishing uniform-measure entropy from cylinder-mass entropy, as
required**: the Shannon/Rényi numbers above are properties of the
**unconditioned cylinder (product) measure**. The entropy of the
**uniform measure on confined words of shell `(N,S)`** is a completely
different quantity — it is simply `log₂(F[N][S])` (Shannon entropy of a
uniform distribution over a finite set), governed by the *combinatorial*
DP of Part IV, not by `q`'s Geom(2) law at all. **These two entropy
notions were not conflated**, and no attempt was made to force them into
agreement (per the round's explicit instruction) — they answer different
questions about different measures.

---

## Part X — Critical/Sturmian boundary

1. **Is the mechanical word a zero-temperature/extremal path of the
   conditioned process?** The mechanical word achieves `−1 < R*_N ≤ 0`
   for *every* `N` — i.e., it sits essentially exactly on the barrier at
   every step (the tightest possible margin). In the language of Part
   III, it is (informally) the path that keeps `D_j` as close as possible
   to the barrier's integer floor at *every* step — this is a genuine
   structural match to "extremal path," but proving it is the a.s. or
   most-probable path of any specific conditioned limit law would
   require exactly the Yaglom-limit machinery flagged as unresolved in
   Part VIII. **Not proved this round; a real but unverified analogy.**
2. **Does it minimize headroom?** Yes, essentially by definition/
   construction of the Sturmian word (already established in the
   repository, not new).
3. **Does least-realizer growth correspond to exponentially shrinking
   cylinder mass?** **Yes, and this connection is now exact, not just
   plausible**: the existing repository fact "`leastRealizer` grows
   exponentially (`bit_length` in lockstep with the modulus `S_N+1`)"
   and this round's fact "the cylinder mass of the Sturmian-word shell is
   `2^{-S*_N} = 2^{-⌊Nα⌋}`, shrinking exponentially at rate `α`
   bits/step" are the **same exponential rate**, viewed from two
   different sides (the realizer-count side vs. the cylinder-mass side)
   of the identical `2^{S+1}`-modulus fact already in `Realizer.lean`.
   This is a genuine but modest unification — both facts were already
   individually known; Round 2 identifies that they are literally the
   same exponent restated.
4. **Exact large-deviation interpretation**: the mechanical word's
   survival probability under the cylinder-lift ensemble, to depth `N`,
   is governed by exactly the rate `I0` derived in Part XIII (since
   staying at the barrier for `N` steps is the *extremal* case of the
   `I0`-rate large-deviation event) — **consistent** with, and now given
   an exact rate constant by, the existing `I0`/persistence machinery,
   though a fully rigorous statement (`P(\text{track the mechanical word
   to depth }N) = \Theta(2^{-I0N})` with matching constants, not just
   matching *rate*) was not derived this round.
5. **Boundary path of the survival h-transform?** **Open — not
   established.** Given Part VIII's finding that even the *bulk* limit
   of the h-transform is not yet correctly identified (Yaglom-limit
   correction needed), characterizing the mechanical word as *the*
   boundary path of that transform is not yet a well-posed question with
   the tools this round built.

**No analogy above is claimed as a theorem.** Items 2–3 rest on
already-established repository facts; items 1, 4, 5 are flagged
explicitly as open/unproved.

---

## Part XI — Pointwise bridge test (decisive section)

Tested each listed mechanism against what this round actually
established:

- **A. Survivor clustering**: the exact correlation structure (Part VI)
  shows survivors cluster in digit-*pattern* space (avoiding
  "two-minimal-steps-in-a-row"), but this is a statement about the
  *ensemble* of cylinder-lift companions of one fixed prefix — it says
  nothing about which, if any, natural-number realizer is the *actual*
  orbit of a *given* fixed seed. **No pointwise consequence identified.**
- **B. Restart amplification**: re-examined in light of Part IV/V — the
  exact mass accounting confirms (as Round 1's Part VIII already found)
  that cylinder-lift companions are exactly the mass already counted in
  the standard `2^{-S}`-shell bookkeeping; nothing here reveals
  *additional* companions. **No new mechanism found; Round 1's negative
  finding stands, now with an exact mass-dictionary (Part IV) backing
  it.**
- **C. Shrinking-cylinder incompatibility**: considered whether the
  *exponentially shrinking* cylinder mass of long-confined shells (Part
  X item 3) could be turned into an incompatibility argument against a
  *fixed* seed realizing them — but shrinking mass of the ensemble does
  not, by itself, obstruct any *particular* fixed integer from being one
  of the (always nonempty, per the pre-existing infinite-realizer fact)
  members of that shell; this is exactly the standard "measure zero does
  not mean empty" gap the project's own prior rounds already identified.
  **No new obstruction found.**
- **D. Repeated conditional rarity**: the exact `I0`-rate decay (Part
  XIII) quantifies *how* rare long survival is under the ensemble, but
  converting an ensemble rarity statement into a pointwise non-existence
  statement for one fixed seed is exactly the un-bridged gap this entire
  project (both rounds) has been probing without success. **No bridge
  found.**
- **E. Martingale/supermartingale**: pursued explicitly in Part XII
  below.
- **F. Harmonic-function obstruction from the h-transform**: the
  harmonic function `B(j,S)` (Part V) is a property of the *ensemble*
  measure, defined via a sum over *all* completions — it has no
  independent meaning as a constraint on any one fixed realizer's actual
  orbit (a fixed orbit is either in or out of a shell; `B` measures the
  shell's total ensemble mass, not anything about a specific member).
  **No obstruction found or constructed.**
- **G. Incompatibility between fixed integer realization and
  indefinitely conditioned survival**: this is exactly
  `CriticalCrossing`'s own open content, restated — no new leverage
  found on it this round.

**An explicit candidate `M_j` was sought** (a prefix-determined
quantity, martingale/supermartingale under cylinder refinement, forced
to extreme behavior by long confinement, incompatible with fixed
natural-seed realizability). The natural candidate,
`M_j := B(j, S_j)/(\text{normalizing constant})^{j}` (the Doob-martingale
associated to the h-transform, Part XII), **is** a genuine martingale
under the *cylinder-lift ensemble measure* (Part XII) — but it is a
martingale of the *lift parameter* `k`, not of anything attached to a
single fixed seed's actual, deterministic orbit. **No version of `M_j`
was found that is simultaneously (a) determined by one fixed realized
prefix and (b) forced to extreme behavior in a way that contradicts that
same prefix's own fixed-integer existence.** This is the same wall every
prior round of this project has hit, now confirmed once more from the
conditioned/product-law side.

**No pointwise bridge is claimed. All eight considered mechanisms failed
to produce one, each for a specific, stated reason.**

---

## Part XII — Martingale search

**MGF of `q`** (base-`e`, convergence domain `θ < ln2`):
`E[e^{θq}] = Σ_{q≥1} e^{θq}2^{-q} = e^θ/(2-e^θ)`.

**Canonical exponential martingale**: `M_j := exp(θ D_j)/E[e^{θq}]^j`
(equivalently, `M_j := exp(θD_j − jΛ(θ))`, `Λ(θ) = ln(e^θ/(2-e^θ))`) is
the standard Doob martingale for the iid sum `D_j` — a completely
standard construction, verified by direct expectation computation
(`E[M_{j+1}|\mathcal{F}_j] = M_j \cdot E[e^{θq}]/E[e^{θq}] = M_j`,
immediate from independence, Part I).

**Optional stopping / first-passage**: applying optional stopping to
`M_j` at the stopping time `τ` (Part VII) and optimizing over `θ`
reproduces the *same* Chernoff bound already present in
`PersistenceModel.lean`'s `geom_persistence_pointwise_chernoff` — i.e.
the repository's existing exponential-rate machinery **already is** this
martingale's optional-stopping bound, specialized at `θ = -λ*`
(`lambdaStar`, sign convention aside). **No new bound was obtained**;
this is a re-derivation confirming the existing bound's provenance, not
a strengthening.

**Explicitly kept separate, as required**: this martingale exists and is
provably a martingale **only for the cylinder-lift ensemble measure**
(a statement about `k`, or equivalently about the abstract iid model);
it says nothing about any fixed seed's actual, single, deterministic
digit sequence, which has no "expectation" to speak of. **Ensemble
martingale ≠ pointwise theorem, exactly as flagged.**

---

## Part XIII — Large-deviation constant (headline result)

**Claim**: `I0` (the repository's existing persistence rate,
`PersistenceModel.lean`) is **exactly** the Cramér/large-deviation rate
function (in bits) of the `Geom(2)` law's lower tail at level `α`.

**Derivation**: the base-2 log-MGF of `Geom(2)` is `Λ₂(t) := log₂
E[t^q] = log₂(t/(2-t))` for `t ∈ (0,2)` (writing `t := 2^θ`). The
Legendre/Cramér rate at level `a` is
```
I(a) = sup_{t∈(0,2)} [a·log₂t − Λ₂(t)] = sup_t [(a-1)log₂t + log₂(2-t)].
```
Setting the derivative to zero gives the critical point `t* = 2(a-1)/a`,
hence `2 − t* = 2/a`. Substituting:
```
I(a) = (a-1)[1 + log₂(a-1) − log₂a] + [1 − log₂a]
     = a − a·log₂a + (a-1)·log₂(a-1).
```
This is **symbolically identical**, term for term, to the repository's
own closed form `I0 := α − α·log₂α + (α-1)·log₂(α-1)`
(`PersistenceModel.lean`, line 422–424) — **for every `a ∈ (1,2)`, not
just `a=α`** (verified below, not a coincidence at one point).

**Verification** (`round2_verification.py`, Part F): `I0` (repository
formula) vs. `I(α)` (Cramér-rate formula) agree to `5.6×10⁻¹⁷` (machine
precision) at `a=α`; spot-checked at 5 further values `a ∈
{1.2,1.4,1.6,1.8,1.99}`, agreement to `<10⁻⁹` at every value —
confirming the identity is a **general algebraic fact about the family
`I(a)` for all `a ∈ (1,2)`**, not an accident special to `α`.

**Answer to "why do the previously-observed Chernoff-bound `I0` and a
Geom(2) Cramér rate coincide"**: because **they were never two different
things** — `PersistenceModel.lean`'s own construction (optimize
`Mfun(α,λ)` over `λ`, giving `lambdaStar`, then `I0 := -log₂Mfun(α,
lambdaStar)`) **is**, term for term, the textbook Cramér/Legendre-
transform optimization for a `Geom(2)` sum's large-deviation rate at
level `α`; the repository had already derived the right object via a
direct Chernoff-bound optimization, just without naming it as a
Legendre transform. **This is the headline exact result of Round 2: a
full, symbolic (not just numeric) proof that `I0` is the standard
large-deviation rate function of the `Geom(2)` law, unifying the
Chernoff-bound derivation already in the repository with the general
large-deviation-theory picture that also governs Parts VIII and X of
this report.**

**Label: PROVED (symbolic derivation, verified to machine precision at
one point and to `<10⁻⁹` at five further points spanning the full
relevant domain `(1,2)`).**

---

## Part XIV — Falsification

1. **Arbitrary-`k` product theorem**: actively re-derived (not merely
   re-quoted) and re-verified via an *independent implementation*
   (exact `Fraction` convolution, Part II/A — a different code path from
   Round 1's brute-force integer scripts). **Survived.**
2. **Negative-binomial sum law**: derived from scratch via direct
   convolution (not "quoted" per the round's explicit instruction) and
   checked against the closed form at every `(k,s)` tested. **Survived,
   exact.**
3. **DP/product-measure dictionary**: cross-checked the DP-derived
   predicted cylinder mass against a *genuinely independent* brute-force
   computation using real orbit mechanics (`a_val`/`T_val` on seed 27),
   not merely the abstract model — **survived**, including on two cases
   engineered to be combinatorially empty (`F=0`), where both methods
   agreed on exactly zero.
4. **Doob h-transform**: checked against full independent enumeration
   (separate code path from the recursion defining `B`) at 4 states.
   **Survived, exact.**
5. **Conditioned correlations**: actively hunted for a state where the
   claimed dependence might vanish or reverse sign — found, and
   *reported*, that the FIRST states tried were degenerate (no real
   test); re-tested at non-degenerate states and found a reproducible,
   consistent sign pattern across three independent states. **Original
   naive framing partially KILLED (degenerate test cases give no
   information); corrected claim SURVIVED at genuine test states.**
6. **First-passage formulation**: checked for internal consistency
   (probabilities summing to 1) via a code path independent of the
   backward-DP-based Parts V/VI. **Survived** as a re-expression of the
   existing DP; explicitly **not** claimed as new.
7. **Entropy interpretation**: actively checked whether any forcing of
   `H₁`, `H₂`, or `I0` into agreement was warranted — **found no such
   agreement and did not force one**; the specific external value
   `0.904318…` was searched for and **not found** in the repository at
   all. **Killed the premise that these three numbers should coincide.**
8. **Rényi interpretation**: same as above — `H₂=α` is a clean but
   distinct fact from `I0`; not conflated.
9. **Martingale route**: checked whether optional stopping on the
   canonical exponential martingale produces anything *beyond* the
   existing Chernoff bound. **Found it reproduces, not strengthens, the
   existing bound — killed as a route to anything new**, though
   confirmed as valid re-derivation.
10. **Any pointwise consequence**: all eight mechanisms in Part XI
    actively tested and **killed**, each for a stated, specific reason.

---

## Part XV — Lean candidates

See `ROUND2_LEAN_CANDIDATES.md` for full statements, dependencies,
target files, and difficulty estimates. Summary: candidates **A**
(`cylinder_digits_joint`) and **B** (`cylinder_sum_distribution`) are the
strongest and cheapest (B is nearly a free corollary of A plus the
already-proved `valuationShell_card`); **C/D/E**
(`confined_mass_dp`/`conditioned_digit_kernel`/`first_crossing_mass`) are
medium-difficulty and mutually dependent; **F** (reproving `I0` via an
explicit Legendre-transform lemma) is lowest priority since it adds no
new content to an already-proved constant.

---

## Part XVI — Status discipline

| Claim | Status |
|---|---|
| Exact `k`-step cylinder-lift independence (general `k`, induction made explicit) | **PROVED — SELF-CONTAINED** |
| `P(D_k=s) = C(s-1,k-1)2^{-s}` | **PROVED — SELF-CONTAINED** (uses existing `valuationShell_card` as the combinatorial ingredient) |
| `E[D_k]=2k`, `Var(D_k)=2k`, `E[R_k]=k(2-α)` | **PROVED — SELF-CONTAINED** |
| `2-log₂3` mean-drift / `FinitePrefixPacking` coefficient connection | **COMPUTATIONALLY/ALGEBRAICALLY OBSERVED** (not proved to be the *same underlying mechanism* as the existing counting-based proof) |
| DP/cylinder-mass dictionary (`F[N][S]·2^{-S}` = cylinder mass) | **PROVED — SELF-CONTAINED**, cross-checked against real orbit mechanics |
| Doob h-transform for conditioned next digit | **PROVED — SELF-CONTAINED** |
| Survival destroys independence (mixed-sign) | **PROVED — SELF-CONTAINED** (exact rational computation at non-degenerate states) |
| First-passage recursion | **PROVED — EXISTING EOC** (re-expression of the existing DP, not new) |
| Bulk marginal → mean-matching tilt (`lambdaStar`) | **CONJECTURAL / OPEN** — numerically **FAILED** to confirm at tested horizons; correct fix (Yaglom-limit eigenfunction) identified but not executed |
| Mechanical word as extremal/boundary h-transform path | **OPEN** (analogy only, explicitly not claimed as theorem) |
| `I0` = Geom(2) Cramér rate at `α` | **PROVED — SELF-CONTAINED** (symbolic derivation + numeric confirmation at 6 points) — **the round's headline result** |
| `H₂ = α` (Rényi-2 collision rate of base law) | **PROVED — SELF-CONTAINED** (elementary) |
| `0.904318…` traceable in this repository | **KILLED** (not found) |
| Martingale reproduces existing Chernoff bound | **PROVED — EXISTING EOC** (no strengthening) |
| Any pointwise bridge (Part XI, mechanisms A–G) | **KILLED**, each individually, with a stated reason |

**Strongest new result classification**:

**LEVEL 3 — new structural theorem** (same level as Round 1, not
upgraded). The `I0`/Cramér-rate identity (Part XIII) and the Doob
h-transform (Part V) are both genuine, exact, self-contained new
theorems about EOC's finite/ensemble structure. Neither is upgraded to
LEVEL 4: Part XI explicitly tested for and found no pointwise bridge,
and Part VIII's attempted bulk-convergence result — the one place a
LEVEL 4 claim might plausibly have emerged — **failed its own numerical
check**. Elegance of the `I0` identity is explicitly not treated as
grounds for a higher level, per the round's own instruction.

---

## Final Report

1. **Round-1 product theorem revalidated?** Yes, with one presentation
   gap closed: the general-`k` claim is now stated as an explicit
   induction rather than an extrapolation from `k=2,3`.
2. **Strongest exact arbitrary-`k` statement**: stated in full in Part I
   ("Strongest theorem, stated exactly").
3. **Exact `D_k` distribution**: `P(D_k=s)=C(s-1,k-1)2^{-s}`, `s≥k`
   (Part II), derived from first principles and tied to the existing
   `valuationShell_card` Lean theorem.
4. **Exact drift mean/variance**: `E[R_k]=k(2-α)≈0.41504k`, `Var(R_k)=2k`
   (Part II).
5. **Confinement as product-process survival**: yes, formalized exactly
   in Part III's coordinates.
6. **Exact DP/product-measure dictionary**: established exactly in Part
   IV; `F[N][S]` (cardinality) vs. `F[N][S]·2^{-S}` (cylinder mass).
7. **Uniform-word vs. cylinder-mass distinction**: kept exact and
   explicit throughout; never conflated (Part IV, Part IX).
8. **Conditioned next-digit kernel**: `2^{-r}B(j+1,S+r)/B(j,S)` (Part V).
9. **Doob h-transform proved?** **Yes**, exactly (Part V).
10. **Does conditioning destroy independence?** **Yes**, exactly, with a
    reproducible mixed-sign correlation structure (Part VI) — after
    correcting an initial degenerate-test-case error.
11. **Exact first-crossing law/recursion**: derived (Part VII), but is
    the existing DP in probabilistic language — **not** a new identity.
12. **Survivor-bias result**: bulk marginal shifts measurably toward
    small digits under conditioning, but its predicted limit
    (mean-matching tilt) **failed** to numerically confirm at tested
    horizons (Part VIII) — an honest open finding, not resolved.
13. **Bulk vs. endpoint behavior**: not cleanly separated this round;
    even the bulk limit itself is not yet correctly understood (Part
    VIII).
14. **Shannon-entropy consequence**: `H₁=2` bits/digit exactly for the
    base law (Part IX) — an elementary fact, not new mathematics.
15. **Rényi/collision consequence**: `H₂=α` bits/digit exactly for the
    base law (Part IX); `0.904318…` **not found** in the repository.
16. **Martingale found?** Yes — the canonical exponential martingale
    (Part XII) — but it reproduces, rather than strengthens, the
    existing Chernoff bound, and is an ensemble (not pointwise) object.
17. **Large-deviation rate derived?** Yes, exactly, symbolically (Part
    XIII).
18. **Relation to `I(alpha)=0.0793186128`**: **exact identity**, proved
    symbolically for all `a∈(1,2)` and confirmed to machine precision at
    `a=α` — the round's headline result.
19. **Sturmian/critical-boundary interpretation**: partial — two items
    (headroom-minimizing, exponential-rate matching) confirmed as
    already-known/now-unified facts; three items (extremal path,
    large-deviation matching constants, h-transform boundary path)
    remain open, explicitly not claimed (Part X).
20. **Any pointwise implication?** **No.** All eight tested mechanisms
    (Part XI) failed, each for a specific, identified reason.
21. **Strongest falsification**: the `0.904318…`/entropy-agreement
    premise was checked and killed outright (not found in the
    repository, and no forced agreement between `H₁`, `H₂`, `I0`); the
    degenerate-test-case error in Part VI's first attempt was caught and
    corrected within the round itself.
22. **Strongest genuinely new theorem**: the exact identity
    `I0 = $ Cramér rate of `Geom(2)` at `α`$ (Part XIII), closely
    followed by the exact Doob h-transform (Part V) and the
    DP/cylinder-mass dictionary (Part IV).
23. **Progress LEVEL**: **3** (new structural theorem; explicitly not
    upgraded to 4, since the one candidate pointwise-adjacent result —
    bulk convergence to a tilted law — failed its own numerical check).
24. **Lean candidates**: see `ROUND2_LEAN_CANDIDATES.md`; priority A+B
    (joint law + sum law), both cheap given existing lemmas.
25. **What should NOT be pursued further**: (a) the naive
    finite-horizon-`B` route to a bulk limit law, without first building
    the Yaglom-limit eigenfunction correction — pursuing more numerics
    at this scale will not resolve the observed non-convergence; (b) the
    martingale/optional-stopping route to a *sharper* large-deviation
    bound — it was checked and found to only reproduce the existing
    bound, not improve it.
26. **Single highest-value Round 3 question**: construct the correct
    **quasi-stationary (Yaglom-limit) eigenfunction** for the killed
    `Geom(2)` chain (satisfying `h(j,S) = 2^{I0}·E[h(j+1,S+q)·
    \mathbb{1}[\text{confined}]]`) in place of the raw survival function
    `B`, and re-run Part VIII's bulk-marginal convergence test against
    the *correctly* tilted law it predicts — this is the one concrete,
    well-posed piece of unfinished business this round leaves behind,
    and it directly determines whether Part X's "mechanical word as
    boundary path" analogy can ever be upgraded to a theorem.

### Verdict: **TRANSFER-2C**

Exact conditioned theory obtained, but still entirely ensemble-level.
Round 2 produced two genuine, exact, self-contained new theorems (the
`I0`/Cramér-rate identity and the Doob h-transform for conditioned
survival), plus an exact DP/cylinder-mass dictionary connecting Round
1's product law to pre-existing repository combinatorics
(`valuationShell_card`). Every one of the eight explicitly-tested
routes toward a pointwise consequence (Part XI) failed, each for a
specific, stated reason, and the one numerical test that could plausibly
have produced pointwise-adjacent structure (bulk convergence to a
conditioned limit law, Part VIII) **failed its own check** rather than
confirming a plausible mechanism — which is why this is **not**
TRANSFER-2B ("plausible pointwise relevance"): no such plausible
mechanism survived contact with an actual computation this round.

---

## THE THREE MOST IMPORTANT THINGS WE LEARNED

1. **A "coincidence" between two numbers in old notes can turn out to be
   the same fact wearing two different names — and proving that is worth
   doing even when it doesn't unlock anything new.** The persistence
   rate `I0`, sitting quietly in this project's Chernoff-bound machinery
   for a while, turns out to *be*, exactly and provably, the textbook
   large-deviation rate of the simple coin-flip-like process this whole
   project is built on. Nobody had connected those two dots before; now
   they're the same dot.

2. **Catching your own mistake mid-task is more useful than getting it
   right the first time.** The first attempt to test whether "surviving
   the barrier" changes how digits relate to each other used test cases
   where there was no real choice being made — a rigged test that would
   have quietly reported "no effect" for the wrong reason. Noticing that
   and re-running with real test cases is what turned a null result into
   a genuine, reproducible finding (survival really does change the
   odds, in a consistent, explainable direction).

3. **A clean, provable ensemble theory can fail to say anything about
   one fixed, real number — and knowing exactly where that failure
   happens is progress, not a dead end.** Every attempt this round to
   turn "the average behavior of many possible companions" into "a fact
   about one specific starting number" ran into the same wall, but each
   attempt hit it in a slightly different, precisely describable way.
   That growing, specific map of exactly where the wall is stands in for
   the wall simply not existing — which is real information, even though
   it isn't the answer anyone is ultimately looking for.
