# Research protocol

Screening rules for a new EOC research session. These are **heuristics for deciding what to
spend effort on**, not proof techniques, and none of them establishes equivalence on its own.

---

## Gate 1 — the coordinate-change / tautology gate

Two expensive-looking rounds collapsed onto problems the repository already had. Both would have
been caught by the same two questions, asked before any development.

When a proposed quantity `X_N` is introduced, ask:

> **(a) Is `X_N` independently constrained, or is it a deterministic function of data already
> fixed — the digit word `d_0 … d_{N-1}`, the orbit state `m_N`, or the prefix sums?**

> **(b) Is the proposed new recurrence a new restriction, or does it follow by unfolding
> definitions plus elementary algebra?**

A sharp mechanical proxy for (b), specific to this repository:

> **If the recurrence's Lean proof is `unfold …; push_cast; ring`, it carries no information.**

A recurrence provable by `ring` is a restatement of the definitions. It cannot constrain anything,
because it is true of *every* sequence satisfying those definitions, realizable or not.

### Worked example 1 — dynamic deficit feedback (closed 2026-09-21)

The proposal was the loop `Δ_N → m_N → d_N = ν₂(3m_N+1) → Δ_{N+1}`, which looks dynamical.

- Test (a): `Δ_N = ⌊Nα⌋ − S_N` is a **function of the digits**, and invertible —
  `S_N = ⌊Nα⌋ − Δ_N`. It is not independent data. **Fails (a).**
- Test (b): the recurrence `Δ_{N+1} = Δ_N + b_{N+1} − d_N` is `CurryFoundation.deficit_succ`,
  whose proof is literally `unfold deficit; push_cast; ring`, and whose docstring already said
  *"Pure algebra from the definitions."* **Fails (b).**

Both tests fail in minutes. The audit that established this formally took a full session.

Secondary lesson worth keeping: the motivating intuition — *a huge state must constrain the next
valuation* — was not merely unproved but **strictly subsumed**. The state-size ceiling
`d_N ≤ log₂(3m_N+1)` is weaker than the corridor ceiling `d_N ≤ Δ_N + b_{N+1}` already assumed,
because `m_N ≥ m₀·2^{Δ_N}`. When a new bound is proposed, check it against the constraints already
in force before developing it.

### Worked example 2 — unbounded prefix realizers (closed 2026-09-21)

The proposal was that `sup_N r_N = ∞` might be an easier target than positive-integer
realizability.

- Test (a): `r_N` is the least realizer of a prefix — determined by the digit word.
  **Fails (a).**
- The audit then proved the collapse outright:
  `sup_N r_N < ∞ ⟺ positive-integer realizer exists ⟺ r_N eventually constant`
  (`ZCRERealizerGrowth.boundedPrefixRealizers_iff_positiveRealizer`). For a fixed seed,
  `r_N = m₀ mod 2^{S_N+1}`, so `r_N = m₀` once `2^{S_N+1} > m₀`.

**Do not reopen either question.** Both are encoded in `research_graph.json` with status
`EQUIVALENCE` / `CLOSED_ROUTE` precisely so that a future session surfaces them immediately.

### Limits of this gate

- It is a **screening heuristic**. Failing (a) does not prove the proposal is worthless; passing
  both does not prove it is useful.
- A quantity can be a function of the digits and still be a useful *reformulation* — a clearer
  proof, a better invariant to compute. What it cannot be is an **additional constraint**.
- The gate says nothing about quantities that depend on data genuinely outside the orbit
  recurrence (for example an external Diophantine or analytic input).

---

## Gate 2 — the discriminator criterion (repository's own, pre-existing)

From `docs/ZERO_CORRIDOR_REALIZABILITY_FRONTIER.md` §28. For any candidate invariant `I(W)`,
before spending further effort:

> Does `I` distinguish finite prefixes coming from a fixed positive-integer orbit from those that
> do not?

Arbitrary complexity statistics with no realizability-connection criterion must pass this bar
first. This gate predates the index; it is reproduced here so both screens sit in one place.

---

## Gate 3 — check the closed-route list before starting

`docs/ZERO_CORRIDOR_REALIZABILITY_FRONTIER.md` §27 lists routes not to repeat without a genuinely
new ingredient, and `research_graph.json` encodes them with status `CLOSED_ROUTE` /
`REFUTED_ROUTE`. Run

```
python3 -m tools.research_context query -q "<your question>"
```

first. If the packet returns a `CLOSED_ROUTE` node at the top, read its source before proceeding.

---

## Gate 4 — status discipline

When recording a result, keep these apart, as the repository's existing documents do:

| label | meaning |
|---|---|
| unconditional | holds for every accelerated orbit |
| Type-II conditional | assumes the divergence normalization |
| Curry conditional | assumes `ReciprocalSummable` |
| asymptotic | holds eventually, with the constants stated |
| computational | verified on a finite range; **cannot** establish Type-II behaviour |

A statement that mixes these silently is the second-most common failure mode after the
coordinate-change trap.

---

## Gate 5 — decompress before claiming

The bootstrap and query packets are **indexes**. Before any claim enters a proof, a manuscript, or
a novelty assessment, open the cited Lean declaration or document section and verify it there.
Compression is for deciding *what to read*, never for deciding *what is true*.
