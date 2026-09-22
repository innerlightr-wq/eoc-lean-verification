# Aksenov et al. method notes

Reading notes taken while building `tools/research_context`. The point of this file is to keep a
hard line between *what the source paper actually says*, *what we changed because EOC is not
Mathlib*, and *what is entirely ours*.

## Citation

> Vitaly Aksenov, Eve Bodnia, Michael H. Freedman, Michael Mulligan.
> *Compression is all you need: Modeling Mathematics.*
> arXiv:2603.20396 (2026). DOI [10.48550/arXiv.2603.20396](https://doi.org/10.48550/arXiv.2603.20396).

**Licence: CC BY 4.0.** Verified directly, not assumed: the DataCite record for
`10.48550/arXiv.2603.20396` carries `rightsIdentifier: cc-by-4.0`
(`Creative Commons Attribution 4.0 International`), and the arXiv API returns the paper with the
four authors above, submitted 2026-03-20. Source `.tex` retrieved from `arxiv.org/e-print` and
read for the definitions below.

**The authors have no connection to this project and have not reviewed, endorsed, or been
consulted about it.** What follows is our reading of a public paper.

---

## Part 1 — directly from Aksenov et al.

Only statements we could point to in the paper's own text.

### Dependency graph (§"Constructing the dependency graph")

- Vertices are Mathlib elements — lemmas, theorems, definitions, structures, inductive types —
  **plus** Lean core elements and a synthetic `Sort` node, which have no further Mathlib
  dependencies and act as the **sinks**.
- Each element has a **signature** (statement/type) and an optional **body** (proof/defining
  expression).
- For each element `u`, count how many times each other element `v` is referenced; that
  multiplicity is the **weight** of a directed edge `u → v`. Edges point *toward* dependencies.
- Extraction is a recursive traversal of the elaborated `Expr`, collecting every `.const` node;
  `.sort` occurrences are folded into the synthetic `Sort` primitive. The paper prints the
  traversal as `collectElems`.
- The construction records **multiplicity only**, forgetting the order of references. Two proofs
  using the same lemmas the same number of times in different ways are indistinguishable.
- Mathlib's graph has a small number of cycles (~60 mutually dependent pairs, all from unsafe
  recursion); they collapse each strongly connected component to a single vertex, taking
  463,719 vertices to 463,661.

### The three structural metrics (§"Wrapped and unwrapped lengths, and depth")

Writing `G` for the primitives (Lean core + `Sort`) and `G' = G ∪ M` for everything:

- **Unwrapped length** `|u|_G` — total primitive count after recursively expanding all
  references. Primitives have `|u|_G = 1`, and for a non-primitive with weighted edges
  `w_1,…,w_k` to `v_1,…,v_k`:

  ```
  |u|_G = Σ w_i · |v_i|_G
  ```

  This is a **weighted** sum. The largest Mathlib element reaches about `10^104` primitives.

- **Wrapped length** — the **token count** of the element's Lean source, as produced by the Lean
  parser. Corresponds to `|u|_{G'\{u}}`.

  The paper explicitly *rejects* the obvious alternative (counting outgoing edge weights, i.e.
  references in the internal representation): tactics like `simp` and `rw` elaborate into many
  internal references, inflating the count without introducing depth, and producing a spurious
  plateau in the compression curve that reflects proof automation rather than mathematics. A
  tactic invocation is one token regardless. Internally generated elements with no human-written
  source are omitted when reporting wrapped lengths.

- **Depth** — length of the **longest** path to primitives in the DAG. Primitives have depth 0.

### Empirical findings on Mathlib

- `log₂(unwrapped)` grows **linearly with depth**, slope ≈ 1 bit per level.
- **Wrapped length is roughly constant across depths.**
- `log₂(unwrapped)` grows linearly with wrapped length, slope ≈ 0.4 bits per token.

### The two compression ratios (§"Application and Outlook")

For an element with signature `S` and body `B`:

- **Reductive compression** ("taste"):
  `T₀(u) = (|S|_G + |B|_G) / (|S|_{G'\{u}} + |B|_{G'\{u}})` — unwrapped over wrapped.
- **Deductive compression** ("interest"):
  `I₀(u) = |B|_{G'\{u}} / |S|_{G'\{u}}` — wrapped body over wrapped signature. Elements without
  bodies have `I₀ = 0`.

The paper is candid that `I₀` **can be gamed**: it cites Pudlák on `k`-consistency and notes that
taking `k = BB(n)` yields a family with enormous `I₀` that few would call interesting.

### PageRank-style refinement (§"A PageRank-style refinement")

- A plain random walk on the DAG accumulates at primitives, which are exactly the uninteresting
  sinks. The fix is teleportation.
- They propose **biasing teleportation toward high-compression elements** via
  `J₀ = β T₀ + (1−β) I₀` (each normalized), giving

  ```
  P(v,u) = α · w(u,v)/W(u) + (1−α) · J₀(v)/Z
  ```

  with `I₁(u) = π(u)` the stationary distribution.
- They note `α` needs tuning to avoid a trivial `π` concentrated at the axioms or at the largest
  `J₀` elements.

### Stated relevance to automated reasoning

The paper's framing is that these are *observables intrinsic to the mathematical representation*
that might give an agent "a sense of direction" — tracking average `T₀` to stay near human
mathematics, and using `I₁` to find "load-bearing" elements. They flag the risk that `T₀` biases
an agent toward abstraction for its own sake, and that proposing new definitions on the fly is
computationally expensive.

### What the paper does *not* claim

- It does not define "reductive/deductive compression" for anything other than a fixed set of
  definitions.
- It offers no retrieval system, no research-status semantics, and no evaluation of agent
  performance. The application section is explicitly an outlook.

---

## Part 2 — our adaptation, and why

EOC is not Mathlib, and several choices had to change.

| | Mathlib (paper) | EOC (here) | why |
|---|---|---|---|
| scale | 463,661 vertices | ~10³ EOC declarations over a Mathlib substrate | statistics that are smooth at 10⁵ may be noise at 10³; we report sample sizes and refuse regressions where the data cannot support them |
| corpus role | a library, largely settled | an **active research** repository with conditional results, refuted routes and closed directions | graph centrality cannot see any of that; hence Part 3 |
| primitives | Lean core + `Sort` | **two views** — see below | inherited-from-Mathlib compression tells us little about what *this repo* contributes |
| wrapped length | token count from the Lean parser | token count over the declaration's source range, via a Lean-aware regex tokenizer | we did not reimplement the Lean parser; this is an approximation and is labelled as such everywhere, never presented as the paper's metric |
| generated elements | omitted when reporting wrapped lengths | **flagged, not dropped** (`generated: true`) | the consumer chooses; dropping silently loses auditability |
| cycles | ~60 SCC collapses | handled by the same SCC collapse, expected to be empty here | EOC has no unsafe recursion; the code still does it defensively |

### The two views (our addition, Gate 4)

- **View A — full formal.** Dependencies descend into Mathlib/core as far as extraction permits.
  Comparable in spirit to the paper's Mathlib experiment.
- **View B — EOC-relative.** Mathlib and Lean core are treated as **terminal primitives**; only
  `EOC.*` declarations are expanded recursively.

View B has no counterpart in the paper. It exists because the question *"what compression does
this repository create?"* is different from *"what compression does it inherit?"*, and for an AI
bootstrap the former is the useful one. The two are stored separately and never mixed.

> **Caveat we impose on ourselves.** In View A our sinks are Mathlib declarations *as they appear
> in EOC's dependency closure*, not Lean core. We do not rebuild Mathlib's internal graph. So
> View A is **not** the paper's Mathlib measurement and its absolute numbers are not comparable
> to the paper's; only the shape of relationships is.

---

## Part 3 — our new semantic layer

**None of this is in Aksenov et al., and none of it should be attributed to them.**

The dependency graph is blind to everything that matters most in a research repository. It cannot
distinguish a foundational theorem from a refuted conjecture, cannot see that two results are the
same result in different coordinates, and has no notion of a frontier. A declaration that closed
a research route may have *low* centrality precisely because the route was abandoned — and that
is exactly the declaration a returning researcher most needs to see.

So we add, as a separate graph with its own provenance requirement:

- **proof-status labels** — `FOUNDATIONAL`, `MAJOR_REDUCTION`, `CURRENT_FRONTIER`,
  `CONDITIONAL_FOUNDATION`, `EQUIVALENCE`, `BOTTLENECK`, `CLOSED_ROUTE`, `REFUTED_ROUTE`,
  `COMPUTATIONAL_ONLY`, `HEURISTIC`;
- **conditional assumptions** — which results hold only under Curry, and which are unconditional;
- **relations** — `IMPLIES`, `EQUIVALENT_TO`, `REDUCES_TO`, `CONDITIONAL_ON`, `BLOCKED_BY`,
  `REFUTES`, `CLOSES_ROUTE`, `SUPERSEDES`, `FORMALIZES`, `SUPPORTS_COMPUTATIONALLY`;
- **closed routes and refuted hypotheses**, each with the reason and a source pointer;
- **the current frontier**;
- **historical persistence** from git, kept as a *separate signal* and never conflated with
  centrality;
- **query-specific expansion** — the retrieval layer.

**Provenance rule.** Every semantic node and edge carries a `source` pointing at a Lean
declaration, a documentation file and section, or a commit. An interpretation without provenance
does not enter the graph. This is the safeguard against a generated summary hardening into
repository fact.

### The one methodological borrowing we consider load-bearing

The paper's observation that a *plain* random walk drains into the sinks, and that the fix is
**biased teleportation**, transfers directly: in EOC a plain walk drains into Mathlib. Our
retrieval biases toward semantically-labelled nodes rather than toward high-compression ones —
a different bias, same structural reason.

---

## Honest limitations

1. **Wrapped length is approximate** (regex tokenizer, not the Lean parser). Reported as
   `wrapped_tokens_approx` everywhere.
2. **View A is not the paper's Mathlib experiment** and its numbers are not comparable.
3. **Small-`n` statistics.** With ~10³ nodes we report distributions and refuse slopes that the
   sample cannot support.
4. **Resemblance is not validation.** If our plots look like the paper's, that says something
   about dependency graphs, and **nothing** about whether EOC's mathematics is correct or its
   research directions are sound.
5. `I₀` is gameable by the paper's own argument; in a repository where many declarations are
   small conditional lemmas, we treat it as one visible component, never as a verdict.
