# Compression-guided research index — MVP report

Prototype letting a researcher or AI begin an EOC session from a compressed, historically
informed map of the repository, descending into Lean modules and old audits only when the
question requires it.

Built on branch `compression-guided-research-index` from `1d087e2`.

---

## A. Starting state

Branch `dynamic-deficit-feedback`, commit `1d087e2` — verified to exist, with `9435bca`
(ZCRE realizer growth), `2c6e790` and `5db34a5` (Curry foundation) confirmed as ancestors.

The main checkout was on `research-sparse-visits-2026-09-16` with **53 dirty and untracked
files**. It was not touched. All work was done in an isolated `git worktree`, sharing the
Mathlib package directory by symlink (read-only) so no rebuild of Mathlib was needed. `main` was
not modified.

## B. Aksenov methodology — what was reproduced faithfully

Source read in full from the arXiv `.tex`, not from the abstract.

- **Dependency extraction.** `collectElems` reimplemented exactly: recursive traversal of each
  declaration's signature and body, collecting every `.const` node with multiplicity, `.sort`
  folded into a synthetic `Sort` primitive. Edges point toward dependencies and carry reference
  counts as weights.
- **Unwrapped length**, weighted: `|u|_G = Σ wᵢ·|vᵢ|_G`, primitives 1.
- **Depth**: longest path to primitives, primitives 0.
- **Wrapped length as token count, not reference count.** The paper explicitly rejects reference
  counts because `simp`/`rw` inflate them without adding depth; we followed that reasoning.
- **SCC collapse** before analysis (the paper collapses ~60 unsafe-recursion pairs).
- **`T₀` reductive and `I₀` deductive compression**, and **`J₀`-biased-teleportation PageRank**
  with `P(v,u) = α·w(u,v)/W(u) + (1−α)·J₀(v)/Z`.

## C. Adaptations, and why

| | paper | here | reason |
|---|---|---|---|
| scale | 463,661 vertices | 7,409-node closure, 3,626 EOC declarations, **1,688 human-written** | smooth statistics at 10⁵ are noisy at 10³; slopes are refused where the sample cannot support them |
| wrapped length | Lean parser token count | regex tokenizer over the declaration source range, named `wrapped_tokens_approx` | we did not reimplement the parser; the approximation is labelled everywhere and never presented as theirs |
| `S`/`B` split | from the elaborated parts | signature/body **reference vectors exact** (kept separate in the extractor); the *token* split is heuristic (first top-level `:=` or `by`) | `T₀`'s numerator is exact; `I₀`'s ratio is approximate |
| generated declarations | omitted when reporting wrapped lengths | **flagged, not dropped** (`generated: true`) | consumer chooses; silent dropping loses auditability. 1,938 of 3,626 are generated |
| primitives | Lean core + `Sort` | **two views** (§F) | the question "what compression does *this repo* create" is not the paper's question |
| corpus | settled library | active research repository | dependency structure cannot see status; hence §H |

## D. Formal dependency extraction — method and validation

`tools/research_context/lean/ExtractDeps.lean` runs against the **elaborated environment**, not
textual grep, and emits newline-delimited JSON: name, module, kind, generated flag, has-body,
separate signature and body reference vectors, and source line range.

It emits the whole **closure reachable from `EOC.*`**, not just EOC declarations, so View A is a
real measurement rather than a relabelling of View B.

**A validation catch worth recording.** The first extraction run silently omitted
`EOC.CurryFoundation` and `EOC.ZCRERealizerGrowth` — the two most research-relevant modules in
the repository — because **`EOC.lean` does not import them**. `import EOC` therefore does not
put them in the environment. The extractor now imports them explicitly. Without the spot-check
(`probe for deficit_succ` → `NOT IN CLOSURE`) the whole index would have been built around a hole
exactly where the current research lives.

Other validation: `Real`, `Nat`, `Real.instAdd` and the Mathlib algebra hierarchy appear with
plausible kinds and dependency counts; 1,727 of 3,747 external nodes carry bodies, confirming the
closure genuinely expands through Mathlib proofs rather than stopping at signatures.

## E. Compression metrics — definitions and limitations

Per declaration: `view_A` and `view_B`, each with `depth` and an `unwrapped` record carrying
`bit_length`, `log2`, and the **exact big integer** when it is under 20,000 bits (with
`exact_omitted: true` otherwise — nothing is silently approximated). Plus
`wrapped_tokens_approx`, `T0_viewB`, `I0_approx`, `pagerank_viewB`, reverse dependencies.

Unwrapped length is computed **dynamically over the DAG in topological order** with Python
arbitrary-precision integers. No expanded expression is ever materialised.

Limitations: wrapped length is approximate (§C); `I₀` inherits the heuristic `S`/`B` token split;
and the paper's own warning that `I₀` is gameable applies here too, so it is exposed as a
component and never as a verdict.

## F. Full versus EOC-relative graph

The two views differ sharply, which is the main justification for keeping both:

| metric (1,688 human-written declarations) | View A (into Mathlib) | View B (EOC-relative) |
|---|---|---|
| depth — median / max | **55** / 88 | **4** / 9 |
| log2(unwrapped) — median / max | **49** / 92 | **8** / 14 |

View A's median unwrapped length is ~10¹⁵ primitives; View B's is ~256. Almost all of the
compression an EOC declaration exhibits is **inherited from Mathlib**, not created by this
repository. That is a real finding about the repository, and it is invisible if only one view is
computed.

## G. Historical-impact model — signals kept separate

No single "importance" number is presented as truth. Stored and displayed separately:

- **formal centrality** — reverse dependencies, `J₀`-biased PageRank, depth;
- **compression** — `log2_unwrapped`, bits per token, `T₀`;
- **historical persistence** — per-file first/last commit and commit count, from git, in
  `repo_inventory.json`. Deliberately *not* folded into any score: old ≠ important;
- **research significance** — the semantic layer (§H), seeded only from documentation.

**Why this separation is not academic.** `boundedPrefixRealizers_iff_positiveRealizer` — the
headline result of the previous research round — has **zero reverse dependencies** inside EOC.
It is a formal leaf. Any centrality-only ranking buries it. The same is true of every closed-route
result: a route that was abandoned has *low* centrality precisely *because* it was abandoned, and
it is exactly what a returning researcher must see first. Centrality measures load-bearing-ness in
a library; it is close to anti-correlated with "this will stop you wasting a week".

## H. Semantic research graph — relations and provenance

`research-index/research_graph.json`: **21 nodes, 19 edges**, all ten status labels available,
eleven relation types. Encodes the Curry conditional foundation and its normalization, the drift
and deficit divergence results, the ZCRE equivalence, the dynamic-feedback closure, the
`FiniteValuationWord` spine, the frontier (Population C), the Chain A bottleneck, the
`TaoMixingHypothesis` gate, five closed routes, one refuted route, and two screening gates.

**Provenance is enforced, not requested.** `validate` checks that every node and edge has a
`source`, that the file exists, and that any cited Lean declaration is present in
`formal_graph.json`. Current status: **OK — 21 nodes, 19 edges, every source resolves.**

### Two claims the brief asked for that the documentation does not support

Both are recorded in the graph's `known_gaps` rather than encoded, because encoding them would
have made a generated interpretation into repository fact:

1. **"The Pell / continued-fraction route was closed because real approximation and 2-adic/carry
   behaviour decouple."** Searching `docs/` for *Pell* returns exactly one line, in
   `ZERO_CORRIDOR_REALIZABILITY_FRONTIER.md` §27, and its stated reason is different and weaker:
   *no repository result connects these to realizability*; it "would need to be developed from
   scratch with a stated realizability connection, not assumed". No document asserts a proved
   decoupling. The node records the documented reason.
2. **"Open Problem E and its relation to a sharp Open Problem C."** Neither string occurs in any
   document at `1d087e2`. The only numbered open problem referenced is *Open Problem 12.8* of the
   occupation program, in `CURRY_FOUNDATION.md`. Nothing was encoded.

This is the provenance rule doing the job it exists for, on its first outing.

## I. AI bootstrap

`research-index/AI_RESEARCH_BOOTSTRAP.md` — **1,236 words (≈1,600–1,900 tokens)**, inside the
2,000–4,000 target. Sections: purpose, mathematical spine, major reductions, conditional
foundations, current frontier, bottlenecks, known equivalences, closed routes, refuted
hypotheses, research protocol, expansion instructions, and an explicit *what this index cannot
tell you*.

It opens and closes on the principle that compressed summaries guide retrieval while claims used
in a proof must be decompressed to primary source.

## J. Query retrieval — algorithm and transparency

Deterministic, lexical, no embeddings. Query tokens (stopworded, expanded through a small
hand-written domain synonym map) are matched against node ids, titles, summaries, keywords and
source paths. Components are **returned and printed individually**:

```
score 1.1667 = relevance 0.6667 + keyword 0.5 + status prior 0.3 · matched realizer, prefix, bounded
```

A status prior deliberately promotes `CLOSED_ROUTE`, `REFUTED_ROUTE` and `EQUIVALENCE` — the
nodes that prevent repeated work — but only when the node already matched lexically, so it can
never manufacture a match. Formal declarations are ranked separately with centrality, depth,
`log2(unwrapped)`, compression and reverse-dependency count all exposed.

## K. Historical benchmark results

Five retrospective questions, each answered from the index alone.

| # | question | packet | top node | decisive source surfaced? |
|---|---|---|---|---|
| 1 | unbounded prefix-realizer growth a weaker route? | 860 w | **Bounded prefix realizers = positive-integer realizability** `EQUIVALENCE` | ✅ `ZCRERealizerGrowth.boundedPrefixRealizers_iff_positiveRealizer` |
| 2 | deficit/state/valuation feedback constrain Type-II? | 832 w | **Dynamic deficit feedback is a reparameterization** `CLOSED_ROUTE` | ✅ `DYNAMIC_DEFICIT_FEEDBACK_AUDIT.md` §D |
| 3 | continued fractions / Pell control the denominator? | 600 w | **Pell / continued-fraction drift approximants** `CLOSED_ROUTE` | ✅ frontier doc §27, with the *documented* reason |
| 4 | current arithmetic bottleneck in Chain A? | 315 w | **PowerOfTwoDangerousWindowSparsity** `BOTTLENECK` | ✅ `ARITHMETIC_FRONTIER.md` §10, exact target not generic Collatz material |
| 5 | what does Curry contribute? | 602 w | Type-II target → **Curry normalization** `CONDITIONAL_FOUNDATION` → drift → −∞ | ✅ conditionality explicit in the label |

**5/5 surfaced the decisive source in the top three nodes**, in packets of 315–860 words. Each
question had previously consumed a full research session's worth of orientation.

Irrelevant material: modest. Test 2's packet also returns the Curry normalization and the Type-II
target — arguably context rather than noise. Test 1 returns the dynamic-feedback closure third,
which is a genuine neighbour.

This is an **initial retrieval evaluation**, not a measurement of AI efficiency (§M).

## L. Aksenov-style empirical results

1,676 human-written declarations with a usable source range (of 1,688; 12 lack one).

| figure | slope | R² | reading |
|---|---|---|---|
| `log2(unwrapped)` vs depth, **View A** | **0.906** | **0.991** | **reproduces the paper's ≈1 bit per level**, with a very tight fit |
| `log2(unwrapped)` vs depth, View B | 0.887 | 0.659 | same slope, much noisier at EOC-relative scale |
| wrapped vs depth, View B | 23.8 | **0.037** | **reproduces "wrapped length is roughly constant across depths"** — no real relationship |
| `log2(unwrapped)` vs wrapped, View B | 0.0031 | 0.125 | **does NOT reproduce** the paper's ≈0.4 bits/token |
| centrality vs compression | 0.0009 | 0.002 | no relationship |

The honest reading: **two of the paper's three Mathlib findings reproduce on EOC; one does not.**
The exponential-in-wrapped-length expansion is absent at EOC-relative scale, consistent with §F —
EOC declarations are long Lean proofs that are shallow in *EOC's own* dependency structure, so
adding tokens does not multiply EOC-relative primitive count. Whether this is a property of
research repositories generally, or of this one, cannot be decided from n=1.

Figures are hand-rendered SVG (stdlib only, diffable in git) in `research-index/plots/`, with
binned medians and per-bin `n` in `plot_stats.json`. Slopes are refused automatically below 30
points or 4 distinct x values.

**A resemblance to the paper's Mathlib plots validates nothing about EOC's mathematics.**

## M. Efficiency evidence — what can and cannot be claimed

**Can be claimed:** the index surfaced the decisive source for 5/5 historical questions in
315–860-word packets, and each packet names the exact file and declaration to open next. The
bootstrap is ~1,200 words against a repository of 30k Lean lines, 97 modules and 13 documents.

**Cannot be claimed:** that this makes an AI or a researcher faster. There is no A/B measurement,
no held-out question set, and the five benchmarks are ones whose answers were known while the
semantic graph was being written — a retrospective evaluation with obvious circularity risk. The
one genuinely blind signal is §H's two `known_gaps`: the system declined to encode two claims
supplied in the task brief, because the repository does not document them. That is evidence the
provenance gate works, not evidence of retrieval speed.

A real evaluation needs questions written *before* the graph, by someone who did not build it.

## N. Failure modes — what compression could hide or distort

Tested, not hypothesised.

1. **Common-word false positives.** *"Does the Riemann hypothesis imply anything here?"* returns
   the Tao and Curry **hypothesis** nodes. One shared common word drives it. A reader who trusted
   the ranking would think the repository had something to say about RH. It does not.
2. **Graceful miss (good).** *"What about modular forms and elliptic curves?"* returns
   *"No semantic node matched … consider that the question may be outside what this repository
   has studied."* — the desired behaviour.
3. **Absence is not evidence of absence.** The semantic graph covers what the documents record. A
   route explored and abandoned without being written down is invisible, and the bootstrap says so.
4. **Staleness.** `validate` catches renamed or deleted declarations. It cannot catch prose that
   has drifted from the mathematics. A `CURRENT_FRONTIER` label is only as fresh as its document.
5. **Centrality is close to anti-correlated with research salience** (§G). Any future attempt to
   collapse the components into one score risks reintroducing exactly the bias the separation
   avoids.
6. **The hole that nearly happened.** §D: two modules missing from the environment produced a
   silently plausible index. Compression makes such holes *harder* to notice, not easier. The
   spot-check that caught it should become a permanent part of `build`.

## O. Attribution and licence

> The formal dependency-compression component of this project is inspired by and adapted from
> Aksenov, Bodnia, Freedman, and Mulligan, "Compression is all you need: Modeling Mathematics,"
> arXiv:2603.20396 (2026), DOI 10.48550/arXiv.2603.20396, licensed CC BY 4.0.
>
> This project extends that framework with EOC-specific research-status metadata, historical
> route tracking, semantic equivalence/implication relations, frontier-aware retrieval, and AI
> context generation. These extensions are not claims of the original authors.

Verified before writing: the arXiv API returns the four authors and a 2026-03-20 submission for
`2603.20396`; DataCite gives `rightsIdentifier: cc-by-4.0` for `10.48550/arXiv.2603.20396`. No
substantial portion of the paper is reproduced. **The authors have no connection to this project
and have not reviewed or endorsed it.**

## P. Files changed

```
docs/AKSENOV_METHOD_NOTES.md                       new
docs/COMPRESSION_GUIDED_CONTEXT_REPORT.md          new  (this file)
tools/__init__.py                                  new
tools/research_context/__init__.py                 new
tools/research_context/__main__.py                 new  CLI
tools/research_context/formal.py                   new  inventory, graph, metrics
tools/research_context/semantic.py                 new  semantic layer + provenance validation
tools/research_context/retrieve.py                 new  ranking and packet rendering
tools/research_context/plots.py                    new  stdlib SVG figures
tools/research_context/README.md                   new  usage + attribution
tools/research_context/lean/ExtractDeps.lean       new  Lean environment extraction
.gitignore                                    modified  ignore raw_decls.jsonl
research-index/repo_inventory.json                 new
research-index/formal_graph.json                   new
research-index/research_graph.json                 new  hand-curated
research-index/research_protocol.md                new
research-index/AI_RESEARCH_BOOTSTRAP.md            new  generated
research-index/benchmarks/test1..5.md              new  generated
research-index/plots/*.svg, plot_stats.json        new  generated
```

**No Lean mathematics was modified.** No theorem statement, proof or existing module was touched;
the only Lean file added is an extraction helper that proves nothing. The sole change to an
existing file is one `.gitignore` entry.

**On versioning generated artifacts.** `formal_graph.json` (4.4 MB) *is* committed, because every
command except `build` reads it, so a fresh clone can run `validate`, `query`, `bootstrap`,
`stats` and `plots` with no Lean build at all — verified by moving the intermediate aside and
re-running them. `raw_decls.jsonl` (3.1 MB) is **not** committed: it is a pure intermediate, it
regenerates from the single `lake env lean` command recorded in `.gitignore` and the README, and
versioning it would add a fresh multi-MB blob on every rebuild. `build` fails with that exact
command when it is absent. This is a real 4.4 MB cost to the repository, accepted deliberately;
if it proves unwelcome, dropping `formal_graph.json` too costs a Lean build per clone.

## Q. Tests and builds

| command | result |
|---|---|
| `lake build EOC` | success, 96 modules |
| `lake build EOC.CurryFoundation EOC.ZCRERealizerGrowth` | success, 2051 jobs |
| `lake env lean tools/research_context/lean/ExtractDeps.lean` | exit 0; 3,626 EOC seeds, 7,409-node closure |
| `python3 -m tools.research_context build` | exit 0 |
| `python3 -m tools.research_context validate` | **OK — 21 nodes, 19 edges, every source resolves** |
| `python3 -m tools.research_context bootstrap` | exit 0, 1,236 words |
| `python3 -m tools.research_context stats` | exit 0 |
| `python3 -m tools.research_context plots` | exit 0, 5 SVG + stats |
| 5 benchmark queries | exit 0, 5/5 decisive source in top three |

## R. Commits

Branch `compression-guided-research-index`, from `1d087e2`.

| commit | contents |
|---|---|
| `69417d3` | Add compression-guided research index (MVP) — tooling, formal graph, semantic graph, bootstrap, protocol, benchmarks, plots, method notes, one `.gitignore` entry |
| (this file) | the MVP report |

No commit touches a Lean theorem, proof or existing module.

## S. Push status

Branch pushed to `origin/compression-guided-research-index` and tracking. **No pull request was
opened.** `main` was not modified, and the dirty main checkout on
`research-sparse-visits-2026-09-16` (53 files) was left exactly as found — all work happened in a
separate `git worktree`.

GitHub's response offered a PR-creation URL; it was not visited.

## T. Verdict

**`USEFUL MVP — CONTINUE`.**

The success criterion was to take someone from "I know almost nothing about this repository" to
knowing its spine, conditional assumptions, closed routes, equivalences and present frontier —
plus exactly which files to open — without reading most of the repository. A 1,236-word bootstrap
plus a 315–860-word query packet does that for all five historical questions.

Two things earn the verdict beyond the retrieval numbers. The provenance gate **refused two
claims** that were handed to it and that the repository does not document (§H) — the failure mode
this design exists to prevent, caught on its first run. And the extraction spot-check found that
the two most research-relevant modules were absent from the environment (§D), which would have
produced a confidently wrong index.

Against that: the Aksenov metrics are informative about *structure* (§L) but did no work in
retrieval — every benchmark was won by the semantic layer and lexical matching, not by
compression or centrality. Centrality is in fact close to anti-correlated with research salience
here (§G). So the honest position is that the **bootstrap and semantic layer are carrying the
value**, the formal metrics are interesting context whose retrieval role is unproven, and the
efficiency claim (§M) remains unmeasured.

Next, in order: (1) a blind benchmark set written by someone who did not build the graph;
(2) fold the §D module-coverage spot-check into `build` so the hole cannot recur; (3) decide
whether the formal metrics earn their keep in retrieval at all, or are better demoted to a
structural report.
