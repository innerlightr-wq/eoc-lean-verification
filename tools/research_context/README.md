# `tools/research_context` — compression-guided research index

Start an EOC research session from a compressed, historically informed map of the repository, and
descend into Lean modules, proofs and old audits **only when the question requires it**.

```
research question
   -> compressed repository map
   -> historically important nodes
   -> current frontier
   -> small relevant context packet
   -> deeper expansion only if necessary
```

## Usage

```bash
# 1. extract the declaration-level dependency graph from Lean's elaborated environment
lake env lean tools/research_context/lean/ExtractDeps.lean > research-index/raw_decls.jsonl

# 2. build the inventory and the formal graph (no network, no model)
python3 -m tools.research_context build

# 3. check that every semantic claim still resolves to real primary evidence
python3 -m tools.research_context validate

# 4. regenerate the compressed entry point
python3 -m tools.research_context bootstrap

# 5. ask a question
python3 -m tools.research_context query -q "Can deficit growth force unbounded prefix realizers?"

# extras
python3 -m tools.research_context stats    # Aksenov-style summary numbers
python3 -m tools.research_context plots    # exploratory SVG figures
```

Steps 1–2 are the only expensive ones and need a built `EOC` library. Everything else is instant.

## What is produced

| file | what it is |
|---|---|
| `research-index/repo_inventory.json` | modules, lines, imports, per-file git history. No importance scores. |
| `research-index/formal_graph.json` | every EOC declaration: dependencies, reverse dependencies, depth, unwrapped length, approximate wrapped tokens, `T0`, `I0`, PageRank — in **two views** |
| `research-index/research_graph.json` | the semantic layer: status labels, relations, closed routes, frontier. **Hand-curated, provenance-enforced.** |
| `research-index/AI_RESEARCH_BOOTSTRAP.md` | ~1,200 words: spine, conditional foundations, frontier, equivalences, closed routes, protocol |
| `research-index/research_protocol.md` | screening gates, including the coordinate-change gate |
| `research-index/benchmarks/` | retrieval evaluation against five historical questions |
| `research-index/plots/` | exploratory SVG figures + `plot_stats.json` |

## Two dependency views

- **View A — full formal.** Expansion descends into the Mathlib/core closure that EOC actually
  touches. Comparable in spirit to the paper's Mathlib experiment, though **not** the same
  measurement: our sinks are where our extracted closure ends.
- **View B — EOC-relative.** Mathlib and Lean core are terminal primitives; only `EOC.*`
  expands. This measures compression *this repository creates* rather than compression it
  inherits, and it is the view the retrieval layer uses.

Stored separately, never mixed.

## Design constraints

- **Auditable, not opaque.** No embeddings in v1. Ranking components are printed alongside every
  result so a reader can see why something ranked where it did, and overrule it.
- **Provenance is mandatory.** Every semantic node and edge carries a source that must resolve to
  a real file, and for Lean sources to a real declaration in `formal_graph.json`. `validate`
  fails loudly otherwise. A generated interpretation never becomes repository fact.
- **Standard library only.** No numpy, no matplotlib, no NetworkX. Plots are hand-rendered SVG,
  which is also diffable in git. Adding a plotting stack to a Lean repository for five
  exploratory scatters would not have been justified.
- **Rebuilding the formal graph requires no model.** Only Lean and Python.
- **The index is not evidence.** Compression decides *what to read*, never *what is true*.

## Attribution

The formal dependency-compression component of this project is inspired by and adapted from
Aksenov, Bodnia, Freedman, and Mulligan, "Compression is all you need: Modeling Mathematics,"
arXiv:2603.20396 (2026), DOI 10.48550/arXiv.2603.20396, licensed CC BY 4.0.

This project extends that framework with EOC-specific research-status metadata, historical route
tracking, semantic equivalence/implication relations, frontier-aware retrieval, and AI context
generation. These extensions are not claims of the original authors.

The paper's metadata and licence were verified directly before this text was written: the arXiv
API returns the four authors and a 2026-03-20 submission date for `2603.20396`, and the DataCite
record for `10.48550/arXiv.2603.20396` carries `rightsIdentifier: cc-by-4.0`. **The authors have
no connection to this project and have not reviewed or endorsed it.**

A detailed separation of their methodology from our additions is in
[`docs/AKSENOV_METHOD_NOTES.md`](../../docs/AKSENOV_METHOD_NOTES.md).

## Known limitations

1. `wrapped_tokens_approx` is a regex tokenizer over the declaration's source range, **not** the
   Lean parser. Named `_approx` everywhere; never presented as the paper's metric.
2. The signature/body split used for `I0` is heuristic (first top-level `:=` or `by`).
3. View A is not the paper's Mathlib measurement; absolute numbers are not comparable.
4. The semantic layer is hand-curated and will drift as the repository moves. Re-run `validate`
   after any refactor; it catches renamed or deleted declarations, not stale prose.
5. Retrieval is lexical with a small hand-written synonym map. It will miss a question phrased
   entirely in vocabulary the repository does not use — see the failure-modes section of
   `docs/COMPRESSION_GUIDED_CONTEXT_REPORT.md`.
