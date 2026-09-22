# Retrieval evaluation

Measures whether each compression signal in the research index earns its place, and provides the
harness for a genuinely blind evaluation later.

Full findings: [`docs/COMPRESSION_INDEX_EVALUATION.md`](../../docs/COMPRESSION_INDEX_EVALUATION.md).

## Layout

| path | what it is |
|---|---|
| `baseline_manifest.json` | **frozen** pre-round state: commit, file hashes, exact retrieval settings, benchmark ids |
| `post_round_manifest.json` | state after the round, and the 4-declaration delta with its cause |
| `regression/questions.json` | the original five questions — **contaminated, regression-only** |
| `regression/baseline/` | their packets as of commit `6b59fd6`, byte-frozen |
| `ood/questions.json` | 18 adversarial out-of-domain, transfer and control questions |
| `ablation/regression/`, `ablation/ood/` | per-mode packets and scores |

## Running it

```bash
# one mode
python3 -m tools.research_context evaluate \
  --questions research-index/evaluation/ood/questions.json --mode semantic

# every mode in the ablation
python3 -m tools.research_context evaluate \
  --questions research-index/evaluation/regression/questions.json \
  --mode all --out research-index/evaluation/ablation/regression
```

Modes: `lexical`, `semantic`, `aksenov`, `full`, `full_tiebreaker`, `semantic_only`, and
`baseline_mvp` (the frozen MVP wiring, kept only for comparison). Definitions in
`tools/research_context/modes.py`.

**Evaluation never mutates the index.** It reads `formal_graph.json` and `research_graph.json`
and writes only under the directory given by `--out`; a test asserts the hashes are unchanged.

## Dropping in a blind question set

The point of the harness. Write a file in the same shape:

```json
{
  "set_id": "blind-2026-10",
  "questions": [
    {
      "id": "b01",
      "question": "...",
      "domain": "in_domain | out_of_domain | transfer",
      "expected_source_type": "lean_declaration | document | none",
      "gold_sources": ["docs/FOO.md", "EOC.Module.declaration"],
      "gold_semantic_nodes": ["node-id"],
      "notes": "..."
    }
  ]
}
```

Only `id`, `question` and `domain` are needed to *run*; the gold fields are needed only to
*score*. Nothing needs rebuilding or retuning first.

To keep the answers away from whoever runs retrieval, split the two steps:

```bash
python3 -m tools.research_context evaluate \
  --questions blind.json --mode all --out results/ --hide-gold
```

`--hide-gold` writes the packets and skips scoring. `evaluate.strip_gold()` produces a
gold-free copy of a question file for handing over. A test asserts retrieval works on a
gold-stripped question, so the gold fields cannot be silently load-bearing.

## Metrics

Recall@1/3/5 (over gold semantic nodes and over gold source files), rank of the first gold node,
rank of the first decisive source, MRR, packet word count, nodes/declarations/distinct files
returned, and irrelevant nodes ranked above gold.

Scoring depends on `domain`:

- `in_domain` — recall and ranks, as above.
- `out_of_domain` — correct iff **no misleading repository material is returned**. An explicit
  refusal and an empty result both count; ranking even one unrelated node is the failure. The
  harm being measured is a reader believing the repository addresses something it does not.
- `transfer` — correct iff the question **passes through**, labelled `TRANSFER_REQUEST`.
  Refusing a legitimate analogy question is also a failure.

## Contamination

`regression/questions.json` is marked `"contaminated": true` and carries the reason in the file.
Those five questions were known while `research_graph.json` was being written, so they can show
that behaviour has not regressed and nothing more. They cannot measure generalization, and no
result in this directory should be quoted as if they do.

`ood/questions.json` is not contaminated in the same way: the correct answer to each is a
*behaviour*, not a document the semantic graph was built around. It is still written by the same
author as the guard, which is its own limitation — it can show the guard does what it was
designed to do, not that the design anticipates what a stranger would ask.
