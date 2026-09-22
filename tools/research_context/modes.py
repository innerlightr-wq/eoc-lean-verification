"""Retrieval-mode definitions for the ablation study.

Gates 3 and 9. Each mode fixes every other behaviour and varies only which
signals may enter a score, so a difference in results is attributable.

A note on fairness, because it decides whether the ablation means anything.
At the MVP baseline the Aksenov metrics could only ever influence the ordering
of the *formal declaration table*; they had no route into semantic-node
ranking at all, and compression carried literally zero weight anywhere. An
ablation that inherited that wiring would compare a fully-wired semantic mode
against a barely-wired Aksenov mode and prove nothing.

So `AKSENOV` here is given a real mechanism: a semantic node whose source is a
Lean declaration inherits that declaration's centrality and compression, and
those inherited values carry scoring weight. If the metrics lose under this
wiring, they lose on the merits rather than on plumbing.

Signals:
  relevance   lexical overlap of query terms with node/declaration text
  keyword     lexical overlap with curated keywords (still lexical)
  status      research-status prior: CLOSED_ROUTE, EQUIVALENCE, ...
  centrality  J0-biased PageRank over View B, normalised
  compression log2(unwrapped)/wrapped_tokens_approx, normalised
  depth       View B dependency depth, normalised
"""
from __future__ import annotations

from dataclasses import dataclass, field


@dataclass(frozen=True)
class Mode:
    name: str
    description: str
    # semantic-node scoring
    w_relevance: float = 1.0
    w_keyword: float = 0.5
    w_status: float = 0.0
    w_node_centrality: float = 0.0
    w_node_compression: float = 0.0
    # formal-declaration scoring
    w_formal_relevance: float = 1.0
    w_formal_centrality: float = 0.0
    w_formal_compression: float = 0.0
    w_formal_depth: float = 0.0
    # presentation / behaviour
    show_semantic_layer: bool = True   # status labels, relations, provenance
    show_status_in_packet: bool = True
    tiebreak_only: bool = False        # Aksenov signals used only for near-ties
    tiebreak_epsilon: float = 0.05
    domain_guard: bool = True
    legacy_tokenizer: bool = False     # reproduce the MVP tokenizer exactly
    notes: str = ""


MODES: dict[str, Mode] = {
    "lexical": Mode(
        name="lexical",
        description="A. LEXICAL ONLY — textual query relevance, nothing else.",
        w_status=0.0,
        show_semantic_layer=False,
        show_status_in_packet=False,
        notes="Semantic nodes are still the retrieval units (they are the only "
              "prose in the index), but their research status is neither scored "
              "nor shown. This isolates lexical matching.",
    ),
    "semantic": Mode(
        name="semantic",
        description="B. LEXICAL + SEMANTIC — textual relevance plus research status, "
                    "relations, closed-route information, frontier labels, provenance. "
                    "No Aksenov compression or centrality.",
        w_status=1.0,
        show_semantic_layer=True,
        notes="Status priors as at baseline.",
    ),
    "aksenov": Mode(
        name="aksenov",
        description="C. LEXICAL + AKSENOV — textual relevance plus compression, "
                    "dependency centrality, depth and PageRank. No research-status layer.",
        w_status=0.0,
        w_node_centrality=1.0,
        w_node_compression=0.5,
        w_formal_centrality=1.0,
        w_formal_compression=0.5,
        w_formal_depth=0.25,
        show_semantic_layer=False,
        show_status_in_packet=False,
        notes="Semantic nodes inherit the centrality and compression of the Lean "
              "declaration they cite, so the formal metrics get a genuine route "
              "into node ranking rather than a crippled one.",
    ),
    "full": Mode(
        name="full",
        description="D. FULL — lexical relevance, semantic layer and Aksenov metrics.",
        w_status=1.0,
        w_node_centrality=1.0,
        w_node_compression=0.5,
        w_formal_centrality=1.0,
        w_formal_compression=0.5,
        w_formal_depth=0.25,
        show_semantic_layer=True,
        notes="Aksenov signals at the same substantial weight as in mode C.",
    ),
    "semantic_only": Mode(
        name="semantic_only",
        description="E. SEMANTIC ONLY — research status priors with no lexical relevance.",
        w_relevance=0.0,
        w_keyword=0.0,
        w_status=1.0,
        w_formal_relevance=0.0,
        show_semantic_layer=True,
        notes="Included because it is nearly free and it bounds how much of mode B's "
              "performance is the status prior rather than the lexical match. "
              "Expected to be poor: with no query term it cannot discriminate.",
    ),
    "full_tiebreaker": Mode(
        name="full_tiebreaker",
        description="D'. FULL_TIEBREAKER — semantic and lexical decide; Aksenov metrics "
                    "break near-ties only.",
        w_status=1.0,
        w_node_centrality=1.0,
        w_node_compression=0.5,
        w_formal_centrality=1.0,
        w_formal_compression=0.5,
        w_formal_depth=0.25,
        show_semantic_layer=True,
        tiebreak_only=True,
        tiebreak_epsilon=0.05,
        notes="Gate 9. Primary score is relevance + keyword + status. Aksenov signals "
              "reorder only within a band of tiebreak_epsilon of each other, so they "
              "can refine an ordering but never override a clear semantic winner.",
    ),
    "baseline_mvp": Mode(
        name="baseline_mvp",
        description="The MVP wiring, reproduced exactly for regression comparison: "
                    "status priors on nodes, PageRank at 0.5 on formal declarations only, "
                    "compression unused, no domain guard.",
        w_status=1.0,
        w_formal_centrality=0.5,
        show_semantic_layer=True,
        domain_guard=False,
        legacy_tokenizer=True,
        notes="Frozen reference. Not a candidate configuration. Uses the MVP stopword "
              "list and does NOT discount generic terms, so its packets reproduce the "
              "archived baseline byte-for-byte.",
    ),
}

DEFAULT_MODE = "full_tiebreaker"
ABLATION_ORDER = ["lexical", "semantic", "aksenov", "full", "full_tiebreaker", "semantic_only"]
