"""Retrieval and rendering: the AI bootstrap and query-specific context packets.

Gates 9, 10 and 11. Our extension, not Aksenov et al.

Design constraint from the brief: components must stay visible. A composite
score is offered for ordering, but every component that produced it is printed
alongside, so a reader can see *why* something ranked where it did and overrule
it. No embeddings in v1 -- deterministic lexical matching plus graph signals.
"""
from __future__ import annotations

import math
import re
from collections import Counter

STOP = {
    "the", "a", "an", "of", "to", "in", "is", "are", "can", "does", "do", "for",
    "and", "or", "on", "by", "with", "what", "which", "that", "this", "it", "as",
    "be", "from", "at", "any", "all", "we", "our", "if", "not", "no", "there",
    "current", "about", "how", "why", "when",
}

# light domain synonymy: the vocabulary of the repository is small and stable,
# so a hand-written map beats an embedding here and stays inspectable
SYNONYMS = {
    "realizer": {"realizer", "realizers", "realizability", "realize", "realizable"},
    "deficit": {"deficit", "corridor", "drift"},
    "valuation": {"valuation", "digit", "nu2", "v2"},
    "divergence": {"divergence", "divergent", "type-ii", "typeii", "escape"},
    "curry": {"curry", "reciprocal", "summable"},
    "bottleneck": {"bottleneck", "blocked", "obstruction", "stuck", "hard"},
    "closed": {"closed", "dead", "refuted", "abandoned", "ruled"},
    "pell": {"pell", "continued", "fraction", "diophantine", "approximation"},
    "chain": {"chain", "fourier", "dangerous", "window", "sparsity", "tao"},
    "frontier": {"frontier", "open", "unresolved", "remaining"},
    "feedback": {"feedback", "dynamic", "loop", "coordinate", "reparameterization"},
    "prefix": {"prefix", "bounded", "unbounded", "growth"},
}


def tokenize(q: str) -> set[str]:
    words = {w for w in re.findall(r"[A-Za-z_][A-Za-z0-9_]*", q.lower()) if w not in STOP}
    expanded = set(words)
    for key, group in SYNONYMS.items():
        if words & group:
            expanded |= {key}
    return expanded


def _text_of(node: dict) -> str:
    parts = [node.get("id", ""), node.get("title", ""), node.get("summary", ""),
             node.get("status", ""), " ".join(node.get("keywords", []))]
    src = node.get("source", {})
    parts += [src.get("file", ""), src.get("declaration", "") or ""]
    return " ".join(parts).lower()


def score_semantic(nodes: list[dict], query: str) -> list[dict]:
    """Rank semantic nodes. Components are returned, never collapsed away."""
    qt = tokenize(query)
    out = []
    for n in nodes:
        text = _text_of(n)
        toks = set(re.findall(r"[a-z_][a-z0-9_]*", text))
        hits = qt & toks
        # keyword hits are worth more than incidental prose matches
        kw = {k.lower() for k in n.get("keywords", [])}
        kw_hits = qt & kw
        relevance = len(hits) / (len(qt) or 1)
        kw_bonus = 0.5 * (len(kw_hits) / (len(qt) or 1))
        # a route that is CLOSED or an EQUIVALENCE is disproportionately useful
        # to surface early: it is what stops a researcher redoing old work
        status = n.get("status", "")
        status_prior = {
            "CLOSED_ROUTE": 0.30, "REFUTED_ROUTE": 0.30, "EQUIVALENCE": 0.30,
            "CURRENT_FRONTIER": 0.25, "BOTTLENECK": 0.25,
            "CONDITIONAL_FOUNDATION": 0.20, "FOUNDATIONAL": 0.15,
            "MAJOR_REDUCTION": 0.15, "COMPUTATIONAL_ONLY": 0.05, "HEURISTIC": 0.05,
        }.get(status, 0.0)
        components = {
            "query_relevance": round(relevance, 4),
            "keyword_match": round(kw_bonus, 4),
            "status_prior": status_prior,
            "matched_terms": sorted(hits),
        }
        composite = relevance + kw_bonus + (status_prior if hits or kw_hits else 0.0)
        if composite > 0:
            out.append({"node": n, "components": components, "composite": round(composite, 4)})
    out.sort(key=lambda r: (-r["composite"], r["node"]["id"]))
    return out


def score_formal(decls: dict, query: str, limit: int = 8) -> list[dict]:
    """Rank Lean declarations by lexical match plus formal signals (visible separately)."""
    qt = tokenize(query)
    if not qt:
        return []
    prs = [d.get("pagerank_viewB", 0.0) for d in decls.values()] or [0.0]
    pr_max = max(prs) or 1.0
    depths = [d["view_B"]["depth"] for d in decls.values()] or [0]
    depth_max = max(depths) or 1
    rows = []
    for name, d in decls.items():
        if d.get("generated"):
            continue
        toks = set(re.findall(r"[a-z_][a-z0-9_]*", name.lower().replace(".", " ")))
        hits = qt & toks
        if not hits:
            continue
        relevance = len(hits) / len(qt)
        centrality = d.get("pagerank_viewB", 0.0) / pr_max
        compression = (d["view_B"]["unwrapped"]["log2"] / (d["wrapped_tokens_approx"] or 1))
        rows.append({
            "name": name,
            "module": d["module"],
            "source": d["source"],
            "components": {
                "query_relevance": round(relevance, 4),
                "formal_centrality_pagerank_norm": round(centrality, 4),
                "depth_viewB": d["view_B"]["depth"],
                "depth_norm": round(d["view_B"]["depth"] / depth_max, 4),
                "log2_unwrapped_viewB": d["view_B"]["unwrapped"]["log2"],
                "compression_bits_per_token": round(compression, 4),
                "rev_deps_eoc": len(d["rev_deps_eoc"]),
                "matched_terms": sorted(hits),
            },
            "composite": round(relevance + 0.5 * centrality, 4),
        })
    rows.sort(key=lambda r: (-r["composite"], r["name"]))
    return rows[:limit]


def render_query_packet(query: str, sem: dict, formal: dict, limit_sem: int = 6) -> str:
    sr = score_semantic(sem["nodes"], query)[:limit_sem]
    fr = score_formal(formal["declarations"], query)
    ids = {r["node"]["id"] for r in sr}
    rel_edges = [e for e in sem["edges"] if e["from"] in ids or e["to"] in ids]

    L: list[str] = []
    L.append(f"# Context packet — {query!r}")
    L.append("")
    L.append("Generated by `tools/research_context`. **This is an index, not evidence.** "
             "Any claim used in a proof or a novelty assessment must be decompressed back to "
             "the cited Lean declaration or document and verified there.")
    L.append("")
    if not sr:
        L.append("_No semantic node matched. Falling back to formal declarations only; "
                 "consider that the question may be outside what this repository has studied._")
        L.append("")
    else:
        L.append("## Most relevant research nodes")
        L.append("")
        for r in sr:
            n, c = r["node"], r["components"]
            L.append(f"### {n['title']}  ·  `{n['status']}`")
            L.append("")
            L.append(n["summary"])
            src = n["source"]
            loc = src["file"] + (f" · `{src['declaration']}`" if src.get("declaration") else "")
            if src.get("section"):
                loc += f" · {src['section']}"
            L.append("")
            L.append(f"- **source:** {loc}")
            L.append(f"- **score {r['composite']}** = relevance {c['query_relevance']} "
                     f"+ keyword {c['keyword_match']} + status prior {c['status_prior']}"
                     + (f" · matched {', '.join(c['matched_terms'])}" if c["matched_terms"] else ""))
            L.append("")
    if rel_edges:
        L.append("## Relations touching these nodes")
        L.append("")
        for e in rel_edges[:12]:
            L.append(f"- `{e['from']}` --**{e['relation']}**--> `{e['to']}` — {e.get('note','')} "
                     f"[{e['source']['file']}]")
        L.append("")
    if fr:
        L.append("## Formal declarations worth opening")
        L.append("")
        L.append("| declaration | module | depth | log2 unwrapped | rev-deps | why |")
        L.append("|---|---|---|---|---|---|")
        for r in fr:
            c = r["components"]
            L.append(f"| `{r['name'].split('.')[-1]}` | {r['module']} | {c['depth_viewB']} | "
                     f"{c['log2_unwrapped_viewB']} | {c['rev_deps_eoc']} | "
                     f"matched {', '.join(c['matched_terms'])} |")
        L.append("")
        L.append("Open with the file and line from `research-index/formal_graph.json`.")
        L.append("")
    L.append("## Before you proceed")
    L.append("")
    L.append("Apply the coordinate-change gate in `research-index/research_protocol.md`: "
             "if the quantity you are about to introduce is a deterministic function of the "
             "digit word or the orbit state, the recurrence you derive for it will be provable "
             "by `ring`, and it carries no new restriction.")
    return "\n".join(L)
