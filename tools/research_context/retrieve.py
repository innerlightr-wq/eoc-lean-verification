"""Retrieval and rendering: the AI bootstrap and query-specific context packets.

Our extension, not Aksenov et al.

Design constraint carried over from the MVP: components must stay visible. A
composite score orders results, but every component that produced it is printed
alongside, so a reader can see *why* something ranked where it did and overrule
it. No embeddings -- deterministic lexical matching plus graph signals.

Two changes from the MVP:

* scoring is driven by a `Mode` (see modes.py) so configurations can be ablated
  against each other instead of one hardcoded wiring;
* a domain guard (see domain.py) runs BEFORE ranking, so a question about
  mathematics the repository has never studied is refused rather than answered
  with whatever shares a word with it.
"""
from __future__ import annotations

import re

from .domain import (GENERIC_TERMS, MVP_STOPWORDS, OOD_MESSAGE, STOPWORDS,
                     classify, repo_vocabulary)
from .modes import MODES, Mode

STOP = STOPWORDS

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

STATUS_PRIORS = {
    "CLOSED_ROUTE": 0.30, "REFUTED_ROUTE": 0.30, "EQUIVALENCE": 0.30,
    "CURRENT_FRONTIER": 0.25, "BOTTLENECK": 0.25,
    "CONDITIONAL_FOUNDATION": 0.20, "FOUNDATIONAL": 0.15,
    "MAJOR_REDUCTION": 0.15, "COMPUTATIONAL_ONLY": 0.05, "HEURISTIC": 0.05,
}


def tokenize(q: str, legacy: bool = False) -> set[str]:
    """Query terms, minus stopwords and minus topically-empty generic terms.

    Excluding GENERIC_TERMS here is the root fix for the MVP's Riemann-hypothesis
    false positive: "hypothesis" can no longer contribute relevance to anything,
    for any query, whether or not the external subject is on any list.

    `legacy=True` reproduces the MVP tokenizer exactly, for the frozen
    baseline_mvp mode only.
    """
    stop = MVP_STOPWORDS if legacy else STOP
    drop = set() if legacy else GENERIC_TERMS
    words = {w for w in re.findall(r"[A-Za-z_][A-Za-z0-9_]*", q.lower())
             if w not in stop and w not in drop}
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


def _formal_norms(decls: dict) -> dict:
    prs = [d.get("pagerank_viewB", 0.0) for d in decls.values()] or [0.0]
    depths = [d["view_B"]["depth"] for d in decls.values()] or [0]
    comps = [d["view_B"]["unwrapped"]["log2"] / (d["wrapped_tokens_approx"] or 1)
             for d in decls.values()] or [0.0]
    return {"pr_max": max(prs) or 1.0,
            "depth_max": max(depths) or 1,
            "comp_max": max(comps) or 1.0}


def score_semantic(nodes: list[dict], query: str, mode: Mode, decls: dict) -> list[dict]:
    """Rank semantic nodes. Components are returned, never collapsed away."""
    qt = tokenize(query, mode.legacy_tokenizer)
    norms = _formal_norms(decls) if decls else {"pr_max": 1.0, "depth_max": 1, "comp_max": 1.0}
    out = []
    for n in nodes:
        text = _text_of(n)
        toks = set(re.findall(r"[a-z_][a-z0-9_]*", text))
        hits = qt & toks
        kw = {k.lower() for k in n.get("keywords", [])}
        kw_hits = qt & kw
        relevance = len(hits) / (len(qt) or 1)
        kw_bonus = len(kw_hits) / (len(qt) or 1)
        status = n.get("status", "")
        status_prior = STATUS_PRIORS.get(status, 0.0)

        # Aksenov signals, inherited from the cited Lean declaration when there
        # is one. Gives modes C/D a real route into node ranking.
        decl_name = n.get("source", {}).get("declaration")
        d = decls.get(decl_name) if decl_name else None
        centrality = compression = 0.0
        if d is not None:
            centrality = d.get("pagerank_viewB", 0.0) / norms["pr_max"]
            compression = (d["view_B"]["unwrapped"]["log2"]
                           / (d["wrapped_tokens_approx"] or 1)) / norms["comp_max"]

        primary = (mode.w_relevance * relevance
                   + mode.w_keyword * kw_bonus
                   + (mode.w_status * status_prior if (hits or kw_hits) else 0.0))
        aksenov = (mode.w_node_centrality * centrality
                   + mode.w_node_compression * compression)

        components = {
            "query_relevance": round(relevance, 4),
            "keyword_match": round(mode.w_keyword * kw_bonus, 4),
            "status_prior": round(mode.w_status * status_prior, 4) if mode.w_status else 0.0,
            "node_centrality": round(centrality, 4),
            "node_compression": round(compression, 4),
            "aksenov_contribution": round(aksenov, 4),
            "matched_terms": sorted(hits),
        }
        # In tiebreak mode the Aksenov part is not added to the score; it only
        # orders within a near-tie band (applied after sorting, below).
        composite = primary if mode.tiebreak_only else primary + aksenov
        if (primary > 0) or (mode.w_relevance == 0 and status_prior > 0):
            out.append({"node": n, "components": components,
                        "primary": round(primary, 4),
                        "aksenov": round(aksenov, 4),
                        "composite": round(composite, 4)})

    out.sort(key=lambda r: (-r["composite"], r["node"]["id"]))
    if mode.tiebreak_only:
        out = _apply_tiebreak(out, mode.tiebreak_epsilon)
    return out


def _apply_tiebreak(rows: list[dict], eps: float) -> list[dict]:
    """Reorder within bands of near-equal primary score using the Aksenov part.

    Gate 9. Groups are formed greedily over the primary-sorted list: a row joins
    the current band while it is within eps of the band's leader. Inside a band
    the Aksenov contribution decides. A clear semantic winner is never overtaken.
    """
    out: list[dict] = []
    i = 0
    while i < len(rows):
        lead = rows[i]["primary"]
        j = i
        while j < len(rows) and abs(rows[j]["primary"] - lead) <= eps:
            j += 1
        band = rows[i:j]
        if len(band) > 1:
            band = sorted(band, key=lambda r: (-r["aksenov"], -r["primary"], r["node"]["id"]))
            for r in band:
                r["tiebroken"] = True
        out.extend(band)
        i = j
    return out


def score_formal(decls: dict, query: str, mode: Mode, limit: int = 8) -> list[dict]:
    """Rank Lean declarations by lexical match plus formal signals (visible separately)."""
    qt = tokenize(query, mode.legacy_tokenizer)
    if not qt:
        return []
    if mode.w_formal_relevance == 0 and not (mode.w_formal_centrality
                                             or mode.w_formal_compression
                                             or mode.w_formal_depth):
        # semantic_only: no signal is allowed to rank declarations
        return []
    norms = _formal_norms(decls)
    rows = []
    for name, d in decls.items():
        if d.get("generated"):
            continue
        toks = set(re.findall(r"[a-z_][a-z0-9_]*", name.lower().replace(".", " ")))
        hits = qt & toks
        if not hits:
            continue
        relevance = len(hits) / len(qt)
        centrality = d.get("pagerank_viewB", 0.0) / norms["pr_max"]
        comp_raw = d["view_B"]["unwrapped"]["log2"] / (d["wrapped_tokens_approx"] or 1)
        compression = comp_raw / norms["comp_max"]
        depth_norm = d["view_B"]["depth"] / norms["depth_max"]

        primary = mode.w_formal_relevance * relevance
        aksenov = (mode.w_formal_centrality * centrality
                   + mode.w_formal_compression * compression
                   + mode.w_formal_depth * depth_norm)
        rows.append({
            "name": name,
            "module": d["module"],
            "source": d["source"],
            "components": {
                "query_relevance": round(relevance, 4),
                "formal_centrality_pagerank_norm": round(centrality, 4),
                "depth_viewB": d["view_B"]["depth"],
                "depth_norm": round(depth_norm, 4),
                "log2_unwrapped_viewB": d["view_B"]["unwrapped"]["log2"],
                "compression_bits_per_token": round(comp_raw, 4),
                "compression_norm": round(compression, 4),
                "rev_deps_eoc": len(d["rev_deps_eoc"]),
                "aksenov_contribution": round(aksenov, 4),
                "matched_terms": sorted(hits),
            },
            "primary": round(primary, 4),
            "aksenov": round(aksenov, 4),
            "composite": round(primary if mode.tiebreak_only else primary + aksenov, 4),
        })
    rows.sort(key=lambda r: (-r["composite"], r["name"]))
    if mode.tiebreak_only:
        rows = _tiebreak_formal(rows, mode.tiebreak_epsilon)
    return rows[:limit]


def _tiebreak_formal(rows: list[dict], eps: float) -> list[dict]:
    out: list[dict] = []
    i = 0
    while i < len(rows):
        lead = rows[i]["primary"]
        j = i
        while j < len(rows) and abs(rows[j]["primary"] - lead) <= eps:
            j += 1
        band = sorted(rows[i:j], key=lambda r: (-r["aksenov"], r["name"])) if j - i > 1 else rows[i:j]
        out.extend(band)
        i = j
    return out


# --------------------------------------------------------------------- packets
def retrieve(query: str, sem: dict, formal: dict, mode_name: str = "full_tiebreaker",
             limit_sem: int = 6) -> dict:
    """Run retrieval and return a structured result. Never mutates the index."""
    mode = MODES[mode_name]
    decls = formal["declarations"]
    guard = (classify(query, repo_vocabulary(sem, formal))
             if mode.domain_guard else
             {"verdict": "IN_DOMAIN", "external_subjects": [], "transfer_intent": [],
              "topical_terms": [], "generic_terms_ignored": [], "guard_disabled": True})

    if guard["verdict"] == "OUT_OF_DOMAIN":
        return {"query": query, "mode": mode_name, "guard": guard,
                "semantic": [], "formal": [], "edges": [], "refused": True}

    sr = score_semantic(sem["nodes"], query, mode, decls)[:limit_sem]
    fr = score_formal(decls, query, mode)
    ids = {r["node"]["id"] for r in sr}
    edges = [e for e in sem["edges"] if e["from"] in ids or e["to"] in ids] \
        if mode.show_semantic_layer else []
    return {"query": query, "mode": mode_name, "guard": guard,
            "semantic": sr, "formal": fr, "edges": edges, "refused": False}


def render_query_packet(query: str, sem: dict, formal: dict,
                        mode_name: str = "full_tiebreaker", limit_sem: int = 6) -> str:
    res = retrieve(query, sem, formal, mode_name, limit_sem)
    return render(res, MODES[mode_name])


def render(res: dict, mode: Mode) -> str:
    L: list[str] = []
    g = res["guard"]
    L.append(f"# Context packet — {res['query']!r}")
    L.append("")
    L.append(f"Generated by `tools/research_context` · retrieval mode `{res['mode']}`. "
             "**This is an index, not evidence.** "
             "Any claim used in a proof or a novelty assessment must be decompressed back to "
             "the cited Lean declaration or document and verified there.")
    L.append("")

    if res["refused"]:
        subj = ", ".join(g["external_subjects"])
        L.append(OOD_MESSAGE.format(subjects=subj, first=g["external_subjects"][0]))
        if g["generic_terms_ignored"]:
            L.append("")
            L.append(f"_Words ignored as topically empty: "
                     f"{', '.join(g['generic_terms_ignored'])}._")
        return "\n".join(L)

    if g["verdict"] == "TRANSFER_REQUEST":
        L.append("## Treated as a transfer request")
        L.append("")
        L.append(f"This question names mathematics outside the repository "
                 f"({', '.join(g['external_subjects'])}) and asks whether it carries over. "
                 "The repository material below is offered **as the nearest EOC-side context "
                 "for such a comparison, not as evidence that any connection exists.** "
                 "No result below mentions "
                 f"{g['external_subjects'][0]}; the analogy is yours to justify.")
        L.append("")
    elif g["verdict"] == "WEAK_MATCH":
        L.append("## Weak match")
        L.append("")
        L.append("No repository vocabulary matched this question. What follows may be "
                 "irrelevant; consider that the question may be outside what this "
                 "repository has studied.")
        L.append("")

    sr, fr = res["semantic"], res["formal"]
    if not sr:
        L.append("_No semantic node matched. Falling back to formal declarations only; "
                 "consider that the question may be outside what this repository has studied._")
        L.append("")
    else:
        L.append("## Most relevant research nodes")
        L.append("")
        for r in sr:
            n, c = r["node"], r["components"]
            head = f"### {n['title']}"
            if mode.show_status_in_packet:
                head += f"  ·  `{n['status']}`"
            L.append(head)
            L.append("")
            L.append(n["summary"])
            src = n["source"]
            loc = src["file"] + (f" · `{src['declaration']}`" if src.get("declaration") else "")
            if src.get("section"):
                loc += f" · {src['section']}"
            L.append("")
            L.append(f"- **source:** {loc}")
            bits = [f"relevance {c['query_relevance']}", f"keyword {c['keyword_match']}"]
            if mode.w_status:
                bits.append(f"status prior {c['status_prior']}")
            if mode.w_node_centrality or mode.w_node_compression:
                bits.append(f"centrality {c['node_centrality']}")
                bits.append(f"compression {c['node_compression']}")
            line = f"- **score {r['composite']}** = " + " + ".join(bits)
            if mode.tiebreak_only:
                line += (f" · primary {r['primary']}, aksenov {r['aksenov']}"
                         + (" (tiebroken)" if r.get("tiebroken") else ""))
            if c["matched_terms"]:
                line += f" · matched {', '.join(c['matched_terms'])}"
            L.append(line)
            L.append("")
    if res["edges"]:
        L.append("## Relations touching these nodes")
        L.append("")
        for e in res["edges"][:12]:
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
