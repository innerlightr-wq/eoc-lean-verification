"""Semantic research layer: load and validate the curated research graph.

This is OUR extension, not part of Aksenov et al. See docs/AKSENOV_METHOD_NOTES.md
Part 3.

The dependency graph cannot see research status. A declaration that closed a
route may have low centrality precisely because the route was abandoned -- and
that is exactly what a returning researcher needs first. So status, relations and
frontier live in a hand-curated graph with a hard provenance requirement.

Invariant enforced here: every node and edge carries `source`, and every source
must resolve to a real file (and, for Lean sources, a real declaration in
formal_graph.json). `validate()` fails loudly otherwise. An interpretation
without provenance never becomes repository fact.
"""
from __future__ import annotations

import json
from pathlib import Path

STATUS_LABELS = {
    "FOUNDATIONAL", "MAJOR_REDUCTION", "CURRENT_FRONTIER", "CONDITIONAL_FOUNDATION",
    "EQUIVALENCE", "BOTTLENECK", "CLOSED_ROUTE", "REFUTED_ROUTE", "COMPUTATIONAL_ONLY",
    "HEURISTIC",
}

RELATIONS = {
    "DEPENDS_ON", "IMPLIES", "EQUIVALENT_TO", "REDUCES_TO", "CONDITIONAL_ON",
    "BLOCKED_BY", "REFUTES", "CLOSES_ROUTE", "SUPERSEDES", "FORMALIZES",
    "SUPPORTS_COMPUTATIONALLY",
}


def load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def validate(graph: dict, repo: Path, formal: dict | None = None) -> list[str]:
    """Return a list of problems; empty means the graph is well-formed."""
    problems: list[str] = []
    ids = {n["id"] for n in graph["nodes"]}
    if len(ids) != len(graph["nodes"]):
        problems.append("duplicate node ids")

    decls = set((formal or {}).get("declarations", {}))

    def check_source(where: str, src: dict) -> None:
        if not src:
            problems.append(f"{where}: missing source (provenance is mandatory)")
            return
        f = src.get("file")
        if not f:
            problems.append(f"{where}: source has no file")
            return
        if not (repo / f).exists():
            problems.append(f"{where}: source file does not exist: {f}")
        d = src.get("declaration")
        if d and decls and d not in decls:
            problems.append(f"{where}: declaration not found in formal graph: {d}")

    for n in graph["nodes"]:
        if n.get("status") not in STATUS_LABELS:
            problems.append(f"node {n['id']}: bad status {n.get('status')!r}")
        check_source(f"node {n['id']}", n.get("source", {}))

    for e in graph["edges"]:
        if e.get("relation") not in RELATIONS:
            problems.append(f"edge {e.get('from')}->{e.get('to')}: bad relation {e.get('relation')!r}")
        for side in ("from", "to"):
            if e.get(side) not in ids:
                problems.append(f"edge: unknown node id {e.get(side)!r}")
        check_source(f"edge {e.get('from')}->{e.get('to')}", e.get("source", {}))
    return problems
