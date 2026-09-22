"""CLI for the compression-guided research index.

    python3 -m tools.research_context build       # rebuild inventory + formal graph
    python3 -m tools.research_context validate    # check semantic-graph provenance
    python3 -m tools.research_context bootstrap   # write AI_RESEARCH_BOOTSTRAP.md
    python3 -m tools.research_context query -q "..."   # question-specific packet
    python3 -m tools.research_context stats       # Aksenov-style summary numbers

`build` consumes research-index/raw_decls.jsonl, produced by

    lake env lean tools/research_context/lean/ExtractDeps.lean \
      > research-index/raw_decls.jsonl

Rebuilding the formal graph requires no network and no model.
"""
from __future__ import annotations

import argparse
import json
import statistics
import sys
from pathlib import Path

from . import formal, plots, retrieve, semantic

REPO = Path(__file__).resolve().parents[2]
IDX = REPO / "research-index"


def _write(path: Path, obj) -> None:
    path = path if path.is_absolute() else (Path.cwd() / path)
    path.parent.mkdir(parents=True, exist_ok=True)
    if isinstance(obj, str):
        path.write_text(obj, encoding="utf-8")
    else:
        path.write_text(json.dumps(obj, indent=1, sort_keys=True) + "\n", encoding="utf-8")
    try:
        shown = path.resolve().relative_to(REPO)
    except ValueError:
        shown = path
    print(f"  wrote {shown}")


def cmd_build(_args) -> int:
    raw = IDX / "raw_decls.jsonl"
    if not raw.is_file():
        print("error: research-index/raw_decls.jsonl missing. Run the Lean extractor first:",
              file=sys.stderr)
        print("  lake env lean tools/research_context/lean/ExtractDeps.lean "
              "> research-index/raw_decls.jsonl", file=sys.stderr)
        return 1
    print("building inventory…")
    _write(IDX / "repo_inventory.json", formal.build_inventory(REPO))
    print("building formal dependency graph…")
    g = formal.build_graph(REPO, raw)
    _write(IDX / "formal_graph.json", g)
    t = g["totals"]
    print(f"  closure {t['closure_nodes']}, EOC declarations {t['eoc_declarations']} "
          f"({t['eoc_declarations_human']} human-written)")
    return 0


def cmd_validate(_args) -> int:
    g = json.loads((IDX / "formal_graph.json").read_text(encoding="utf-8")) \
        if (IDX / "formal_graph.json").is_file() else None
    sem = semantic.load(IDX / "research_graph.json")
    problems = semantic.validate(sem, REPO, g)
    if problems:
        print(f"PROVENANCE FAILURES ({len(problems)}):")
        for p in problems:
            print("  -", p)
        return 1
    print(f"OK — {len(sem['nodes'])} nodes, {len(sem['edges'])} edges, "
          f"every source resolves to a real file/declaration.")
    return 0


def cmd_stats(_args) -> int:
    g = json.loads((IDX / "formal_graph.json").read_text(encoding="utf-8"))
    d = [x for x in g["declarations"].values() if not x["generated"]]
    if not d:
        print("no human-written declarations found")
        return 1

    def summ(vals):
        vals = [v for v in vals if v is not None]
        if not vals:
            return "n/a"
        return (f"n={len(vals)} min={min(vals)} median={statistics.median(vals):.2f} "
                f"max={max(vals)}")

    print("Aksenov-style metrics over human-written EOC declarations")
    print("  (wrapped lengths are APPROXIMATE; see docs/AKSENOV_METHOD_NOTES.md)")
    print()
    print("  depth  (view B, EOC-relative) :", summ([x["view_B"]["depth"] for x in d]))
    print("  depth  (view A, into Mathlib) :", summ([x["view_A"]["depth"] for x in d]))
    print("  log2 unwrapped (view B)       :", summ([x["view_B"]["unwrapped"]["log2"] for x in d]))
    print("  log2 unwrapped (view A)       :", summ([x["view_A"]["unwrapped"]["log2"] for x in d]))
    print("  wrapped tokens (approx)       :", summ([x["wrapped_tokens_approx"] for x in d]))
    print("  T0 (view B)                   :", summ([x["T0_viewB"] for x in d]))
    print()
    top = sorted(d, key=lambda x: -x.get("pagerank_viewB", 0))[:10]
    print("  top 10 by J0-biased PageRank (view B):")
    for x in top:
        print(f"    {x.get('pagerank_viewB', 0):.6f}  depth={x['view_B']['depth']:2d} "
              f"revdeps={len(x['rev_deps_eoc']):3d}  {x['name']}")
    return 0


def cmd_bootstrap(_args) -> int:
    g = json.loads((IDX / "formal_graph.json").read_text(encoding="utf-8"))
    sem = semantic.load(IDX / "research_graph.json")
    _write(IDX / "AI_RESEARCH_BOOTSTRAP.md", render_bootstrap(sem, g))
    return 0


def cmd_plots(_args) -> int:
    rep = plots.generate(IDX / "formal_graph.json", IDX / "plots")
    print(f"  wrote {len(rep['figures'])} SVG figures + plot_stats.json to research-index/plots")
    for name, st in rep["figures"].items():
        print(f"    {name}: {st}")
    return 0


def cmd_query(args) -> int:
    g = json.loads((IDX / "formal_graph.json").read_text(encoding="utf-8"))
    sem = semantic.load(IDX / "research_graph.json")
    out = retrieve.render_query_packet(args.question, sem, g)
    if args.out:
        _write(Path(args.out), out)
    else:
        print(out)
    return 0


# --------------------------------------------------------------------- Gate 9
def render_bootstrap(sem: dict, g: dict) -> str:
    by_status: dict[str, list[dict]] = {}
    for n in sem["nodes"]:
        by_status.setdefault(n["status"], []).append(n)

    def block(status: str, heading: str, limit: int | None = None) -> list[str]:
        ns = by_status.get(status, [])
        if not ns:
            return []
        L = [f"## {heading}", ""]
        for n in (ns[:limit] if limit else ns):
            src = n["source"]
            loc = src["file"] + (f" · `{src['declaration']}`" if src.get("declaration") else "")
            L.append(f"- **{n['title']}** — {n['summary']}  \n  *{loc}*")
        L.append("")
        return L

    t = g["totals"]
    L = [
        "# EOC research bootstrap",
        "",
        "Compressed entry point for a researcher or AI starting a session in this repository. "
        "Generated by `tools/research_context`; every line below points at primary evidence.",
        "",
        "> **Compressed summaries guide retrieval. Claims used in a proof or a novelty "
        "assessment must be decompressed back to their primary Lean/document source and "
        "verified there.** This file is an index, never evidence.",
        "",
        "## Repository purpose",
        "",
        "Formal (Lean 4 + Mathlib) and documentary investigation of the Collatz problem via the "
        "accelerated map, aimed at excluding Type-II divergent orbits. "
        f"{t['eoc_declarations_human']} human-written declarations across "
        f"{len(set(d['module'] for d in g['declarations'].values()))} modules; "
        f"dependency closure {t['closure_nodes']} nodes.",
        "",
    ]
    L += block("FOUNDATIONAL", "Mathematical spine")
    L += block("MAJOR_REDUCTION", "Major reductions")
    L += block("CONDITIONAL_FOUNDATION", "Conditional foundations — read the hypothesis before using")
    L += block("CURRENT_FRONTIER", "Current frontier")
    L += block("BOTTLENECK", "Major bottlenecks")
    L += block("EQUIVALENCE", "Known equivalences — do not relabel these as new problems")
    L += block("CLOSED_ROUTE", "Closed routes")
    L += block("REFUTED_ROUTE", "Refuted hypotheses")
    L += block("COMPUTATIONAL_ONLY", "Computational-only results")

    L += [
        "## Research protocol",
        "",
        "Full text in `research-index/research_protocol.md`. The gate that has paid for itself "
        "twice:",
        "",
        "> Before developing a proposed quantity `X_N`, ask whether it is **independently "
        "constrained** or a **deterministic function** of data already fixed (the digit word, "
        "the orbit state). If the latter, any recurrence you derive for it will be provable by "
        "`unfold; ring`, and it restricts nothing.",
        "",
        "This is a screening heuristic, not a proof of equivalence.",
        "",
        "## Expansion instructions",
        "",
        "Do **not** read the repository breadth-first. Start here, then:",
        "",
        "- for a specific question, run "
        "`python3 -m tools.research_context query -q \"…\"` and open only what it names;",
        "- for the formal shape of a result, open the declaration cited above and read its "
        "statement, not its proof;",
        "- for research status and non-claims, `docs/RESEARCH_STATUS.md` and the `## Non-claims` "
        "section of the relevant audit;",
        "- for what has already been ruled out, "
        "`docs/ZERO_CORRIDOR_REALIZABILITY_FRONTIER.md` §27 and §28;",
        "- `research-index/formal_graph.json` has file and line for every declaration.",
        "",
        "## What this index cannot tell you",
        "",
        "- whether a proof is *correct* — only Lean's kernel does that;",
        "- whether a documented status is still accurate if the docs have drifted;",
        "- anything about routes nobody wrote down. Absence here is not evidence of absence.",
        "",
    ]
    return "\n".join(L)


def main(argv=None) -> int:
    p = argparse.ArgumentParser(prog="tools.research_context",
                                description="Compression-guided research index for the EOC repository")
    sub = p.add_subparsers(dest="cmd", required=True)
    sub.add_parser("build", help="rebuild inventory and formal graph").set_defaults(fn=cmd_build)
    sub.add_parser("validate", help="check semantic-graph provenance").set_defaults(fn=cmd_validate)
    sub.add_parser("bootstrap", help="write AI_RESEARCH_BOOTSTRAP.md").set_defaults(fn=cmd_bootstrap)
    sub.add_parser("stats", help="Aksenov-style summary numbers").set_defaults(fn=cmd_stats)
    sub.add_parser("plots", help="Aksenov-style exploratory SVG plots").set_defaults(fn=cmd_plots)
    q = sub.add_parser("query", help="question-specific context packet")
    q.add_argument("-q", "--question", required=True)
    q.add_argument("--out", default=None)
    q.set_defaults(fn=cmd_query)
    args = p.parse_args(argv)
    return args.fn(args)


if __name__ == "__main__":
    raise SystemExit(main())
