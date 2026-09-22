"""Evaluation harness for retrieval configurations.

Gates 5 and 6. Built so that an EXTERNAL question set can be dropped in later
without rebuilding or tuning the index, which is the only way to get a
benchmark this session has not contaminated.

Two properties matter and are enforced here:

* **The harness never mutates the index.** It opens formal_graph.json and
  research_graph.json read-only and writes only under the results directory it
  is given. Nothing it does can change a later evaluation's inputs.
* **Gold answers are hidden during retrieval.** `run_question` passes only the
  question text to the retrieval layer. Gold sources are read afterwards, by
  the scorer. A question file may also be supplied with gold fields stripped
  (`--hide-gold`), which writes the packets without scoring, so retrieval can
  be run by one party and scored by another.

Metrics: Recall@1/3/5 over gold semantic nodes and gold source files, rank of
the first decisive source, MRR, packet size, and counts of returned files and
declarations. Out-of-domain items are scored on whether the system correctly
refused rather than on recall.
"""
from __future__ import annotations

import json
import statistics
from pathlib import Path

from .modes import MODES
from .retrieve import render, retrieve


def load_questions(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _gold_hit(rank_items: list[str], gold: set[str], k: int) -> bool:
    return bool(gold) and bool(set(rank_items[:k]) & gold)


def run_question(q: dict, sem: dict, formal: dict, mode: str) -> dict:
    """Retrieve for one question. Gold fields are NOT read here."""
    res = retrieve(q["question"], sem, formal, mode)
    packet = render(res, MODES[mode])
    node_ids = [r["node"]["id"] for r in res["semantic"]]
    node_srcs = [r["node"]["source"]["file"] for r in res["semantic"]]
    decl_names = [r["name"] for r in res["formal"]]
    decl_files = [r["source"]["file"] for r in res["formal"] if r.get("source")]
    return {
        "id": q["id"],
        "question": q["question"],
        "mode": mode,
        "refused": res["refused"],
        "guard_verdict": res["guard"]["verdict"],
        "external_subjects": res["guard"]["external_subjects"],
        "transfer_intent": bool(res["guard"]["transfer_intent"]),
        "ranked_node_ids": node_ids,
        "ranked_node_sources": node_srcs,
        "ranked_declarations": decl_names,
        "ranked_declaration_files": decl_files,
        "packet_words": len(packet.split()),
        "n_nodes_returned": len(node_ids),
        "n_declarations_returned": len(decl_names),
        "n_distinct_files_returned": len(set(node_srcs) | set(decl_files)),
        "packet": packet,
    }


def score_question(q: dict, r: dict) -> dict:
    """Score a retrieval result against gold. Read separately from retrieval."""
    domain = q.get("domain", "in_domain")
    out: dict = {"id": q["id"], "domain": domain, "mode": r["mode"],
                 "refused": r["refused"], "guard_verdict": r["guard_verdict"]}

    if domain == "out_of_domain":
        # The harm being measured is returning misleading Collatz material, so an
        # explicit refusal and an empty result both count as correct. Ranking a
        # single unrelated node is the failure, whatever the guard label says.
        out["refused_explicitly"] = bool(r["refused"])
        out["false_positive_nodes"] = 0 if r["refused"] else r["n_nodes_returned"]
        out["correct"] = out["false_positive_nodes"] == 0
        out["expected"] = "refusal, or at minimum no ranked repository material"
        return out
    if domain == "transfer":
        # correct behaviour is to pass through, labelled, without refusing
        out["correct"] = (not r["refused"]) and r["guard_verdict"] == "TRANSFER_REQUEST"
        out["expected"] = "pass through as TRANSFER_REQUEST"
        return out

    gold_nodes = set(q.get("gold_semantic_nodes", []))
    gold_srcs = set(q.get("gold_sources", []))
    nodes = r["ranked_node_ids"]
    # a gold "source" may be a file path or a declaration name
    combined: list[str] = []
    for i, n in enumerate(nodes):
        combined.append(n)
    src_rank = [s for s in r["ranked_node_sources"]]

    for k in (1, 3, 5):
        out[f"recall_at_{k}_nodes"] = _gold_hit(nodes, gold_nodes, k)
        out[f"recall_at_{k}_sources"] = _gold_hit(src_rank, gold_srcs, k) or _gold_hit(
            r["ranked_declarations"], gold_srcs, k)

    rank = None
    for i, n in enumerate(nodes, 1):
        if n in gold_nodes:
            rank = i
            break
    out["rank_of_first_gold_node"] = rank
    out["mrr_nodes"] = round(1.0 / rank, 4) if rank else 0.0

    # rank of the first decisive SOURCE (file or declaration), whichever comes first
    srank = None
    for i, s in enumerate(src_rank, 1):
        if s in gold_srcs:
            srank = i
            break
    if srank is None:
        for i, d in enumerate(r["ranked_declarations"], 1):
            if d in gold_srcs:
                srank = i
                break
    out["rank_of_first_decisive_source"] = srank

    out["irrelevant_nodes_above_gold"] = (rank - 1) if rank else r["n_nodes_returned"]
    out["packet_words"] = r["packet_words"]
    out["n_nodes_returned"] = r["n_nodes_returned"]
    out["n_declarations_returned"] = r["n_declarations_returned"]
    out["n_distinct_files_returned"] = r["n_distinct_files_returned"]
    return out


def evaluate(questions: dict, sem: dict, formal: dict, mode: str,
             outdir: Path | None = None, hide_gold: bool = False) -> dict:
    results, scores = [], []
    for q in questions["questions"]:
        r = run_question(q, sem, formal, mode)
        results.append(r)
        if not hide_gold:
            scores.append(score_question(q, r))
        if outdir:
            d = outdir / mode
            d.mkdir(parents=True, exist_ok=True)
            (d / f"{q['id']}.md").write_text(r["packet"], encoding="utf-8")

    summary = aggregate(scores, mode) if not hide_gold else {
        "mode": mode, "hidden_gold": True,
        "note": "packets written; scoring deferred to whoever holds the gold answers"}
    return {"mode": mode, "set_id": questions.get("set_id"),
            "results": [{k: v for k, v in r.items() if k != "packet"} for r in results],
            "scores": scores, "summary": summary}


def aggregate(scores: list[dict], mode: str) -> dict:
    ind = [s for s in scores if s["domain"] == "in_domain"]
    ood = [s for s in scores if s["domain"] == "out_of_domain"]
    tra = [s for s in scores if s["domain"] == "transfer"]
    s: dict = {"mode": mode, "n_in_domain": len(ind),
               "n_out_of_domain": len(ood), "n_transfer": len(tra)}
    if ind:
        for k in (1, 3, 5):
            s[f"recall_at_{k}_nodes"] = round(
                sum(x[f"recall_at_{k}_nodes"] for x in ind) / len(ind), 4)
            s[f"recall_at_{k}_sources"] = round(
                sum(x[f"recall_at_{k}_sources"] for x in ind) / len(ind), 4)
        ranks = [x["rank_of_first_gold_node"] for x in ind if x["rank_of_first_gold_node"]]
        s["mean_rank_of_first_gold_node"] = round(statistics.fmean(ranks), 3) if ranks else None
        s["mrr_nodes"] = round(statistics.fmean([x["mrr_nodes"] for x in ind]), 4)
        s["mean_packet_words"] = round(statistics.fmean([x["packet_words"] for x in ind]), 1)
        s["mean_irrelevant_above_gold"] = round(
            statistics.fmean([x["irrelevant_nodes_above_gold"] for x in ind]), 3)
        s["n_gold_never_returned"] = sum(
            1 for x in ind if x["rank_of_first_gold_node"] is None)
    if ood:
        s["ood_no_misleading_material"] = sum(1 for x in ood if x["correct"])
        s["ood_explicit_refusals"] = sum(1 for x in ood if x.get("refused_explicitly"))
        s["ood_false_positives"] = sum(1 for x in ood if not x["correct"])
        s["ood_false_positive_nodes_total"] = sum(x["false_positive_nodes"] for x in ood)
        s["ood_accuracy"] = round(s["ood_no_misleading_material"] / len(ood), 4)
    if tra:
        s["transfer_correct_passthrough"] = sum(1 for x in tra if x["correct"])
        s["transfer_accuracy"] = round(s["transfer_correct_passthrough"] / len(tra), 4)
    return s


def strip_gold(questions: dict) -> dict:
    """Produce a gold-free copy, for handing retrieval to a party that must not see answers."""
    out = json.loads(json.dumps(questions))
    for q in out["questions"]:
        for k in ("gold_sources", "gold_semantic_nodes", "notes"):
            q.pop(k, None)
    out["gold_hidden"] = True
    return out
