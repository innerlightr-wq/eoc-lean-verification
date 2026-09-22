"""Tests for the research-index hardening and retrieval modes.

    python3 -m unittest tools.research_context.tests -v

Standard library only. The negative tests matter more than the positive ones:
several reconstruct the exact MVP failure and assert that it is now caught.
Each works on a deep copy or a temporary tree, so nothing here can mutate the
real index.
"""
from __future__ import annotations

import copy
import hashlib
import json
import shutil
import tempfile
import unittest
from pathlib import Path

from . import coverage, evaluate as ev, semantic
from .domain import classify, repo_vocabulary
from .modes import ABLATION_ORDER, MODES
from .retrieve import retrieve, tokenize

REPO = Path(__file__).resolve().parents[2]
IDX = REPO / "research-index"

GRAPH = coverage.load_json(IDX / "formal_graph.json")
SEM = semantic.load(IDX / "research_graph.json")
REG = coverage.load_json(IDX / "module_registry.json")
SENT = coverage.load_json(IDX / "sentinel_declarations.json")
VOCAB = repo_vocabulary(SEM, GRAPH)

# The two modules that actually went missing in the MVP round.
MVP_CASUALTIES = ["EOC.CurryFoundation", "EOC.ZCRERealizerGrowth"]


class TestModuleCoverage(unittest.TestCase):
    def test_current_state_is_clean(self):
        errors, _ = coverage.check_modules(REPO, GRAPH, REG)
        self.assertEqual(errors, [], f"coverage should be clean, got: {errors}")

    def test_all_physical_modules_classified(self):
        phys = set(coverage.physical_modules(REPO))
        self.assertEqual(phys - set(REG["modules"]), set())
        self.assertEqual(len(phys), 97)

    def test_missing_required_module_is_hard_failure(self):
        """The exact MVP failure: a research module absent from the graph."""
        for victim in MVP_CASUALTIES:
            with self.subTest(module=victim):
                self.assertEqual(REG["modules"][victim]["category"],
                                 "REQUIRED_RESEARCH_MODULE")
                g = copy.deepcopy(GRAPH)
                g["declarations"] = {k: v for k, v in g["declarations"].items()
                                     if v["module"] != victim}
                errors, _ = coverage.check_modules(REPO, g, REG)
                self.assertTrue(errors, "dropping a required module must error")
                blob = "\n".join(errors)
                self.assertIn(victim, blob)
                self.assertIn("required research modules missing", blob)

    def test_missing_support_module_is_hard_failure(self):
        victim = next(m for m, v in REG["modules"].items()
                      if v["category"] == "SUPPORT_MODULE")
        g = copy.deepcopy(GRAPH)
        g["declarations"] = {k: v for k, v in g["declarations"].items()
                             if v["module"] != victim}
        errors, _ = coverage.check_modules(REPO, g, REG)
        self.assertTrue(any(victim in e for e in errors))

    def test_unclassified_module_is_hard_failure(self):
        """A new Lean file nobody classified must stop the build."""
        reg = copy.deepcopy(REG)
        reg["modules"].pop("EOC.CurryFoundation")
        errors, _ = coverage.check_modules(REPO, GRAPH, reg)
        blob = "\n".join(errors)
        self.assertIn("UNKNOWN", blob)
        self.assertIn("EOC.CurryFoundation", blob)

    def test_excluded_module_needs_a_reason(self):
        reg = copy.deepcopy(REG)
        reg["modules"]["EOC.CurryFoundation"] = {
            "category": "GENERATED_OR_EXCLUDED", "reason": None, "rules_fired": []}
        errors, _ = coverage.check_modules(REPO, GRAPH, reg)
        self.assertTrue(any("gives no reason" in e for e in errors))

        reg["modules"]["EOC.CurryFoundation"]["reason"] = "documented elsewhere"
        errors, _ = coverage.check_modules(REPO, GRAPH, reg)
        self.assertEqual([e for e in errors if "CurryFoundation" in e], [])

    def test_stale_registry_entry_warns_but_does_not_fail(self):
        reg = copy.deepcopy(REG)
        reg["modules"]["EOC.ModuleThatWasDeleted"] = {
            "category": "SUPPORT_MODULE", "reason": None, "rules_fired": []}
        errors, warnings = coverage.check_modules(REPO, GRAPH, reg)
        self.assertTrue(any("no longer exist" in w for w in warnings))
        self.assertEqual(errors, [])


class TestImportBlock(unittest.TestCase):
    def test_import_block_is_in_sync(self):
        self.assertEqual(coverage.check_imports_in_sync(REPO), [])

    def test_new_module_on_disk_is_detected(self):
        """A module added to EOC/ but not imported is the root cause of the MVP bug.

        Runs in a temporary copy of the tree so the real repository is untouched.
        """
        with tempfile.TemporaryDirectory() as td:
            tmp = Path(td) / "repo"
            (tmp / "EOC").mkdir(parents=True)
            for f in (REPO / "EOC").rglob("*.lean"):
                dest = tmp / f.relative_to(REPO)
                dest.parent.mkdir(parents=True, exist_ok=True)
                dest.write_text("", encoding="utf-8")
            ext = tmp / coverage.EXTRACTOR
            ext.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy(REPO / coverage.EXTRACTOR, ext)
            self.assertEqual(coverage.check_imports_in_sync(tmp), [],
                             "copied tree should start in sync")

            (tmp / "EOC" / "BrandNewFrontier.lean").write_text("-- new work\n")
            problems = coverage.check_imports_in_sync(tmp)
            self.assertTrue(problems)
            self.assertIn("EOC.BrandNewFrontier", problems[0])
            self.assertIn("NOT IMPORTED", problems[0])

            coverage.write_import_block(tmp)
            self.assertEqual(coverage.check_imports_in_sync(tmp), [],
                             "regeneration should restore sync")

    def test_regeneration_is_idempotent(self):
        text = (REPO / coverage.EXTRACTOR).read_text(encoding="utf-8")
        before = hashlib.sha256(text.encode()).hexdigest()
        block = coverage.render_import_block(REPO)
        self.assertIn(block, text)
        self.assertEqual(before, hashlib.sha256(text.encode()).hexdigest())


class TestSentinels(unittest.TestCase):
    def test_all_sentinels_resolve(self):
        self.assertEqual(coverage.check_sentinels(REPO, GRAPH, SEM, SENT), [])

    def test_sentinels_span_multiple_epochs(self):
        epochs = {s["epoch"] for s in SENT["sentinels"]}
        self.assertGreaterEqual(len(epochs), 8)

    def test_zcre_headline_result_is_a_sentinel(self):
        """It has zero reverse dependencies, so no formal signal protects it."""
        name = "EOC.ZCRERealizerGrowth.boundedPrefixRealizers_iff_positiveRealizer"
        names = [s["declaration"] for s in SENT["sentinels"]]
        self.assertIn(name, names)
        self.assertEqual(len(GRAPH["declarations"][name]["rev_deps_eoc"]), 0)

    def test_missing_sentinel_declaration_is_detected(self):
        g = copy.deepcopy(GRAPH)
        victim = SENT["sentinels"][0]["declaration"]
        g["declarations"].pop(victim)
        errors = coverage.check_sentinels(REPO, g, SEM, SENT)
        self.assertTrue(any(victim in e for e in errors))

    def test_renamed_sentinel_module_is_detected(self):
        g = copy.deepcopy(GRAPH)
        victim = SENT["sentinels"][0]["declaration"]
        g["declarations"][victim] = dict(g["declarations"][victim], module="EOC.Elsewhere")
        errors = coverage.check_sentinels(REPO, g, SEM, SENT)
        self.assertTrue(any("expected" in e and victim in e for e in errors))

    def test_orphaned_semantic_pointer_is_detected(self):
        sem = copy.deepcopy(SEM)
        target = next(s for s in SENT["sentinels"] if s.get("semantic_node"))
        for n in sem["nodes"]:
            if n["source"].get("declaration") == target["declaration"]:
                n["source"]["declaration"] = "EOC.Renamed.thing"
        errors = coverage.check_sentinels(REPO, GRAPH, sem, SENT)
        self.assertTrue(any(target["declaration"] in e for e in errors))


class TestDomainGuard(unittest.TestCase):
    def test_riemann_hypothesis_is_refused(self):
        """The exact MVP false positive."""
        q = "Does the Riemann hypothesis imply anything here?"
        c = classify(q, VOCAB)
        self.assertEqual(c["verdict"], "OUT_OF_DOMAIN")
        self.assertIn("Riemann hypothesis", c["external_subjects"])
        res = retrieve(q, SEM, GRAPH, "full_tiebreaker")
        self.assertTrue(res["refused"])
        self.assertEqual(res["semantic"], [])
        self.assertEqual(res["formal"], [])

    def test_hypothesis_alone_cannot_score(self):
        """Root-cause fix, independent of the entity list."""
        self.assertNotIn("hypothesis", tokenize("Does the Riemann hypothesis imply anything?"))
        for w in ("hypothesis", "conjecture", "theorem", "problem", "result"):
            self.assertEqual(tokenize(w), set(), f"{w!r} must carry no relevance")

    def test_unlisted_external_subject_still_cannot_win_on_generic_words(self):
        """A subject nobody listed must not produce confident matches."""
        res = retrieve("Does the Collatz-unrelated Hodge-Arakelov theorem imply anything?",
                       SEM, GRAPH, "full_tiebreaker")
        if not res["refused"]:
            self.assertIn(res["guard"]["verdict"], ("WEAK_MATCH", "TRANSFER_REQUEST",
                                                    "IN_DOMAIN"))

    def test_transfer_request_passes_through(self):
        q = ("Could a technique from the Riemann hypothesis literature help the "
             "EOC arithmetic bottleneck?")
        c = classify(q, VOCAB)
        self.assertEqual(c["verdict"], "TRANSFER_REQUEST")
        res = retrieve(q, SEM, GRAPH, "full_tiebreaker")
        self.assertFalse(res["refused"], "a transfer question must not be refused")
        self.assertTrue(res["semantic"], "a transfer question should still return context")

    def test_in_domain_question_unaffected(self):
        for q in ("What is the current arithmetic bottleneck in Chain A?",
                  "What does Curry contribute to excluding Type-II divergence?"):
            c = classify(q, VOCAB)
            self.assertEqual(c["verdict"], "IN_DOMAIN", q)

    def test_vocabulary_excludes_generic_terms(self):
        self.assertNotIn("hypothesis", VOCAB)
        self.assertNotIn("theorem", VOCAB)


class TestRetrievalModes(unittest.TestCase):
    QUESTION = "Can unbounded prefix-realizer growth provide a weaker route than EOC?"

    def test_all_modes_run(self):
        for m in ABLATION_ORDER:
            with self.subTest(mode=m):
                res = retrieve(self.QUESTION, SEM, GRAPH, m)
                self.assertIn("semantic", res)

    def test_determinism(self):
        for m in ABLATION_ORDER:
            a = retrieve(self.QUESTION, SEM, GRAPH, m)
            b = retrieve(self.QUESTION, SEM, GRAPH, m)
            self.assertEqual([r["node"]["id"] for r in a["semantic"]],
                             [r["node"]["id"] for r in b["semantic"]], m)
            self.assertEqual([r["composite"] for r in a["semantic"]],
                             [r["composite"] for r in b["semantic"]], m)

    def test_lexical_mode_hides_status(self):
        self.assertFalse(MODES["lexical"].show_status_in_packet)
        self.assertEqual(MODES["lexical"].w_status, 0.0)

    def test_aksenov_mode_has_a_real_route_into_node_ranking(self):
        """Otherwise the ablation would be a strawman."""
        m = MODES["aksenov"]
        self.assertGreater(m.w_node_centrality, 0.0)
        res = retrieve(self.QUESTION, SEM, GRAPH, "aksenov")
        self.assertTrue(any(r["components"]["aksenov_contribution"] > 0
                            for r in res["semantic"]),
                        "aksenov mode must actually move node scores")

    def test_tiebreaker_never_overrides_a_clear_winner(self):
        full = retrieve(self.QUESTION, SEM, GRAPH, "full")
        tb = retrieve(self.QUESTION, SEM, GRAPH, "full_tiebreaker")
        sem_only = retrieve(self.QUESTION, SEM, GRAPH, "semantic")
        if sem_only["semantic"]:
            top_primary = sem_only["semantic"][0]["primary"]
            runner = (sem_only["semantic"][1]["primary"]
                      if len(sem_only["semantic"]) > 1 else 0.0)
            if top_primary - runner > MODES["full_tiebreaker"].tiebreak_epsilon:
                self.assertEqual(tb["semantic"][0]["node"]["id"],
                                 sem_only["semantic"][0]["node"]["id"],
                                 "a clear semantic winner must survive tiebreaking")
        self.assertTrue(full["semantic"])


class TestEvaluationHarness(unittest.TestCase):
    def _questions(self):
        return ev.load_questions(IDX / "evaluation/regression/questions.json")

    def test_evaluate_does_not_mutate_the_index(self):
        paths = [IDX / "formal_graph.json", IDX / "research_graph.json",
                 IDX / "module_registry.json", IDX / "sentinel_declarations.json"]
        before = {p: hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
        sem, g = copy.deepcopy(SEM), copy.deepcopy(GRAPH)
        for m in ABLATION_ORDER:
            ev.evaluate(self._questions(), sem, g, m)
        after = {p: hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
        self.assertEqual(before, after, "evaluation must be read-only")
        self.assertEqual(sem, SEM, "in-memory semantic graph must not be mutated")
        self.assertEqual(g, GRAPH, "in-memory formal graph must not be mutated")

    def test_gold_is_not_visible_to_retrieval(self):
        """run_question must work on a gold-stripped question."""
        qs = ev.strip_gold(self._questions())
        for q in qs["questions"]:
            self.assertNotIn("gold_sources", q)
            r = ev.run_question(q, SEM, GRAPH, "full_tiebreaker")
            self.assertTrue(r["packet"])

    def test_scoring_is_separable_from_retrieval(self):
        qs = self._questions()
        q = qs["questions"][0]
        r = ev.run_question(q, SEM, GRAPH, "semantic")
        s = ev.score_question(q, r)
        self.assertIn("recall_at_1_nodes", s)
        self.assertIn("rank_of_first_gold_node", s)

    def test_gold_node_ids_all_exist(self):
        ids = {n["id"] for n in SEM["nodes"]}
        for q in self._questions()["questions"]:
            for gid in q.get("gold_semantic_nodes", []):
                self.assertIn(gid, ids, f"{q['id']} cites unknown node {gid}")


if __name__ == "__main__":
    unittest.main()
