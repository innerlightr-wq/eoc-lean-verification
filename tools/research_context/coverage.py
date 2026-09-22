"""Module- and declaration-coverage checks for the research index.

Gates 1 and 2 of the evaluation round. Exists because of a real failure: in the
MVP round `EOC.CurryFoundation` and `EOC.ZCRERealizerGrowth` -- the two modules
the semantic layer cares most about -- were absent from the extracted closure,
because `EOC.lean` does not import them. A hand spot-check caught it. Nothing
mechanical would have.

The failure mode is not random. It is biased *toward the research frontier*:
a module is missing from `EOC.lean` precisely when it is new, and new work is
what a returning researcher most needs. So coverage cannot be left to chance.

Two independent defences, because detection alone is weaker than prevention:

1. `AllModules.lean` is GENERATED from the filesystem, so the extractor imports
   every physical module whether or not `EOC.lean` knows about it. This removes
   the failure at its root. `check_imports_in_sync` fails if it drifts.
2. `module_registry.json` classifies every physical module. An unclassified
   module is UNKNOWN and fails the build; a REQUIRED_RESEARCH_MODULE or
   SUPPORT_MODULE missing from the graph fails the build.

Neither check needs a model, a network call, or Lean itself.
"""
from __future__ import annotations

import json
import re
from pathlib import Path

CATEGORIES = (
    "REQUIRED_RESEARCH_MODULE",   # must be indexed; research-salient
    "SUPPORT_MODULE",             # must be indexed; proved library, not frontier
    "EXPERIMENTAL",               # may be absent; warns
    "GENERATED_OR_EXCLUDED",      # may be absent; needs a documented reason
    "UNKNOWN",                    # never acceptable: hard failure
)

# Categories whose absence from the formal graph is a hard error.
MUST_BE_INDEXED = {"REQUIRED_RESEARCH_MODULE", "SUPPORT_MODULE"}

REQUIRED_RULES = {
    "R1": "cited by a node in research-index/research_graph.json",
    "R2": "named (word-boundary, by module basename) in any docs/*.md",
    "R3": "at least 100 reverse dependencies inside EOC (formal spine load-bearer)",
}
R3_THRESHOLD = 100


def physical_modules(repo: Path) -> list[str]:
    """Every Lean module physically present under EOC/, as a module name."""
    return sorted(
        str(f.relative_to(repo)).replace("/", ".")[:-5]
        for f in (repo / "EOC").rglob("*.lean")
    )


def indexed_modules(graph: dict) -> set[str]:
    return {d["module"] for d in graph["declarations"].values()}


# ---------------------------------------------------------------- registry gen
def derive_registry(repo: Path, graph: dict, sem: dict) -> dict:
    """Derive the registry mechanically from repository evidence.

    Deliberately rule-based rather than hand-curated: a hand list would encode
    one session's taste and rot silently. Each module records which rules fired,
    so a reader can audit and override with a documented reason.
    """
    mods = physical_modules(repo)
    decls = graph["declarations"]

    sem_mods: set[str] = set()
    for n in sem["nodes"]:
        d = n["source"].get("declaration")
        if d:
            # EOC.CurryFoundation.foo -> EOC.CurryFoundation (namespace == module here)
            sem_mods.add(".".join(d.split(".")[:2]))
    doc_text = " ".join(
        p.read_text(encoding="utf-8", errors="ignore") for p in sorted((repo / "docs").glob("*.md"))
    )
    revdeps: dict[str, int] = {}
    for d in decls.values():
        if not d.get("generated"):
            revdeps[d["module"]] = revdeps.get(d["module"], 0) + len(d["rev_deps_eoc"])

    entries = {}
    for m in mods:
        base = m.split(".")[-1]
        fired = []
        if m in sem_mods:
            fired.append("R1")
        if re.search(r"\b" + re.escape(base) + r"\b", doc_text):
            fired.append("R2")
        if revdeps.get(m, 0) >= R3_THRESHOLD:
            fired.append("R3")
        entries[m] = {
            "category": "REQUIRED_RESEARCH_MODULE" if fired else "SUPPORT_MODULE",
            "rules_fired": fired,
            "rev_deps_eoc": revdeps.get(m, 0),
            "reason": None,
        }
    return {
        "registry_id": "eoc-module-registry-v1",
        "policy": {
            "categories": list(CATEGORIES),
            "must_be_indexed": sorted(MUST_BE_INDEXED),
            "unknown_is_fatal": True,
            "required_rules": REQUIRED_RULES,
            "r3_threshold": R3_THRESHOLD,
            "note": (
                "REQUIRED vs SUPPORT expresses research salience, not coverage: BOTH must be "
                "indexed. Any physical module absent from this registry is UNKNOWN and fails "
                "the build until classified. To exclude a module, set its category to "
                "GENERATED_OR_EXCLUDED and give a 'reason'; an empty reason is itself an error."
            ),
        },
        "generated_from": "tools/research_context/coverage.py derive_registry",
        "modules": entries,
    }


# -------------------------------------------------------------------- checking
def check_modules(repo: Path, graph: dict, registry: dict) -> tuple[list[str], list[str]]:
    """Return (errors, warnings). Errors must fail the build."""
    errors: list[str] = []
    warnings: list[str] = []
    phys = set(physical_modules(repo))
    idx = indexed_modules(graph)
    reg = registry["modules"]

    unknown = sorted(phys - set(reg))
    if unknown:
        errors.append(
            "unclassified Lean modules (category UNKNOWN). Classify each in "
            "research-index/module_registry.json:\n" + "".join(f"    {m}\n" for m in unknown).rstrip()
        )

    stale = sorted(set(reg) - phys)
    if stale:
        warnings.append(
            "registry lists modules that no longer exist on disk:\n"
            + "".join(f"    {m}\n" for m in stale).rstrip()
        )

    missing_required: list[str] = []
    missing_support: list[str] = []
    for m in sorted(phys & set(reg)):
        cat = reg[m].get("category", "UNKNOWN")
        if cat not in CATEGORIES:
            errors.append(f"module {m} has unrecognised category {cat!r}")
            continue
        if cat == "UNKNOWN":
            errors.append(f"module {m} is explicitly UNKNOWN; classify it")
            continue
        if cat == "GENERATED_OR_EXCLUDED" and not reg[m].get("reason"):
            errors.append(f"module {m} is GENERATED_OR_EXCLUDED but gives no reason")
        if m in idx:
            continue
        if cat == "REQUIRED_RESEARCH_MODULE":
            missing_required.append(m)
        elif cat == "SUPPORT_MODULE":
            missing_support.append(m)
        elif cat == "EXPERIMENTAL":
            warnings.append(f"EXPERIMENTAL module not indexed: {m}")

    if missing_required:
        errors.append(
            "required research modules missing from the dependency graph:\n"
            + "".join(f"    {m}\n" for m in missing_required).rstrip()
            + "\n  These are cited by the semantic layer or the frontier docs. The index would "
              "be confidently wrong about the current research frontier."
        )
    if missing_support:
        errors.append(
            "support modules missing from the dependency graph:\n"
            + "".join(f"    {m}\n" for m in missing_support).rstrip()
        )
    return errors, warnings


# ------------------------------------------------------------- generated Lean
# The extractor's import list is generated into ExtractDeps.lean between these
# markers. A separate AllModules.lean would be tidier, but it does not sit on
# Lean's module search path (it is not part of the EOC lake package), so
# `import AllModules` would not resolve. A marker-delimited block inside the
# one file that `lake env lean` actually compiles keeps this honest.
BEGIN = "-- BEGIN GENERATED IMPORTS -- python3 -m tools.research_context imports"
END = "-- END GENERATED IMPORTS"

EXTRACTOR = "tools/research_context/lean/ExtractDeps.lean"

NOTE = """\
-- Every Lean module physically present under EOC/ is imported below, so the
-- extractor sees the whole library regardless of what `EOC.lean` imports. In
-- the MVP round EOC.CurryFoundation and EOC.ZCRERealizerGrowth were silently
-- absent from the closure for exactly that reason: a module is missing from
-- EOC.lean precisely when it is new, which is when it matters most.
"""


def render_import_block(repo: Path) -> str:
    mods = physical_modules(repo)
    return (BEGIN + "\n" + NOTE + "".join(f"import {m}\n" for m in mods) + END)


def check_imports_in_sync(repo: Path) -> list[str]:
    path = repo / EXTRACTOR
    if not path.is_file():
        return [f"extractor missing: {path}"]
    text = path.read_text(encoding="utf-8")
    if BEGIN not in text or END not in text:
        return [f"{EXTRACTOR} has no generated-import block."
                " Run `python3 -m tools.research_context imports`."]
    block = text.split(BEGIN)[1].split(END)[0]
    have = set(re.findall(r"^import (\S+)", block, re.M))
    phys = set(physical_modules(repo))
    if have == phys:
        return []
    detail = ""
    if phys - have:
        detail += ("\n  NOT IMPORTED (would be silently missing from the index): "
                   + ", ".join(sorted(phys - have)))
    if have - phys:
        detail += "\n  imported but absent from disk: " + ", ".join(sorted(have - phys))
    return [f"{EXTRACTOR} import block is out of sync with the filesystem."
            " Run `python3 -m tools.research_context imports`." + detail]


def write_import_block(repo: Path) -> str:
    """Rewrite the generated import block in place. Returns a short summary."""
    path = repo / EXTRACTOR
    text = path.read_text(encoding="utf-8")
    block = render_import_block(repo)
    if BEGIN in text and END in text:
        head, rest = text.split(BEGIN, 1)
        _, tail = rest.split(END, 1)
        text = head + block + tail
    else:
        raise SystemExit(f"{EXTRACTOR}: no generated-import block markers found")
    path.write_text(text, encoding="utf-8")
    return f"{len(physical_modules(repo))} modules imported in {EXTRACTOR}"


# ------------------------------------------------------------------- sentinels
def check_sentinels(repo: Path, graph: dict, sem: dict, sentinels: dict) -> list[str]:
    """Gate 2: named declarations from each research epoch must still resolve.

    Checks the declaration exists in the graph, sits in the module we expect,
    and -- when the sentinel claims a semantic pointer -- that the semantic
    layer really does cite it.
    """
    errors: list[str] = []
    decls = graph["declarations"]
    sem_decls = {n["source"].get("declaration") for n in sem["nodes"]}
    for s in sentinels["sentinels"]:
        name, mod = s["declaration"], s["module"]
        d = decls.get(name)
        if d is None:
            errors.append(
                f"sentinel declaration absent from formal_graph: {name}\n"
                f"    epoch: {s['epoch']}\n"
                f"    expected module: {mod}\n"
                "    Either the declaration was renamed, or extraction lost its module."
            )
            continue
        if d["module"] != mod:
            errors.append(f"sentinel {name} is in module {d['module']}, expected {mod}")
        if s.get("semantic_node") and name not in sem_decls:
            errors.append(
                f"sentinel {name} should be cited by semantic node "
                f"{s['semantic_node']!r} but no node cites it"
            )
        if s.get("semantic_node"):
            ids = {n["id"] for n in sem["nodes"]}
            if s["semantic_node"] not in ids:
                errors.append(f"sentinel {name} names semantic node "
                              f"{s['semantic_node']!r}, which does not exist")
    return errors


def load_json(p: Path) -> dict:
    return json.loads(p.read_text(encoding="utf-8"))
