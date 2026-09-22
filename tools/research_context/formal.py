"""Formal-layer construction: inventory, dependency graph, Aksenov-style metrics.

Gates 1-4 and the data behind Gate 12.

Method adapted from Aksenov, Bodnia, Freedman and Mulligan, "Compression is all
you need: Modeling Mathematics", arXiv:2603.20396 (2026), CC BY 4.0. See
docs/AKSENOV_METHOD_NOTES.md for exactly what is theirs and what is ours.

Everything here is deterministic and stdlib-only.
"""
from __future__ import annotations

import json
import re
import subprocess
from collections import defaultdict
from pathlib import Path

# A declaration whose exact unwrapped length exceeds this many bits is stored by
# bit length and log2 only. Nothing is silently approximated: `unwrapped_exact`
# is then null and `unwrapped_exact_omitted` is true.
EXACT_BITS_CAP = 20_000


# --------------------------------------------------------------------- Gate 1
def build_inventory(repo: Path) -> dict:
    """Repository inventory. No importance scores here, by design."""
    lean_files = sorted(p for p in (repo / "EOC").rglob("*.lean"))
    docs = sorted(p for p in (repo / "docs").glob("*.md")) if (repo / "docs").is_dir() else []
    scratch = sorted(p for p in (repo / "scratch").iterdir() if p.is_dir()) \
        if (repo / "scratch").is_dir() else []

    def git(*args: str) -> str:
        try:
            return subprocess.run(["git", "-C", str(repo), *args],
                                  capture_output=True, text=True, timeout=60).stdout.strip()
        except Exception:
            return ""

    modules = []
    for p in lean_files:
        text = p.read_text(encoding="utf-8", errors="replace")
        imports = re.findall(r"^import\s+(\S+)", text, re.M)
        modules.append({
            "path": str(p.relative_to(repo)),
            "module": "EOC." + str(p.relative_to(repo / "EOC")).removesuffix(".lean").replace("/", "."),
            "lines": text.count("\n") + 1,
            "imports": imports,
            "eoc_imports": [i for i in imports if i.startswith("EOC")],
            # cheap textual counts; the authoritative counts come from the Lean dump
            "textual_decls": len(re.findall(r"^\s*(?:private\s+|protected\s+|noncomputable\s+)*"
                                            r"(theorem|lemma|def|abbrev|instance|structure|inductive)\s",
                                            text, re.M)),
            "last_commit": git("log", "-1", "--format=%H", "--", str(p.relative_to(repo))),
            "first_commit": git("log", "--reverse", "--format=%H", "--", str(p.relative_to(repo))).split("\n")[0],
            "n_commits": len([x for x in git("log", "--format=%H", "--",
                                             str(p.relative_to(repo))).split("\n") if x]),
        })

    return {
        "schema": "eoc-research-index/repo_inventory/1",
        "generated_by": "tools/research_context",
        "repo_head": git("rev-parse", "HEAD"),
        "branch": git("rev-parse", "--abbrev-ref", "HEAD"),
        "totals": {
            "lean_modules": len(lean_files),
            "lean_lines": sum(m["lines"] for m in modules),
            "docs": len(docs),
            "scratch_dirs": len(scratch),
            "commits": int(git("rev-list", "--count", "HEAD") or 0),
        },
        "modules": modules,
        "docs": [{"path": str(p.relative_to(repo)),
                  "lines": p.read_text(encoding='utf-8', errors='replace').count("\n") + 1,
                  "title": _first_heading(p)} for p in docs],
        "scratch_dirs": [str(p.relative_to(repo)) for p in scratch],
        "preexisting_tooling": {
            "dependency_extraction": False,
            "declaration_metadata": False,
            "import_graph": False,
            "theorem_registry": False,
            "status_registry": False,
            "note": "Searched for these before building; none present at 1d087e2. "
                    "Nothing was duplicated.",
        },
    }


def _first_heading(p: Path) -> str:
    for line in p.read_text(encoding="utf-8", errors="replace").splitlines():
        if line.startswith("#"):
            return line.lstrip("#").strip()
    return p.stem


# ----------------------------------------------------------------- Gates 2-4
def load_raw(path: Path) -> dict[str, dict]:
    nodes: dict[str, dict] = {}
    with path.open(encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            # the Lean #eval frontend interleaves its summary line on stdout; skip
            # anything that is not a JSON object rather than failing the whole load
            if not line.startswith("{"):
                continue
            d = json.loads(line)
            nodes[d["name"]] = d
    return nodes


def _tarjan_sccs(adj: dict[str, list[str]]) -> list[list[str]]:
    """Iterative Tarjan. Defensive: the theorem graph should be acyclic."""
    index: dict[str, int] = {}
    low: dict[str, int] = {}
    on: dict[str, bool] = {}
    stack: list[str] = []
    out: list[list[str]] = []
    counter = 0
    for root in adj:
        if root in index:
            continue
        work = [(root, iter(adj.get(root, ())))]
        index[root] = low[root] = counter
        counter += 1
        stack.append(root)
        on[root] = True
        while work:
            v, it = work[-1]
            advanced = False
            for w in it:
                if w not in adj:
                    continue
                if w not in index:
                    index[w] = low[w] = counter
                    counter += 1
                    stack.append(w)
                    on[w] = True
                    work.append((w, iter(adj.get(w, ()))))
                    advanced = True
                    break
                if on.get(w):
                    low[v] = min(low[v], index[w])
            if advanced:
                continue
            work.pop()
            if work:
                low[work[-1][0]] = min(low[work[-1][0]], low[v])
            if low[v] == index[v]:
                comp = []
                while True:
                    w = stack.pop()
                    on[w] = False
                    comp.append(w)
                    if w == v:
                        break
                out.append(comp)
    return out


def _tokenize_lean(src: str) -> int:
    """Approximate the Lean parser's token count for a source span.

    NOT the Lean parser. Reported everywhere as `wrapped_tokens_approx`.
    Comments are stripped; identifiers/numbers are one token; each operator or
    bracket is one token. A tactic name is one token, which is the property the
    paper relies on to avoid the `simp`/`rw` reference-count artifact.
    """
    src = re.sub(r"/-.*?-/", " ", src, flags=re.S)
    src = re.sub(r"--[^\n]*", " ", src)
    return len(re.findall(r"[A-Za-z_α-ωΑ-Ω][A-Za-z0-9_'!?₀-₉.α-ω]*"
                          r"|\d+"
                          r"|[^\sA-Za-z0-9_]", src))


def _wrapped_tokens(repo: Path, node: dict, cache: dict[str, list[str]]) -> tuple[int, int, int]:
    """(total, signature, body) approximate token counts for an EOC declaration."""
    if not node.get("eoc") or not node.get("start_line"):
        return (0, 0, 0)
    mod = node["module"]
    rel = mod.replace(".", "/") + ".lean"
    if rel not in cache:
        p = repo / rel
        cache[rel] = p.read_text(encoding="utf-8", errors="replace").splitlines() if p.is_file() else []
    lines = cache[rel]
    s, e = node["start_line"], node["end_line"]
    if not lines or s < 1 or e < s or e > len(lines):
        return (0, 0, 0)
    text = "\n".join(lines[s - 1:e])
    total = _tokenize_lean(text)
    # split signature / body at the first top-level ':=' or ' by' -- approximate
    m = re.search(r":=|\bby\b", text)
    if m:
        sig = _tokenize_lean(text[:m.start()])
        body = _tokenize_lean(text[m.end():])
    else:
        sig, body = total, 0
    return (total, sig, body)


def build_graph(repo: Path, raw_path: Path) -> dict:
    """Construct both dependency views and all Aksenov-style metrics."""
    raw = load_raw(raw_path)

    # combined (signature + body) weighted adjacency, per the paper
    adj_w: dict[str, dict[str, int]] = {}
    for name, d in raw.items():
        w: dict[str, int] = defaultdict(int)
        for k, c in d.get("sig_deps", {}).items():
            w[k] += c
        for k, c in d.get("body_deps", {}).items():
            w[k] += c
        adj_w[name] = dict(w)

    # SCC collapse (paper does this for ~60 unsafe-recursion pairs)
    adj_plain = {n: [d for d in ws if d in adj_w] for n, ws in adj_w.items()}
    sccs = [c for c in _tarjan_sccs(adj_plain) if len(c) > 1]
    collapsed = {n: c[0] for c in sccs for n in c}
    n_collapsed = sum(len(c) for c in sccs)

    def rep(n: str) -> str:
        return collapsed.get(n, n)

    # ---- the two views -------------------------------------------------
    # View A: every node in the emitted closure expands; sinks are nodes with no
    #         recorded dependencies (Lean core, `Sort`, and anything outside the dump).
    # View B: EOC declarations expand; every non-EOC node is a terminal primitive.
    def compute(view: str) -> dict[str, dict]:
        def expands(n: str) -> bool:
            d = raw.get(n)
            if d is None:
                return False
            if view == "B" and not d.get("eoc"):
                return False
            return bool(adj_w.get(n))

        order: list[str] = []
        state: dict[str, int] = {}

        for root in raw:
            if state.get(root):
                continue
            stack = [(root, False)]
            while stack:
                n, done = stack.pop()
                if done:
                    state[n] = 2
                    order.append(n)
                    continue
                if state.get(n):
                    continue
                state[n] = 1
                stack.append((n, True))
                if expands(n):
                    for dep in adj_w.get(n, {}):
                        r = rep(dep)
                        if r != n and not state.get(r):
                            stack.append((r, False))

        unwrapped: dict[str, int] = {}
        depth: dict[str, int] = {}
        for n in order:
            if not expands(n):
                unwrapped[n] = 1
                depth[n] = 0
                continue
            tot = 0
            dmax = 0
            for dep, w in adj_w.get(n, {}).items():
                r = rep(dep)
                if r == n:
                    continue
                tot += w * unwrapped.get(r, 1)
                dmax = max(dmax, depth.get(r, 0) + 1)
            unwrapped[n] = tot if tot else 1
            depth[n] = dmax
        return {"unwrapped": unwrapped, "depth": depth}

    viewA = compute("A")
    viewB = compute("B")

    # ---- per-declaration records (EOC only) ----------------------------
    src_cache: dict[str, list[str]] = {}
    rev_eoc: dict[str, set[str]] = defaultdict(set)
    for n, ws in adj_w.items():
        if not raw.get(n, {}).get("eoc"):
            continue
        for dep in ws:
            if raw.get(dep, {}).get("eoc"):
                rev_eoc[dep].add(n)

    decls = {}
    for name, d in raw.items():
        if not d.get("eoc"):
            continue
        tot, sig_t, body_t = _wrapped_tokens(repo, d, src_cache)
        # exact unwrapped split over signature and body, View B
        def uw(deps: dict[str, int], view: dict) -> int:
            return sum(w * view["unwrapped"].get(rep(k), 1) for k, w in deps.items()) or 0
        uw_sig_B = uw(d.get("sig_deps", {}), viewB)
        uw_body_B = uw(d.get("body_deps", {}), viewB)
        uB = viewB["unwrapped"].get(name, 1)
        uA = viewA["unwrapped"].get(name, 1)

        def pack(u: int) -> dict:
            bits = u.bit_length()
            return {
                "bit_length": bits,
                "log2": (u.bit_length() - 1) if u > 0 else 0,
                "exact": str(u) if bits <= EXACT_BITS_CAP else None,
                "exact_omitted": bits > EXACT_BITS_CAP,
            }

        eoc_deps = {k: w for k, w in adj_w[name].items() if raw.get(k, {}).get("eoc")}
        ext_deps = {k: w for k, w in adj_w[name].items() if not raw.get(k, {}).get("eoc")}
        decls[name] = {
            "name": name,
            "module": d["module"],
            "kind": d["kind"],
            "generated": d["generated"],
            "has_body": d["has_body"],
            "source": {"file": d["module"].replace(".", "/") + ".lean",
                       "start_line": d["start_line"], "end_line": d["end_line"]},
            "deps_eoc": eoc_deps,
            "deps_external_count": sum(ext_deps.values()),
            "deps_external_distinct": len(ext_deps),
            "rev_deps_eoc": sorted(rev_eoc.get(name, ())),
            "wrapped_tokens_approx": tot,
            "wrapped_tokens_sig_approx": sig_t,
            "wrapped_tokens_body_approx": body_t,
            "view_A": {"depth": viewA["depth"].get(name, 0), "unwrapped": pack(uA)},
            "view_B": {"depth": viewB["depth"].get(name, 0), "unwrapped": pack(uB),
                       "unwrapped_sig": pack(uw_sig_B or 1),
                       "unwrapped_body": pack(uw_body_B or 1)},
            # Aksenov T_0 / I_0, on View B, with approximate wrapped lengths
            "T0_viewB": round((uw_sig_B + uw_body_B) / tot, 4) if tot else None,
            "I0_approx": round(body_t / sig_t, 4) if sig_t and d["has_body"] else 0.0,
        }

    pr = _pagerank(decls)
    for n, v in pr.items():
        decls[n]["pagerank_viewB"] = round(v, 8)

    return {
        "schema": "eoc-research-index/formal_graph/1",
        "method": {
            "adapted_from": "arXiv:2603.20396 (CC BY 4.0)",
            "extraction": "Lean elaborated environment; .const multiplicities over "
                          "signature and body; .sort folded into synthetic `Sort`",
            "wrapped_length": "APPROXIMATE regex tokenizer over the declaration source "
                              "range, not the Lean parser; see docs/AKSENOV_METHOD_NOTES.md",
            "view_A": "closure emitted from Lean expands; sinks are nodes with no recorded deps",
            "view_B": "EOC declarations expand; every non-EOC node is a terminal primitive",
            "scc_collapsed_nodes": n_collapsed,
            "exact_bits_cap": EXACT_BITS_CAP,
        },
        "totals": {
            "closure_nodes": len(raw),
            "eoc_declarations": len(decls),
            "eoc_declarations_human": sum(1 for d in decls.values() if not d["generated"]),
        },
        "declarations": decls,
    }


def _pagerank(decls: dict[str, dict], alpha: float = 0.85, beta: float = 0.5,
              iters: int = 200, tol: float = 1e-12) -> dict[str, float]:
    """J0-biased PageRank over the EOC-relative graph (paper, §PageRank-style refinement).

    Teleportation is biased by J0 = beta*T0 + (1-beta)*I0 after min-max normalising
    each to [0,1], exactly as the paper proposes. Restricted to View B because a walk
    on View A drains into Mathlib, which is the paper's own reason for teleportation.
    """
    names = sorted(decls)
    if not names:
        return {}
    idx = {n: i for i, n in enumerate(names)}

    def norm(key, get):
        vals = [get(decls[n]) or 0.0 for n in names]
        lo, hi = min(vals), max(vals)
        span = (hi - lo) or 1.0
        return [(v - lo) / span for v in vals]

    t0 = norm("T0", lambda d: d.get("T0_viewB"))
    i0 = norm("I0", lambda d: d.get("I0_approx"))
    j0 = [beta * a + (1 - beta) * b for a, b in zip(t0, i0)]
    z = sum(j0) or 1.0
    tele = [v / z for v in j0]

    out: list[list[tuple[int, float]]] = [[] for _ in names]
    for n in names:
        ws = {k: w for k, w in decls[n]["deps_eoc"].items() if k in idx}
        tot = sum(ws.values())
        if tot:
            out[idx[n]] = [(idx[k], w / tot) for k, w in ws.items()]

    x = [1.0 / len(names)] * len(names)
    for _ in range(iters):
        nxt = [(1 - alpha) * t for t in tele]
        dangling = 0.0
        for i, edges in enumerate(out):
            if not edges:
                dangling += x[i]
                continue
            for j, w in edges:
                nxt[j] += alpha * x[i] * w
        if dangling:
            for j in range(len(names)):
                nxt[j] += alpha * dangling * tele[j]
        s = sum(nxt) or 1.0
        nxt = [v / s for v in nxt]
        if max(abs(a - b) for a, b in zip(nxt, x)) < tol:
            x = nxt
            break
        x = nxt
    return {n: x[idx[n]] for n in names}
