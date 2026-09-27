"""SPINE TASK 4 -- the Bellman EQUALITY GRAPH of the verified certificates (K=24, K=32).

Input: ../transient_2026-09-16/t5_cert.json (the VERIFIED certificates).
For every edge e = (u,v) with integer weight w_int (= ceil(P*DEN)) and potential phi:
      slack  delta(e) = theta + phi(u) - phi(v) - w(e)          [EXACT rationals, den = DEN]
with theta = theta_max = 137/1000.  Since the stored phi was built at rho_min, the edges
with delta(e) = theta - rho_min are exactly the edges TIGHT for the max-cycle-mean problem,
i.e. the Bellman equality graph of the optimal (rho_min) potential.

Reports: multiplicity of the minimum, near-equality shells, SCCs of the tight subgraph, its
max cycle mean (Karp, exact floats on integer weights), and the signatures of the tight
vertices.  Signature = (sum nblack over window // 40, max pre // 3, max depth // 2).

usage: python3 s4_bellman.py
"""
import json, os, sys
from fractions import Fraction
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tgraph import tarjan, karp_sub

DIR = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(DIR, "..", "transient_2026-09-16", "t5_cert.json")
CERT = json.load(open(SRC))
THETA = Fraction(137, 1000)
OUT = {}
L = []


def pr(s=""):
    print(s)
    L.append(s)


pr("=" * 100)
pr("SPINE TASK 4 -- Bellman equality graph (EXACT rationals)")
pr("=" * 100)

for Ks in ("24", "32"):
    C = CERT[Ks]
    DEN = C["DEN"]
    verts = [tuple(v["state"]) for v in C["vertices"]]
    phi = [Fraction(v["phi_int"], DEN) for v in C["vertices"]]
    rho_min = Fraction(C["rho_min"])
    E = [(e["u"], e["v"], Fraction(e["w_int"], DEN)) for e in C["edges"]]
    n = len(verts)
    slacks = [THETA + phi[u] - phi[v] - w for (u, v, w) in E]
    dmin = min(slacks)
    pr()
    pr("-" * 100)
    pr(f"K = {Ks}:  |V| = {n}, |E| = {len(E)}, rho_min = {rho_min} = {float(rho_min):.6f}, "
       f"theta = {THETA}")
    pr(f"  min slack delta_min = {dmin} = {float(dmin):.9f}   "
       f"(= theta - rho_min ? {dmin == THETA - rho_min})")
    mult = sum(1 for s in slacks if s == dmin)
    pr(f"  edges AT the minimum: {mult} / {len(E)}  ({100.0*mult/len(E):.2f}%)")
    ss = sorted(set(slacks))
    pr(f"  distinct slack values: {len(ss)};  smallest 12: " +
       ", ".join(f"{float(x):.6f}" for x in ss[:12]))
    # gap above the minimum
    if len(ss) > 1:
        pr(f"  GAP above the minimum slack: {ss[1]-ss[0]} = {float(ss[1]-ss[0]):.9f}")
    shells = {}
    for eps in (0, Fraction(1, 1000), Fraction(5, 1000), Fraction(1, 100), Fraction(2, 100)):
        thr = dmin + eps
        sub = [(u, v, w) for (u, v, w), s in zip(E, slacks) if s <= thr]
        nodes = sorted({u for u, v, w in sub} | {v for u, v, w in sub})
        adj = [[] for _ in range(n)]
        for (u, v, w) in sub:
            adj[u].append(v)
        comp, nc = tarjan(n, adj)
        # nontrivial SCCs restricted to nodes touched
        cnt = {}
        for x in nodes:
            cnt[comp[x]] = cnt.get(comp[x], 0) + 1
        big = sorted([c for c in cnt if cnt[c] > 1], key=lambda c: -cnt[c])
        selfloops = [(u, v) for (u, v, w) in sub if u == v]
        ed = {}
        for (u, v, w) in sub:
            if (u, v) not in ed or w > ed[(u, v)]:
                ed[(u, v)] = float(w)
        mcm, cyc = (None, None)
        if nodes:
            mcm, cyc = karp_sub(nodes, ed)
        shells[str(float(eps))] = {
            "edges": len(sub), "vertices": len(nodes),
            "nontrivial_SCCs": [cnt[c] for c in big], "self_loops": len(selfloops),
            "max_cycle_mean": None if mcm is None or mcm == float("-inf") else mcm,
            "cycle": [list(verts[i]) for i in cyc] if cyc else None}
        pr(f"  shell eps={float(eps):<7.4f}: |E'|={len(sub):>4} |V'|={len(nodes):>4} "
           f"self-loops={len(selfloops):>3} nontrivial SCC sizes={[cnt[c] for c in big][:6]} "
           f"max cycle mean={('none' if mcm is None or mcm==float('-inf') else f'{mcm:.6f}')}")
        if cyc:
            pr(f"      a max-mean cycle: {[list(verts[i]) for i in cyc]}")
    # tight vertices
    tight = [(u, v) for (u, v, w), s in zip(E, slacks) if s == dmin]
    tv = sorted({u for u, v in tight} | {v for u, v in tight})
    pr(f"  tight subgraph touches {len(tv)} vertices; their signatures "
       f"(sum_nblack//40, max_pre//3, max_depth//2):")
    for i in tv:
        outd = sum(1 for u, v in tight if u == i)
        ind = sum(1 for u, v in tight if v == i)
        pr(f"      {verts[i]}  phi={phi[i]} ({float(phi[i]):+.6f})  tight out={outd} in={ind}")
    # where does the maximum-weight edge sit?
    wmax = max(w for u, v, w in E)
    pr(f"  max edge weight = {wmax} = {float(wmax):.6f}; attained on "
       f"{sum(1 for u,v,w in E if w==wmax)} edge(s):")
    for (u, v, w) in E:
        if w == wmax:
            pr(f"      {verts[u]} -> {verts[v]}   slack={float(THETA+phi[u]-phi[v]-w):.6f}")
    OUT[Ks] = {"n": n, "m": len(E), "rho_min": str(rho_min), "delta_min": str(dmin),
               "mult_min": mult, "n_distinct_slacks": len(ss),
               "slack_gap_above_min": str(ss[1] - ss[0]) if len(ss) > 1 else None,
               "shells": shells,
               "tight_vertices": [{"state": list(verts[i]), "phi": str(phi[i])} for i in tv],
               "max_edge_weight": str(wmax)}

json.dump(OUT, open(os.path.join(DIR, "s4_bellman.json"), "w"), indent=1)
open(os.path.join(DIR, "S4_BELLMAN.txt"), "w").write("\n".join(L) + "\n")
print("\nwrote s4_bellman.json / S4_BELLMAN.txt")
