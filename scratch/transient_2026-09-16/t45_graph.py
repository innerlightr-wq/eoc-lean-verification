"""TASKS 4 + 5 -- compatibility graph of the TRUE low-frequency environments,
max cycle mean, Bellman potential, exactly verified.

WEIGHT (exact additive decomposition, see t4_corpus.py):
    a_r = log2 max_S M_{Rend-r}(r)[S],  a_Rend = 0,   w_r = (a_r - a_{r+1})/2,
    sum_{r0<=r<r1} w_r = (a_{r0}-a_{r1})/2  and  mean over [r0,Rend) = Lambda(r0,.),
so w is a genuine per-block cost in bits per ternary digit-step; target = theta_max = 0.137.

GRAPH.  Vertex = a symbolic local state sigma_r of the environment; EDGE = an observed
transition sigma_r -> sigma_{r+1} carrying the ACTUAL weight w_r of that occurrence
(parallel edges collapsed to their max).  Only states/transitions that occur in the TRUE
low-frequency corpus are kept.  A cycle of the graph is a symbolic itinerary that could in
principle repeat forever; its mean weight bounds the long-run pressure of any environment
realising it.  Cycles live inside the nontrivial strongly connected components, so we
Tarjan-decompose first and run Karp only inside each nontrivial SCC.

TRANSIENCE TEST (the central hypothesis).  A block occurrence whose state lies in a trivial
SCC can NEVER recur in this graph -- it is structurally transient.  We report the fraction of
all blocks, and of HIGH-weight blocks, that are recurrent.

usage: python3 t45_graph.py [designs...]
"""
import json, math, os, sys
from fractions import Fraction

DIR = os.path.dirname(os.path.abspath(__file__))
THETA_MAX = 0.137
DEN = 10 ** 6
MARGIN = 20
CORP = json.load(open(os.path.join(DIR, "corpus.json")))


def clip(x, c):
    return x if x < c else c


def state_fn(D, F, C=8, use_phase=False, nb=0):
    def f(c, r):
        t = tuple(clip(c["pre"][r + i], C) for i in range(-D, F + 1))
        if use_phase:
            t = t + (tuple(c["phase"][r]),)
        if nb:
            t = t + tuple(clip(c["nblack"][r + i] // nb, 8) for i in range(-0, F + 1))
        return t
    return f


def build(f, D, F):
    """returns verts, edge dict (u,v)->maxw, occ list [(state, w)]"""
    ew = {}
    occ = []
    for c in CORP:
        Rend = c["Rend"]
        lo = max(8, D)
        hi = Rend - MARGIN - F - 1
        for r in range(lo, hi):
            s1 = f(c, r)
            s2 = f(c, r + 1)
            w = c["w"][r]
            occ.append((s1, w))
            k = (s1, s2)
            if k not in ew or w > ew[k]:
                ew[k] = w
    verts = sorted({u for u, v in ew} | {v for u, v in ew})
    return verts, ew, occ


from tgraph import tarjan, karp_sub


def analyse(name, f, D, F):
    incomplete = [False]
    verts, ew, occ = build(f, D, F)
    ix = {v: i for i, v in enumerate(verts)}
    n = len(verts)
    adj = [[] for _ in range(n)]
    for (u, v) in ew:
        adj[ix[u]].append(ix[v])
    comp, nc = tarjan(n, adj)
    members = {}
    for i, c in enumerate(comp):
        members.setdefault(c, []).append(i)
    selfloop = set(ix[u] for (u, v) in ew if u == v)
    nontriv = {c for c, ms in members.items()
               if len(ms) > 1 or (len(ms) == 1 and ms[0] in selfloop)}
    recur_states = {verts[i] for c in nontriv for i in members[c]}
    nrec = sum(1 for s, w in occ if s in recur_states)
    hi_occ = [(s, w) for s, w in occ if w > THETA_MAX]
    nrec_hi = sum(1 for s, w in hi_occ if s in recur_states)
    mu, cyc = float("-inf"), None
    ncyc_scc = 0
    for c in nontriv:
        ms = members[c]
        nodes = [verts[i] for i in ms]
        ns = set(nodes)
        sub = {(u, v): w for (u, v), w in ew.items() if u in ns and v in ns}
        if not sub:
            continue
        ncyc_scc += 1
        if len(nodes) > 900:
            print(f"    (SCC of size {len(nodes)} too large for Karp -- mu_max below is a "
                  f"LOWER bound only; the exact answer comes from the Bellman-Ford test)")
            incomplete[0] = True
            continue
        m, cy = karp_sub(nodes, sub)
        if m > mu:
            mu, cyc = m, cy
    return {"name": name, "V": n, "E": len(ew), "occ": len(occ),
            "maxw": max(w for _, w in occ),
            "nontrivial_SCC": len(nontriv),
            "recurrent_states": len(recur_states),
            "recurrent_occ": nrec, "recurrent_frac": nrec / len(occ),
            "high_occ": len(hi_occ), "high_recurrent": nrec_hi,
            "high_recurrent_frac": (nrec_hi / len(hi_occ)) if hi_occ else 0.0,
            "mu_max": mu, "cycle_len": len(cyc) if cyc else 0,
            "cycle": [str(x) for x in cyc] if cyc else None,
            "incomplete": incomplete[0], "ew": ew, "verts": verts}


DESIGNS = [
    ("pre D0F0", state_fn(0, 0)),
    ("pre D1F1", state_fn(1, 1)),
    ("pre D2F2", state_fn(2, 2)),
    ("pre D2F2+ph", state_fn(2, 2, use_phase=True)),
    ("pre D3F3", state_fn(3, 3)),
    ("pre D4F4", state_fn(4, 4)),
    ("pre D4F4+ph", state_fn(4, 4, use_phase=True)),
    ("pre D6F6", state_fn(6, 6)),
    ("pre D8F8", state_fn(8, 8)),
    ("pre D6F6+nb3", state_fn(6, 6, nb=3)),
]
DF = {"pre D0F0": (0, 0), "pre D1F1": (1, 1), "pre D2F2": (2, 2), "pre D2F2+ph": (2, 2),
      "pre D3F3": (3, 3), "pre D4F4": (4, 4), "pre D4F4+ph": (4, 4), "pre D6F6": (6, 6),
      "pre D8F8": (8, 8), "pre D6F6+nb3": (6, 6)}

print("=" * 108)
print("TASK 4 -- block-level compatibility graph, TRUE low-frequency environments only")
print("=" * 108)
print(f"corpus: {len(CORP)} environments; target theta_max = {THETA_MAX} bits/step")
print(f"  {'state design':14} {'|V|':>6} {'|E|':>7} {'#SCC>1':>7} {'recur':>7} {'hi-recur':>9} "
      f"{'max w':>7} {'mu_max':>9} {'<target':>8}")
RES = {}
best_cert = None
for name, f in DESIGNS:
    D, F = DF[name]
    r = analyse(name, f, D, F)
    RES[name] = {k: v for k, v in r.items() if k not in ("ew", "verts")}
    mu = r["mu_max"]
    print(f"  {name:14} {r['V']:>6} {r['E']:>7} {r['nontrivial_SCC']:>7} "
          f"{r['recurrent_frac']:>7.4f} {r['high_recurrent_frac']:>9.4f} "
          f"{r['maxw']:>7.4f} "
          f"{(f'{mu:.5f}' if mu > -1e8 else 'no cycle'):>9} "
          f"{('YES' if mu < THETA_MAX else 'NO')+('?' if r['incomplete'] else ''):>8}")
    if mu < THETA_MAX and not r["incomplete"] and best_cert is None:
        best_cert = (name, r)

print()
if best_cert:
    nm, r = best_cert
    print(f"SMALLEST STATE THAT CLOSES: '{nm}'  |V|={r['V']} |E|={r['E']}  "
          f"mu_max = {r['mu_max']:.6f} < {THETA_MAX}")
else:
    nm = max(RES, key=lambda k: -RES[k]["mu_max"] if RES[k]["mu_max"] > -1e8 else -1e9)
    print("NO tested design gives a finite mu_max below the target; see the table.")
for name in RES:
    if RES[name]["cycle"]:
        print(f"  argmax cycle of '{name}' (length {RES[name]['cycle_len']}, "
              f"mu = {RES[name]['mu_max']:.5f}):")
        for s in RES[name]["cycle"][:8]:
            print(f"      {s}")
        break

# ---------------------------------------------------------------- TASK 5
print()
print("=" * 108)
print("TASK 5 -- Bellman potential on the FULL graph, verified in exact integer arithmetic")
print("=" * 108)
CERT = None
for name, f in DESIGNS:
    D, F = DF[name]
    verts, ew, occ = build(f, D, F)
    n = len(verts)
    ix = {v: i for i, v in enumerate(verts)}
    T = int(round(THETA_MAX * DEN))
    # integer edge weights, rounded UP so the certificate covers the float weights
    E = [(ix[u], ix[v], int(math.ceil(w * DEN))) for (u, v), w in ew.items()]
    phi = [0] * n
    rounds, changed = 0, True
    while changed and rounds <= n + 2:
        changed = False
        rounds += 1
        for (u, v, wi) in E:
            cand = phi[u] + T - wi
            if cand < phi[v]:
                phi[v] = cand
                changed = True
    if changed:
        print(f"  '{name}': integer Bellman-Ford DID NOT converge "
              f"(a cycle with mean > {THETA_MAX} exists) -- no certificate")
        continue
    slack = min(T - wi - phi[v] + phi[u] for (u, v, wi) in E)
    okall = all(wi + phi[v] - phi[u] <= T for (u, v, wi) in E)
    fr = Fraction(slack, DEN)
    print(f"  '{name}': |V|={n} |E|={len(E)}; Bellman-Ford converged in {rounds} passes")
    print(f"     every edge verified exactly (integers, DEN={DEN}): {okall}")
    print(f"     delta_min = {fr} = {float(fr):+.9f} bits/step;  "
          f"phi range [{min(phi)/DEN:.5f}, {max(phi)/DEN:.5f}]")
    if CERT is None and okall:
        CERT = {"design": name, "DEN": DEN, "target_int": T,
                "target": str(Fraction(T, DEN)), "V": n, "E": len(E),
                "mu_max_float": RES[name]["mu_max"],
                "delta_min": str(fr), "delta_min_float": float(fr),
                "bellman_passes": rounds, "all_edges_verified": True,
                "vertices": [{"i": i, "state": str(v), "phi_int": phi[i]}
                             for i, v in enumerate(verts)],
                "edges": [{"u": u, "v": v, "w_int": wi} for (u, v, wi) in E],
                "note": ("w_int = ceil(w*DEN) >= w.  The verified statement is the exact "
                         "integer inequality w_int(u,v) + phi(v) - phi(u) <= target_int for "
                         "EVERY edge, hence w(u,v) + phi(v)/DEN - phi(u)/DEN <= target. "
                         "The weights w themselves come from floating-point transfer-operator "
                         "arithmetic on exact 3-adic input; that is the only inexact step.")}

json.dump({"results": RES, "certificate": CERT},
          open(os.path.join(DIR, "t45_graph.json"), "w"), indent=1)
print("\nwrote t45_graph.json")
