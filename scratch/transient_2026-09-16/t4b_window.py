"""TASK 4 (window level) -- the operationally meaningful compatibility graph.

A K-window already averages the pressure over 2K blocks, and a DISJOINT tiling
j, j+2K, j+4K, ... is what actually multiplies up into a long product.  So:

  vertex   sigma_j = a coarse structural signature of the window at anchor j
  edge     sigma_j -> sigma_{j+2K}   (disjoint successor), all offsets, all environments
  weight   P_j = max_S log2(M_2K/M_K)(S)/(2K)      [bits per digit-step]

Cycles of this graph are exactly the itineraries of disjoint windows that could repeat.
Tarjan -> nontrivial SCCs -> Karp gives the max cycle mean.  We also report the
RECURRENCE of the bad windows: how many of the windows with P_j > theta_max sit in a
nontrivial SCC at all.  That is the direct test of the transience hypothesis.

Also reported (assumption free): the longest run of consecutive BAD windows in a disjoint
tiling, over every environment and every offset.

usage: python3 t4b_window.py
"""
import json, math, os
from tload import load, series, THETA_MAX

DIR = os.path.dirname(os.path.abspath(__file__))
from tgraph import tarjan, karp_sub

DATA = {}
for J in (400, 800):
    meta, envs = load(J)
    if envs:
        DATA[J] = envs


def bucket(x, w):
    return int(x // w)


def sigs(pre, nbl, dep, j, K, G, wnb, wpre, wdep):
    """coarse signature of the window [j, j+2K): G groups of bucketed black counts,
    plus bucketed max prefix run and bucketed max depth."""
    L = 2 * K
    g = L // G
    t = []
    for u in range(G):
        s = sum(nbl[j + u * g: j + (u + 1) * g])
        t.append(bucket(s, wnb))
    t.append(bucket(max(pre[j:j + L]), wpre))
    t.append(bucket(max(dep[j:j + L]), wdep))
    return tuple(t)


print("=" * 110)
print("TASK 4b -- DISJOINT-TILING window graph (true low-frequency environments only)")
print("=" * 110)
print("  recur   = fraction of window occurrences whose state lies in a nontrivial SCC")
print("  badrec  = same, restricted to windows with P_j > theta_max = 0.137")
print("  mu_max  = max cycle mean of P over the graph; target = 0.137")
print()
OUT = {}
print(f"  {'K':>3} {'G':>2} {'wnb':>4} {'wpre':>4} {'wdep':>4} {'|V|':>6} {'|E|':>6} "
      f"{'#SCC>1':>7} {'recur':>7} {'badrec':>7} {'maxP':>7} {'mu_max':>9} {'<target':>8}")
for K in (16, 24, 32):
    for (G, wnb, wpre, wdep) in [(1, 10 ** 9, 10 ** 9, 10 ** 9), (1, 40, 3, 2),
                                 (2, 20, 3, 2), (4, 10, 2, 1), (4, 5, 1, 1),
                                 (8, 5, 1, 1)]:
        ew = {}
        occ = []
        badocc = []
        maxrun_disj = 0
        maxP = -9.0
        for J in DATA:
            for lam, rec in DATA[J].items():
                s = series(rec, K)
                if s is None:
                    continue
                j0, P = s
                pre, nbl, dep = rec["pre"], rec["nblack"], rec["depth"]
                n = len(P)
                Pmap = {j0 + i: P[i] for i in range(n)}
                maxP = max(maxP, max(P))
                for off in range(2 * K):
                    seq = list(range(j0 + off, j0 + n, 2 * K))
                    run = best = 0
                    for j in seq:
                        if Pmap[j] > THETA_MAX:
                            run += 1
                            best = max(best, run)
                        else:
                            run = 0
                    maxrun_disj = max(maxrun_disj, best)
                    for t in range(len(seq) - 1):
                        j, jn = seq[t], seq[t + 1]
                        s1 = sigs(pre, nbl, dep, j, K, G, wnb, wpre, wdep)
                        s2 = sigs(pre, nbl, dep, jn, K, G, wnb, wpre, wdep)
                        w = Pmap[j]
                        occ.append((s1, w))
                        if w > THETA_MAX:
                            badocc.append(s1)
                        k = (s1, s2)
                        if k not in ew or w > ew[k]:
                            ew[k] = w
        verts = sorted({u for u, v in ew} | {v for u, v in ew})
        ix = {v: i for i, v in enumerate(verts)}
        adj = [[] for _ in verts]
        for (u, v) in ew:
            adj[ix[u]].append(ix[v])
        comp, nc = tarjan(len(verts), adj)
        members = {}
        for i, c in enumerate(comp):
            members.setdefault(c, []).append(i)
        selfl = set(ix[u] for (u, v) in ew if u == v)
        nontriv = {c for c, ms in members.items()
                   if len(ms) > 1 or (len(ms) == 1 and ms[0] in selfl)}
        rec_states = {verts[i] for c in nontriv for i in members[c]}
        nrec = sum(1 for s, w in occ if s in rec_states)
        nbadrec = sum(1 for s in badocc if s in rec_states)
        mu = float("-inf")
        cyc = None
        for c in nontriv:
            ms = members[c]
            nodes = [verts[i] for i in ms]
            ns = set(nodes)
            sub = {(u, v): w for (u, v), w in ew.items() if u in ns and v in ns}
            if not sub or len(nodes) > 700:
                continue
            m, cy = karp_sub(nodes, sub)
            if m > mu:
                mu, cyc = m, cy
        print(f"  {K:>3} {G:>2} {min(wnb,999):>4} {min(wpre,999):>4} {min(wdep,999):>4} "
              f"{len(verts):>6} {len(ew):>6} {len(nontriv):>7} "
              f"{nrec/len(occ):>7.4f} "
              f"{(nbadrec/len(badocc) if badocc else 0):>7.4f} {maxP:>7.4f} "
              f"{(f'{mu:.5f}' if mu > -1e8 else '  none'):>9} "
              f"{('YES' if mu < THETA_MAX else 'NO'):>8}")
        OUT[f"K{K}_G{G}_{wnb}_{wpre}_{wdep}"] = {
            "V": len(verts), "E": len(ew), "nontrivSCC": len(nontriv),
            "occ": len(occ), "bad": len(badocc), "recur": nrec / len(occ),
            "badrecur": (nbadrec / len(badocc) if badocc else 0),
            "mu_max": mu if mu > -1e8 else None,
            "cycle": [str(x) for x in cyc] if cyc else None,
            "maxrun_disjoint_bad": maxrun_disj}
    print(f"      K={K}: longest run of consecutive BAD windows in ANY disjoint tiling "
          f"(all offsets, all environments) = {maxrun_disj}")
json.dump(OUT, open(os.path.join(DIR, "t4b_window.json"), "w"), indent=1)
print("\nwrote t4b_window.json")
