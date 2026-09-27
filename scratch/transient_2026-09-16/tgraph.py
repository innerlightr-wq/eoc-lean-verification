"""Tarjan SCC + Karp max-cycle-mean helpers (shared by t45_graph.py and t4b_window.py)."""

def tarjan(n, adj):
    idx = [0] * n
    low = [0] * n
    on = [False] * n
    comp = [-1] * n
    stk = []
    counter = [1]
    nc = [0]
    for s in range(n):
        if idx[s]:
            continue
        work = [(s, 0)]
        while work:
            v, pi = work[-1]
            if pi == 0:
                idx[v] = low[v] = counter[0]
                counter[0] += 1
                stk.append(v)
                on[v] = True
            recurse = False
            for i in range(pi, len(adj[v])):
                u = adj[v][i]
                if not idx[u]:
                    work[-1] = (v, i + 1)
                    work.append((u, 0))
                    recurse = True
                    break
                elif on[u]:
                    if idx[u] < low[v]:
                        low[v] = idx[u]
            if recurse:
                continue
            if low[v] == idx[v]:
                while True:
                    u = stk.pop()
                    on[u] = False
                    comp[u] = nc[0]
                    if u == v:
                        break
                nc[0] += 1
            work.pop()
            if work:
                pv = work[-1][0]
                if low[v] < low[pv]:
                    low[pv] = low[v]
    return comp, nc[0]


def karp_sub(nodes, edges):
    """max cycle mean on the subgraph with given node list and edge dict (u,v)->w."""
    n = len(nodes)
    ix = {v: i for i, v in enumerate(nodes)}
    inc = [[] for _ in range(n)]
    for (u, v), w in edges.items():
        inc[ix[v]].append((ix[u], w))
    NEG = float("-inf")
    D = [[NEG] * n for _ in range(n + 1)]
    PAR = [[-1] * n for _ in range(n + 1)]
    for i in range(n):
        D[0][i] = 0.0
    for k in range(1, n + 1):
        Dk, Dp, Pk = D[k], D[k - 1], PAR[k]
        for v in range(n):
            best, bu = NEG, -1
            for (u, w) in inc[v]:
                if Dp[u] == NEG:
                    continue
                c = Dp[u] + w
                if c > best:
                    best, bu = c, u
            Dk[v] = best
            Pk[v] = bu
    mu, bv = NEG, None
    for v in range(n):
        if D[n][v] == NEG:
            continue
        m = float("inf")
        for k in range(n):
            if D[k][v] == NEG:
                continue
            val = (D[n][v] - D[k][v]) / (n - k)
            if val < m:
                m = val
        if m > mu:
            mu, bv = m, v
    cyc = None
    if bv is not None:
        path = [bv]
        v = bv
        for k in range(n, 0, -1):
            v = PAR[k][v]
            if v < 0:
                break
            path.append(v)
        seen = {}
        for i, v in enumerate(path):
            if v in seen:
                cyc = [nodes[j] for j in reversed(path[i:seen[v] + 1])]
                break
            seen[v] = i
    return mu, cyc


