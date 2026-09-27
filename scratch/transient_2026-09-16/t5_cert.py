"""TASK 5 -- exact Bellman potential for the window-level disjoint-tiling graph.

Graph (from t4b_window.py):
   vertex  sigma_j = ( floor(sum of black counts over the window / 40),
                       floor(max prefix-black-run over the window / 3),
                       floor(max triangle depth over the window / 2) )
   edge    sigma_j -> sigma_{j+2K}   for every anchor j and every offset, every environment
   weight  w(edge) = max over occurrences of P_j = max_S log2(M_2K/M_K)(S)/(2K)

Certificate: integers on the common denominator DEN = 10^6, with every edge weight
ROUNDED UP (w_int = ceil(P*DEN) >= P*DEN), so the verified integer inequality
     w_int(u,v) + phi(v) - phi(u) <= rho_int
implies the real inequality for the float pressures.  delta_min is the minimum slack.

Also: binary search for the SMALLEST rho that admits a potential (= the exact max cycle
mean of the integer-rounded graph).

usage: python3 t5_cert.py
"""
import json, math, os
from fractions import Fraction
from tload import load, series, THETA_MAX
from tgraph import tarjan, karp_sub

DIR = os.path.dirname(os.path.abspath(__file__))
DEN = 10 ** 6
WNB, WPRE, WDEP = 40, 3, 2

DATA = {}
for J in (400, 800):
    meta, envs = load(J)
    if envs:
        DATA[J] = envs


def sig(pre, nbl, dep, j, K):
    L = 2 * K
    return (int(sum(nbl[j:j + L]) // WNB), int(max(pre[j:j + L]) // WPRE),
            int(max(dep[j:j + L]) // WDEP))


def build(K):
    ew = {}
    occ = {}
    for J in DATA:
        for lam, rec in DATA[J].items():
            s = series(rec, K)
            if s is None:
                continue
            j0, P = s
            pre, nbl, dep = rec["pre"], rec["nblack"], rec["depth"]
            n = len(P)
            Pm = {j0 + i: P[i] for i in range(n)}
            for off in range(2 * K):
                seq = list(range(j0 + off, j0 + n, 2 * K))
                for t in range(len(seq) - 1):
                    a, b = seq[t], seq[t + 1]
                    s1 = sig(pre, nbl, dep, a, K)
                    s2 = sig(pre, nbl, dep, b, K)
                    w = Pm[a]
                    occ[s1] = occ.get(s1, 0) + 1
                    if (s1, s2) not in ew or w > ew[(s1, s2)]:
                        ew[(s1, s2)] = w
    return ew, occ


def bellman(E, n, rho_int):
    phi = [0] * n
    rounds, changed = 0, True
    while changed and rounds <= n + 2:
        changed = False
        rounds += 1
        for (u, v, wi) in E:
            c = phi[u] + rho_int - wi
            if c < phi[v]:
                phi[v] = c
                changed = True
    return (None if changed else phi), rounds


CERTS = {}
print("=" * 100)
print("TASK 5 -- exact Bellman potential, window-level disjoint-tiling graph")
print("=" * 100)
for K in (16, 24, 32):
    ew, occ = build(K)
    verts = sorted({u for u, v in ew} | {v for u, v in ew})
    ix = {v: i for i, v in enumerate(verts)}
    n = len(verts)
    E = [(ix[u], ix[v], int(math.ceil(w * DEN))) for (u, v), w in ew.items()]
    print(f"\nK={K}: |V| = {n}, |E| = {len(E)}, "
          f"{sum(occ.values())} window occurrences, max edge weight "
          f"{max(w for _, _, w in E)/DEN:.6f}")
    # smallest certifiable rho (exact integer binary search = exact max cycle mean of the
    # integer-rounded graph)
    lo, hi = -10 ** 6, 10 ** 6
    while lo < hi:
        mid = (lo + hi) // 2
        phi, _ = bellman(E, n, mid)
        if phi is None:
            lo = mid + 1
        else:
            hi = mid
    rho_min = lo
    print(f"  SMALLEST certifiable rho (exact integer bisection) = {Fraction(rho_min, DEN)}"
          f" = {rho_min/DEN:.6f} bits/step")
    T = int(round(THETA_MAX * DEN))
    # build the potential at rho_min, then measure the slack against theta_max: this gives a
    # UNIFORM positive slack (>= theta_max - rho_min) instead of the 0 that the shortest-path
    # solution at rho = theta_max necessarily has on its tree edges.
    phi, rounds = bellman(E, n, rho_min)
    if phi is not None and rho_min > T:
        phi = None
    if phi is None:
        print(f"  target theta_max = {THETA_MAX}: NO potential exists "
              f"(a cycle of mean > theta_max is realised)")
        CERTS[str(K)] = {"K": K, "V": n, "E": len(E), "rho_min": str(Fraction(rho_min, DEN)),
                         "rho_min_float": rho_min / DEN, "certificate_at_theta_max": False}
        continue
    slack = min(T - wi - phi[v] + phi[u] for (u, v, wi) in E)
    okall = all(wi + phi[v] - phi[u] <= T for (u, v, wi) in E)
    fr = Fraction(slack, DEN)
    print(f"  potential built at rho_min = {Fraction(rho_min,DEN)}; Bellman-Ford converged in "
          f"{rounds} passes")
    print(f"  EVERY edge verified in exact integers: {okall}")
    print(f"  delta_min = {fr} = {float(fr):+.9f} bits/step")
    print(f"  phi in [{Fraction(min(phi),DEN)}, {Fraction(max(phi),DEN)}] "
          f"= [{min(phi)/DEN:.6f}, {max(phi)/DEN:.6f}]")
    # exact re-verification with Fractions (independent of the integer loop)
    RT = Fraction(T, DEN)
    bad = 0
    mnf = None
    for (u, v, wi) in E:
        lhs = Fraction(wi, DEN) + Fraction(phi[v], DEN) - Fraction(phi[u], DEN)
        d = RT - lhs
        if d < 0:
            bad += 1
        if mnf is None or d < mnf:
            mnf = d
    print(f"  independent Fraction re-verification: violations = {bad}, "
          f"min slack = {mnf} = {float(mnf):+.9f}")
    CERTS[str(K)] = {
        "K": K, "V": n, "E": len(E),
        "signature": f"(sum_nblack//{WNB}, max_pre//{WPRE}, max_depth//{WDEP}) over [j, j+2K)",
        "DEN": DEN, "rho": str(Fraction(T, DEN)), "rho_float": T / DEN,
        "rho_min": str(Fraction(rho_min, DEN)), "rho_min_float": rho_min / DEN,
        "delta_min": str(fr), "delta_min_float": float(fr),
        "bellman_passes": rounds, "all_edges_verified": bool(okall and bad == 0),
        "vertices": [{"i": i, "state": list(v), "phi_int": phi[i]} for i, v in enumerate(verts)],
        "edges": [{"u": u, "v": v, "w_int": wi} for (u, v, wi) in E],
        "note": ("w_int = ceil(P*DEN) >= P*DEN.  Verified statement, exact integers: for every "
                 "edge (u,v), w_int(u,v) + phi(v) - phi(u) <= rho*DEN.  Hence for every cycle C, "
                 "(1/|C|) sum P <= rho.  The pressures P themselves come from floating-point "
                 "transfer-operator arithmetic on exact 3-adic input -- the only inexact step. "
                 "The graph contains ONLY states and transitions observed in the 30 true "
                 "low-frequency environments (lambda in {1,3,5,7,9,11,13,17,19,23,25,29,31,101,"
                 "1025}, J in {400,800}); it is NOT a bound over all 3-adic units.")}

json.dump(CERTS, open(os.path.join(DIR, "t5_cert.json"), "w"), indent=1)
print("\nwrote t5_cert.json")
