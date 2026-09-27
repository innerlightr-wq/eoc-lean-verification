"""TASKS 2 + 3 -- episode decomposition and the excess/credit budget.

Episode (as specified): ENTRY at the first j with P_j > theta_max; the episode CONTINUES
while P_j > theta_safe and ENDS at the first j with P_j <= theta_safe.
Return time = (entry of next episode) - (end of this episode).

UNITS.  P_j is already a log2 quantity (bits per block: P_j = log2(M_2K/M_K)/(2K)),
so the meaningful budget is measured in P-units, not in log2(P).  We report
   excess(E)   = sum_{j in E} max(0, P_j - rho)              [bits per block, summed]
   credit      = sum_{j not in any E} max(0, rho - P_j)
and, for completeness, the literal reading  sum log2(P_j/rho)  as well.

OVERLAP CAVEAT.  Stride-1 windows of length 2K overlap, so a single bad region is counted
up to 2K times.  We therefore also report a DISJOINT tiling (anchors j = j0, j0+2K, ...)
which is the version that actually bounds a long product.

usage: python3 t23_episodes.py
"""
import json, math, os, statistics
from tload import load, series, THETA_MAX

SAFE = [0.10, 0.08, 0.06]
RHOS = [THETA_MAX, 0.10]
out = {"theta_max": THETA_MAX, "theta_safe": SAFE, "rho": RHOS, "episodes": {}, "budget": {}}


def episodes(P, tmax, tsafe):
    """list of (start_idx, end_idx_exclusive, peak, sumP)."""
    eps = []
    i, n = 0, len(P)
    while i < n:
        if P[i] > tmax:
            k = i
            while k < n and P[k] > tsafe:
                k += 1
            eps.append((i, k, max(P[i:k]), sum(P[i:k])))
            i = k
        else:
            i += 1
    return eps


def stats(xs):
    if not xs:
        return None
    xs = sorted(xs)
    return (xs[0], xs[len(xs) // 2], xs[-1], sum(xs) / len(xs))


print("=" * 100)
print("TASK 2 -- EPISODE DECOMPOSITION (stride-1 anchors, true low-frequency environments)")
print("=" * 100)
ALL = {}
for J in (400, 800):
    meta, envs = load(J)
    if not envs:
        continue
    ALL[J] = envs
    for K in (16, 24, 32):
        for tsafe in SAFE:
            durs, peaks, sums, rets, nep = [], [], [], [], 0
            per_lam = {}
            for lam in sorted(envs):
                s = series(envs[lam], K)
                if s is None:
                    continue
                j0, P = s
                eps = episodes(P, THETA_MAX, tsafe)
                nep += len(eps)
                for a, b, pk, sm in eps:
                    durs.append(b - a)
                    peaks.append(pk)
                    sums.append(sm)
                for u in range(len(eps) - 1):
                    rets.append(eps[u + 1][0] - eps[u][1])
                if eps:
                    per_lam[lam] = [[j0 + a, b - a, round(pk, 5)] for a, b, pk, sm in eps]
            if nep == 0:
                print(f"J={J} K={K:2d} theta_safe={tsafe}:  NO EPISODES")
                continue
            d = stats(durs); p = stats(peaks); r = stats(rets)
            print(f"J={J} K={K:2d} theta_safe={tsafe}: {nep:3d} episodes over "
                  f"{len(per_lam)} lambda")
            print(f"      duration    min/med/max/mean = {d[0]:4d} /{d[1]:4d} /{d[2]:4d} / {d[3]:7.2f}")
            print(f"      peak P      min/med/max/mean = {p[0]:.4f} / {p[1]:.4f} / {p[2]:.4f} / {p[3]:.4f}")
            print(f"      sum P over E min/med/max/mean= {min(sums):.3f} / {sorted(sums)[len(sums)//2]:.3f}"
                  f" / {max(sums):.3f} / {sum(sums)/len(sums):.3f}")
            if r:
                print(f"      RETURN TIME min/med/max/mean = {r[0]:4d} /{r[1]:4d} /{r[2]:4d} / {r[3]:7.2f}"
                      f"      *** MIN RETURN TIME = {r[0]} ***")
            else:
                print("      RETURN TIME: only one episode per lambda, none measurable")
            out["episodes"][f"{J}_{K}_{tsafe}"] = {
                "n": nep, "dur": d, "peak": p, "ret": r,
                "per_lam": per_lam}

print()
print("=" * 100)
print("TASK 3 -- EXCESS / CREDIT BUDGET   (does the quiet stretch pay for the burst?)")
print("=" * 100)
print("  excess = sum_{j in episode} max(0, P_j - rho);  credit = sum_{j outside} max(0, rho - P_j)")
print()
for J in sorted(ALL):
    envs = ALL[J]
    for K in (16, 24, 32):
        for rho in RHOS:
            for tsafe in (0.10, 0.06):
                tot_e = tot_c = 0.0
                tot_e_log = tot_c_log = 0.0
                de = dc = 0.0
                worst_lam = None
                worst_ratio = 0.0
                any_ep = False
                for lam in sorted(envs):
                    s = series(envs[lam], K)
                    if s is None:
                        continue
                    j0, P = s
                    eps = episodes(P, THETA_MAX, tsafe)
                    inep = [False] * len(P)
                    for a, b, _, _ in eps:
                        for i in range(a, b):
                            inep[i] = True
                    e = sum(max(0.0, P[i] - rho) for i in range(len(P)) if inep[i])
                    c = sum(max(0.0, rho - P[i]) for i in range(len(P)) if not inep[i])
                    el = sum(max(0.0, math.log2(P[i] / rho)) for i in range(len(P))
                             if inep[i] and P[i] > 0)
                    cl = sum(max(0.0, math.log2(rho / P[i])) for i in range(len(P))
                             if not inep[i] and P[i] > 0)
                    tot_e += e; tot_c += c; tot_e_log += el; tot_c_log += cl
                    if e > 0:
                        any_ep = True
                        rt = e / c if c > 0 else float("inf")
                        if rt > worst_ratio:
                            worst_ratio, worst_lam = rt, lam
                    # disjoint tiling
                    idx = list(range(0, len(P), 2 * K))
                    Pd = [P[i] for i in idx]
                    epd = episodes(Pd, THETA_MAX, tsafe)
                    ind = [False] * len(Pd)
                    for a, b, _, _ in epd:
                        for i in range(a, b):
                            ind[i] = True
                    de += sum(max(0.0, Pd[i] - rho) for i in range(len(Pd)) if ind[i])
                    dc += sum(max(0.0, rho - Pd[i]) for i in range(len(Pd)) if not ind[i])
                if not any_ep:
                    continue
                print(f"J={J} K={K:2d} rho={rho:.3f} safe={tsafe}: "
                      f"excess={tot_e:8.4f}  credit={tot_c:9.4f}  ratio={tot_e/tot_c:8.5f}   "
                      f"| log2-form {tot_e_log:7.3f} / {tot_c_log:8.3f} = {tot_e_log/tot_c_log:7.4f}")
                print(f"{'':>34}disjoint tiling: excess={de:8.4f} credit={dc:8.4f} "
                      f"ratio={(de/dc if dc else float('inf')):8.5f}   worst single lambda "
                      f"e/c = {worst_ratio:.5f} (lam={worst_lam})")
                out["budget"][f"{J}_{K}_{rho}_{tsafe}"] = {
                    "excess": tot_e, "credit": tot_c, "ratio": tot_e / tot_c,
                    "excess_log": tot_e_log, "credit_log": tot_c_log,
                    "disjoint_excess": de, "disjoint_credit": dc,
                    "worst_lam": worst_lam, "worst_ratio": worst_ratio}

json.dump(out, open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                 "t23_episodes.json"), "w"), indent=1)
print("\nwrote t23_episodes.json")
