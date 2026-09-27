"""TASK 1 consolidation (adversarial-population densities) + TASK 7 threshold rule.

usage: python3 t1b_density.py
"""
import json, os
from tload import load, series, THETA_MAX

DIR = os.path.dirname(os.path.abspath(__file__))
LAMS = [1, 3, 5, 7, 9, 11, 13, 17, 19, 23, 25, 29, 31, 101, 1025]
OUT = {"theta_max": THETA_MAX}

print("=" * 104)
print("TASK 1 -- adversarial population density  a_N = #{j : P_j > theta_max} / N   (stride 1)")
print("=" * 104)
print("  lambda and 2*lambda give the same environment up to a shift of m; lambda and -lambda")
print("  give IDENTICAL black rows (blackness depends on |y|), so these odd positives are")
print("  orbit representatives.  lambda = 3, 9 are NOT 3-adic units (v_3 > 0) -- marked (*).")
print()
DATA = {}
for J in (400, 800):
    meta, envs = load(J)
    if envs:
        DATA[J] = envs
hdr = "  lam   "
for J in (400, 800):
    for K in (16, 24, 32):
        hdr += f" | J={J} K={K:2d}: a_N      maxP"
print(hdr)
tot = {}
for lam in LAMS:
    line = f"  {lam:5d}{'*' if lam % 3 == 0 else ' '} "
    for J in (400, 800):
        for K in (16, 24, 32):
            rec = DATA.get(J, {}).get(lam)
            s = series(rec, K) if rec else None
            if s is None:
                line += " |      -         -   "
                continue
            j0, P = s
            N = len(P)
            A = sum(1 for p in P if p > THETA_MAX)
            line += f" | {A:3d}/{N:3d} {A/N:7.5f} {max(P):7.4f}"
            tot.setdefault((J, K), []).append((lam, A, N, max(P)))
    print(line)
print()
print(f"  {'J':>4} {'K':>3} {'sum A_N':>8} {'sum N':>7} {'pooled a_N':>11} "
      f"{'max a_N':>9} {'argmax':>7} {'max P':>8} {'argmax':>7}")
for (J, K), rows in sorted(tot.items()):
    sA = sum(r[1] for r in rows)
    sN = sum(r[2] for r in rows)
    ma = max(rows, key=lambda r: r[1] / r[2])
    mp = max(rows, key=lambda r: r[3])
    print(f"  {J:>4} {K:>3} {sA:>8} {sN:>7} {sA/sN:>11.5f} "
          f"{ma[1]/ma[2]:>9.5f} {ma[0]:>7} {mp[3]:>8.4f} {mp[0]:>7}")
    OUT[f"{J}_{K}"] = {"sumA": sA, "sumN": sN, "pooled": sA / sN,
                       "max_density": ma[1] / ma[2], "argmax_density": ma[0],
                       "maxP": mp[3], "argmax_P": mp[0],
                       "per_lambda": [[r[0], r[1], r[2], r[3]] for r in rows]}

print()
print("=" * 104)
print("TASK 7d -- the best single-feature THRESHOLD rule for P_j > theta_max")
print("=" * 104)
print("  For each feature f and threshold t: sens = P(f >= t | bad), spec = P(f < t | good).")
print("  We report the t maximising Youden's J = sens + spec - 1, plus the t that gives")
print("  sens = 1 (a genuine NECESSARY condition) and its density.\n")


def feats(rec, j, K):
    L = 2 * K
    pre, nbl, dep = rec["pre"], rec["nblack"], rec["depth"]
    return {"sum nblack": sum(nbl[j:j + L]),
            "mean nblack": sum(nbl[j:j + L]) / L,
            "max nblack": max(nbl[j:j + L]),
            "max depth": max(dep[j:j + L]),
            "max pre": max(pre[j:j + L]),
            "max 8-blk nblack": max(sum(nbl[j + a:j + a + 8]) for a in range(L - 7))}


T7 = {}
for J in (400, 800):
    for K in (16, 24):
        recs = []
        for lam, rec in DATA.get(J, {}).items():
            s = series(rec, K)
            if s is None:
                continue
            j0, P = s
            for i, p in enumerate(P):
                recs.append((feats(rec, j0 + i, K), p > THETA_MAX))
        if not recs:
            continue
        nb = sum(1 for _, b in recs if b)
        ng = len(recs) - nb
        if nb == 0:
            continue
        print(f"J={J} K={K}: {nb} bad / {len(recs)}")
        print(f"  {'feature':18} {'best t':>9} {'sens':>6} {'spec':>6} {'Youden':>7} "
              f"| {'t for sens=1':>12} {'density':>8}")
        for name in recs[0][0]:
            vals = sorted({f[name] for f, _ in recs})
            bestJ, bt, bs, bp = -2, None, 0, 0
            for t in vals:
                se = sum(1 for f, b in recs if b and f[name] >= t) / nb
                sp = sum(1 for f, b in recs if not b and f[name] < t) / ng
                if se + sp - 1 > bestJ:
                    bestJ, bt, bs, bp = se + sp - 1, t, se, sp
            t1 = min(f[name] for f, b in recs if b)
            d1 = sum(1 for f, _ in recs if f[name] >= t1) / len(recs)
            print(f"  {name:18} {bt:>9.4g} {bs:>6.3f} {bp:>6.3f} {bestJ:>7.4f} "
                  f"| {t1:>12.4g} {d1:>8.4f}")
            T7.setdefault(f"{J}_{K}", {})[name] = {
                "best_t": bt, "sens": bs, "spec": bp, "youden": bestJ,
                "t_sens1": t1, "density_sens1": d1}
        print()
OUT["threshold"] = T7
json.dump(OUT, open(os.path.join(DIR, "t1b_density.json"), "w"), indent=1)
print("wrote t1b_density.json")
