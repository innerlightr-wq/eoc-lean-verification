"""TASK 5 -- is a SMALL statistic of the black pattern enough to predict the block weight?

Exact conditional-variance decomposition  R^2 = 1 - E[Var(w | stat)]/Var(w)  for discrete
statistics, plus OLS R^2 for the continuous/window ones.  J = 400, 15 lam.
usage: python3 t5_blackness.py
"""
import json, math, os
import qstat as S

DIR = os.path.dirname(os.path.abspath(__file__))
CORP = [r for r in json.load(open(os.path.join(DIR, "corpus.json"))) if r["J"] == 400]

L = []
L.append("TASK 5 -- variance of the block weight explained by black-pattern statistics (J=400)")
L.append("  'cond R2' = 1 - E[Var(w|stat)]/Var(w) (exact grouping);  'OLS R2' = linear fit.")
L.append("  #g = number of groups used by the conditional decomposition.")
L.append("")

AGG = {}
for rec in CORP:
    Rend = rec["Rend"]
    lo, hi = 2, Rend - 21
    w = rec["w"][lo:hi + 1]
    nb, dep, pre, ncell = rec["nblack"], rec["depth"], rec["pre"], rec["ncell"]
    sym = rec["sym"]

    def win(v, k, r):
        return sum(v[r:r + k])

    stats = {}
    stats["nblack_r"] = ([nb[r] for r in range(lo, hi + 1)], True)
    stats["nblack window 4"] = ([win(nb, 4, r) for r in range(lo, hi + 1)], True)
    stats["nblack window 8"] = ([win(nb, 8, r) for r in range(lo, hi + 1)], True)
    stats["maxdepth_r (bucket)"] = ([min(int(dep[r]), 6) for r in range(lo, hi + 1)], True)
    stats["prefix black run"] = ([pre[r] for r in range(lo, hi + 1)], True)
    stats["ncell_r"] = ([ncell[r] for r in range(lo, hi + 1)], True)
    stats["(nblack, sym)"] = ([(nb[r], sym[r]) for r in range(lo, hi + 1)], True)
    stats["(nblack, depth bucket)"] = ([(nb[r], min(int(dep[r]), 6)) for r in range(lo, hi + 1)], True)
    stats["(nblack_r, nblack_{r+1})"] = ([(nb[r], nb[r + 1]) for r in range(lo, hi + 1)], True)
    stats["(nb_r,nb_{r+1},nb_{r+2})"] = ([(nb[r], nb[r + 1], nb[r + 2]) for r in range(lo, hi + 1)], True)
    stats["nblack window 16"] = ([win(nb, 16, r) for r in range(lo, hi + 1)], True)

    n = len(w)
    for nm, (v, disc) in stats.items():
        r2, ng, wsd = S.group_r2(w, v)
        AGG.setdefault(nm, []).append((r2, ng, wsd, (ng - 1) / (n - 1), n))

    # OLS on numeric features
    feats = {
        "OLS: nblack_r": [[nb[r]] for r in range(lo, hi + 1)],
        "OLS: nblack_r + depth": [[nb[r], dep[r]] for r in range(lo, hi + 1)],
        "OLS: nb window4": [[win(nb, 4, r)] for r in range(lo, hi + 1)],
        "OLS: nb window8": [[win(nb, 8, r)] for r in range(lo, hi + 1)],
        "OLS: nb_r..nb_{r+3}": [[nb[r], nb[r + 1], nb[r + 2], nb[r + 3]] for r in range(lo, hi + 1)],
        "OLS: nb_r..nb_{r+7}": [[nb[r + k] for k in range(8)] for r in range(lo, hi + 1)],
        "OLS: nb_r..nb_{r+7}+sym": [[nb[r + k] for k in range(8)] + [sym[r]] for r in range(lo, hi + 1)],
        "OLS: ncell,nblack,depth,pre": [[ncell[r], nb[r], dep[r], pre[r]] for r in range(lo, hi + 1)],
    }
    for nm, X in feats.items():
        r2, rsd, _ = S.ols_r2(w, X)
        AGG.setdefault(nm, []).append((r2, len(X[0]) + 1, rsd, len(X[0]) / (n - 1), n))

hdr = (f"  {'statistic':30s} {'#g/#p':>7s} {'mean R2':>9s} {'min R2':>8s} {'max R2':>8s} "
       f"{'chance':>8s} {'excess':>8s}")
L.append(hdr)
L.append("  " + "-" * (len(hdr) - 2))
rows = sorted(((S.mean([v[0] for v in AGG[k]]) - S.mean([v[3] for v in AGG[k]]), k)
               for k in AGG), reverse=True)
for exc, k in rows:
    vs = AGG[k]
    mr2 = S.mean([v[0] for v in vs])
    ch = S.mean([v[3] for v in vs])
    L.append(f"  {k:30s} {S.mean([v[1] for v in vs]):7.1f} {mr2:9.4f} "
             f"{min(v[0] for v in vs):8.4f} {max(v[0] for v in vs):8.4f} {ch:8.4f} {exc:8.4f}")
L.append("")
L.append(f"  n (blocks per environment) = {S.mean([v[4] for v in AGG[rows[0][1]]]):.0f}")
L.append("  'chance' = (#groups-1)/(n-1): the R2 a RANDOM labelling with the same number of")
L.append("  groups would get.  'excess' = mean R2 - chance, sorted by excess.  Statistics with")
L.append("  #g comparable to n (ncell_r, 3-block tuples) are degenerate/overfit, not informative.")
best = rows[0]
L.append(f"best statistic by excess: {best[1]}  (excess = {best[0]:.4f})")
L.append("R2 >= 0.80 reached by: " +
         (", ".join(k for m, k in sorted(((S.mean([v[0] for v in AGG[k]]), k) for k in AGG),
                                         reverse=True) if m >= 0.80)
          or "NONE of the statistics tested"))
L.append("excess >= 0.80 reached by: " +
         (", ".join(k for m, k in rows if m >= 0.80) or "NONE of the statistics tested"))
txt = "\n".join(L)
print(txt)
open(os.path.join(DIR, "T5_BLACKNESS.txt"), "w").write(txt + "\n")
json.dump({k: [S.mean([v[0] for v in AGG[k]]), S.mean([v[1] for v in AGG[k]]),
               S.mean([v[3] for v in AGG[k]])] for k in AGG},
          open(os.path.join(DIR, "t5_blackness.json"), "w"), indent=1)
