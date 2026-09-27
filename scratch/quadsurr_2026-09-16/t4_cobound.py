"""TASK 4 -- coboundary test:  w_r = wbar + phi(s(r+1)) - phi(s(r)) + eps_r ?

phi is fitted by exact least squares (graph-Laplacian normal equations, gauge phi(s_0)=0).
Reported: residual sd and fraction of Var(w) explained, for each candidate finite state.
A state whose label is essentially unique per block (e.g. raw headroom) fits perfectly for
trivial reasons -- #states is printed so that degeneracy is visible.
usage: python3 t4_cobound.py
"""
import json, math, os
import qstat as S

DIR = os.path.dirname(os.path.abspath(__file__))
CORP = [r for r in json.load(open(os.path.join(DIR, "corpus.json"))) if r["J"] == 400]


def candidates(rec, lo, hi):
    """dict name -> list of state labels for r = lo .. hi (inclusive) ; length hi-lo+1."""
    sym, sym1, sym2 = rec["sym"], rec["sym1"], rec["sym2"]
    head, nb, dep = rec["head"], rec["nblack"], rec["depth"]
    nbc = [min(v, 4) for v in nb]
    dpb = [min(int(v), 4) for v in dep]
    C = {}
    rng = range(lo, hi + 1)
    C["(a) headroom raw"] = [head[r] for r in rng]
    C["(a') headroom mod2"] = [head[r] % 2 for r in rng]
    C["(a'') headroom mod3"] = [head[r] % 3 for r in rng]
    C["(a''') headroom mod5"] = [head[r] % 5 for r in rng]
    C["(b) nblack"] = [nb[r] for r in rng]
    C["(b') nblack clip4"] = [nbc[r] for r in rng]
    C["(c) barrier sym {3,4}"] = [sym[r] for r in rng]
    C["(c') (sym1,sym2)"] = [(sym1[r], sym2[r]) for r in rng]
    C["(c'') sym 2-window"] = [(sym[r], sym[r + 1]) for r in rng]
    C["(c''') sym 3-window"] = [(sym[r], sym[r + 1], sym[r + 2]) for r in rng]
    C["(d) (sym,nblack clip4)"] = [(sym[r], nbc[r]) for r in rng]
    C["(d') (sym,nblack)"] = [(sym[r], nb[r]) for r in rng]
    C["(d'') (nblack clip4, depth clip4)"] = [(nbc[r], dpb[r]) for r in rng]
    C["(d''') (sym1,sym2,nblack clip4)"] = [(sym1[r], sym2[r], nbc[r]) for r in rng]
    C["(e) depth clip4"] = [dpb[r] for r in rng]
    C["(f) nblack 2-window"] = [(nbc[r], nbc[r + 1]) for r in rng]
    return C


AGG = {}
L = []
L.append("TASK 4 -- coboundary decomposition of the block weights over a finite state (J = 400)")
L.append("  model:  w_r - wbar = phi(s_{r+1}) - phi(s_r) + eps_r,  phi by least squares")
L.append("  'fracVar' = 1 - Var(eps)/Var(w).  #st = number of distinct states actually used.")
L.append("")
for rec in CORP:
    Rend = rec["Rend"]
    lo, hi = 2, Rend - 21          # w index range; states need r .. hi+1 (+3 for windows)
    w = rec["w"][lo:hi + 1]
    C = candidates(rec, lo, hi + 1)
    n = len(w)
    for nm, st in C.items():
        r_sd, fv, K, _ = S.coboundary_fit(w, st)
        key = (rec["name"], nm)
        AGG.setdefault(key, []).append((fv, r_sd, K, S.sd(w), (K - 1) / n, n))

names = sorted({k[0] for k in AGG}, key=lambda s: (s != "alpha", s))
cands = list(candidates(CORP[0], 2, CORP[0]["Rend"] - 20).keys())
for nm in names:
    L.append(f"--- barrier {nm} (mean over 15 lam at J=400; sd(w) ~ "
             f"{S.mean([v[3] for v in AGG[(nm, cands[0])]]):.5f}) ---")
    L.append(f"  {'candidate state':34s} {'#st':>5s} {'fracVar':>9s} {'resid sd':>10s} "
             f"{'chance':>8s} {'excess':>8s}")
    rows = []
    for c in cands:
        vs = AGG[(nm, c)]
        rows.append((S.mean([v[0] for v in vs]), c, S.mean([v[1] for v in vs]),
                     S.mean([v[2] for v in vs]), S.mean([v[4] for v in vs])))
    for fv, c, rsd, K, ch in sorted(rows, key=lambda t: -(t[0] - t[4])):
        L.append(f"  {c:34s} {K:5.1f} {fv:9.4f} {rsd:10.6f} {ch:8.4f} {fv-ch:8.4f}")
    L.append(f"  (n = {S.mean([v[5] for v in AGG[(nm, cands[0])]]):.0f} blocks; "
             f"'chance' = (#st-1)/n = free parameters per data point; sorted by excess)")
    L.append("")
txt = "\n".join(L)
print(txt)
open(os.path.join(DIR, "T4_COBOUND.txt"), "w").write(txt + "\n")
json.dump({f"{k[0]}|{k[1]}": [S.mean([v[0] for v in AGG[k]]), S.mean([v[1] for v in AGG[k]]),
                              S.mean([v[2] for v in AGG[k]])] for k in AGG},
          open(os.path.join(DIR, "t4_cobound.json"), "w"), indent=1)
