"""TASK 3 -- Cramer statistics for each barrier.

pooled mean(w - theta), theta = 0.137, and lambda* solving E[e^{lambda(w-theta)}] = 1
over the pooled block weights of the 30-environment corpus (15 lam x 2 J).
Reference (previous round, alpha): lambda* = 2.3948, mean(w-theta) = -0.10021.
usage: python3 t3_cramer.py
"""
import json, math, os
import qstat as S

DIR = os.path.dirname(os.path.abspath(__file__))
THETA = 0.137
CORP = json.load(open(os.path.join(DIR, "corpus.json")))

pool = {}
for rec in CORP:
    Rend = rec["Rend"]
    seg = rec["w"][2:Rend - 20]
    pool.setdefault(rec["name"], {"x": [], "n_env": 0, "diff": rec["diff"]})
    pool[rec["name"]]["x"].extend(x - THETA for x in seg)
    pool[rec["name"]]["n_env"] += 1

order = ["alpha"] + [k for k in pool if k != "alpha"]
L = []
L.append("TASK 3 -- Cramer statistics, pooled over the 30-environment corpus (lam x J), theta = 0.137")
L.append("  lambda* solves  (1/n) sum_i exp(lambda (w_i - theta)) = 1  (bisection, 300 iters)")
L.append("")
hdr = (f"{'barrier':13s} {'|b-a|':11s} {'n_env':>6s} {'n_w':>7s} {'mean(w-th)':>11s} "
       f"{'sd(w)':>8s} {'max(w-th)':>10s} {'lambda*':>9s} {'ln2/lam*':>9s} {'d_lam*':>9s}")
L.append(hdr)
L.append("-" * len(hdr))
out = {}
ref = None
for nm in order:
    d = pool[nm]
    x = d["x"]
    lam = S.cramer_lambda(x)
    if nm == "alpha":
        ref = lam
    out[nm] = dict(n_env=d["n_env"], n_w=len(x), mean=S.mean(x), sd=S.sd(x),
                   mx=max(x), lam_star=lam, slope=(math.log(2) / lam if lam else None),
                   diff=d["diff"])
    L.append(f"{nm:13s} {abs(d['diff']):.4e} {d['n_env']:6d} {len(x):7d} {S.mean(x):11.6f} "
             f"{S.sd(x):8.5f} {max(x):10.5f} {lam:9.4f} {math.log(2)/lam:9.5f} "
             f"{(lam-ref):+9.2e}")
L.append("")
L.append("per-J split (alpha only, for comparability with the previous round):")
for J in (400, 800):
    x = []
    for rec in CORP:
        if rec["name"] == "alpha" and rec["J"] == J:
            x.extend(v - THETA for v in rec["w"][2:rec["Rend"] - 20])
    lam = S.cramer_lambda(x)
    L.append(f"  J={J}: n={len(x)} mean={S.mean(x):.6f} lambda*={lam:.4f} ln2/lam*={math.log(2)/lam:.5f}")
txt = "\n".join(L)
print(txt)
open(os.path.join(DIR, "T3_CRAMER.txt"), "w").write(txt + "\n")
json.dump(out, open(os.path.join(DIR, "t3_cramer.json"), "w"), indent=1)
