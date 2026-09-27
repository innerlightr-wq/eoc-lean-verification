"""Corpus for TASKS 3-7: exact block weights + exact 3-adic structural statistics
for a representative set of barriers.

Environment set is the SAME 30 used by the previous round (lam x J), so the alpha
numbers are directly comparable to lambda* = 2.3948, mean(w-theta) = -0.10021.
usage: python3 t3_corpus.py
"""
import json, math, os, time
import qcommon as Q
import qirr as QI
from qcommon import cell_xrange, row_values, ETA_DEN

DIR = os.path.dirname(os.path.abspath(__file__))
LAMS = [1, 3, 5, 7, 9, 11, 13, 17, 19, 23, 25, 29, 31, 101, 1025]
JS = [400, 800]
SUBSET = ["golden_m4", "silver_m4", "match3_m4", "golden_m6", "match2_m6",
          "golden_m8", "match2_m8", "silver_m10", "match3_m10"]

fams = {d["name"]: d for d in QI.families()}
bars = [("alpha", "alpha", None, 0.0, QI.floor_alpha)]
for nm in SUBSET:
    d = fams[nm]
    bars.append((nm, d["fam"], d["m"], float(QI.to_decimal(d["trip"]) - QI._ALD),
                 QI.make_floor(d["trip"])))
bars.append(("rat_65_41", "rational", None, 65 / 41 - QI.AL_FLOAT,
             lambda j: (65 * j) // 41))


def stats(G, lam):
    """exact per-block 3-adic structure under this barrier."""
    pre, nbl, dep, ncell = [], [], [], []
    for r in range(G.R):
        lo, hi = cell_xrange(G, r)
        b = 2 * r + 2
        qb = 3 ** b
        if hi < lo:
            pre.append(0); nbl.append(0); dep.append(0.0); ncell.append(0)
            continue
        v = row_values(G, r, lo, hi, lam)
        k, ok, cnt, md = 0, True, 0, 0.0
        for x in range(lo, hi + 1):
            ay = abs(v[x])
            bl = ETA_DEN * ay < qb
            if bl:
                cnt += 1
                md = max(md, math.log(qb / (ETA_DEN * ay)) if ay else 1e9)
            if ok:
                if bl:
                    k += 1
                else:
                    ok = False
        pre.append(k); nbl.append(cnt); dep.append(md); ncell.append(hi - lo + 1)
    return pre, nbl, dep, ncell


CORP = []
for (name, fam, m, diff, f) in bars:
    t0 = time.time()
    for J in JS:
        G = Q.geom_with(J, f)
        sym = [G.top[2 * r + 2] - G.top[2 * r] for r in range(G.R - 1)]
        sym1 = [G.top[2 * r + 1] - G.top[2 * r] for r in range(G.R - 1)]
        sym2 = [G.top[2 * r + 2] - G.top[2 * r + 1] for r in range(G.R - 1)]
        head = [G.top[2 * r] - 2 * r for r in range(G.R)]
        st = None
        for lam in LAMS:
            w, Rend = Q.weights(G, lam)
            rec = dict(name=name, fam=fam, m=m, diff=diff, J=J, lam=lam,
                       Rend=Rend, w=w, sym=sym, sym1=sym1, sym2=sym2, head=head)
            if J == 400:
                pre, nbl, dep, ncell = stats(G, lam)
                rec.update(pre=pre, nblack=nbl, depth=dep, ncell=ncell)
            CORP.append(rec)
    print(f"{name:13s} done ({time.time()-t0:.1f}s)", flush=True)

json.dump(CORP, open(os.path.join(DIR, "corpus.json"), "w"))
print(f"wrote corpus.json: {len(CORP)} environments, {len(bars)} barriers")
