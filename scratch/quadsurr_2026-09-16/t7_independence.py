"""TASK 7 -- decisive kill test: does the barrier symbol control the black pattern?

(A) STRUCTURAL: the blackness predicate for the cell of block r at column x is
    54*|centered(XI*2^{-(m-x)} mod 3^{2r+2})| < 3^{2r+2}.  It depends on (XI, r, x) and on
    m = sg + t + 1 -- NOT on top[].  m does depend on the barrier only through
    sg = floor(J*alpha), which we hold FIXED (geom_with caps at G.sg).  So across barriers
    the black field is literally the same function; only the read window [lo,hi] moves.
    Verified here by comparing the raw black rows over a common window.

(B) STATISTICAL: Pearson correlation of the barrier symbol sym_r = top[2r+2]-top[2r] in
    {3,4} with the block's black-cell count, with the block weight, and with the window size.
usage: python3 t7_independence.py
"""
import json, math, os
import qcommon as Q
import qirr as QI
import qstat as S
from qcommon import row_black_list, cell_xrange

DIR = os.path.dirname(os.path.abspath(__file__))
J = 400
LAM_FIX = 11
CORP = [r for r in json.load(open(os.path.join(DIR, "corpus.json"))) if r["J"] == 400]

fams = {d["name"]: d for d in QI.families()}
bars = [("alpha", QI.floor_alpha)]
for nm in ["golden_m4", "silver_m4", "golden_m8", "silver_m10"]:
    bars.append((nm, QI.make_floor(fams[nm]["trip"])))
bars.append(("rat_65_41", lambda j: (65 * j) // 41))

L = []
L.append("TASK 7 -- barrier symbol vs blackness (decisive kill test)")
L.append("")
L.append(f"(A) raw black field comparison, lam = {LAM_FIX}, J = {J}, common window x = 2r..2r+40")
L.append("    (the blackness predicate does not read top[]; m = sg+t+1 is held fixed at sg = floor(J*alpha))")
Ga = Q.geom_with(J, QI.floor_alpha)
ref = {}
for r in range(0, Ga.R, 1):
    ref[r] = row_black_list(Ga, r, 2 * r, 2 * r + 40, LAM_FIX)
L.append(f"    {'barrier':13s} {'m':>6s} {'sg':>5s} {'rows identical to alpha':>26s} {'#cells differing':>18s}")
for nm, f in bars:
    G = Q.geom_with(J, f)
    same = 0
    diffc = 0
    for r in range(G.R):
        row = row_black_list(G, r, 2 * r, 2 * r + 40, LAM_FIX)
        if row == ref[r]:
            same += 1
        diffc += sum(1 for a, b in zip(row, ref[r]) if a != b)
    L.append(f"    {nm:13s} {G.m:6d} {G.sg:5d} {str(same)+'/'+str(G.R):>26s} {diffc:18d}")
L.append("")
L.append("(B) black DENSITY as actually read (window moves with the barrier), lam = %d" % LAM_FIX)
L.append(f"    {'barrier':13s} {'#cells read':>12s} {'#black':>8s} {'density':>9s} {'mean ncell/blk':>15s}")
for nm, f in bars:
    G = Q.geom_with(J, f)
    tot = blk = 0
    for r in range(G.R):
        lo, hi = cell_xrange(G, r)
        if hi < lo:
            continue
        row = row_black_list(G, r, lo, hi, LAM_FIX)
        tot += len(row)
        blk += sum(row)
    L.append(f"    {nm:13s} {tot:12d} {blk:8d} {blk/tot:9.5f} {tot/G.R:15.3f}")
L.append("")
L.append("(C) Pearson correlations, J = 400, averaged over the 15 lam of the corpus")
L.append(f"    {'barrier':13s} {'corr(sym,nblack)':>18s} {'corr(sym,w)':>13s} {'corr(sym,ncell)':>16s} "
         f"{'corr(nblack,w)':>15s} {'corr(ncell,w)':>14s}")
COR = {}
for nm in sorted({r['name'] for r in CORP}, key=lambda s: (s != "alpha", s)):
    recs = [r for r in CORP if r["name"] == nm]
    c1 = []; c2 = []; c3 = []; c4 = []; c5 = []
    for rec in recs:
        Rend = rec["Rend"]
        lo, hi = 2, Rend - 21
        w = rec["w"][lo:hi + 1]
        sym = [rec["sym"][r] for r in range(lo, hi + 1)]
        nb = [rec["nblack"][r] for r in range(lo, hi + 1)]
        nc = [rec["ncell"][r] for r in range(lo, hi + 1)]
        c1.append(S.pearson(sym, nb)); c2.append(S.pearson(sym, w))
        c3.append(S.pearson(sym, nc)); c4.append(S.pearson(nb, w))
        c5.append(S.pearson(nc, w))
    COR[nm] = [S.mean(c1), S.mean(c2), S.mean(c3), S.mean(c4), S.mean(c5)]
    L.append(f"    {nm:13s} {S.mean(c1):18.5f} {S.mean(c2):13.5f} {S.mean(c3):16.5f} "
             f"{S.mean(c4):15.5f} {S.mean(c5):14.5f}")
L.append("")
L.append("(D) black density CONDITIONED on the barrier symbol (alpha, J=400, all 15 lam)")
for nm in ["alpha", "golden_m4"]:
    recs = [r for r in CORP if r["name"] == nm]
    if not recs:
        continue
    g = {3: [], 4: []}
    gd = {3: [], 4: []}
    for rec in recs:
        Rend = rec["Rend"]
        for r in range(2, Rend - 20):
            s = rec["sym"][r]
            if s in g and rec["ncell"][r] > 0:
                g[s].append(rec["nblack"][r])
                gd[s].append(rec["nblack"][r] / rec["ncell"][r])
    L.append(f"    {nm}: sym=3 -> n={len(g[3])} mean nblack {S.mean(g[3]):.4f} "
             f"mean black-density {S.mean(gd[3]):.5f}")
    L.append(f"    {nm}: sym=4 -> n={len(g[4])} mean nblack {S.mean(g[4]):.4f} "
             f"mean black-density {S.mean(gd[4]):.5f}")
txt = "\n".join(L)
print(txt)
open(os.path.join(DIR, "T7_INDEP.txt"), "w").write(txt + "\n")
json.dump(COR, open(os.path.join(DIR, "t7_indep.json"), "w"), indent=1)
