"""TASK 6 -- superblock / renormalisation test for the quadratic barriers.

level-0 word  u_r = top[2r+2] - top[2r] in {3,4} (the barrier increment over one block)
level-1 superblocks = maximal  3^k 4  units  -> derived word over the observed k-values
level-2 = same construction applied to the derived word (renormalisation step)

For each level and type: mean/var of the summed block weight W, the length L, and the
EXCESS  max_occurrences (W - theta*L).  A 2x2 matrix  M[t][t'] = 1{t->t' occurs} *
exp(max excess of t)  has Perron root < 1 exactly when every type's excess is negative,
which would certify rate < theta blockwise.
usage: python3 t6_superblock.py
"""
import json, math, os
import qstat as S

DIR = os.path.dirname(os.path.abspath(__file__))
THETA = 0.137
CORP = json.load(open(os.path.join(DIR, "corpus.json")))


def runlen(word, rare):
    """split into maximal (common^k rare) units ; returns list of (k, start, length)."""
    out = []
    k = 0
    start = 0
    for i, c in enumerate(word):
        if c == rare:
            out.append((k, start, k + 1))
            k = 0
            start = i + 1
        else:
            k += 1
    return out


def perron2(M):
    a, b = M[0]
    c, d = M[1]
    tr = a + d
    det = a * d - b * c
    disc = tr * tr - 4 * det
    if disc < 0:
        return abs(complex(tr / 2, math.sqrt(-disc) / 2))
    return (tr + math.sqrt(disc)) / 2


L = []
L.append("TASK 6 -- superblock renormalisation of the barrier word and the pressure (J = 400)")
L.append(f"  theta = {THETA}.  Excess(t) = max over occurrences of (sum w - theta * #blocks).")
L.append("")

BAR = ["alpha", "golden_m4", "silver_m4", "golden_m8", "match2_m8", "silver_m10", "rat_65_41"]
RES = {}
for nm in BAR:
    recs = [r for r in CORP if r["name"] == nm and r["J"] == 400]
    if not recs:
        continue
    sym = recs[0]["sym"]
    Rend = recs[0]["Rend"]
    common, rare = 3, 4
    cnt3 = sym.count(3); cnt4 = sym.count(4)
    if cnt4 > cnt3:
        common, rare = 4, 3
    units = runlen(sym[:Rend], rare)
    ks = sorted({k for k, _, _ in units})
    kc = {k: sum(1 for kk, _, _ in units if kk == k) for k in ks}
    L.append(f"=== barrier {nm} ===")
    L.append(f"  level-0 word over {{3,4}}: #3 = {cnt3}, #4 = {cnt4}, "
             f"density of 4 = {cnt4/(cnt3+cnt4):.5f}")
    L.append(f"  level-1 run lengths k in '{common}^k {rare}' : {ks}  counts {kc}")
    if len(ks) == 2:
        kA, kB = ks
        L.append(f"  -> EXACTLY TWO superblock types: A = {common}^{kA}{rare} (len {kA+1}), "
                 f"B = {common}^{kB}{rare} (len {kB+1})")
        der = "".join("A" if k == kA else "B" for k, _, _ in units)
        rareD = "A" if der.count("A") < der.count("B") else "B"
        commD = "B" if rareD == "A" else "A"
        u2 = runlen(der, rareD)
        if len(u2) > 2:
            u2 = u2[1:-1]            # drop the two boundary-truncated runs
        ks2 = sorted({k for k, _, _ in u2})
        L.append(f"  level-2 (derived word over {{A,B}}, len {len(der)}): rare symbol {rareD}, "
                 f"run lengths {ks2}")
        if len(ks2) == 2:
            L.append(f"  -> SUBSTITUTION (level2 -> level1): "
                     f"X = {commD}^{ks2[0]}{rareD},  Y = {commD}^{ks2[1]}{rareD}")
        L.append(f"  derived word prefix: {der[:60]}")
    else:
        L.append(f"  -> {len(ks)} run lengths, NOT a two-type (Sturmian) decomposition here")
        kA = kB = None
        der = None

    # pressure per superblock type, aggregated over lam
    per = {}
    exc = {}
    trans = {}
    for rec in recs:
        w = rec["w"]
        for i, (k, st, ln) in enumerate(units):
            if st + ln > len(w):
                continue
            if st < 2 or st + ln > Rend - 20:
                continue
            W = sum(w[st:st + ln])
            per.setdefault(k, []).append(W)
            exc.setdefault(k, []).append(W - THETA * ln)
    for k in sorted(per):
        v = per[k]
        L.append(f"  type k={k} (L={k+1}): n={len(v):5d}  mean W = {S.mean(v):.5f}  "
                 f"sd = {S.sd(v):.5f}  mean W/L = {S.mean(v)/(k+1):.5f}  "
                 f"max excess = {max(exc[k]):+.5f}")
    if len(ks) == 2 and all(k in per for k in ks):
        # transitions between consecutive units
        T = [[0, 0], [0, 0]]
        idx = {ks[0]: 0, ks[1]: 1}
        for i in range(len(units) - 1):
            T[idx[units[i][0]]][idx[units[i + 1][0]]] += 1
        M = [[(math.exp(max(exc[ks[a]])) if T[a][b] else 0.0) for b in range(2)]
             for a in range(2)]
        pr = perron2(M)
        L.append(f"  transition counts {T}")
        L.append(f"  2x2 excess matrix M[a][b] = 1{{a->b}} exp(max excess a) = "
                 f"[[{M[0][0]:.4f},{M[0][1]:.4f}],[{M[1][0]:.4f},{M[1][1]:.4f}]]")
        L.append(f"  Perron root = {pr:.5f}   -> certificate rate < theta blockwise: {pr < 1.0}")
        # renormalised level: pairs of consecutive superblocks
        exc2 = {}
        for rec in recs:
            w = rec["w"]
            for i in range(len(units) - 1):
                k1, st1, l1 = units[i]
                k2, st2, l2 = units[i + 1]
                if st1 < 2 or st2 + l2 > min(len(w), Rend - 20):
                    continue
                W = sum(w[st1:st2 + l2])
                exc2.setdefault((k1, k2), []).append(W - THETA * (l1 + l2))
        L.append("  renormalised (pairs of superblocks):")
        for key in sorted(exc2):
            v = exc2[key]
            L.append(f"    pair {key}: n={len(v):5d} mean excess {S.mean(v):+.5f} "
                     f"max excess {max(v):+.5f}")
        mx1 = max(max(exc[k]) for k in ks)
        mx2 = max(max(v) for v in exc2.values())
        L.append(f"  max excess level1 = {mx1:+.5f} ; level2 (pairs) = {mx2:+.5f} ; "
                 f"contracts (per block): {mx2/2 < mx1}")
        RES[nm] = dict(ks=ks, perron=pr, max_exc1=mx1, max_exc2=mx2,
                       meanW={str(k): S.mean(per[k]) for k in ks})
    L.append("")

L.append("TASK 6b -- how long must a window be before the excess is UNIFORMLY negative?")
L.append(f"  max over all block windows of length Lw (all 15 lam, J=400) of  sum w - {THETA}*Lw")
L.append(f"  {'barrier':13s} " + " ".join(f"{'Lw='+str(k):>9s}" for k in
                                          [1, 2, 4, 8, 16, 32, 64, 128]) + "   first Lw<0")
for nm in BAR:
    recs = [r for r in CORP if r["name"] == nm and r["J"] == 400]
    if not recs:
        continue
    Rend = recs[0]["Rend"]
    vals = []
    firstneg = None
    for Lw in [1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64, 96, 128, 160]:
        mx = -1e9
        for rec in recs:
            w = rec["w"]
            lo, hi = 2, Rend - 20
            run = sum(w[lo:lo + Lw]) if lo + Lw <= hi else None
            if run is None:
                continue
            best = run - THETA * Lw
            for st in range(lo + 1, hi - Lw + 1):
                run += w[st + Lw - 1] - w[st - 1]
                best = max(best, run - THETA * Lw)
            mx = max(mx, best)
        if Lw in (1, 2, 4, 8, 16, 32, 64, 128):
            vals.append(mx)
        if firstneg is None and mx < 0:
            firstneg = Lw
    L.append(f"  {nm:13s} " + " ".join(f"{v:9.4f}" for v in vals) +
             f"   {firstneg if firstneg else '>160'}")
L.append("")
L.append("  (a uniform blockwise certificate exists exactly at the first Lw whose max is < 0;")
L.append("   a 2x2 superblock matrix built from max-excess per type needs Lw of that order,")
L.append("   so the 5-6 block superblocks of the barrier substitution are far too short.)")

txt = "\n".join(L)
print(txt)
open(os.path.join(DIR, "T6_SUPERBLOCK.txt"), "w").write(txt + "\n")
json.dump(RES, open(os.path.join(DIR, "t6_superblock.json"), "w"), indent=1)
