"""TASK 7 -- DeepBlackRun and the weakest structural signature of a high-pressure window.

DEFINITION (formalised).  For block r let
    pre(r) = length of the leading all-black prefix of the readable row of block r,
             i.e. the largest k with cells x = lo(r), ..., lo(r)+k-1 all BLACK, where
             lo(r) = 2r+1 and the readable range is lo(r) .. min(top[2r+1], top[2r+2]-1);
             BLACK(x) iff 54*|centered(XI*2^{x-m} mod 3^{2r+2})| < 3^{2r+2}.
    DeepBlackRun(c, L) at r  :=  pre(r'), ..., pre(r'+L-1) all >= c for some r' in the window.
The previous round's separator is DeepBlackRun(6, 6).

TEST.  Does  P_j > theta_max  imply that the window [j, j+2K) contains a DeepBlackRun(c,L)?
We scan the whole lattice (c, L) and report, for each, whether the implication holds
(coverage = 1) and how many windows overall satisfy the signature (the smaller, the sharper).

usage: python3 t7_signature.py
"""
import json, os
from tload import load, series, THETA_MAX

DIR = os.path.dirname(os.path.abspath(__file__))
out = {"theta_max": THETA_MAX, "grid": {}, "deepblackrun_66": {}, "alt": {}}


def maxrun(pre, a, b, c):
    """longest run of consecutive blocks r in [a,b) with pre[r] >= c."""
    best = cur = 0
    for r in range(a, min(b, len(pre))):
        cur = cur + 1 if pre[r] >= c else 0
        if cur > best:
            best = cur
    return best


print("=" * 100)
print("TASK 7 -- DeepBlackRun(6,6) as a necessary condition for P_j > theta_max")
print("=" * 100)
CORP = {}
for J in (400, 800):
    meta, envs = load(J)
    if envs:
        CORP[J] = envs

for J in sorted(CORP):
    envs = CORP[J]
    # global DeepBlackRun(6,6) census
    tot_blocks = 0
    tot_pre6 = 0
    lr = {}
    for lam in sorted(envs):
        pre = envs[lam]["pre"]
        tot_blocks += len(pre)
        tot_pre6 += sum(1 for k in pre if k >= 6)
        lr[lam] = maxrun(pre, 0, len(pre), 6)
    print(f"\nJ={J}: blocks with pre >= 6 : {tot_pre6}/{tot_blocks} "
          f"= {tot_pre6/tot_blocks:.5f};  longest run of such blocks per lambda:")
    print("   " + ", ".join(f"{l}:{v}" for l, v in sorted(lr.items())))
    out["deepblackrun_66"][str(J)] = {"pre6_blocks": tot_pre6, "blocks": tot_blocks,
                                      "longest_run": lr}
    for K in (16, 24, 32):
        nb = ns = nbs = 0
        for lam in sorted(envs):
            s = series(envs[lam], K)
            if s is None:
                continue
            j0, P = s
            pre = envs[lam]["pre"]
            for i, p in enumerate(P):
                j = j0 + i
                sig = maxrun(pre, j, j + 2 * K, 6) >= 6
                if p > THETA_MAX:
                    nb += 1
                    if sig:
                        nbs += 1
                if sig:
                    ns += 1
        print(f"  K={K:2d}: bad windows {nb:4d}; windows with DeepBlackRun(6,6) {ns:4d}; "
              f"bad AND signature {nbs:4d}  -> implication holds: {nb == nbs and nb > 0}"
              f"{'  (REFUTED)' if nb > nbs else ''}")

print()
print("=" * 100)
print("TASK 7b -- search for the WEAKEST signature DeepBlackRun(c,L) that covers every bad window")
print("=" * 100)
print("  coverage = (#bad windows with the signature)/(#bad);  density = (#windows with sig)/N")
print("  a usable separator needs coverage = 1.000 and density as small as possible.")
for J in sorted(CORP):
    envs = CORP[J]
    for K in (16, 24):
        rows = []
        tot = badtot = 0
        data = []
        for lam in sorted(envs):
            s = series(envs[lam], K)
            if s is None:
                continue
            j0, P = s
            pre = envs[lam]["pre"]
            for i, p in enumerate(P):
                data.append((pre, j0 + i, p))
        if not data:
            continue
        tot = len(data)
        badtot = sum(1 for _, _, p in data if p > THETA_MAX)
        if badtot == 0:
            print(f"J={J} K={K}: no bad windows")
            continue
        print(f"\nJ={J} K={K}: N={tot} windows, {badtot} bad")
        print(f"  {'c':>3} {'L':>3} {'coverage':>9} {'density':>9} {'lift':>7}")
        best = []
        for c in range(1, 13):
            for L in range(1, 13):
                cov = den = 0
                for pre, j, p in data:
                    sig = maxrun(pre, j, j + 2 * K, c) >= L
                    if sig:
                        den += 1
                        if p > THETA_MAX:
                            cov += 1
                if den == 0:
                    continue
                cv = cov / badtot
                dn = den / tot
                best.append((cv, -dn, c, L, cov, den))
                if cv >= 0.999:
                    print(f"  {c:>3} {L:>3} {cv:>9.4f} {dn:>9.4f} "
                          f"{(cov/den)/(badtot/tot):>7.3f}")
        best.sort(key=lambda t: (-t[0], t[1]))
        top = [b for b in best if b[0] >= 0.999]
        if top:
            sharp = min(top, key=lambda t: t[5])
            print(f"  -> sharpest full-coverage signature: DeepBlackRun(c={sharp[2]}, L={sharp[3]}), "
                  f"density {sharp[5]}/{tot} = {sharp[5]/tot:.4f}, lift {(sharp[4]/sharp[5])/(badtot/tot):.3f}")
        else:
            print("  -> NO (c,L) in 1..12 x 1..12 achieves full coverage")
        # best by lift regardless of coverage
        bylift = sorted([b for b in best if b[5] >= 5],
                        key=lambda t: -((t[4] / t[5]) / (badtot / tot)))[:3]
        for b in bylift:
            print(f"     best-lift: c={b[2]} L={b[3]} coverage {b[0]:.3f} density {b[5]/tot:.4f} "
                  f"lift {(b[4]/b[5])/(badtot/tot):.2f}")
        out["grid"][f"{J}_{K}"] = {"N": tot, "bad": badtot,
                                   "full_cov": [[b[2], b[3], b[4], b[5]] for b in top]}

print()
print("=" * 100)
print("TASK 7c -- alternative window statistics; which one separates best?")
print("=" * 100)
for J in sorted(CORP):
    envs = CORP[J]
    for K in (16, 24):
        recs = []
        for lam in sorted(envs):
            s = series(envs[lam], K)
            if s is None:
                continue
            j0, P = s
            pre, nbl, dep = envs[lam]["pre"], envs[lam]["nblack"], envs[lam]["depth"]
            for i, p in enumerate(P):
                j = j0 + i
                w = slice(j, j + 2 * K)
                pw, nw, dw = pre[w], nbl[w], dep[w]
                feats = {
                    "max pre": max(pw),
                    "sum pre": sum(pw),
                    "max run pre>=3": maxrun(pre, j, j + 2 * K, 3),
                    "max run pre>=4": maxrun(pre, j, j + 2 * K, 4),
                    "sum nblack": sum(nw),
                    "max nblack": max(nw),
                    "max depth": max(dw),
                    "max 8-blk sum pre": max(sum(pw[a:a + 8]) for a in range(len(pw) - 7)),
                    "max 4-blk sum pre": max(sum(pw[a:a + 4]) for a in range(len(pw) - 3)),
                }
                recs.append((feats, p > THETA_MAX))
        if not recs:
            continue
        nbad = sum(1 for _, b in recs if b)
        if nbad == 0:
            continue
        print(f"\nJ={J} K={K}: {nbad} bad of {len(recs)}")
        print(f"  {'feature':22} {'min over bad':>13} {'#good >= that':>14} {'density':>9} {'AUC':>7}")
        for name in recs[0][0]:
            vals = [(f[name], b) for f, b in recs]
            mnbad = min(v for v, b in vals if b)
            ngood = sum(1 for v, b in vals if not b and v >= mnbad)
            ntot = sum(1 for v, b in vals if v >= mnbad)
            # rank-AUC
            sv = sorted(range(len(vals)), key=lambda i: vals[i][0])
            ranks = [0.0] * len(vals)
            i = 0
            while i < len(sv):
                k = i
                while k + 1 < len(sv) and vals[sv[k + 1]][0] == vals[sv[i]][0]:
                    k += 1
                rr = (i + k) / 2.0 + 1
                for t in range(i, k + 1):
                    ranks[sv[t]] = rr
                i = k + 1
            sb = sum(ranks[i] for i in range(len(vals)) if vals[i][1])
            ng = len(vals) - nbad
            auc = (sb - nbad * (nbad + 1) / 2) / (nbad * ng)
            print(f"  {name:22} {mnbad:>13.4g} {ngood:>14d} {ntot/len(recs):>9.4f} {auc:>7.4f}")
            out["alt"].setdefault(f"{J}_{K}", {})[name] = [mnbad, ngood, ntot / len(recs), auc]

json.dump(out, open(os.path.join(DIR, "t7_signature.json"), "w"), indent=1)
print("\nwrote t7_signature.json")
