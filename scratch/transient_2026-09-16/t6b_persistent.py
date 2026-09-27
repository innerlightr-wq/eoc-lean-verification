"""TASK 6 -- persistent-adversary hunt: report every stretch in a TRUE low-frequency
environment where the pressure stays above theta_max, and compare with the ACTUAL
long-product growth rate of the same stretch.

(i)  disjoint-tiling runs of consecutive bad K-windows (all offsets, all environments);
(ii) for each such stretch, the exact long-product rate  (a_{r0}-a_{r1})/(2(r1-r0));
(iii) aggregation of the wide-lambda scans (T6_w*.txt): max Lambda_long and max burst(L).

usage: python3 t6b_persistent.py
"""
import glob, json, math, os
from tload import load, series, THETA_MAX

DIR = os.path.dirname(os.path.abspath(__file__))
CORP = {(c["J"], c["lam"]): c for c in json.load(open(os.path.join(DIR, "corpus.json")))}
DATA = {}
for J in (400, 800):
    meta, envs = load(J)
    if envs:
        DATA[J] = envs
OUT = {}

print("=" * 108)
print("TASK 6(i,ii) -- runs of consecutive BAD windows in a DISJOINT tiling of a TRUE environment")
print("=" * 108)
print(f"  theta_max = {THETA_MAX}.  'rate' = exact long-product growth (a_r0-a_r1)/(2(r1-r0))")
print("  over the SAME block range, i.e. what the operator product really does there.\n")
found = []
for K in (16, 24, 32):
    runs = []
    for J in DATA:
        for lam, rec in DATA[J].items():
            s = series(rec, K)
            if s is None:
                continue
            j0, P = s
            Pm = {j0 + i: P[i] for i in range(len(P))}
            for off in range(2 * K):
                seq = list(range(j0 + off, j0 + len(P), 2 * K))
                cur = []
                for j in seq:
                    if Pm[j] > THETA_MAX:
                        cur.append(j)
                    else:
                        if len(cur) >= 2:
                            runs.append((J, lam, K, cur[:], [Pm[x] for x in cur]))
                        cur = []
                if len(cur) >= 2:
                    runs.append((J, lam, K, cur[:], [Pm[x] for x in cur]))
    # deduplicate by (J,lam,first anchor,len)
    seen = set()
    uniq = []
    for r in runs:
        k = (r[0], r[1], r[3][0], len(r[3]))
        if k in seen:
            continue
        seen.add(k)
        uniq.append(r)
    uniq.sort(key=lambda r: (-len(r[3]), -max(r[4])))
    print(f"K={K}: {len(uniq)} maximal runs of length >= 2 "
          f"(max length {max((len(r[3]) for r in uniq), default=0)})")
    for (J, lam, KK, anch, ps) in uniq[:12]:
        r0, r1 = anch[0], anch[-1] + 2 * KK
        c = CORP[(J, lam)]
        w = c["w"]
        r1c = min(r1, len(w))
        rate = sum(w[r0:r1c]) / (r1c - r0)
        print(f"   J={J} lam={lam:5d} len={len(anch):2d} anchors {anch[0]}..{anch[-1]} "
              f"(blocks {r0}..{r1}) P = [" +
              ", ".join(f"{p:.4f}" for p in ps) + f"]  actual rate over the stretch = {rate:.5f}"
              f"  {'** ABOVE theta_max **' if rate > THETA_MAX else ''}")
        found.append({"J": J, "lam": lam, "K": KK, "len": len(anch), "anchors": anch,
                      "P": ps, "blocks": [r0, r1], "actual_rate": rate})
    print()
OUT["disjoint_runs"] = found

print("=" * 108)
print("TASK 6(ii') -- the WORST sustained stretch in every true environment, all lengths")
print("=" * 108)
print("  max over r0 of the exact long-product rate over [r0, r0+L), by L "
      "(30-environment corpus)\n")
LS = [8, 16, 32, 48, 64, 96, 128, 160]
print(f"  {'J':>4} {'lam':>6} " + " ".join(f"L={L:<6}" for L in LS))
tbl = {}
for (J, lam), c in sorted(CORP.items()):
    w = c["w"]
    n = len(w)
    ps = [0.0]
    for x in w:
        ps.append(ps[-1] + x)
    row = []
    for L in LS:
        best = max((ps[a + L] - ps[a]) / L for a in range(2, n - L - 20))
        row.append(best)
    tbl[f"{J}_{lam}"] = row
    print(f"  {J:>4} {lam:>6} " + " ".join(f"{v:<8.4f}" for v in row))
OUT["burst_table"] = tbl
mx = {L: max(tbl[k][i] for k in tbl) for i, L in enumerate(LS)}
print("\n  MAXIMUM over the whole 30-environment corpus:")
print("   " + "  ".join(f"L={L}: {mx[L]:.4f}" for L in LS))
print(f"   theta_max = {THETA_MAX}: exceeded for L <= "
      f"{max([L for L in LS if mx[L] > THETA_MAX], default=0)}, "
      f"below it for L >= {min([L for L in LS if mx[L] <= THETA_MAX], default=None)}")
OUT["burst_max"] = {str(L): mx[L] for L in LS}

print()
print("=" * 108)
print("TASK 6(iii) -- WIDE lambda scan aggregation")
print("=" * 108)
for pat, label in [("T6_w400_s*.txt", "J=400"), ("T6_w800_u*.txt", "J=800")]:
    rows = []
    for fn in sorted(glob.glob(os.path.join(DIR, pat))):
        for line in open(fn):
            t = line.split()
            if len(t) >= 9 and t[0].isdigit():
                try:
                    rows.append([int(t[0])] + [float(x) for x in t[1:7]] +
                                [int(t[7]), int(t[8])])
                except ValueError:
                    pass
    if not rows:
        continue
    rows.sort()
    LSb = [8, 16, 32, 64, 128]
    print(f"\n{label}: {len(rows)} lambda scanned "
          f"(odd, 1 <= lambda <= {max(r[0] for r in rows)})")
    print(f"  Lambda_long : min {min(r[1] for r in rows):.5f}  "
          f"median {sorted(r[1] for r in rows)[len(rows)//2]:.5f}  "
          f"MAX {max(r[1] for r in rows):.5f} (lam={max(rows,key=lambda r:r[1])[0]})")
    for i, L in enumerate(LSb):
        col = [r[2 + i] for r in rows]
        am = max(rows, key=lambda r: r[2 + i])
        nover = sum(1 for v in col if v > THETA_MAX)
        print(f"  burst(L={L:3d}) : median {sorted(col)[len(col)//2]:.5f}  "
              f"MAX {max(col):.5f} (lam={am[0]})  #lambda with burst > theta_max: "
              f"{nover}/{len(rows)} = {nover/len(rows):.4f}")
    nd = sum(1 for r in rows if r[8] >= 6)
    np6 = sum(r[7] for r in rows)
    print(f"  DeepBlackRun(6,6) present: {nd}/{len(rows)} lambda;  "
          f"total blocks with pre >= 6: {np6};  max run observed: {max(r[8] for r in rows)}")
    top = sorted(rows, key=lambda r: -r[1])[:10]
    print("  top-10 lambda by Lambda_long: " +
          ", ".join(f"{r[0]}({r[1]:.4f})" for r in top))
    top64 = sorted(rows, key=lambda r: -r[5])[:10]
    print("  top-10 lambda by burst(64)  : " +
          ", ".join(f"{r[0]}({r[5]:.4f})" for r in top64))
    OUT[label] = {"n": len(rows), "max_Lambda_long": max(r[1] for r in rows),
                  "argmax": max(rows, key=lambda r: r[1])[0],
                  "burst_max": {str(L): max(r[2 + i] for r in rows)
                                for i, L in enumerate(LSb)},
                  "top10_long": [[r[0], r[1]] for r in top],
                  "top10_b64": [[r[0], r[5]] for r in top64],
                  "dbr_lambda": nd}

json.dump(OUT, open(os.path.join(DIR, "t6b_persistent.json"), "w"), indent=1)
print("\nwrote t6b_persistent.json")
