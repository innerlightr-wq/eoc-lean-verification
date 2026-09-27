"""TASK 1 -- exact data for each quadratic surrogate beta.

minimal polynomial, numerical value, |beta-alpha|, side, CF period, discriminant,
first j with floor(j*beta) != floor(j*alpha), mismatch density up to N=10^5.
Everything exact except the printed decimal expansions (140-digit Decimal).
usage: python3 t1_betadata.py [N]
"""
import json, os, sys
from decimal import Decimal
import qirr as Q

DIR = os.path.dirname(os.path.abspath(__file__))
N = int(sys.argv[1]) if len(sys.argv) > 1 else 100000

fams = Q.families()
ALD = Q._ALD
rows = []
L = []
L.append(f"alpha = log2 3 ; CF = {Q.ALPHA_CF[:16]} ...")
L.append(f"alpha = {ALD:.30f}")
L.append("")
L.append("TASK 1 -- quadratic surrogate barriers (all barrier arithmetic EXACT, integer only)")
L.append("")
hdr = (f"{'name':13s} {'minpoly A,B,C':26s} {'beta (30 dp)':34s} {'|b-a|':12s} "
       f"{'side':6s} {'period':10s} {'disc':9s} {'firstDiff':10s} {'dens(1e5)':10s}")
L.append(hdr)
L.append("-" * len(hdr))
for d in fams:
    P, Qq, S, D = d["trip"]
    A, B, C = Q.minpoly(P, Qq, S, D)
    disc = Q.disc_of(A, B, C)
    bd = Q.to_decimal(d["trip"])
    diff = bd - ALD
    side = "above" if diff > 0 else "below"
    f = Q.make_floor(d["trip"])
    first = None
    cnt = 0
    for j in range(1, N + 1):
        if f(j) != Q.floor_alpha(j):
            cnt += 1
            if first is None:
                first = j
    rows.append(dict(name=d["name"], fam=d["fam"], m=d["m"], prefix=d["prefix"],
                     period=d["period"], trip=[P, Qq, S, D], minpoly=[A, B, C],
                     disc=disc, beta=str(bd)[:40], diff=float(diff), side=side,
                     first_diff=first, n_mismatch=cnt, density=cnt / N))
    L.append(f"{d['name']:13s} {str((A,B,C)):26s} {str(bd)[:34]:34s} {float(abs(diff)):.4e} "
             f"{side:6s} {str(d['period']):10s} {disc:9d} "
             f"{(str(first) if first else '>'+str(N)):10s} {cnt/N:.6f}")
L.append("")
L.append("NOTE: match2_m10 has period [2,2] which is the same tail as silver -> identical beta.")
L.append("All floors verified exact against 140-digit Decimal for j<=1e5 (see T0_EXACT.txt).")
txt = "\n".join(L)
print(txt)
open(os.path.join(DIR, "T1_BETADATA.txt"), "w").write(txt + "\n")
json.dump(rows, open(os.path.join(DIR, "t1_betadata.json"), "w"), indent=1)
