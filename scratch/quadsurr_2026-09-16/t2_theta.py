"""TASK 2 -- Theta_beta: exact long-run block-weight rate under each quadratic barrier.

J in {400, 800}, lam in {1,5,7,11,19,101}.  Only G.top changes; the 3-adic environment
(blackness mod 3^{2r+2}) and the chain weights are held fixed.
usage: python3 t2_theta.py
"""
import json, math, os, time
import qcommon as Q
import qirr as QI

DIR = os.path.dirname(os.path.abspath(__file__))
LAMS = [1, 5, 7, 11, 19, 101]
JS = [400, 800]
THETA = Q.THETA_MAX

fams = QI.families()
bars = [dict(name="alpha", fam="alpha", m=None, diff=0.0, f=QI.floor_alpha)]
for d in fams:
    bd = QI.to_decimal(d["trip"])
    bars.append(dict(name=d["name"], fam=d["fam"], m=d["m"],
                     diff=float(bd - QI._ALD), f=QI.make_floor(d["trip"])))
bars.append(dict(name="rat_65_41", fam="rational", m=None,
                 diff=float(65 / 41 - QI.AL_FLOAT), f=lambda j: (65 * j) // 41))

# sanity: Geom's float floor == exact floor_alpha on the range we use
for i in range(0, 801):
    assert math.floor(i * Q.T.AL) == QI.floor_alpha(i), i

RES = {}
L = []
L.append("TASK 2 -- Theta_beta = max over lam of the exact long-run rate mean(w[2:Rend-20])")
L.append(f"          theta_max = {THETA};  lam in {LAMS}")
for J in JS:
    L.append("")
    L.append(f"=== J = {J} ===")
    hdr = f"{'barrier':13s} {'|b-a|':11s} " + " ".join(f"{'lam='+str(l):>9s}" for l in LAMS) + \
          f" {'Theta':>9s} {'margin':>8s} {'dev_alpha':>10s}"
    L.append(hdr)
    L.append("-" * len(hdr))
    ref = None
    for b in bars:
        t0 = time.time()
        G = Q.geom_with(J, b["f"])
        rates = []
        for lam in LAMS:
            w, Rend = Q.weights(G, lam)
            rates.append(Q.longrun(w, Rend)[0])
        Th = max(rates)
        if b["name"] == "alpha":
            ref = Th
        RES[f"{J}|{b['name']}"] = dict(J=J, name=b["name"], fam=b["fam"], m=b["m"],
                                       diff=b["diff"], rates=rates, Theta=Th,
                                       margin=THETA - Th, sg=G.sg,
                                       top=G.top[:min(len(G.top), 2000)])
        L.append(f"{b['name']:13s} {abs(b['diff']):.4e} " +
                 " ".join(f"{x:9.5f}" for x in rates) +
                 f" {Th:9.5f} {THETA-Th:8.5f} {Th-ref:+10.6f}")
        print(L[-1], f"({time.time()-t0:.1f}s)", flush=True)

L.append("")
L.append("CONVERGENCE: |Theta_beta - Theta_alpha| vs |beta - alpha| (J = 400 and 800)")
L.append(f"{'barrier':13s} {'m':>3s} {'|b-a|':11s} {'|dTh| J=400':12s} {'ratio400':10s} "
         f"{'|dTh| J=800':12s} {'ratio800':10s}")
for b in bars:
    if b["name"] == "alpha":
        continue
    e = abs(b["diff"])
    r4 = RES.get("400|" + b["name"])
    r8 = RES.get("800|" + b["name"])
    d4 = abs(r4["Theta"] - RES["400|alpha"]["Theta"])
    d8 = abs(r8["Theta"] - RES["800|alpha"]["Theta"])
    L.append(f"{b['name']:13s} {str(b['m']):>3s} {e:.4e} {d4:.6e} {d4/e:10.4f} "
             f"{d8:.6e} {d8/e:10.4f}")

txt = "\n".join(L)
print(txt)
open(os.path.join(DIR, "T2_THETA.txt"), "w").write(txt + "\n")
json.dump(RES, open(os.path.join(DIR, "t2_theta.json"), "w"))
