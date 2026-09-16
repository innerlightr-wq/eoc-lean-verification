"""N0 / d / theta trade-off from the PROVED (LEAN) constraints of lowFreqDecay_of_summedPressure:
   nu + kap <= Kmax(N0) = 1/2 - 31/100 - 317/(200(N0+2)),   gamma <= nu*log2((1+s)/2) - theta',  s = 3,
   gamma <= 8 kap d^2 / (N0 ln 2),   gamma <= 1/300.
Two hypotheses on the pressure at dark threshold d:
   (F) the formal round target theta = 0.17;
   (M) theta = measured max over the J = 400 d-scan + 0.02 (COMPUTATIONAL input, not a theorem)."""
import json, math
res = json.load(open('dscan_400.json'))
meas = {}
for j, t, lam, D, P, c in res: meas[D] = max(meas.get(D, 0), P)
def Kmax(N0): return 0.19 - 317 / (200 * (N0 + 2))
def best_gamma(N0, d, theta):
    K = Kmax(N0); c = 8 * d * d / (N0 * math.log(2)); g_best = 0.0
    if K <= theta: return 0.0
    # maximise min(1/300, K - kap - theta, c*kap) over kap in (0, K - theta): crossing point
    kap = (K - theta) / (1 + c)
    return max(0.0, min(1 / 300, K - kap - theta, c * kap))
N0s = (30, 50, 75, 100, 150, 200, 300, 500, 1000)
for label, th in (("(F) theta = 0.17", lambda D: 0.17), ("(M) theta = measured max + 0.02", lambda D: meas[D] + 0.02)):
    print(label)
    print("   N0   Kmax  " + "".join(f"  d=1/{D:<5}" for D in sorted(meas, reverse=True)))
    for N0 in N0s:
        print(f"  {N0:4d} {Kmax(N0):.4f}" + "".join(
            f"  {best_gamma(N0, 1 / D, th(D)):9.2e}" if meas[D] + (0 if label[1] == 'M' else 0) < (0.17 if label[1] == 'F' else 1) else "  (P>0.17)"
            for D in sorted(meas, reverse=True)))
print("measured max pressure (J=400 d-scan):", {f"1/{D}": round(v, 4) for D, v in sorted(meas.items(), reverse=True)})
