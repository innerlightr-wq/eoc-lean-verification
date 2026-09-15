"""Part XV: phase of record depths.  Block maxima M_b over 2^B-blocks in [2^35, 2^36) (theta = 1
for short blocks).  Predicted law P(M_b <= N) = exp(-(B/2) p_N), so P(M_b = N) = F(N) - F(N-1)
already contains the renewal phase and the Sturmian exit clock.  Compare the observed distribution
of phi(M_b) = {alpha M_b} (10 windows) and of the renewal coefficient class with the prediction."""
import json, struct
from math import exp, log2
A = log2(3)
T = json.load(open("pn_table.json"))["0"]
lp = {r["N"]: r["lP"] for r in T}
data = open("surv_U0_2p36_T80.bin", "rb").read()
for B in (20, 24):
    mx = {}
    for off in range(0, len(data), 12):
        mu, e = struct.unpack_from("<QI", data, off)
        if mu >= 2 ** 35:
            k = mu >> B
            if e > mx.get(k, 0):
                mx[k] = e
    nb = 2 ** (35 - B)
    F = lambda N: exp(-(2.0 ** (B - 1)) * 2.0 ** lp[N])
    pred = [0.0] * 10
    for N in range(81, 1400):
        pred[int(((N * A) % 1) * 10)] += F(N) - F(N - 1)
    obs = [0] * 10
    for v in mx.values():
        obs[int(((v * A) % 1) * 10)] += 1
    tot = sum(obs)
    chi = sum((obs[w] - tot * pred[w] / sum(pred)) ** 2 / (tot * pred[w] / sum(pred)) for w in range(10))
    print(f"B={B}: {tot} block maxima (of {nb} blocks); phase of the record depth, observed vs predicted")
    print("   window     obs frac   pred frac   obs/pred")
    for w in range(10):
        pf = pred[w] / sum(pred)
        print(f"   [{w/10:.1f},{(w+1)/10:.1f})   {obs[w]/tot:.4f}    {pf:.4f}     {obs[w]/tot/pf:.3f}")
    print(f"   chi^2 = {chi:.1f} on 9 dof (95% point 16.9)")
