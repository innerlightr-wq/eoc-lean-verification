"""Part XVI: extreme-value law for stopping-time records with clustering.
(a) dyadic prefixes [0, X): record depth M_X vs independent model P(M<=N) = exp(-(X/2) p_N) and the
    clustered model exp(-theta (X/2) p_N), theta = clusters/survivors (measured ~ 1/2.92).
(b) block maxima over disjoint short blocks [bB, (b+1)B) inside [2^35, 2^36): clusters (orbit
    segments x, T^i x ~ x 2^-R_i) essentially never fit inside a short block, so theta_block ~ 1."""
import json
import re
import struct
from math import exp, log, log2
T = json.load(open("pn_table.json"))["0"]
lp = {r["N"]: r["lP"] for r in T}          # log2 p_N (c = 0)
p = lambda N: 2.0 ** lp[N]
# ---- (a) records through 2^40 (c = 0): combine the 2^32 scan and the 2^32..2^40 sieve runs
rec = []
txt = open("../pair_valuation_2026-09-14/hist_2p32.out").read()
rec += [(int(a), int(b)) for a, b in re.findall(r"(\d+):(\d+)", re.search(r"EXIT_RECORDS U=0:(.*)", txt).group(1))]
for fn in ("glide_sieve_32_36.out", "glide_sieve_36_40.out"):
    rec += [(int(a), int(b)) for a, b in re.findall(r"(\d+):(\d+)", re.search(r"RECORDS:(.*)", open("../pair_valuation_2026-09-14/" + fn).read()).group(1))]
theta = 1 / 2.92
print("(a) dyadic prefixes: u = P(M <= M_obs) under each model (Uniform(0,1) if the model is right)")
print("  log2X  M_obs   N_med(indep)  N_med(clust)   u_indep  u_clust")
ui, uc = [], []
for k in range(16, 41, 2):
    X = 2.0 ** k
    M = max(e for mu, e in rec if mu < X)
    med = lambda th: next(N for N in range(1, 1400) if th * X / 2 * p(N) < log(2))
    a, b = exp(-X / 2 * p(M)), exp(-theta * X / 2 * p(M))
    ui.append(a); uc.append(b)
    print(f"  {k:5d}  {M:4d}   {med(1):8d}      {med(theta):8d}      {a:6.3f}   {b:6.3f}")
print(f"  mean u: independent {sum(ui)/len(ui):.3f}   clustered {sum(uc)/len(uc):.3f}   (ideal 0.5; nested, correlated)")
# ---- (b) block maxima in [2^35, 2^36) from the exit>=80 dump
mx = {}
with open("surv_U0_2p36_T80.bin", "rb") as f:
    data = f.read()
for off in range(0, len(data), 12):
    mu, e = struct.unpack_from("<QI", data, off)
    if mu >= 2 ** 35:
        for B in (20, 24, 28):
            key = (B, mu >> B)
            if e > mx.get(key, 0):
                mx[key] = e
print("\n(b) block maxima, blocks of size 2^B inside [2^35, 2^36)")
for B in (20, 24, 28):
    vals = sorted(v for (bb, _), v in mx.items() if bb == B)
    nb = 2 ** (35 - B)
    vals += [0] * (nb - len(vals))   # blocks with no survivor >= 80
    import statistics
    Bn = 2.0 ** B
    for th, name in ((1.0, "theta=1"), (theta, "theta=1/2.92")):
        # KS-type comparison: predicted CDF at observed quantiles, and mean of u
        us = [exp(-th * Bn / 2 * p(v)) if v >= 80 else None for v in vals]
        us = [u for u in us if u is not None]
        mean_u = sum(us) / len(us)
        # fraction of blocks with max <= predicted median
        medN = next(N for N in range(1, 1400) if th * Bn / 2 * p(N) < log(2))
        frac = sum(v <= medN for v in vals) / nb
        print(f"  B={B}: {nb} blocks, median(max) = {statistics.median(vals)}, {name}: predicted median {medN}, "
              f"P(max <= pred median) = {frac:.3f}, mean u = {mean_u:.3f}")
