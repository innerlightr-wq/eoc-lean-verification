"""Part X: effective number of independent trials.  Dispersion index D = E[(count-mean)^2]/mean of
survivor counts (depth N) in intervals [a, lambda a), mean = ((lambda-1) a / 2) p_N.  Orbit clusters
are multiplicative (x, T^i x ~ x 2^{-R_i}), so short intervals (lambda -> 1) should be Poisson
(D = 1) and long ones approach the Palm cluster size.  N_eff = count / D."""
import json, struct, bisect, random
from math import log2
rng = random.Random(1)
T = json.load(open("pn_table.json"))["0"]
lp = {r["N"]: r["lP"] for r in T}
data = open("surv_U0_2p36_T80.bin", "rb").read()
for N in (100, 130):
    mus = sorted(struct.unpack_from("<Q", data, off)[0] for off in range(0, len(data), 12)
                 if struct.unpack_from("<I", data, off + 8)[0] > N)
    p = 2.0 ** lp[N]
    print(f"N={N}: {len(mus)} survivors below 2^36")
    for lam in (1.0005, 1.01, 1.1, 1.5, 2.0, 3.0, 8.0):
        zs, tot, n = 0.0, 0.0, 0
        # disjoint intervals [a, lam a) with a on a geometric grid covering [2^26, 2^36 / lam)
        a = 2.0 ** 26 * (1 + rng.random() * (lam - 1))
        while a * lam < 2.0 ** 36:
            lo, hi = int(a), int(a * lam)
            cnt = bisect.bisect_left(mus, hi) - bisect.bisect_left(mus, lo)
            mean = (hi - lo) / 2 * p
            if mean > 3:
                zs += (cnt - mean) ** 2
                tot += mean
                n += 1
            a *= lam if lam > 1.01 else 1 + (lam - 1)   # contiguous tiling
            if lam <= 1.01:
                a = hi
        if n:
            print(f"   lambda={lam:<7} intervals {n:6d}   dispersion index D = {zs / tot:6.3f}")
