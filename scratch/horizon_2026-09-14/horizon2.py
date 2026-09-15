"""Is the empirical horizon noise-limited?  For each K and eps: depth N_first of the stable exit,
the expected count M there, E = Q-1 at exit, and the Poisson z = E sqrt(M).  Also Q at fixed
A = N/K (scaling collapse test) and the Poisson-normalized deviation z vs M."""
import json, sys
from math import sqrt, log2
c = int(sys.argv[1])
Q = {int(K): {int(N): v for N, v in d.items()} for K, d in json.load(open(f"Q_c{c}.json")).items()}
print(f"c={c}: stable exit (3 consecutive |E|>eps): N, M(N), E, z_Poisson = E*sqrt(M)")
for eps in (0.003, 0.01, 0.03):
    print(f"  eps={eps}")
    for K in sorted(Q):
        if K % 2: continue
        d = Q[K]; Ns = sorted(d)
        for i, N in enumerate(Ns[:-2]):
            if all(abs(d[Ns[i + j]][0] - 1) > eps for j in range(3)):
                q, M = d[N]
                print(f"    K={K}: N={N} A={N/K:.2f} M={M:10.1f} E={q-1:+.4f} z={(q-1)*sqrt(M):+.2f}")
                break
print(f"\nc={c}: Q at fixed A = N/K (values; '-' if M < 1)")
As = [1.0, 1.5, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0]
print("   K   " + "  ".join(f"A={a:<4}" for a in As))
for K in sorted(Q):
    if K % 2: continue
    row = []
    for a in As:
        N = round(a * K)
        if N in Q[K] and Q[K][N][1] >= 1:
            row.append(f"{Q[K][N][0]:.4f}")
        else:
            row.append("   -  ")
    print(f"  {K:2d}   " + "  ".join(row))
# collapse in M: rms of z = E sqrt(M) in bins of M, pooled over K (only depths past the fresh-bit horizon)
T = json.load(open("pn_table.json"))[str(c)]
sN = {r["N"]: r["sN"] for r in T}
bins = [(1e1, 1e2), (1e2, 1e3), (1e3, 1e4), (1e4, 1e5), (1e5, 1e6), (1e6, 1e7), (1e7, 1e8), (1e8, 1e10)]
print(f"\nc={c}: post-fresh-bit deviations in Poisson units z = E*sqrt(M), binned by expected count M (all K)")
print("   M range          #pts   mean z    rms z    (pure Poisson: 0, 1; clustered Poisson: rms ~ sqrt(D))")
for lo, hi in bins:
    zs = [(q - 1) * sqrt(M) for K in Q for N, (q, M) in Q[K].items() if lo <= M < hi and sN[N] + 1 > K]
    if zs:
        m = sum(zs) / len(zs); r = sqrt(sum(z * z for z in zs) / len(zs))
        print(f"   [{lo:.0e},{hi:.0e})   {len(zs):5d}   {m:+.3f}   {r:.3f}")
