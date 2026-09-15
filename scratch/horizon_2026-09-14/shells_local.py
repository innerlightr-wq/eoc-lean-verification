"""Non-nested test: dyadic shells [2^(k-1), 2^k) are disjoint, so shell counts at different k are
independent samples (apart from clusters spanning shells).  z = (S_shell - M_shell)/sqrt(M_shell),
restricted to depths past the shell's fresh-bit horizon, binned by M."""
import json, re, sys
from math import sqrt
c, hf = int(sys.argv[1]), sys.argv[2]
T = json.load(open("pn_table.json"))[str(c)]
lp = {r["N"]: r["lP"] for r in T}; sN = {r["N"]: r["sN"] for r in T}
H = {}
for line in open(hf):
    m = re.match(r"HIST k=(\d+):(.*)", line)
    if m: H[int(m.group(1))] = {int(a): int(b) for a, b in re.findall(r"(\d+):(\d+)", m.group(2))}
bins = [(1e1, 1e2), (1e2, 1e3), (1e3, 1e4), (1e4, 1e5), (1e5, 1e6), (1e6, 1e8)]
acc = {b: [] for b in bins}
for k in range(20, max(H) + 1):
    h = H[k]; emax = max(h)
    S, a = {}, 0
    for e in range(emax + 1, 0, -1):
        a += h.get(e, 0); S[e - 1] = a
    n = 2 ** (k - 1)   # odd seeds in [2^k, 2^(k+1))
    for N in range(1, 1400):
        M = n * 2.0 ** lp[N]
        if M < 10: break
        if sN[N] + 1 <= k: continue
        z = (S.get(N, 0) - M) / sqrt(M)
        for b in bins:
            if b[0] <= M < b[1]: acc[b].append(z)
print(f"c={c}: disjoint dyadic shells, post-fresh-bit z (Poisson units)")
for b in bins:
    zs = acc[b]
    if zs:
        m = sum(zs) / len(zs); r = sqrt(sum(z * z for z in zs) / len(zs))
        print(f"   M in [{b[0]:.0e},{b[1]:.0e}): {len(zs):4d} pts  mean z {m:+.3f}  rms z {r:.3f}")
