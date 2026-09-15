"""Local equidistribution at scales beyond exhaustive reach: NB random full periods (2^K seeds each)
of odd mu in [2^(S-1), 2^S).  Short blocks => clusters do not fit => Poisson (D ~ 1).
Q_loc(N) = #{exit > N} / (n p_N), z = (Q-1) sqrt(n p_N)."""
import json, re, sys
from math import sqrt
c, fn = int(sys.argv[1]), sys.argv[2]
T = json.load(open("pn_table.json"))[str(c)]
lp = {r["N"]: r["lP"] for r in T}
for line in open(fn):
    m = re.match(r"# sample U=\d+ K=(\d+) scale 2\^(\d+) blocks (\d+) seeds (\d+)", line)
    if m:
        K, S, nb, n = map(int, m.groups())
        continue
    m = re.match(r"SAMPLE S=(\d+):(.*)", line)
    if not m:
        continue
    h = {int(a): int(b) for a, b in re.findall(r"(\d+):(\d+)", m.group(2))}
    tot = sum(h.values()); assert tot == n
    emax = max(h)
    Sx, acc = {}, 0
    for e in range(emax + 1, 0, -1):
        acc += h.get(e, 0); Sx[e - 1] = acc
    out = []; zs = []
    for N in range(30, 400):
        M = n * 2.0 ** lp[N]
        if M < 30: break
        q = Sx.get(N, 0) / M
        z = (q - 1) * sqrt(M)
        zs.append(z)
        if N % 30 == 0:
            out.append(f"N={N}(A={N/S:.1f}):Q={q:.4f},z={z:+.1f}")
    rms = sqrt(sum(z * z for z in zs) / len(zs))
    print(f"c={c} scale 2^{S}: n={n:.2e}, depths 30..{29+len(zs)}, rms z = {rms:.2f}, mean z = {sum(zs)/len(zs):+.2f}")
    print("    " + "  ".join(out))
