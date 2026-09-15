"""Part XVI-XVII: conditional (prefix-level) uniformity.  For each confined prefix P of length j0
(sum S_P), its realizers below X = 2^HI form an arithmetic progression of L_P = 2^(HI-1-S_P) seeds;
the Haar prediction for the number surviving to depth N is E_P = L_P * B(j0, S_P -> N).
Observed O_P from the survivor dump.  All confined prefixes (including those with O_P = 0) are
included via exact prefix counts A_{j0}(s).  Reports the distribution of z_P = (O_P-E_P)/sqrt(E_P)
across prefixes: mean, rms, quantiles, fraction |z|>3, worst, and mass of 'bad' prefixes.
usage: python3 prefix_conditional.py dump.bin HI N j0 c"""
import struct, sys
from math import floor, log2, sqrt
from collections import Counter
fn, HI, N, j0, c = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
A = log2(3)
def Kf(j):
    s = floor(c + j * A)
    while (1 << (s - c)) > 3 ** j: s -= 1
    return s
K = [10 ** 9] + [Kf(j) for j in range(1, N + 2)]
B = [None] * (N + 1)
B[N] = {s: 1.0 for s in range(N, K[N] + 1)}
for j in range(N - 1, -1, -1):
    nxt = B[j + 1]; top = K[j + 1]; vals, t = {}, 0.0
    for s in range(top - 1, j - 1, -1):
        t = 0.5 * (nxt.get(s + 1, 0.0) + t); vals[s] = t
    B[j] = {s: vals[s] for s in range(j, (K[j] if j > 0 else 0) + 1) if s in vals}
# exact counts of confined prefixes of length j0 by sum
layer = {0: 1}
for j in range(1, j0 + 1):
    new = {}
    for S, v in layer.items():
        for d in range(1, K[j] - S + 1):
            new[S + d] = new.get(S + d, 0) + v
    layer = new
# observed survivors per prefix
obs = Counter()
data = open(fn, "rb").read()
for off in range(0, len(data), 12):
    mu, e = struct.unpack_from("<QI", data, off)
    if e <= N or mu >= 2 ** HI: continue
    m, S, dig = mu, 0, []
    for _ in range(j0):
        x = 3 * m + 1; d = (x & -x).bit_length() - 1; m = x >> d; S += d; dig.append(d)
    obs[tuple(dig)] += 1
# per-sum aggregation: prefixes with the same S have the same E
zs = {10: [], 30: [], 100: [], 1000: []}
ratio_all = []
bad_mass = {10: [0, 0], 30: [0, 0], 100: [0, 0], 1000: [0, 0]}
byS = {}
for P, o in obs.items(): byS.setdefault(sum(P), []).append(o)
for S, cnt in layer.items():
    if S > HI - 2: continue
    L = 2 ** (HI - 1 - S); E = L * B[j0].get(S, 0.0)
    if E <= 0: continue
    os_ = byS.get(S, []) + [0] * (cnt - len(byS.get(S, [])))
    for thr in zs:
        if E >= thr:
            for o in os_:
                z = (o - E) / sqrt(E); zs[thr].append(z)
                bad_mass[thr][1] += E
                if abs(z) > 3: bad_mass[thr][0] += E
print(f"X=2^{HI} N={N} (A={N/HI:.2f}) prefix depth j0={j0}: {sum(layer.values())} confined prefixes")
print("  E>=thr   #prefixes   mean z   rms z   q05    q50    q95    frac|z|>3   worst z   Haar-mass of bad prefixes")
for thr in (10, 30, 100, 1000):
    z = sorted(zs[thr])
    if len(z) < 5: continue
    q = lambda p: z[min(len(z) - 1, int(p * len(z)))]
    print(f"  {thr:5d}   {len(z):8d}   {sum(z)/len(z):+.3f}  {sqrt(sum(t*t for t in z)/len(z)):.3f}  {q(.05):+.2f}  {q(.5):+.2f}  {q(.95):+.2f}"
          f"    {sum(abs(t)>3 for t in z)/len(z):.4f}    {max(z, key=abs):+.2f}    {bad_mass[thr][0]/bad_mass[thr][1]:.4f}")
