"""(a) typical terminal drift of uniformly counted U-confined words (is the Curry dip generic?);
   (b) deep-dip recovery on unbiased random large seeds (no record seeds)."""
import random
from math import log2, floor, sqrt
ALPHA = log2(3)
rng = random.Random(7)
def v2(n): return (n & -n).bit_length() - 1
def layer_counts(U, N):
    layer = {0: 1}
    for r in range(1, N + 1):
        smax = floor(U + r * ALPHA)
        while smax - U >= 0 and (1 << (smax - U)) > 3 ** r:
            smax -= 1
        keys = sorted(layer); acc = 0; idx = 0; new = {}
        for Sp in range(r, smax + 1):
            while idx < len(keys) and keys[idx] < Sp:
                acc += layer[keys[idx]]; idx += 1
            if acc: new[Sp] = acc
        layer = new
    return layer
print("(a) uniformly counted U-confined words: terminal drift R_N (count-weighted)")
for U in (0, 2):
    for N in (100, 400, 800):
        lay = layer_counts(U, N)
        tot = sum(lay.values())
        mean = sum(c * (S - N * ALPHA) for S, c in lay.items()) / tot
        # fraction of words with R_N <= -B log2 N for B = 1.0359 (Curry threshold), B = 3
        f1 = sum(c for S, c in lay.items() if S - N * ALPHA <= -1.0359 * log2(N)) / tot
        f3 = sum(c for S, c in lay.items() if S - N * ALPHA <= -3 * log2(N)) / tot
        print(f"   U={U} N={N}: mean R_N = {mean:7.2f}  (-sqrt(N) = {-sqrt(N):6.2f});"
              f"  P(R_N <= -1.036 log2 N) = {f1:.3f};  P(R_N <= -3 log2 N) = {f3:.3f}")
print("(b) unbiased random 512-bit seeds: first dip R_t <= -G, then time to R > 2")
for G in (3, 5, 8):
    rec = []
    for _ in range(6000):
        m = rng.getrandbits(512) | 1
        S = n = 0; t = None
        while n < 5000:
            x = 3 * m + 1; d = v2(x); m = x >> d; S += d; n += 1
            R = S - n * ALPHA
            if t is None and R <= -G: t = n
            if t is not None and R > 2:
                rec.append(n - t); break
            if t is None and n > 400: break
    rec.sort()
    if rec:
        print(f"   G={G}: dips {len(rec)}/6000, mean recovery {sum(rec)/len(rec):6.1f}, median {rec[len(rec)//2]},"
              f" 99% {rec[int(.99*len(rec))]}; ensemble Wald (G+2+~1.4)/0.415 = {(G+3.4)/(2-ALPHA):.1f}")
