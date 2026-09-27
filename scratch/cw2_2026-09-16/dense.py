"""Denser anchor scan of the fixed-K CW value (h = M_K look-ahead)."""
import math, sys
exec(open('cw2.py').read().split('print(f"J={J} s={SV}')[0])
STRIDE = int(sys.argv[3]) if len(sys.argv) > 3 else 2
def MK(r0, L):
    V = {S: 1.0 for S in range(2 * (r0 + L), top[2 * (r0 + L)] + 1)}
    for r in range(r0 + L - 1, r0 - 1, -1):
        V = apply_T(r, V)
    return V
for K in (24, 32):
    if 2 * K + 2 >= R: continue
    worst = -1e9; arg = None; n = 0
    for r0 in range(1, R - 2 * K, STRIDE):
        n += 1
        V1 = MK(r0, K); V2 = MK(r0, 2 * K)
        for S in V1:
            if V1[S] > 0 and V2.get(S, 0) > 0:
                v = math.log2(V2[S] / V1[S]) / (2 * K)
                if v > worst: worst, arg = v, (r0, S)
    print(f"J={J} K={K}: {n} anchors (stride {STRIDE}): max CW = {worst:.4f} at {arg}", flush=True)
