"""Logarithmic superblocks for the N_odd exponential moment (Parts XXXIV-XXXVII).

Killed P* pair chain on confined even states; over a window of K pair blocks starting at r0,
  M_K(S) = E*_S[ s^{#black own odd cells in the window} ; confined through the window ],
with transition weight from S to S2 = sum over admissible internal x of p^2 q^{u-2} s^{black(m-x, 2r+2)}.
Blockwise Chernoff gives E_conf[s^{N_odd}] <= poly * prod_windows sup_S M_K, so the route needs
  P_K = (1/(2K)) log2 max_{r0} sup_S M_K(S)   <   the threshold theta (0.085 at s = 3, N0 = 4, g = 0.1).
Reported for K = c log2 J and for fixed K.  sup over S is over all confined even states; max over r0 is over
sampled anchors in the bulk (so P_K is a LOWER bound for the true worst-window value).
usage: python3 oddsuper.py J [s]"""
import math, sys

AL = math.log2(3); p = 1 / AL; q = 1 - p
J = int(sys.argv[1]); SV = float(sys.argv[2]) if len(sys.argv) > 2 else 3.0
R = J // 2; sg = math.floor(J * AL); t = J // 6; m = sg + t + 1
top = [min(math.floor(i * AL), sg) for i in range(J + 1)]
UMAX = 30
def row_black(b, x_lo, x_hi):
    qb = 3 ** b; rr = pow(2, -(m - x_lo), qb) % qb; out = {}
    for x in range(x_lo, x_hi + 1):
        y = rr if rr <= qb // 2 else rr - qb
        out[x] = 54 * abs(y) < qb; rr = rr * 2 % qb
    return out
blk = [row_black(2 * r + 2, 2 * r, top[2 * r + 1] + 1) for r in range(R)]
wu = [0.0, 0.0] + [p * p * q ** (u - 2) for u in range(2, UMAX + 1)]

def MK(r0, K):
    V = {S: 1.0 for S in range(2 * (r0 + K), top[2 * (r0 + K)] + 1)}
    for r in range(r0 + K - 1, r0 - 1, -1):
        cap = top[2 * r + 1]; row = blk[r]; nV = {}
        for S in range(2 * r, top[2 * r] + 1):
            acc = 0.0
            for S2 in range(S + 2, min(S + UMAX, top[2 * r + 2]) + 1):
                v = V.get(S2)
                if v is None: continue
                hi = min(S2 - 1, cap)
                if hi <= S: continue
                w = sum(SV if row.get(x, False) else 1.0 for x in range(S + 1, hi + 1))
                acc += w * wu[S2 - S] * v
            nV[S] = acc
        V = nV
    return V

L = max(int(math.log2(J)), 2)
KS = sorted({L, 2 * L, 4 * L, 8, 16, 32, 64})
print(f"J={J} s={SV}: log2 J = {L}; threshold for the reduction at s=3 is 0.085 bits/step")
for K in KS:
    if r0max := int(0.9 * R) - K:
        anchors = list(range(int(0.1 * R), r0max, max(1, R // 12)))
    if not anchors: continue
    best = -1e9; worst_typ = -1e9
    for r0 in anchors:
        V = MK(r0, K)
        vals = [v for v in V.values() if v > 0]
        if vals: best = max(best, math.log2(max(vals)) / (2 * K))
    print(f"  K={K:3d} ({len(anchors)} anchors, K/log2 J = {K / L:.1f}): "
          f"P_K = (1/2K) log2 max_r0 sup_S M_K = {best:.4f} bits/step", flush=True)
