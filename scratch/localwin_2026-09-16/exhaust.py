"""Exhaustive worst-window scan (Parts V-VII): every anchor r0, every confined start state S.

Window of K pair blocks from r0, killed P* chain on confined even states:
  M_K(r0,S) = E*_S[ s^{#black own odd cells in the window} ; confined through the window ],
  transition S -> S2 with weight (sum over admissible internal x of s^{black(m-x,2r+2)}) p^2 q^{u-2}.
P_K = (1/2K) log2 M_K  (bits per step; the reduction needs P_K <= theta ~ 0.10 at s = 3).
Also records, for the worst windows, the local black structure (black cells in the window band, longest run,
number of runs) and correlates log M_K with those statistics.
usage: python3 exhaust.py J [s] [stride]"""
import math, sys

AL = math.log2(3); p = 1 / AL; q = 1 - p
J = int(sys.argv[1]); SV = float(sys.argv[2]) if len(sys.argv) > 2 else 3.0
STRIDE = int(sys.argv[3]) if len(sys.argv) > 3 else 1
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
# per-block, per-state weight of a transition S -> S2 (cached per block)
def block_weights(r):
    cap = top[2 * r + 1]; row = blk[r]; W = {}
    for S in range(2 * r, top[2 * r] + 1):
        run = 0.0; lst = []
        for x in range(S + 1, min(cap, top[2 * r + 2] - 1) + 1):
            run += SV if row.get(x, False) else 1.0
            lst.append(run)                      # cumulative weight of choices up to x
        W[S] = lst
    return W

def MK(r0, K, WS):
    V = {S: 1.0 for S in range(2 * (r0 + K), top[2 * (r0 + K)] + 1)}
    for r in range(r0 + K - 1, r0 - 1, -1):
        cap = top[2 * r + 1]; W = WS[r]; nV = {}
        for S in range(2 * r, top[2 * r] + 1):
            lst = W[S]; acc = 0.0
            for S2 in range(S + 2, min(S + UMAX, top[2 * r + 2]) + 1):
                v = V.get(S2)
                if v is None: continue
                hi = min(S2 - 1, cap)
                k = hi - S - 1
                if k < 0: continue
                acc += (lst[k] if k < len(lst) else (lst[-1] if lst else 0.0)) * wu[S2 - S] * v
            nV[S] = acc
        V = nV
    return V

L = max(int(math.log2(J)), 2)
print(f"J={J} s={SV}: log2 J = {L}; exhaustive over anchors (stride {STRIDE}) and ALL confined start states")
WS = [block_weights(r) for r in range(R)]
for c0 in (2, 4, 6, 8, 10):
    K = c0 * L
    if K >= R - 2: continue
    best = (-1e9, None)
    for r0 in range(0, R - K, STRIDE):
        V = MK(r0, K, WS)
        for S, v in V.items():
            if v > 0:
                val = math.log2(v) / (2 * K)
                if val > best[0]: best = (val, (r0, S))
    r0, S = best[1]
    # local structure of the worst window
    nb = 0; runs = []; cur = 0
    for r in range(r0, r0 + K):
        row = blk[r]; hit = any(row.get(x, False) for x in range(2 * r, top[2 * r + 1] + 1))
        blacks = sum(1 for x in range(2 * r, top[2 * r + 1] + 1) if row.get(x, False))
        nb += blacks
        if hit: cur += 1
        else:
            if cur: runs.append(cur)
            cur = 0
    if cur: runs.append(cur)
    print(f"  c0={c0:2d} K={K:3d}: P_K^max = {best[0]:.4f} at anchor r0={r0} (r0/R={r0/R:.2f}), S={S}, "
          f"headroom={top[2 * r0] - S}; window has {nb} black band cells, "
          f"{len(runs)} row-runs, longest {max(runs) if runs else 0}", flush=True)
