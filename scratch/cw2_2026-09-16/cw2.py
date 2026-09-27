"""Track A: analytic / compressed super-eigenvectors, and fixed-K CW (Parts A3-A13).

One-block operator (killed P* pair chain, tilt s at black own odd cells):
  (T_r f)(S) = sum_{S2} [ sum_{x admissible} s^{black(m-x,2r+2)} ] p^2 q^{S2-S-2} f(S2).
Collatz-Wielandt: if h_r > 0 with (T_r h_{r+1})(S) <= M h_r(S) for all r, S, then the window/global bound holds
with per-step exponent log2(M)/2.  Tested weights:
  h = 1                      (the crude sup bound)
  h_r(S) = exp(a Q_r(S))     (Q = predictable black probability; local, O(1) digits)
  h_r(S) = (1 + b Q_r(S))
  h_r(S) = M_K(r,S)          (look-ahead; local, O(K) digits)  -- reported by cw.py
Also: fixed K (not growing with J) CW values, and the exact global pressure for reference.
usage: python3 cw2.py J [s]"""
import math, sys

AL = math.log2(3); p = 1 / AL; q = 1 - p
J = int(sys.argv[1]); SV = float(sys.argv[2]) if len(sys.argv) > 2 else 3.0
R = J // 2; sg = math.floor(J * AL); t = J // 6; m = sg + t + 1
top = [min(math.floor(i * AL), sg) for i in range(J + 1)]
UMAX = 30; DMAX = 60
def row_black(b, x_lo, x_hi):
    qb = 3 ** b; rr = pow(2, -(m - x_lo), qb) % qb; out = {}
    for x in range(x_lo, x_hi + 1):
        y = rr if rr <= qb // 2 else rr - qb
        out[x] = 54 * abs(y) < qb; rr = rr * 2 % qb
    return out
blk = [row_black(2 * r + 2, 2 * r, top[2 * r] + DMAX) for r in range(R)]
wu = [0.0, 0.0] + [p * p * q ** (u - 2) for u in range(2, UMAX + 1)]
# cumulative internal weights and Q values
cumw = []; Q = []
for r in range(R):
    cap = top[2 * r + 1]; row = blk[r]; W = {}; qd = {}
    for S in range(2 * r, top[2 * r] + 1):
        run = 0.0; lst = []
        for x in range(S + 1, min(cap, top[2 * r + 2] - 1) + 1):
            run += SV if row.get(x, False) else 1.0
            lst.append(run)
        W[S] = lst
        qd[S] = sum(p * q ** (d - 1) for d in range(1, DMAX + 1) if row.get(S + d, False))
    cumw.append(W); Q.append(qd)

def apply_T(r, f):
    """(T_r f)(S) for S at block r, f defined at block r+1."""
    cap = top[2 * r + 1]; W = cumw[r]; out = {}
    for S in range(2 * r, top[2 * r] + 1):
        lst = W[S]; acc = 0.0
        for S2 in range(S + 2, min(S + UMAX, top[2 * r + 2]) + 1):
            v = f.get(S2)
            if v is None: continue
            k = min(S2 - 1, cap) - S - 1
            if k < 0: continue
            acc += (lst[k] if k < len(lst) else (lst[-1] if lst else 0.0)) * wu[S2 - S] * v
        out[S] = acc
    return out

def cw_ratio(hfun, lo=1, hi=None):
    """max over blocks r in [lo,hi) and states S of (T_r h_{r+1})(S)/h_r(S); per-step bits."""
    hi = hi if hi is not None else R - 1
    worst = -1e9; arg = None
    for r in range(lo, hi):
        hnext = {S: hfun(r + 1, S) for S in Q[r + 1]}
        Th = apply_T(r, hnext)
        for S, v in Th.items():
            hv = hfun(r, S)
            if v > 0 and hv > 0:
                val = math.log2(v / hv) / 2
                if val > worst: worst = val; arg = (r, S)
    return worst, arg

print(f"J={J} s={SV}: one-block Collatz-Wielandt with analytic weights (per-step bits; theta_max = 0.137)")
r0, _ = cw_ratio(lambda r, S: 1.0)
print(f"  h = 1 (crude sup bound):            {r0:.4f}")
best = (1e9, None)
for a in (0.5, 1.0, 1.5, 2.0, 3.0, 4.0, 6.0):
    v, arg = cw_ratio(lambda r, S, a=a: math.exp(a * Q[r][S]))
    if v < best[0]: best = (v, ("exp", a, arg))
    print(f"  h = exp({a} Q):                      {v:.4f}")
for b in (1.0, 2.0, 4.0, 8.0, 16.0):
    v, arg = cw_ratio(lambda r, S, b=b: 1.0 + b * Q[r][S])
    if v < best[0]: best = (v, ("lin", b, arg))
    print(f"  h = 1 + {b} Q:                       {v:.4f}")
print(f"  best analytic: {best[0]:.4f} bits/step  ({best[1][0]} param {best[1][1]}, worst at block/state {best[1][2]})")

# fixed-K CW (h = M_K look-ahead), K not growing with J
def MK(r0, L):
    V = {S: 1.0 for S in range(2 * (r0 + L), top[2 * (r0 + L)] + 1)}
    for r in range(r0 + L - 1, r0 - 1, -1):
        V = {S: v for S, v in apply_T(r, V).items()}
    return V
out = []
for K in (8, 16, 24, 32):
    if 2 * K + 2 >= R: continue
    worst = -1e9
    for r0 in range(1, R - 2 * K, max(1, R // 12)):
        V1 = MK(r0, K); V2 = MK(r0, 2 * K)
        for S in V1:
            if V1[S] > 0 and V2.get(S, 0) > 0:
                worst = max(worst, math.log2(V2[S] / V1[S]) / (2 * K))
    out.append(f"K={K}: {worst:.4f}")
print("  fixed-K CW (h = M_K): " + "  ".join(out))
# global pressure for reference
v = [0.0] * (sg + 2); v[0] = 1.0; lg = 0.0
Zf = [None] * (J + 1)
cnt = {0: 1}
for i in range(J):
    acc = 0.0; nv = [0.0] * (sg + 2)
    odd = (i + 1) % 2 == 1
    for S2 in range(i + 1, top[i + 1] + 1):
        acc += v[S2 - 1]
        if acc:
            nv[S2] = acc * (SV if (odd and blk[i // 2].get(S2, False)) else 1.0)
    mx = max(nv); lg += math.log2(mx); v = [x / mx for x in nv]
Fc = {0: 1}
for i in range(J):
    acc = 0; nx = {}
    for S2 in range(i + 1, top[i + 1] + 1):
        acc += Fc.get(S2 - 1, 0)
        if acc: nx[S2] = acc
    Fc = nx
Z = Fc[sg]
print(f"  global pressure (1/J) log2 E[s^N_odd] = {(lg + math.log2(v[sg]) - math.log2(Z)) / J:.4f} bits/step")
