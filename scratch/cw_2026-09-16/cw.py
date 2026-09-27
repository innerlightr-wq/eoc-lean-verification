"""Collatz-Wielandt (super-eigenvector) relaxation of LocalWindowPressure (Parts VI, XXV-XXX).

The window product bound needs, for each window, a factor M with (T_K h)(S) <= M h(S) for a positive weight h
(Collatz-Wielandt); the sup version is h = 1.  Taking h = M_K (the next window's own value) gives
  M_eff = max_S M_{2K}(r0,S) / M_K(r0,S),      P^CW_K = (1/2K) log2 M_eff,
which is exactly the "conditional" pressure of the second window given the first: bad start states inflate both
numerator and denominator, so the adversarial states cancel.  Compare:
  P_K^sup  = max_S (1/2K) log2 M_K(r0,S)          (current LocalWindowPressure)
  P_K^CW   = max_S (1/2K) log2 (M_{2K}/M_K)(S)    (relaxed, still local: depends on 4K rows)
  P_bridge = (1/2K) log2 ( sum_S pi(S) M_K(S) )   (weighted, for reference)
Also reports the bridge mass of high-pressure states (Parts XXVIII-XXIX).
usage: python3 cw.py J c0 [s]"""
import math, sys

AL = math.log2(3); p = 1 / AL; q = 1 - p
J = int(sys.argv[1]); C0 = int(sys.argv[2]); SV = float(sys.argv[3]) if len(sys.argv) > 3 else 3.0
R = J // 2; sg = math.floor(J * AL); t = J // 6; m = sg + t + 1
top = [min(math.floor(i * AL), sg) for i in range(J + 1)]
UMAX = 30; K = C0 * max(int(math.log2(J)), 2)
def row_black(b, x_lo, x_hi):
    qb = 3 ** b; rr = pow(2, -(m - x_lo), qb) % qb; out = {}
    for x in range(x_lo, x_hi + 1):
        y = rr if rr <= qb // 2 else rr - qb
        out[x] = 54 * abs(y) < qb; rr = rr * 2 % qb
    return out
blk = [row_black(2 * r + 2, 2 * r, top[2 * r + 1] + 1) for r in range(R)]
wu = [0.0, 0.0] + [p * p * q ** (u - 2) for u in range(2, UMAX + 1)]
cumw = []
for r in range(R):
    cap = top[2 * r + 1]; row = blk[r]; W = {}
    for S in range(2 * r, top[2 * r] + 1):
        run = 0.0; lst = []
        for x in range(S + 1, min(cap, top[2 * r + 2] - 1) + 1):
            run += SV if row.get(x, False) else 1.0
            lst.append(run)
        W[S] = lst
    cumw.append(W)

def MK(r0, L):
    """values M_L(r0, S) for all confined S at block r0."""
    V = {S: 1.0 for S in range(2 * (r0 + L), top[2 * (r0 + L)] + 1)}
    for r in range(r0 + L - 1, r0 - 1, -1):
        cap = top[2 * r + 1]; W = cumw[r]; nV = {}
        for S in range(2 * r, top[2 * r] + 1):
            lst = W[S]; acc = 0.0
            for S2 in range(S + 2, min(S + UMAX, top[2 * r + 2]) + 1):
                v = V.get(S2)
                if v is None: continue
                k = min(S2 - 1, cap) - S - 1
                if k < 0: continue
                acc += (lst[k] if k < len(lst) else (lst[-1] if lst else 0.0)) * wu[S2 - S] * v
            nV[S] = acc
        V = nV
    return V

# bridge marginals at even times (environment independent)
F = [None] * (J + 1); F[0] = {0: 1}
for i in range(J):
    acc = 0; nx = {}
    for S2 in range(i + 1, top[i + 1] + 1):
        acc += F[i].get(S2 - 1, 0)
        if acc: nx[S2] = acc
    F[i + 1] = nx
G = [None] * (J + 1); G[J] = {sg: 1}
for i in range(J - 1, -1, -1):
    acc = 0; cur = {}
    for S in range(top[i + 1] - 1, i - 1, -1):
        acc += G[i + 1].get(S + 1, 0)
        if acc and S <= top[i]: cur[S] = acc
    G[i] = cur
Z = F[J][sg]; sh = max(Z.bit_length() - 60, 0)
def pi_even(r):
    i = 2 * r
    return {S: (F[i][S] * G[i][S] >> sh) / (Z >> sh) for S in F[i] if S in G[i]}

print(f"J={J} K={K} (c0={C0}) s={SV}: sup vs Collatz-Wielandt vs bridge-weighted window pressure")
sup_all = cw_all = wt_all = -1e9; hp_mass = 0.0; hp_cnt = 0; tot_states = 0
anchors = list(range(int(0.05 * R), R - 2 * K, max(1, R // 25)))
for r0 in anchors:
    V1 = MK(r0, K); V2 = MK(r0, 2 * K)
    pi = pi_even(r0)
    s1 = max((math.log2(v) / (2 * K) for v in V1.values() if v > 0), default=-1e9)
    cw = max((math.log2(V2[S] / V1[S]) / (2 * K) for S in V1 if V1.get(S, 0) > 0 and V2.get(S, 0) > 0),
             default=-1e9)
    wt = sum(pi.get(S, 0.0) * V1[S] for S in V1)
    wt = math.log2(wt) / (2 * K) if wt > 0 else -1e9
    sup_all = max(sup_all, s1); cw_all = max(cw_all, cw); wt_all = max(wt_all, wt)
    thr = 2 ** (2 * K * 0.10)
    for S, v in V1.items():
        tot_states += 1
        if v > thr: hp_cnt += 1; hp_mass = max(hp_mass, pi.get(S, 0.0))
print(f"  P_K^sup   (current hypothesis)      = {sup_all:.4f} bits/step")
print(f"  P_K^CW    (super-eigenvector h=M_K) = {cw_all:.4f} bits/step")
print(f"  P_K^bridge(weighted over states)    = {wt_all:.4f} bits/step")
print(f"  high-pressure states (M_K > 2^(2K*0.10)): {hp_cnt} of {tot_states} over {len(anchors)} anchors; "
      f"max bridge mass of such a state {hp_mass:.3e}")
