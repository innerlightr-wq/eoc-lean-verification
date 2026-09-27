"""Worst-state superblock pressure for the predictable occupation (Parts XXVII-XXIX).

Killed P* pair chain on confined even states: from S at block r, pair sum u with weight
  w_r(S -> S+u) = nB * p^2 q^(u-2),   nB = min(S+u-1, top[2r+1]) - S   (paths staying confined through the block),
potential e^{tau Q_r(S)}, Q_r(S) = sum_d p q^(d-1) black(m-S-d, 2r+2) (P* predictable black probability).
  M_K(tau, S, r0) = E*_S[ exp(tau sum_{r=r0}^{r0+K-1} Q_r(S_{2r})) ; confined through the K blocks ].
Blockwise Chernoff (PROVED MATH, see REPORT): P*(C', sum_r Q_r >= theta R) <= e^{-tau theta R} prod_blocks sup_S M_K,
so the per-pair rate is  tau*theta - (1/K) max_{r0} ln sup_S M_K(tau,S,r0).  Reported: q*_K = min_tau max_{S,r0}
ln M_K/(tau K)  (block Chernoff works for theta > q*_K), for sup over ALL confined states and over typical states.
usage: python3 superblock.py J [env=true|random]"""
import math, sys, random

AL = math.log2(3); p = 1 / AL; q = 1 - p
J = int(sys.argv[1]); env = sys.argv[2] if len(sys.argv) > 2 else "true"
R = J // 2; sg = math.floor(J * AL); t = J // 6; m = sg + t + 1
top = [min(math.floor(i * AL), sg) for i in range(J + 1)]
DMAX = 60; UMAX = 40
xi = 1
if env == "random":
    random.seed(7000 + J); xi = random.randrange(1, 3 ** (J + 2))
    while xi % 3 == 0: xi = random.randrange(1, 3 ** (J + 2))
def row_black(b, x_lo, x_hi):
    qb = 3 ** b; rr = xi * pow(2, -(m - x_lo), qb) % qb; out = {}
    for x in range(x_lo, x_hi + 1):
        y = rr if rr <= qb // 2 else rr - qb
        out[x] = 54 * abs(y) < qb; rr = rr * 2 % qb
    return out
Q = []
for r in range(R):
    row = row_black(2 * r + 2, 2 * r + 1, top[2 * r] + DMAX)
    Q.append({S: sum(p * q ** (d - 1) for d in range(1, DMAX + 1) if row.get(S + d, False))
              for S in range(2 * r, top[2 * r] + 1)})
# confined path marginal at even times (typical states)
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
Z = F[J][sg]
typical = []
for r in range(R):
    i = 2 * r; w = {S: F[i][S] * G[i][S] for S in F[i] if S in G[i]}
    thr = Z >> 40                                        # mass > 2^-40
    typical.append({S for S, v in w.items() if v > thr})

wu = [0.0, 0.0] + [p * p * q ** (u - 2) for u in range(2, UMAX + 1)]
def MK(tau, r0, K):
    V = {S: 1.0 for S in range(2 * (r0 + K), top[2 * (r0 + K)] + 1)}
    for r in range(r0 + K - 1, r0 - 1, -1):
        cap = top[2 * r + 1]; nV = {}
        for S in range(2 * r, top[2 * r] + 1):
            s = 0.0
            for S2 in range(S + 2, min(S + UMAX, top[2 * r + 2]) + 1):
                v = V.get(S2)
                if v is None: continue
                nB = min(S2 - 1, cap) - S
                if nB > 0: s += nB * wu[S2 - S] * v
            nV[S] = math.exp(tau * Q[r][S]) * s
        V = nV
    return V
TAUS = (0.1, 0.25, 0.5, 1.0, 2.0)
THETAS = (0.05, 0.06, 0.075, 0.10)
print(f"J={J} env={env}: superblock worst-state pressure (killed P* chain), anchors in [0.1R, 0.9R-K]")
print("  per-step rate (bits) of the block Chernoff bound for P*(C', sum Q_r >= theta R): "
      "max_tau [tau theta - max_r0 ln sup_S M_K / K] / (2 ln 2)")
for K in (4, 8, 16, 32, 64):
    anchors = list(range(int(0.1 * R), int(0.9 * R) - K, max(1, R // 15)))
    la_ = {}; lt_ = {}
    for tau in TAUS:
        sa = st = -1e9
        for r0 in anchors:
            V = MK(tau, r0, K)
            sa = max(sa, max(math.log(v) for v in V.values() if v > 0))
            st = max(st, max(math.log(V[S]) for S in typical[r0] if V.get(S, 0) > 0))
        la_[tau] = sa / K; lt_[tau] = st / K
    qa = min(la_[x] / x for x in TAUS); qt = min(lt_[x] / x for x in TAUS)
    ra = [max(x * th - la_[x] for x in TAUS) / (2 * math.log(2)) for th in THETAS]
    rt = [max(x * th - lt_[x] for x in TAUS) / (2 * math.log(2)) for th in THETAS]
    print(f"  K={K:3d} ({len(anchors)} anchors): q*_K all={qa:.4f} typ={qt:.4f} | rate(theta) all: "
          + " ".join(f"{th}:{v:+.4f}" for th, v in zip(THETAS, ra)) + " | typ: "
          + " ".join(f"{th}:{v:+.4f}" for th, v in zip(THETAS, rt)), flush=True)
