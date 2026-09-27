"""Per-state local reduction: fix the window anchor r0 and the START STATE S0.  All cells used by the window are
(m - S, b) with S >= S0, b in [b0, b0+2K-2], b0 = 2r0+2, and their values are centered(W 2^{S-S0} mod 3^b)/3^b
with W = xi 2^{S0}.  So the window depends on xi only through W mod 3^{b0+2K}, i.e. through U_0 = centered(W mod
3^{b0})/3^{b0} and the 2K new digits.  Truncating U_0 at precision 3^{-n} should change M_K(S0) by an amount
decaying in n.  Experiment: randomize W's digits below position b0 - n, keep the rest, measure |dP_K|.
usage: python3 perstate.py J K r0frac"""
import math, random, sys
AL = math.log2(3); p = 1 / AL; q = 1 - p
J = int(sys.argv[1]); K = int(sys.argv[2]); RF = float(sys.argv[3]) if len(sys.argv) > 3 else 0.4
SV = 3.0
R = J // 2; sg = math.floor(J * AL); t = J // 6; m = sg + t + 1
top = [min(math.floor(i * AL), sg) for i in range(J + 1)]
UMAX = 30; wu = [0.0, 0.0] + [p * p * q ** (u - 2) for u in range(2, UMAX + 1)]
r0 = int(RF * R); b0 = 2 * r0 + 2; DEPTH = b0 + 2 * K + 2
def MK_from_W(W, S0):
    """M_K for the window starting at (r0, S0), environment given by W = xi 2^{S0} mod 3^DEPTH."""
    rows = []
    for r in range(r0, r0 + K):
        b = 2 * r + 2; qb = 3 ** b; d = {}
        v = W % qb                       # = xi 2^{S0} mod 3^b  (S = S0)
        for S in range(S0, top[2 * r + 1] + 2):
            y = v if v <= qb // 2 else v - qb
            d[S] = 54 * abs(y) < qb; v = v * 2 % qb
        rows.append(d)
    V = {S: 1.0 for S in range(2 * (r0 + K), top[2 * (r0 + K)] + 1)}
    for j in range(K - 1, -1, -1):
        r = r0 + j; cap = top[2 * r + 1]; row = rows[j]; nV = {}
        for S in range(max(2 * r, S0), top[2 * r] + 1):
            acc = 0.0
            for S2 in range(S + 2, min(S + UMAX, top[2 * r + 2]) + 1):
                v2 = V.get(S2)
                if v2 is None: continue
                hi = min(S2 - 1, cap)
                if hi <= S: continue
                w = sum(SV if row.get(x, False) else 1.0 for x in range(S + 1, hi + 1))
                acc += w * wu[S2 - S] * v2
            nV[S] = acc
        V = nV
    return math.log2(V[S0]) / (2 * K) if V.get(S0, 0) > 0 else float('-inf')
random.seed(5)
print(f"J={J} K={K} r0={r0} (b0={b0}): per-state sensitivity to the deep digits of W = xi 2^(S0)")
for S0 in (2 * r0, (2 * r0 + top[2 * r0]) // 2, top[2 * r0]):
    W0 = pow(2, S0 - m, 3 ** DEPTH) % 3 ** DEPTH   # W = xi 2^{S0-m}, xi = 1
    base = MK_from_W(W0, S0)
    out = []
    for n in (0, 2, 4, 8, 16, 32):
        dev = 0.0
        for _ in range(10):
            lo = max(b0 - n, 0)
            W2 = (W0 - (W0 % 3 ** lo) + random.randrange(3 ** lo)) % 3 ** DEPTH
            if W2 % 3 == 0: W2 += 1
            dev = max(dev, abs(MK_from_W(W2, S0) - base))
        out.append(f"n={n}: {dev:.4f}")
    print(f"  S0={S0} (headroom {top[2*r0]-S0}), P_K = {base:.4f}: max|dP_K| over 10 perturbations: " + "  ".join(out), flush=True)
