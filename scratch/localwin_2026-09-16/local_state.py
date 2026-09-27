"""Local-state reduction (Parts XIII-XX): how many ternary digits does one K-window inspect?

Theory (see REPORT §2): with A = xi 2^{S_0} mod 3^{b_0+2K} split as A = A_low + 3^{b_0} H,
  U_l = < 2^{Delta S_l} (U_0 + H) / 3^l >   (centered fractional part),   U_0 = centered(A_low)/3^{b_0},
so the window's colours depend on xi only through the REAL number U_0 and the 2K new digits, and U_0 is needed
only to precision eta 3^l / 2^{Delta S_l} (= O(eta) for typical paths).  Experiment: perturb the deep residue
below its top n digits (i.e. keep U_0 only to precision 3^{-n}) and measure the change in P_K = log2 M_K/(2K).
Also: density of BAD local windows for Haar-random environments, and the fitted decay rate in K.
usage: python3 local_state.py J K [mode=digits|density] [s] [samples]"""
import math, random, sys

AL = math.log2(3); p = 1 / AL; q = 1 - p
J = int(sys.argv[1]); K = int(sys.argv[2])
MODE = sys.argv[3] if len(sys.argv) > 3 else "digits"
SV = float(sys.argv[4]) if len(sys.argv) > 4 else 3.0
NS = int(sys.argv[5]) if len(sys.argv) > 5 else 60
R = J // 2; sg = math.floor(J * AL); t = J // 6; m = sg + t + 1
top = [min(math.floor(i * AL), sg) for i in range(J + 1)]
UMAX = 30
wu = [0.0, 0.0] + [p * p * q ** (u - 2) for u in range(2, UMAX + 1)]

def rows(xi, r0, K):
    """black tables for the window's rows."""
    out = []
    for r in range(r0, r0 + K):
        b = 2 * r + 2; qb = 3 ** b; x_lo = 2 * r; x_hi = top[2 * r + 1] + 1
        rr = xi * pow(2, -(m - x_lo), qb) % qb; d = {}
        for x in range(x_lo, x_hi + 1):
            y = rr if rr <= qb // 2 else rr - qb
            d[x] = 54 * abs(y) < qb; rr = rr * 2 % qb
        out.append(d)
    return out

def MKsup(bl, r0, K):
    V = {S: 1.0 for S in range(2 * (r0 + K), top[2 * (r0 + K)] + 1)}
    for j in range(K - 1, -1, -1):
        r = r0 + j; cap = top[2 * r + 1]; row = bl[j]; nV = {}
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
    vals = [v for v in V.values() if v > 0]
    return math.log2(max(vals)) / (2 * K) if vals else float('-inf')

if MODE == "digits":
    random.seed(11)
    print(f"J={J} K={K} s={SV}: sensitivity of P_K to the DEEP digits (xi = 1 perturbed below its top n digits "
          f"of the deep part).  b_0 = 2 r0 + 2.")
    for r0 in (int(0.3 * R), int(0.6 * R)):
        b0 = 2 * r0 + 2
        base = MKsup(rows(1, r0, K), r0, K)
        line = []
        for n in (0, K // 2, K, 2 * K, 3 * K, 4 * K):
            dev = 0.0
            for _ in range(8):
                # keep xi mod 3^{b0} only to its top n digits: perturb the low b0-n digits
                pert = random.randrange(3 ** max(b0 - n, 0))
                xi2 = 1 + 3 ** 0 * 0 + (pert - (1 % 3 ** max(b0 - n, 0)))   # xi2 = xi with low digits replaced
                xi2 = xi2 if xi2 % 3 else xi2 + 3 ** max(b0 - n, 0)          # keep it a unit
                dev = max(dev, abs(MKsup(rows(xi2, r0, K), r0, K) - base))
            line.append(f"n={n}: max|dP_K| = {dev:.4f}")
        print(f"  anchor r0={r0} (b_0={b0}), P_K(true) = {base:.4f}: " + "  ".join(line), flush=True)
else:
    random.seed(23)
    MOD = 3 ** (J + 2)
    r0s = [int(f * R) for f in (0.2, 0.4, 0.6, 0.8) if int(f * R) + K < R]
    vals = []
    for _ in range(NS):
        xi = random.randrange(1, MOD)
        while xi % 3 == 0: xi = random.randrange(1, MOD)
        for r0 in r0s:
            vals.append(MKsup(rows(xi, r0, K), r0, K))
    vals.sort()
    n = len(vals)
    print(f"J={J} K={K} s={SV}: {n} Haar windows (sup over ALL confined start states): "
          f"mean {sum(vals)/n:.4f}, median {vals[n//2]:.4f}, max {vals[-1]:.4f}")
    for th in (0.08, 0.10, 0.12, 0.15):
        c = sum(1 for v in vals if v >= th)
        print(f"   P(P_K >= {th}) = {c}/{n} = {c/n:.4f}" + (f"  (rate -log2 P / K = {-math.log2(c/n)/K:.4f})" if c else "  (0)"))
