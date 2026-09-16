"""Sanity check of the rigorous shape-only bound at finite J against the exact DP probabilities (GB.txt).
The bound must dominate the exact probability: log2(bound) >= log2 P_conf(G_sh < gR).
Also computes exact |C_J| (big-integer DP) and the cycle-lemma lower bound binom(sg-1,J-1)/J.
usage: python3 check_bound.py"""
import math, re
from shape_ld import AL, p, q, F, golden, lbinom2, log2_int, LN2

def count_confined(J):
    sg = math.floor(J * AL); top = [min(math.floor(i * AL), sg) for i in range(J + 1)]
    v = {0: 1}
    for i in range(J):
        nv = {}
        acc = 0; items = sorted(v.items())
        # S' ranges over (S, top[i+1]]: prefix sums over S
        pref = {}; run = 0
        for S, c in items: run += c; pref[S] = run
        keys = [S for S, _ in items]
        import bisect
        for S2 in range(i + 1, top[i + 1] + 1):
            k = bisect.bisect_left(keys, S2) - 1
            if k >= 0: nv[S2] = pref[keys[k]]
        v = nv
    return v[sg]

def bound(J, N0, g, logC):
    R = J // 2; sg = math.floor(J * AL); a = math.ceil(g * R) - 1
    lb = lbinom2(sg - 1, J - 1)
    den = logC + J * math.log2(p) + (sg - J) * math.log2(q)          # log2 P*(C_J, S_J = sg)
    def term1(n):     # log2 of J t^{-n} x^{-sg} F_t(x)^R / binom, minimized over t, x   (n = a + k - 1)
        def f1(lt):
            t = math.exp(lt)
            s, v = golden(lambda s: R * math.log(F(t, math.exp(s), N0)) - sg * s, -12, -1e-9, 60)
            return -n * lt / LN2 + v / LN2
        return math.log2(J) - lb + golden(f1, -40, 0.0, 60)[1]
    best = (1e9, None)
    for k in range(1, R - a):
        t2 = k * math.log2(p) - den
        t1 = term1(a + k - 1)
        tot = max(t1, t2) + math.log2(1 + 2 ** (-abs(t1 - t2)))
        if tot < best[0]: best = (tot, k, t1, t2)
        if t1 > best[0] + 3: break
    return best

gb = open('../whitecount_2026-09-16/GB.txt').read()
print("J  N0  g   | log2|C_J| exact  cycle-lemma LB | exact log2 P(G_sh<gR) (DP) | rigorous log2 bound (k*) | rate DP  rate bound")
for J in (200, 400, 800, 1200):
    C = count_confined(J); lC = log2_int(C)
    sg = math.floor(J * AL); lcyc = lbinom2(sg - 1, J - 1) - math.log2(J)
    for N0 in (2, 4):
        m = re.search(rf"J={J} N0={N0} UMAX=30 SHAPE-ONLY[^\n]*\n[^\n]*P\(#good < 0\.1R\) = 2\^-([0-9.]+)", gb)
        ex = -float(m.group(1)) if m else float('nan')
        b = bound(J, N0, 0.1, lC)
        print(f"{J:5d} {N0} 0.1 | {lC:10.2f}  {lcyc:10.2f} | {ex:10.2f} | {b[0]:10.2f} (k={b[1]}) | {-ex / J:.4f}  {-b[0] / J:.4f}"
              + ("   OK" if b[0] >= ex else "   VIOLATION"), flush=True)
