"""Is triangle-size information enough to control N_odd?  Greedy adversarial 3-adic environment.

Environment: y(a,b) = centered(xi 2^{-a} mod 3^b), black iff 54|y| < 3^b (three zero leading balanced-ternary
digits).  Every deterministic lemma of TriangleArray / TriangleHop holds for EVERY 3-adic unit xi; the true
environment is xi = 1.  We build xi digit by digit (row b fixes digit b-1) to maximise, against the path-marginal
of the confined law pi_i (environment independent), the objective
   [b even] * sum_S pi_{b-1}(S) 1{black(m-S, b)}              (odd-cell black mass of row b)
   + LA * sum_S pi_b(S) 1{|U(m-S,b)| < 3 eta} + LA^2 * sum_S pi_{b+1}(S) 1{|U(m-S,b)| < 9 eta}   (lookahead)
subject (cap mode) to: every support cell of row b has depth ln(eta/|U|) <= KCAP (if possible).
Depth of a black cell <= size of its triangle; the triangle apex is the deepest cell.
Writes xi mod 3^(J+2) to ADV_xi_J_KCAP.txt for exact evaluation with odd_dp.py env=file:...
usage: python3 adversary.py J KCAP [LA]"""
import math, sys

AL = math.log2(3)
J = int(sys.argv[1]); KCAP = float(sys.argv[2]); LA = float(sys.argv[3]) if len(sys.argv) > 3 else 0.5
R = J // 2; sg = math.floor(J * AL); t = J // 6; m = sg + t + 1
top = [min(math.floor(i * AL), sg) for i in range(J + 1)]
eta = 1 / 54
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
Z = F[J][sg]; sh = Z.bit_length() - 60
pi = []
for i in range(J + 1):
    d = {S: (F[i][S] * G[i][S] >> sh) / (Z >> sh) for S in F[i] if S in G[i]}
    pi.append({S: v for S, v in d.items() if v > 1e-15})

xi = 0; maxdepth = 0.0; Nodd = 0.0; Nall = 0.0
for b in range(1, J + 1):
    qb = 3 ** b; half = qb // 2
    cols = sorted(set(pi[b - 1]) | set(pi[b]) | (set(pi[b + 1]) if b + 1 <= J else set()))
    lo = cols[0]
    base = xi * pow(2, -(m - lo), qb) % qb; unit = 3 ** (b - 1) * pow(2, -(m - lo), qb) % qb
    W = {}; C = {}
    for S in range(lo, cols[-1] + 1):
        W[S] = base; C[S] = unit
        base = base * 2 % qb; unit = unit * 2 % qb
    best = None
    for e in ((1, 2) if b == 1 else (0, 1, 2)):
        obj = 0.0; dep = 0.0; blackm = 0.0
        for S in cols:
            v = (W[S] + e * C[S]) % qb
            y = v if v <= half else v - qb
            u = abs(y) / qb
            if S in pi[b - 1]:
                if u < eta:
                    dep = max(dep, math.log(eta / u) if u > 0 else 1e9)
                    blackm += pi[b - 1][S]
            if S in pi[b] and u < 3 * eta: obj += LA * pi[b][S]
            if b + 1 <= J and S in pi[b + 1] and u < 9 * eta: obj += LA * LA * pi[b + 1][S]
        obj += blackm if b % 2 == 0 else 0.0
        ok = dep <= KCAP
        key = (ok, obj if ok else -dep)
        if best is None or key > best[0]: best = (key, e, dep, blackm)
    _, e, dep, blackm = best
    xi = xi + e * 3 ** (b - 1)
    maxdepth = max(maxdepth, dep); Nall += blackm
    if b % 2 == 0: Nodd += blackm
open(f"ADV_xi_{J}_{KCAP:g}.txt", "w").write(str(xi) + "\n")
print(f"J={J} KCAP={KCAP} LA={LA}: greedy environment: E[N_odd]/R = {Nodd / R:.4f}, E[N_black all cells]/J = {Nall / J:.4f}, "
      f"max depth of a black support cell = {maxdepth:.2f}")
