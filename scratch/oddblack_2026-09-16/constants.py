"""Constants for the odd-black reduction.
(A) Generic-environment annealed pressure (PROVED MATH): for Haar xi and ANY fixed path,
    E_xi[s^{N_odd}] <= C rho(s)^R, rho(s) = spectral radius of the worst-alignment 2-state operator (see REPORT §4).
    Validated by Monte Carlo over xi for sampled confined paths.
(B) Improved reduction (PROVED MATH):  P(G_true < gR) <= P(G_sh < (g+beta)R) + E_conf[s^{N_odd}] ((1+s)/2)^{-beta R}.
    Rate (bits/step) = min( c_sh(g+beta), beta log2((1+s)/2)/2 - P_odd(s) ),  P_odd(s) = (1/J) log2 E_conf s^{N_odd}.
    c_sh = rigorous shape rate (pressure round), P_odd from exact J=1200 true environment (COMPUTATIONAL input) or from
    the generic bound log2 rho(s)/2 + eps (PROVED for all xi outside Haar measure 2^{-eps J}).
usage: python3 constants.py"""
import math, random, sys
sys.path.insert(0, '../pressure_2026-09-16')
from shape_ld import rate_pair, AL, LN2

def rho(s, it=4000):
    # states x in {0,1}: x = first-digit condition of the current cell holds.  Max over alignments C/D per step.
    h0, h1 = 1.0, 1.0; lam = 1.0
    for _ in range(it):
        n0 = h1 / 3 + 2 * h0 / 3
        c = (s / 9 + 2 / 9) * h1 + (6 / 9) * h0          # alignment coincide
        d = (3 / 9) * h1 + ((s + 5) / 9) * h0            # alignment differ
        n1 = max(c, d)
        lam = max(n0, n1); h0, h1 = n0 / lam, n1 / lam
    return lam

def c_sh(gp, N0=4):
    pg = sum((u - 1) * (1 / AL) ** 2 * (1 - 1 / AL) ** (u - 2) for u in range(3, N0 + 2))
    if gp >= pg - 0.011: return 0.0
    return max(min(rate_pair(gp + e, N0)[0] / (2 * LN2), e * math.log2(AL) / 2)
               for e in [i / 200 for i in range(1, int(200 * (pg - gp)))])

S_GRID = (1.25, 1.5, 2.0, 2.5, 3.0, 4.0, 6.0)
P_TRUE_1200 = {1.25: 0.00645, 1.5: 0.01278, 2.0: 0.02500, 2.5: 0.03665, 3.0: 0.04796, 4.0: 0.07072, 6.0: 0.11125}
P_TRUE_800 = {1.25: 0.00542, 1.5: 0.01082, 2.0: 0.02146, 2.5: 0.03177, 3.0: 0.04165, 4.0: 0.05999, 6.0: 0.09149}

if __name__ == "__main__":
    print("(A) generic annealed pressure per step (bits) log2 rho(s)/2  vs independent Bernoulli(1/27) and true J=1200:")
    for s in S_GRID:
        print(f"   s={s}: generic {math.log2(rho(s)) / 2:.5f}   Bernoulli(1/27) {math.log2(1 + (s - 1) / 27) / 2:.5f}   "
              f"true(1200) {P_TRUE_1200[s]:.5f}")
    for q in (0.05, 0.06, 0.075, 0.10):
        r = max(q * math.log2(s) / 2 - math.log2(rho(s)) / 2 for s in [1 + i / 20 for i in range(1, 200)])
        print(f"   generic annealed P(N_odd >= {q} R) rate: {r:.4f} bits/step")
    # Monte Carlo validation of (A): fixed confined path, random xi
    random.seed(5); J = 80; R = J // 2; sg = math.floor(J * AL); t = J // 6; m = sg + t + 1
    top = [min(math.floor(i * AL), sg) for i in range(J + 1)]
    # sample a confined path by rejection from the uniform law on compositions (small J)
    def path():
        while True:
            cuts = sorted(random.sample(range(1, sg), J - 1)); S = [0] + cuts + [sg]
            if all(S[i] <= top[i] for i in range(J + 1)): return S
    for trial in range(3):
        S = path(); cells = [(m - S[2 * r + 1], 2 * r + 2) for r in range(R)]
        n = 20000; acc = {s: 0.0 for s in (2.0, 3.0, 6.0)}
        for _ in range(n):
            xi = random.randrange(1, 3 ** (J + 2))
            while xi % 3 == 0: xi = random.randrange(1, 3 ** (J + 2))
            N = 0
            for a, b in cells:
                qb = 3 ** b; v = xi * pow(2, -a, qb) % qb; y = v if v <= qb // 2 else v - qb
                N += 54 * abs(y) < qb
            for s in acc: acc[s] += s ** N
        C = {x: 3 * rho(x) - 2 for x in (2.0, 3.0, 6.0)}   # eigenvector ratio h1/h0 = 3 rho - 2
        print(f"   MC path {trial}: " + "  ".join(f"s={s}: (1/R)ln E_xi s^N = {math.log(acc[s] / n) / R:.4f} <= ln rho + ln(C)/R = {math.log(rho(s)) + math.log(C[s]) / R:.4f}"
                                             for s in acc))
    print("(B) optimized reduction, N0 = 4, g = 0.1 (bits/step):")
    for label, P in (("true env J=1200 pressure (COMPUTATIONAL input)", P_TRUE_1200),
                     ("true env J=800 pressure (COMPUTATIONAL input)", P_TRUE_800),
                     ("generic xi (PROVED; exceptional Haar measure 2^{-eps J}, eps = rate)", None)):
        best = (-1, None)
        for beta in [i / 100 for i in range(2, 44)]:
            cs = c_sh(0.1 + beta)
            for s in S_GRID:
                if P is not None:
                    r2 = beta * math.log2((1 + s) / 2) / 2 - P[s]
                    tot = min(cs, r2)
                else:
                    r2 = beta * math.log2((1 + s) / 2) / 2 - math.log2(rho(s)) / 2
                    tot = min(cs, r2 / 2)            # split: eps = r2/2 for the exceptional set, r2/2 for the bound
                if tot > best[0]: best = (tot, (beta, s, cs, r2))
        b, s, cs, r2 = best[1]
        print(f"   {label}: rate {best[0]:.4f} at beta = {b}, s = {s} (shape rate {cs:.4f}, black-term rate {r2:.4f})")
    print("   Hoeffding form needs P(N_odd >= beta R/4): with beta = 0.3 -> threshold 0.075 R (the original target).")
