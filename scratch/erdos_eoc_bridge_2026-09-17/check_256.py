"""Independent brute-force check of dim C(1, 2^a): count x in {0,1}^D (as x = sum d_i 3^i) such that the
low D ternary digits of M*x all lie in {0,1}.  These digits depend only on x mod 3^D.
Growth rate log3(N_D)/D -> dim_H C(1,M) (prefix counts of a right-resolving presentation;
dead-end prefixes change N_D by at most a polynomial factor)."""
import math, sys
from automata import build_stationary, count_words, spectral_radius
def digits_ok(v, D):
    for _ in range(D):
        if v % 3 == 2: return False
        v //= 3
    return True
def brute(M, D):
    # extend prefixes digit by digit (exact, no automaton)
    pref = [0]
    counts = []
    for n in range(D):
        new = []
        mod = 3 ** (n + 1)
        for x in pref:
            for d in (0, 1):
                y = x + d * 3 ** n
                if (M * y % mod) // 3 ** n != 2:   # digit n of M*y (depends only on y mod 3^{n+1})
                    new.append(y)
        pref = new
        counts.append(len(pref))
    return counts
for a in (6, 8, 10, 12):
    M = 2 ** a
    c = brute(M, 40)
    order, edges = build_stationary([M])
    rho = spectral_radius(order, edges)
    auto = [count_words(order, edges, D) for D in (20, 30, 40)]
    print(f"M=2^{a}: brute N_20,N_30,N_40 = {c[19]},{c[29]},{c[39]}  automaton = {auto}  "
          f"ratio N_40/N_30 per digit = {(c[39]/c[29])**0.1:.6f}  rho = {rho:.6f}  dim(rho) = {math.log(rho,3):.6f}")
