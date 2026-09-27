"""hweight tail (PROVED MATH skeleton, numeric constants): with sigma = b(j0) - x, B = b(N), N = j0 + L, K = b_U(j0)+1,
  r(x) = C(sigma-1, j0-1) C(B-sigma, L) / C(B-1, N-1) <= prod_{y<x} q0 (alpha L + y)/((alpha-1) L + y),  r(0) <= 1,
so  N sum_{x > xs} r(x) <= N r(xs+1)/(1-rho),  rho = q0 (alpha L + xs)/((alpha-1)L + xs).
htail needs  N sum r <= kappa 2^{K-B-1},  and  K - B - 1 >= -(alpha L + U + 2).  Take kappa = 1, U = 0.
Good pairs need hnum:  2t + log2(2(sigma+3)(sigma+t+1) L / eps^2) <= gamma j0  for all t <= alpha L + xs + 2.
Output: minimal xs/L, the implied j0 = L/lambda, and the exponent gain Delta E = I0 (A - 1/alpha) ~ (I0/alpha) L/j0."""
import math
AL = math.log2(3); q0 = 0.37; I0 = AL * (1 - 0.9499555)
def log_r(L, x):
    return sum(math.log(q0 * (AL * L + y) / ((AL - 1) * L + y)) for y in range(x))
def min_xs(L, lnN):
    x = 0; lr = math.log(q0 * (AL * L) / ((AL - 1) * L))   # log r(1)
    while True:
        rho = q0 * (AL * L + x) / ((AL - 1) * L + x)
        if rho < 1:
            lhs = lnN + lr - math.log(1 - rho)
            if lhs <= -(AL * L + 2) * math.log(2): return x
        x += 1
        lr += math.log(q0 * (AL * L + x) / ((AL - 1) * L + x))
for gamma in (8.6e-8, 2.5e-4):
    print(f"gamma = {gamma}")
    for L in (10, 100, 1000, 10000, 100000):
        # iterate: j0 determined by hnum at the largest t; lnN ~ ln j0
        j0 = 10 ** 9
        for _ in range(5):
            xs = min_xs(L, math.log(j0 + L))
            tmax = AL * L + xs + 2
            sig = AL * j0
            need = 2 * tmax + math.log2(2 * (sig + 3) * (sig + tmax + 1) * L)   # eps = 1
            j0 = need / gamma
        print(f"  L={L:6d} xs={xs:6d} xs/L={xs/L:.3f} j0={j0:.3e} L/j0={L/j0:.3e}  DeltaE={I0/AL*L/j0:.3e}  DeltaE/gamma={I0/AL*L/j0/gamma:.4f}")
