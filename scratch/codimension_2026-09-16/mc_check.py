"""Sanity check (COMPUTATIONAL): Haar Monte Carlo of the K-window mass per start state versus the rigorous
moment bound E_xi[val(x0)] <= e^T M^K 1 (haar_bound.py, q = 37/100).  Uses the true d = 1/108 eligible-dark
predicate (3-adic form), which is dominated by the black model in the proof."""
import math, random, sys
from multiprocessing import Pool
sys.path.insert(0, '../pressure_exact_2026-09-16')
from pexact import Instance
from geo import apply, make_ops
J, K, NS = 400, 8, 24
def sample(seed):
    random.seed(seed); xi = random.randrange(1, 3 ** (J + 2)); xi += (xi % 3 == 0)
    I = Instance(J, J // 6, D=108, mode='3adic', xi=xi); p, q = make_ops(I)
    out = {}
    for r0 in range(20, I.R - K, 17):
        f = [1.0] * (I.top[2 * (r0 + K)] - 2 * (r0 + K) + 1)
        for r in range(r0 + K - 1, r0 - 1, -1): f = apply(I, r, f, 3.0, p, q, 2 * r + 2)
        out[r0] = f
    return out
if __name__ == '__main__':
    with Pool(6) as pool: res = pool.map(sample, range(NS))
    worst_mean = 0; avg = []
    for r0 in res[0]:
        n = len(res[0][r0])
        means = [sum(s[r0][i] for s in res) / NS for i in range(n)]
        worst_mean = max(worst_mean, max(means)); avg.append(sum(means) / n)
    print(f"J={J} K={K}: Haar mean window mass per state: max over (window,state) {worst_mean:.4f}, "
          f"average {sum(avg)/len(avg):.4f};  rigorous bound e^T M^K 1 = 1.3251 (q=37/100)")
