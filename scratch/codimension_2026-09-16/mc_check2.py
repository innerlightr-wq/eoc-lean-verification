"""Targeted re-check: the (window, state) pairs with the largest 24-sample means, re-estimated with 720
independent Haar samples each (fresh seeds), with a standard error."""
import math, random, sys
from multiprocessing import Pool
sys.path.insert(0, '../pressure_exact_2026-09-16')
from pexact import Instance
from geo import apply, make_ops
from mc_check import sample, J, K
def sample_big(seed): return sample(10_000 + seed)
if __name__ == '__main__':
    with Pool(6) as pool: first = pool.map(sample, range(24))
    cand = []
    for r0 in first[0]:
        n = len(first[0][r0])
        for i in range(n):
            cand.append((sum(s[r0][i] for s in first) / 24, r0, i))
    cand.sort(reverse=True); top = cand[:5]
    with Pool(6) as pool: big = pool.map(sample_big, range(720))
    for m24, r0, i in top:
        vals = [s[r0][i] for s in big]
        mu = sum(vals) / len(vals); sd = math.sqrt(sum((v - mu) ** 2 for v in vals) / (len(vals) - 1))
        print(f"window r0={r0} state#{i}: 24-sample mean {m24:.4f} -> 720-sample mean {mu:.4f} +- {sd/math.sqrt(len(vals)):.4f} "
              f"(max sample {max(vals):.2f}); bound 1.3251")
    allmeans = []
    for r0 in big[0]:
        for i in range(len(big[0][r0])):
            allmeans.append(sum(s[r0][i] for s in big) / 720)
    print(f"720-sample means over all {len(allmeans)} (window,state) pairs: max {max(allmeans):.4f}, average {sum(allmeans)/len(allmeans):.4f}")
