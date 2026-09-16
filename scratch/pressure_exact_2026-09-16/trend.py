"""Fixed-K dangerous-window fraction versus j (sup-norm windows, geometric normalisation, s = 3, d = 1/108)."""
import json, sys
from multiprocessing import Pool
from pexact import Instance
from geo import window_norms
TH = (0.05, 0.08, 0.10, 0.12, 1 / 6)
def job(a):
    j, K, lam, t = a
    I = Instance(j, t, lam=lam, D=108, mode='auto')
    rr = [v / (2 * K) for v in window_norms(I, K)]
    return (j, K, lam, t, max(rr), {f"{th:.3f}": sum(1 for v in rr if v > th) / len(rr) for th in TH})
if __name__ == '__main__':
    tasks = [(j, K, lam, t) for j in (400, 800, 1600, 3200) for K in (8, 16) for (lam, t) in ((1, 7), (5, j // 6))
             if not (j == 3200 and K == 16)]
    with Pool(7) as p: res = p.map(job, tasks, chunksize=1)
    json.dump(res, open('trend.json', 'w'))
    for r in sorted(res): print(r)
