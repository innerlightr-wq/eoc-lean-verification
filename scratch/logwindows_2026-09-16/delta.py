"""Per-(window, start-state) danger density delta_K (floats, discovery): fraction of pairs (disjoint window
start r0, state x at layer r0) whose K-window mass from x exceeds 2^{2K/10}; also the per-window sup fraction.
Environments: Haar-random 3-adic unit and lambda = 1 (t = j/6), j = 1600."""
import json, math, random, sys
from multiprocessing import Pool
sys.path.insert(0, '../pressure_exact_2026-09-16')
from pexact import Instance
from geo import apply, make_ops
KS = (2, 4, 6, 8, 10, 12, 16, 20, 24)
def run(spec):
    kind, j, K = spec
    if kind == 'haar':
        random.seed(4242); xi = random.randrange(1, 3 ** (j + 2)); xi += (xi % 3 == 0)
        I = Instance(j, j // 6, D=108, mode='3adic', xi=xi)
    else:
        I = Instance(j, j // 6, lam=1, D=108, mode='auto')
    p, q = make_ops(I)
    W = I.R // K; pairs = bad = 0; badwin = 0
    for i in range(W):
        r0, r1 = i * K, (i + 1) * K
        f = [1.0] * (I.top[2 * r1] - 2 * r1 + 1)
        for r in range(r1 - 1, r0 - 1, -1): f = apply(I, r, f, 3.0, p, q, 2 * r + 2)
        thr = 2 ** (2 * K / 10)
        nb = sum(1 for v in f if v > thr); pairs += len(f); bad += nb; badwin += nb > 0
    return {'kind': kind, 'j': j, 'K': K, 'delta': bad / pairs, 'pairs': pairs, 'win_frac': badwin / W}
if __name__ == '__main__':
    specs = [(k, 1600, K) for k in ('haar', 'lam1') for K in KS]
    with Pool(2) as p: res = p.map(run, specs)
    json.dump(res, open('delta.json', 'w'))
    for r in res:
        d = r['delta']
        print(f"{r['kind']:5s} K={r['K']:2d} delta={d:.3e} (-log3 delta = {(-math.log(d,3) if d>0 else float('inf')):.2f}) per-window sup fraction {r['win_frac']:.3f}")
