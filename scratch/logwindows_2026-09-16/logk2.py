"""Logarithmic-K dangerous-window scan (floats; discovery only, not certification).
Geometric normalisation, s = 3, d = 1/108, exact Lean dark predicate (pexact 'auto' / '3adic' for Haar).
For each environment and each A in AS: K = ceil(A log2 j), W = floor(R/K) disjoint windows from block 0,
window rate = log2 max_x (Lt_{r0..r0+K-1} 1)(x) / (2K); dangerous at theta_d if rate > theta_d.
Results are appended one JSON object per line to logk2.jsonl as each environment finishes."""
import json, math, random, sys, time
from multiprocessing import Pool
sys.path.insert(0, '../pressure_exact_2026-09-16')
from pexact import Instance
from geo import apply, make_ops

AS = (1, 2, 3, 4, 6, 8)
THD = (0.08, 0.10, 0.12)

def run(spec):
    j, t, kind, val = spec
    t0 = time.time()
    I = Instance(j, t, lam=val, D=108, mode='auto') if kind == 'true' else Instance(j, t, D=108, mode='3adic', xi=val)
    p, q = make_ops(I)
    out = {'j': j, 't': t, 'kind': kind, 'lam': val if kind == 'true' else 'haar', 'setup_s': round(time.time() - t0, 1), 'A': {}}
    for A in AS:
        K = math.ceil(A * math.log2(j)); W = I.R // K
        if W < 2:
            continue
        rates = []
        for i in range(W):
            r0, r1 = i * K, (i + 1) * K
            f = [1.0] * (I.top[2 * r1] - 2 * r1 + 1)
            for r in range(r1 - 1, r0 - 1, -1):
                f = apply(I, r, f, 3.0, p, q, 2 * r + 2)
            rates.append(math.log2(max(f)) / (2 * K))
        out['A'][A] = {'K': K, 'W': W, 'max': max(rates), 'mean': sum(rates) / W,
                       'frac': {str(th): sum(1 for v in rates if v > th) / W for th in THD},
                       'count': {str(th): sum(1 for v in rates if v > th) for th in THD}}
    out['total_s'] = round(time.time() - t0, 1)
    return out

if __name__ == '__main__':
    specs = []
    for j in (400, 800, 1600, 3200):
        for t in (1, 7, j // 6, j, 5 * j):
            specs.append((j, t, 'true', 1))
        for lam in (3, 17):
            specs.append((j, j // 6, 'true', lam))
        random.seed(99 + j)
        xi = random.randrange(1, 3 ** (j + 2)); xi += (xi % 3 == 0)
        specs.append((j, j // 6, 'haar', xi))
    for t in (1, 6400 // 6, 6400):
        specs.append((6400, t, 'true', 1))
    random.seed(99 + 6400)
    xi = random.randrange(1, 3 ** 6402); xi += (xi % 3 == 0)
    specs.append((6400, 6400 // 6, 'haar', xi))
    open('logk2.jsonl', 'w').close()
    with Pool(6) as pool:
        for res in pool.imap_unordered(run, specs):
            with open('logk2.jsonl', 'a') as fh:
                fh.write(json.dumps(res) + '\n')
    print('done', len(specs))
