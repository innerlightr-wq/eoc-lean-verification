"""Many-shift scan (floats, discovery): lambda = 1, K = ceil(A log2 j) with A = 2 (A = 5 on a subset),
dangerous threshold 1/10, geometric window sup-norm from block 0.  For each shift t: dangerous count / W,
max window rate, longest run of consecutive dangerous windows.  Haar-random 3-adic environments for comparison.
Writes one JSON line per environment to shifts.jsonl."""
import json, math, random, sys
from multiprocessing import Pool
sys.path.insert(0, '../pressure_exact_2026-09-16')
from pexact import Instance
from geo import apply, make_ops
def run(spec):
    j, t, kind, A, seed = spec
    if kind == 'haar':
        random.seed(seed); xi = random.randrange(1, 3 ** (j + 2)); xi += (xi % 3 == 0)
        I = Instance(j, t, D=108, mode='3adic', xi=xi)
    else:
        I = Instance(j, t, lam=1, D=108, mode='auto')
    p, q = make_ops(I)
    K = math.ceil(A * math.log2(j)); W = I.R // K; rates = []
    for i in range(W):
        r0, r1 = i * K, (i + 1) * K
        f = [1.0] * (I.top[2 * r1] - 2 * r1 + 1)
        for r in range(r1 - 1, r0 - 1, -1): f = apply(I, r, f, 3.0, p, q, 2 * r + 2)
        rates.append(math.log2(max(f)) / (2 * K))
    bad = [v > 0.1 for v in rates]; run_ = best = 0
    for x in bad:
        run_ = run_ + 1 if x else 0; best = max(best, run_)
    return {'j': j, 't': t, 'kind': kind, 'A': A, 'K': K, 'W': W, 'bad': sum(bad), 'frac': sum(bad) / W,
            'max_rate': max(rates), 'mean_rate': sum(rates) / W, 'max_run': best, 'rates': [round(v, 4) for v in rates]}
if __name__ == '__main__':
    specs = []
    for j, nt in ((400, 600), (800, 300), (1600, 120)):
        base = j // 6
        specs += [(j, base + k, 'lam1', 2, 0) for k in range(nt // 2)]            # consecutive block
        rng = random.Random(j)
        specs += [(j, rng.randrange(1, 50 * j), 'lam1', 2, 0) for _ in range(nt // 2)]   # scattered
        specs += [(j, base, 'haar', 2, 1000 + s) for s in range(nt // 6)]
    specs += [(800, 133 + k, 'lam1', 5, 0) for k in range(40)]
    with Pool(6) as pool, open('shifts.jsonl', 'w') as fh:
        for r in pool.imap_unordered(run, specs, chunksize=2):
            fh.write(json.dumps(r) + '\n'); fh.flush()
