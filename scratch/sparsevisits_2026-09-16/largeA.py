"""A = 5, 7 logarithmic windows (floats, discovery): dangerous counts at theta_d = 1/10 and max window rate."""
import json, math, sys
from multiprocessing import Pool
sys.path.insert(0, '../pressure_exact_2026-09-16')
from pexact import Instance
from geo import apply, make_ops
def run(spec):
    j, t = spec
    I = Instance(j, t, lam=1, D=108, mode='auto'); p, q = make_ops(I); out = {'j': j, 't': t}
    for A in (5, 7):
        K = math.ceil(A * math.log2(j)); W = I.R // K; rates = []
        for i in range(W):
            r0, r1 = i * K, (i + 1) * K
            f = [1.0] * (I.top[2 * r1] - 2 * r1 + 1)
            for r in range(r1 - 1, r0 - 1, -1): f = apply(I, r, f, 3.0, p, q, 2 * r + 2)
            rates.append(math.log2(max(f)) / (2 * K))
        out[A] = {'K': K, 'W': W, 'max': round(max(rates), 4), 'bad': sum(v > 0.1 for v in rates),
                  'remainder_blocks': I.R - W * K}
    return out
if __name__ == '__main__':
    specs = [(j, t) for j in (400, 800, 1600, 3200) for t in (1, j // 6)]
    with Pool(6) as p:
        for r in p.imap(run, specs): print(json.dumps(r))
