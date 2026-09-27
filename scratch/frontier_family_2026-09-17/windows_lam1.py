"""Stage Two, lambda = 1, u = 0 (true Lean environments, exact Lean dark predicate via pexact 'auto' mode).
For disjoint K-windows i (rows iK..(i+1)K-1): per-state window mass val(x) (geometric kernel, s = 3, d = 1/108);
window rate = log2 max_x val(x) / (2K); dangerous iff some val(x) > 2^{2K/10}.
Records: danger flags, dangerous start states x0 and exponents a = m - x0, window depth B = 2(i+1)K."""
import json, math, sys
sys.path.insert(0, '../pressure_exact_2026-09-16')
from pexact import Instance
from geo import apply, make_ops
from multiprocessing import Pool
def run(spec):
    j, t, K = spec
    I = Instance(j, t, lam=1, D=108, mode='auto')
    p, q = make_ops(I)
    W = I.R // K; thr = 2 ** (2 * K / 10)
    wins = []
    for i in range(W):
        r0, r1 = i * K, (i + 1) * K
        f = [1.0] * (I.top[2 * r1] - 2 * r1 + 1)
        for r in range(r1 - 1, r0 - 1, -1):
            f = apply(I, r, f, 3.0, p, q, 2 * r + 2)
        lo = 2 * r0
        mx = max(f)
        bad = [lo + k for k, v in enumerate(f) if v > thr]
        wins.append({'i': i, 'rate': math.log2(mx) / (2 * K) if mx > 0 else -9, 'bad_states': bad[:50], 'nbad': len(bad),
                     'nstates': len(f)})
    return {'j': j, 't': t, 'K': K, 'm': I.m, 'W': W, 'wins': wins}
if __name__ == '__main__':
    specs = [(j, t, K) for j in (1600, 3200) for t in (1, 7, j // 6) for K in (3, 4, 6, 8, 12)]
    out = []
    with Pool(7) as pool:
        for res in pool.imap_unordered(run, specs):
            out.append(res)
            nb = sum(1 for w in res['wins'] if w['nbad'] > 0)
            print(f"j={res['j']} t={res['t']} K={res['K']} W={res['W']} dangerous={nb} frac={nb/res['W']:.3f} maxrate={max(w['rate'] for w in res['wins']):.4f}", flush=True)
    json.dump(out, open('windows_lam1.json', 'w'))
