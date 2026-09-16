"""Route A / B measurements in the geometric normalisation (s = 3, d = 1/108 unless stated).
For each environment:
  P      exact count pressure (1/j) log2 E_conf[3^N]
  G      (1/j) log2 e_0^T Lt_0..Lt_{R-1} 1   (unpinned geometric exponent)
  cert1  (1/j) sum_r log2 max_x (Lt_r 1)(x)        (Level-1 certificate h = 1)
  certK  min over offsets of (1/j)[sum over K-windows log2 ||Lt_w||_inf + remainder log2 3^K]  (Level-4, h = 1)
  window rates (1/2K) log2 ||Lt_w||_inf over all starts: max, median, fraction above theta_d
"""
import json, math, random, sys
from multiprocessing import Pool
from pexact import Instance, log2ratio, barrier
from geo import global_geo, one_block_cert, window_norms

KS = (1, 2, 4, 8, 16, 32)
THD = (0.05, 0.08, 0.10, 0.12, 1 / 6)

def run(spec):
    j, t, kind, val = spec
    if kind == 'true':
        I = Instance(j, t, lam=val, D=108, mode='auto')
    else:
        I = Instance(j, t, D=108, mode='3adic', xi=val)
    Z3, Z1 = I.moment(3), I.moment(1)
    out = {'j': j, 't': t, 'kind': kind, 'lam': val if kind == 'true' else None,
           'P': log2ratio(Z3, Z1) / j, 'G': global_geo(I, 3.0, pinned=False) / j,
           'cert1': one_block_cert(I) / j}
    certK = {}; rates = {}
    for K in KS:
        wn = window_norms(I, K)
        best = min(sum(wn[o + i * K] for i in range((I.R - o) // K)) + (o + (I.R - o) % K) * math.log2(3)
                   for o in range(K))
        certK[K] = best / j
        rr = sorted(v / (2 * K) for v in wn)
        rates[K] = {'max': rr[-1], 'median': rr[len(rr) // 2],
                    'frac': {f"{th:.4f}": sum(1 for v in rr if v > th) / len(rr) for th in THD}}
    out['certK'] = certK; out['rates'] = rates
    return out

if __name__ == '__main__':
    specs = []
    for j in (400, 800):
        for lam in (1, 3, 5, 17):
            for t in (1, 7, j // 6, j, 5 * j):
                specs.append((j, t, 'true', lam))
        random.seed(20260916 + j)
        for k in range(4):
            xi = random.randrange(1, 3 ** (j + 2))
            while xi % 3 == 0: xi += 1
            specs.append((j, j // 6, 'haar', xi))
        sg = barrier(j); m = sg + 1 + j // 6
        specs.append((j, j // 6, 'xi=2^m', pow(2, m, 3 ** (j + 2))))
    with Pool(7) as pool:
        res = pool.map(run, specs, chunksize=1)
    json.dump(res, open('geo_scan.json', 'w'))
    for r in res:
        lab = f"j={r['j']} t={r['t']:>4} {r['kind']:6s} {'' if r['lam'] is None else 'lam='+str(r['lam'])}"
        print(f"{lab:32s} P={r['P']:.4f} G={r['G']:.4f} cert1={r['cert1']:.4f} "
              + " ".join(f"cert{K}={r['certK'][K]:.3f}" for K in KS)
              + " | winmax " + " ".join(f"{K}:{r['rates'][K]['max']:.3f}" for K in (8, 16, 32))
              + " | frac>0.10 " + " ".join(f"{K}:{r['rates'][K]['frac']['0.1000']:.2f}" for K in (8, 16, 32)))
