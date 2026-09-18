"""Exact integer certification of logarithmic windows, K = ceil(2 log2 j), dangerous threshold 1/10.
Window mass from state x (geometric weight p = (j-1)/(sigma-1), q = (sigma-j)/(sigma-1), s = 3, d = 1/108):
  val(x) = G_{r0}(x) / D^{T-x},  D = sigma - 1,  T = top(2 r1),  G_{r1}(y) = D^{T-y},
  G_r(x) = sum_y (j-1)^2 Q^{y-x-2} W_r(x,y) G_{r+1}(y),  Q = sigma - j          (exact integers)
Safe (certified) iff for every state x:  val(x) <= 2^{2K/10}  <=>  G(x)^5 <= 2^K * D^{5(T-x)}.
This is exactly the per-window hypothesis of DangerousWindows.summedPressure_of_tenth_twoNinths
(LocalWindow.val of the geometric kernel from every state at start i*K)."""
import json, math, sys, time
from multiprocessing import Pool
sys.path.insert(0, '../pressure_exact_2026-09-16')
from pexact import Instance
from logk import apply_int

def certify(spec):
    j, t, lam = spec
    t0 = time.time()
    I = Instance(j, t, lam=lam, D=108, mode='auto')
    K = math.ceil(2 * math.log2(j)); W = I.R // K
    D = I.sg - 1
    unsafe = []; worst = -1e9
    for i in range(W):
        r0, r1 = i * K, (i + 1) * K
        T = I.top[2 * r1]
        G = [D ** (T - y) for y in range(2 * r1, T + 1)]
        for r in range(r1 - 1, r0 - 1, -1):
            G = apply_int(I, r, G, 2 * r + 2)
        lo = 2 * r0
        ok = True
        for k, g in enumerate(G):
            if g == 0: continue
            e = T - (lo + k)
            if g ** 5 > (D ** (5 * e)) << K:
                ok = False
            # exact-derived rate for reporting (log of exact integers)
            sh = max(0, g.bit_length() - 60)
            rate = ((math.log2(g >> sh) + sh) - e * math.log2(D)) / (2 * K)
            worst = max(worst, rate)
        if not ok: unsafe.append(i)
    return {'j': j, 't': t, 'lam': lam, 'K': K, 'W': W, 'certified_safe': W - len(unsafe),
            'unsafe': unsafe, 'worst_rate': worst, 'seconds': round(time.time() - t0, 1)}

if __name__ == '__main__':
    specs = []
    for j in (400, 800, 1600):
        for t in (1, 7, j // 6, j, 5 * j):
            specs.append((j, t, 1))
        specs.append((j, j // 6, 17))
    specs.append((3200, 3200 // 6, 1))
    open('certify.jsonl', 'w').close()
    with Pool(4) as pool:
        for res in pool.imap_unordered(certify, specs):
            with open('certify.jsonl', 'a') as fh: fh.write(json.dumps(res) + '\n')
    print('done', len(specs))
