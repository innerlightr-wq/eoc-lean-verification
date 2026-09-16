"""Exact corpus scan of the Lean odd-dark pressure over the true low-frequency family.
For each (j, t, odd lam): exact P = (1/j) log2(sum_P 3^{N_odd} / |P|) at d = 1/108 and d = 1/54,
certified comparisons with 17/100 and 1/6 (exact integers), and window maxima of the exact
telescoping block weights (floats) for K = 16, 24, 32, 64, 128 (rate per step = sum w / (2K)).
usage: python3 corpus.py J LAMMAX T1,T2,...  -> corpus_J.json"""
import json, sys
from multiprocessing import Pool
from pexact import Instance, log2ratio, below

KS = (16, 24, 32, 64, 128)

def job(args):
    j, t, lam = args
    out = {'j': j, 't': t, 'lam': lam}
    for D in (108, 54):
        I = Instance(j, t, lam=lam, D=D, mode='auto', obs='odd')
        Z3, Z1 = I.moment(3), I.moment(1)
        rec = {'P': log2ratio(Z3, Z1) / j, 'lt017': below(Z3, Z1, j, 17, 100), 'lt16': below(Z3, Z1, j, 1, 6)}
        if D == 108:
            w, _ = I.blocks(3)
            win = {}
            for K in KS:
                if K <= len(w):
                    best, arg, acc = -1.0, 0, sum(w[:K])
                    for a in range(len(w) - K + 1):
                        if a:
                            acc += w[a + K - 1] - w[a - 1]
                        if acc > best:
                            best, arg = acc, a
                    win[K] = (best / (2 * K), arg)
            rec['win'] = win
        out[D] = rec
    return out

if __name__ == '__main__':
    j = int(sys.argv[1]); lammax = int(sys.argv[2]); ts = [int(x) for x in sys.argv[3].split(',')]
    tasks = [(j, t, lam) for t in ts for lam in range(1, lammax + 1, 2)]
    with Pool() as p:
        res = p.map(job, tasks, chunksize=1)
    json.dump(res, open(f'corpus_{j}.json', 'w'))
    print(j, len(res), 'done')
