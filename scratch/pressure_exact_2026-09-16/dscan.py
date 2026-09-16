"""Exact Lean odd-dark pressure (s = 3) as a function of the dark threshold d = 1/D (even D)."""
import sys, json
from multiprocessing import Pool
from pexact import Instance, log2ratio, below
DS = (108, 54, 36, 24, 16, 12, 8, 6, 4)
def job(a):
    j, t, lam, D = a
    I = Instance(j, t, lam=lam, D=D, mode='auto'); Z3, Z1 = I.moment(3), I.moment(1)
    return (j, t, lam, D, log2ratio(Z3, Z1) / j, below(Z3, Z1, j, 17, 100))
if __name__ == '__main__':
    j = int(sys.argv[1])
    tasks = [(j, t, lam, D) for D in DS for t in (0, 3, j // 6, j, 1000003) for lam in range(1, 64, 2)]
    with Pool(4) as p: res = p.map(job, tasks)
    json.dump(res, open(f'dscan_{j}.json', 'w'))
    for D in DS:
        v = [r for r in res if r[3] == D]
        mx = max(v, key=lambda r: r[4])
        print(f"d=1/{D:<4} max P {mx[4]:.4f} (lam={mx[2]}, t={mx[1]})  mean {sum(r[4] for r in v)/len(v):.4f}  certified<0.17 {sum(r[5] for r in v)}/{len(v)}")
