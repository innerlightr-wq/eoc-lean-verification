"""Part XIV: structure of upper-exit record holders vs ordinary anchors; plus exact uniform sampling of
U-confined words to test whether Curry-type dips are typical along the path (not just at the end)."""
import random, re
from math import log2, floor
ALPHA = log2(3)
rng = random.Random(11)
def v2(n): return (n & -n).bit_length() - 1
def profile(mu, U):
    m, S, n = mu, 0, 0
    ds, Rs, mmin = [], [], mu
    while True:
        x = 3 * m + 1; d = v2(x); m = x >> d; S += d; n += 1
        ds.append(d); R = S - n * ALPHA; Rs.append(R); mmin = min(mmin, m)
        if S - U > 0 and (1 << (S - U)) > 3 ** n: break
    ex = n
    while m != 1: m, d = (3 * m + 1) >> v2(3 * m + 1), 0; n += 1
    runs, cur = [], 0
    for d in ds:
        if d == 1: cur += 1
        else: runs.append(cur); cur = 0
    runs.append(cur)
    return dict(mu=mu, exit=ex, ratio=ex / log2(mu), ones=ds.count(1) / len(ds), dmax=max(ds),
                ge4=sum(d >= 4 for d in ds) / len(ds), run=max(runs), Rmin=min(Rs), argmin=Rs.index(min(Rs)) + 1,
                Rmax=max(Rs[:-1]) if len(Rs) > 1 else Rs[0], shrink=log2(mmin / mu),
                trail1=v2(mu + 1), h_after=n - ex, prefix=ds[:30])
txt = open("upper_exit_records_2p32.out").read()
for U in (0, 2):
    recs = [int(a) for a, b in re.findall(r"(\d+):(\d+)", re.search(rf"EXIT_RECORDS U={U}:(.*)", txt).group(1))]
    recs = [r for r in recs if r >= 1000]
    print(f"== U={U}: exit-time record holders (mu >= 1000) ==")
    print("   mu          exit ratio  %1s  dmax %>=4 run  Rmin(at)      Rmax  log2(min m/mu) trailing1s  steps-to-1-after")
    P = [profile(r, U) for r in recs]
    for p in P:
        print(f"   {p['mu']:<11d} {p['exit']:4d} {p['ratio']:5.2f} {p['ones']:.2f} {p['dmax']:4d} {p['ge4']:.3f} {p['run']:3d} "
              f"{p['Rmin']:7.2f}({p['argmin']:3d}) {p['Rmax']:5.2f} {p['shrink']:8.2f} {p['trail1']:6d} {p['h_after']:8d}")
    print("   prefix of the largest record:", P[-1]["prefix"])
    # comparison groups at matched sizes: ordinary odd seeds, and seeds with long exits (>= 100)
    ordin, longx = [], []
    while len(ordin) < 3000 or len(longx) < 200:
        mu = rng.getrandbits(32) | 1 | (1 << 31)
        p = profile(mu, U)
        if len(ordin) < 3000: ordin.append(p)
        if p["exit"] >= 100 and len(longx) < 200: longx.append(p)
    for name, grp in (("record holders", P), ("ordinary 32-bit", ordin), ("32-bit with exit>=100", longx)):
        k = len(grp)
        avg = lambda key: sum(g[key] for g in grp) / k
        print(f"   {name:24s} n={k:5d}: frac(d=1) {avg('ones'):.3f}, frac(d>=4) {avg('ge4'):.3f}, "
              f"longest 1-run {avg('run'):5.1f}, Rmin {avg('Rmin'):7.2f}, trailing 1s of mu {avg('trail1'):5.2f}, "
              f"exit {avg('exit'):6.1f}")
print("\n== exact uniform sampling of 0-confined words of length N (backward-count DP) ==")
def sample_confined(U, N, nsamp):
    import bisect
    # back[r][S] = number of confined completions from state (r, S) to length N
    smax = [floor(U + r * ALPHA) for r in range(N + 1)]
    for r in range(N + 1):
        while smax[r] - U >= 0 and (1 << (smax[r] - U)) > 3 ** r: smax[r] -= 1
    back = [None] * (N + 1)
    back[N] = {S: 1 for S in range(N, smax[N] + 1)}
    for r in range(N - 1, -1, -1):
        nxt = back[r + 1]; keys = sorted(nxt, reverse=True)
        cur = {}; acc = 0; idx = 0
        for S in range(smax[r], r - 1, -1):
            while idx < len(keys) and keys[idx] > S:
                acc += nxt[keys[idx]]; idx += 1
            if acc: cur[S] = acc
        back[r] = cur
    out = []
    for _ in range(nsamp):
        S, path = 0, []
        for r in range(N):
            nxt = back[r + 1]; tot = back[r][S]
            x = rng.randrange(tot); d = 1
            while True:
                c = nxt.get(S + d, 0)
                if x < c: break
                x -= c; d += 1
            S += d; path.append(S - (r + 1) * ALPHA)
        out.append(path)
    return out
for N in (200, 400):
    paths = sample_confined(0, N, 400)
    mid = [p[N // 2 - 1] for p in paths]
    dip = sum(any(p[n] <= -1.036 * log2(n + 2) for n in range(N // 4, 3 * N // 4)) for p in paths) / len(paths)
    occ = [sum(1 for R in p if R >= -5) for p in paths]
    print(f"   N={N}: mean R at N/2 = {sum(mid)/len(mid):6.2f} (sqrt(N) = {N**0.5:.1f}); P(dip below -1.036 log2 n "
          f"somewhere in [N/4,3N/4]) = {dip:.3f}; mean #{{n: R_n >= -5}} = {sum(occ)/len(occ):.1f} of {N}")
