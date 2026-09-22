"""Empirical probe of G_max(H): the post-failure transport-budget gain binned by
pre-failure budget H.  Directly targets Open Problem 37 / Gate 10."""
import math, sys
sys.path.insert(0, 'scratch')
from transport_regeneration import v2, orbit

def scan(m0, N, pad=300):
    ds, ms = orbit(m0, N)
    S = [0]*(N+1)
    for j in range(1, N+1): S[j] = S[j-1] + ds[j]
    P = S[N] + pad; M2 = 1 << P
    inv3 = pow(3, -1, M2)
    C = 0; out = []
    Cs = [0]*(N+1)
    for j in range(N): Cs[j+1] = 3*Cs[j] + (1 << S[j])
    prev = None
    inv3p = [pow(inv3, k, M2) for k in range(N+2)]
    for j in range(1, N):
        Sj = S[j]; dn = ds[j+1]
        xi = (-Cs[j] * inv3p[j]) % M2
        chi = xi % (1 << Sj); T = xi >> Sj; Tprec = P - Sj
        A = 0; D = 0
        for rr in range(0, N-j):
            A = (A + (1 << D) * inv3p[j+1+rr]) % M2
            D += ds[j+1+rr]
            if D >= Tprec: break
        lim = min(Tprec, D)
        X = (T - A) % (1 << lim); Mj = v2(X)
        if Mj is None or Mj >= lim: continue
        F = Sj - math.log2(chi); H = F + Mj
        K = (T - inv3p[j+1]) % (1 << dn)
        if K == 0: continue
        if v2(K) != Mj: continue          # restrict to genuine FIRST failures (Prop 20)
        a = (T - A) >> Mj; u = K >> Mj
        au = v2((a - u) % (1 << (lim - Mj)))
        if au is None or au >= lim - Mj - 2: continue
        delta = math.log2(1 + (2.0**min(F + Mj, 900)) * u) if F+Mj < 900 else None
        G = au - (F + Mj + math.log2(u)) if u > 0 else None
        # exact delta via logs:  delta = log2(1 + 2^F * K)
        ld = math.log2(1 + 2.0**min(F, 900) * K) if F < 900 else None
        if ld is None: continue
        out.append((H, au - ld))
    return out

seeds = [m for m in range(3, 60001, 2)]
pairs = []
for m0 in seeds:
    try: pairs += scan(m0, 55)
    except Exception: pass
print(f"first-failure events: {len(pairs)}")
bins = {}
for H, G in pairs:
    b = int(H)
    if b not in bins: bins[b] = [0, -1e9, 0]
    bins[b][0] += 1
    bins[b][1] = max(bins[b][1], G)
    if G > 0: bins[b][2] += 1
print(f"{'H bin':>6} {'events':>8} {'G>0':>7} {'max G':>9}")
for b in sorted(bins):
    n, mx, npos = bins[b]
    if n >= 3: print(f"{b:>6} {n:>8} {npos:>7} {mx:>9.3f}")
pos = [(H,G) for H,G in pairs if G > 0]
print(f"\ntotal G>0: {len(pos)}/{len(pairs)}   max H with G>0: {max((H for H,_ in pos), default=0):.2f}")
print(f"max G overall: {max((G for _,G in pairs), default=0):.3f}")
deep = [(H,G) for H,G in pos if H >= 8]
print(f"G>0 events at H>=8: {len(deep)}; max G there = {max((G for _,G in deep), default=0):.3f}")
