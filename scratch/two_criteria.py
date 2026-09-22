"""D.9 uses  v2(a-u) > H_tr ;  a budget INCREASE needs  v2(a-u) > delta_fail.
Cor 34 gives delta_fail > H_tr strictly, so the two differ by the wedge
   w := delta_fail - H_tr = log2(1 + 2^{F+M} u) - (F+M)  ~=  log2 u.
Count both criteria separately."""
import math, sys
sys.path.insert(0, 'scratch')
from transport_regeneration import v2, orbit

def scan(m0, N, pad=300):
    ds, ms = orbit(m0, N)
    S = [0]*(N+1)
    for j in range(1, N+1): S[j] = S[j-1] + ds[j]
    P = S[N] + pad; M2 = 1 << P
    inv3 = pow(3, -1, M2); inv3p = [pow(inv3, k, M2) for k in range(N+2)]
    Cs = [0]*(N+1)
    for j in range(N): Cs[j+1] = 3*Cs[j] + (1 << S[j])
    out = []
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
        if F > 800: continue
        K = (T - inv3p[j+1]) % (1 << dn)
        if K == 0 or v2(K) != Mj: continue
        a = X >> Mj; u = K >> Mj
        au = v2((a - u) % (1 << (lim - Mj)))
        if au is None or au >= lim - Mj - 2: continue
        delta = math.log2(1 + 2.0**F * K)
        out.append((H, au, delta, math.log2(u)))
    return out

pairs = []
for m0 in range(3, 200001, 2):
    try: pairs += scan(m0, 50)
    except Exception: pass
print(f"genuine first-failure events: {len(pairs)}")
print(f"{'H bin':>6} {'events':>8} {'v2>H':>8} {'v2>delta':>9} {'maxG':>8} {'med wedge':>10}")
bins = {}
for H, au, delta, lu in pairs:
    b = int(H); bins.setdefault(b, []).append((au, delta, H, lu))
tot_w, tot_s = 0, 0
for b in sorted(bins):
    v = bins[b]
    if len(v) < 3: continue
    nw = sum(1 for au, d, H, lu in v if au > H)
    ns = sum(1 for au, d, H, lu in v if au > d)
    mg = max(au - d for au, d, H, lu in v)
    wedges = sorted(d - H for au, d, H, lu in v)
    med = wedges[len(wedges)//2]
    tot_w += nw; tot_s += ns
    print(f"{b:>6} {len(v):>8} {nw:>8} {ns:>9} {mg:>8.3f} {med:>10.3f}")
print(f"\nTOTAL   v2(a-u) > H_tr : {tot_w}      v2(a-u) > delta_fail : {tot_s}")
deep = [(H,au,d,lu) for H,au,d,lu in pairs if H >= 8]
print(f"events with H>=8: {len(deep)}")
print(f"   of these, v2(a-u) > H_tr    : {sum(1 for H,au,d,lu in deep if au > H)}")
print(f"   of these, v2(a-u) > delta   : {sum(1 for H,au,d,lu in deep if au > d)}")
print(f"   max (v2 - H)  on H>=8       : {max((au-H for H,au,d,lu in deep), default=0):.3f}")
print(f"   max (v2 - delta) on H>=8    : {max((au-d for H,au,d,lu in deep), default=0):.3f}")
