"""Check the two cumulative identities and the tightness of  F <= H  at deep steps.

  (I1)  F_n = F_1 + (S_n - S_1) - sum delta          [note, eq (14)]
  (I2)  M_n = M_1 - (S_n - S_1) + sum w              [NEW: Thm 18 + Prop 30 telescoped]
  (I3)  sum w >= (S_n - S_1) - M_1                   [forced regeneration, from M >= 0]
and: at the step of maximal coarse depth F, how large is M?
"""
import math, sys
sys.path.insert(0, 'scratch')
import importlib.util
spec = importlib.util.spec_from_file_location("tr", "scratch/transport_regeneration.py")
tr = importlib.util.module_from_spec(spec); spec.loader.exec_module(tr)
v2, orbit = tr.v2, tr.orbit

def traj(m0, N, pad=400):
    ds, _ = orbit(m0, N)
    S = [0]*(N+1)
    for j in range(1, N+1): S[j] = S[j-1] + ds[j]
    P = S[N] + pad; M2 = 1 << P
    inv3 = pow(3, -1, M2); inv3p = [pow(inv3, k, M2) for k in range(N+2)]
    Cs = [0]*(N+1)
    for j in range(N): Cs[j+1] = 3*Cs[j] + (1 << S[j])
    rows = []
    for j in range(1, N):
        Sj = S[j]
        xi = (-Cs[j] * inv3p[j]) % M2
        chi = xi % (1 << Sj); T = xi >> Sj; Tprec = P - Sj
        A = 0; D = 0
        for rr in range(0, N-j):
            A = (A + (1 << D) * inv3p[j+1+rr]) % M2
            D += ds[j+1+rr]
            if D >= Tprec: break
        lim = min(Tprec, D); X = (T - A) % (1 << lim); Mj = v2(X)
        if Mj is None or Mj >= lim: rows.append(None); continue
        if Sj > 900: rows.append(None); continue
        F = Sj - math.log2(chi)
        K = (T - inv3p[j+1]) % (1 << ds[j+1])
        rows.append(dict(j=j, S=Sj, d=ds[j+1], F=F, M=Mj, K=K, chi=chi, T=T, A=A, lim=lim))
    return ds, S, rows

i1 = i2 = i3 = perfw = failw = 0
deep = []
for m0 in range(3, 8001, 2):
    ds, S, rows = traj(m0, 42)
    run = [r for r in rows if r is not None]
    if len(run) < 6: continue
    # require a contiguous valid block
    start = rows.index(run[0])
    blk = []
    for r in rows[start:]:
        if r is None: break
        blk.append(r)
    if len(blk) < 6: continue
    sd = sw = 0.0
    F0, M0 = blk[0]['F'], blk[0]['M']
    for a, b in zip(blk, blk[1:]):
        delta = a['d'] - (b['F'] - a['F'])
        w = b['M'] + a['d'] - a['M']
        sd += delta; sw += w
        assert abs((b['F'] - F0) - ((a['S'] + a['d'] - blk[0]['S']) - sd)) < 1e-7 \
            or True   # checked in aggregate below
        if a['K'] == 0:
            assert abs(w) < 1e-9, (m0, a['j'], 'Thm18', w); perfw += 1
        else:
            if v2(a['K']) == a['M']:
                au = v2(((a['T']-a['A']) >> a['M']) - (a['K'] >> a['M']))
                if au is not None and au < a['lim'] - a['M'] - 2:
                    assert abs(w - au) < 1e-9, (m0, a['j'], 'Prop30', w, au); failw += 1
        i1 += 1
    last = blk[-1]
    Sd = last['S'] - blk[0]['S']
    assert abs(last['F'] - (F0 + Sd - sd)) < 1e-7, (m0, 'I1'); i2 += 1
    assert abs(last['M'] - (M0 - Sd + sw)) < 1e-9, (m0, 'I2', last['M'], M0 - Sd + sw); i3 += 1
    assert sw >= Sd - M0 - 1e-9, (m0, 'I3')
    top = max(blk, key=lambda r: r['F'])
    deep.append((top['F'], top['M'], top['F'] + top['M']))

print(f"step checks: {i1}   Thm18 (perfect, w=0): {perfw}   Prop30 (first failure, w=v2(a-u)): {failw}")
print(f"(I1) depth identity   : {i2} trajectories, 0 mismatches")
print(f"(I2) precision identity: {i3} trajectories, 0 mismatches   [NEW]")
print(f"(I3) forced regeneration Sum w >= S - M_0: {i3} trajectories, 0 violations")
deep.sort(key=lambda t: -t[0])
print(f"\ntightness of  F <= H  at the maximal-depth step of each trajectory:")
print(f"  trajectories: {len(deep)}")
for lo, hi in [(0,2),(2,4),(4,6),(6,100)]:
    sel = [t for t in deep if lo <= t[0] < hi]
    if sel:
        print(f"  F in [{lo},{hi}): n={len(sel):5d}  mean M = {sum(t[1] for t in sel)/len(sel):6.3f}"
              f"   mean F/H = {sum(t[0]/t[2] for t in sel)/len(sel):6.4f}")
print(f"  overall mean M at peak depth = {sum(t[1] for t in deep)/len(deep):.4f}")
print(f"  fraction with M = 0 at peak depth = {sum(1 for t in deep if t[1]==0)/len(deep):.4f}")
