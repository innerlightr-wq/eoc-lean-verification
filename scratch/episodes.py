"""Exact episode decomposition of the corridor {n : R_n <= c}.

Restart relation (exact):  R_{a+k}(m_0) = R_a(m_0) + R_k(m_a),
since valuations concatenate: S_{a+k}(m_0) = S_a(m_0) + S_k(m_a).

Episode i occupies [a_i, b_i], length l_i = b_i - a_i + 1, and for n = a_i + k,
    R_n <= c   <=>   R_k(m_{a_i}) <= c_i,      c_i := c - R_{a_i}(m_0) >= 0.
So l_i = 1 + L_{c_i}(m_{a_i}): each episode is the initial confined window of the
RESTARTED orbit at its own LOCAL threshold.  O_c = sum_i l_i.

THE NAIVE BOUND.  A corridor-uniform single-window bound L_{c'}(m) <= K(log2 m + c')
gives, via the orbit-floor identity log2 m_{a_i} = log2 m_0 - R_{a_i} + E_{a_i},

    l_i <= 1 + K(log2 m_0 + E_{a_i} + c - 2 R_{a_i}).

Every summand is >= log2 m_0 - 2c.  Hence  O_c >= P (log2 m_0 - 2c)  is the scale of
the bound, so the route yields O(log m_0) ONLY IF the episode count P is O(1).

This script measures P.
"""
import math
alpha = math.log2(3)
def v2(x):
    r=0
    while x&1==0: x>>=1; r+=1
    return r

def episodes(m0, c=1.0, cap=5000):
    mi=m0; S=0; n=0; E=0.0
    inC=None; eps=[]; a=None; Rs=[]; ms=[]
    Rmin=0.0
    while True:
        R = S - alpha*n
        Rmin=min(Rmin,R)
        cur = (R <= c)
        if cur and not inC:
            a=n; a_m=mi; a_R=R
        if (not cur) and inC:
            eps.append((a, n-1, n-a, a_m, a_R))
        inC=cur
        if mi==1 and n>0: break
        t=3*mi+1; d=v2(t); E += math.log2(1+1/(3*mi))
        S += d; mi = t>>d; n += 1
        if n>cap: return None
    if inC: eps.append((a, n, n-a+1, a_m, a_R))
    return eps, E, Rmin, n

print(f"{'m0':>9} {'log2m0':>7} {'O_c':>6} {'P':>4} {'maxl':>5} {'O/log2m0':>9} {'P/log2m0':>9} {'min R_a':>8} {'-Rmin':>7}")
rows=[]
for m0 in [27, 703, 6171, 285175, 837799, 1723519, 6649279, 8400511, 63728127]:
    r = episodes(m0, c=1.0)
    if r is None: continue
    eps,E,Rmin,tot = r
    O = sum(e[2] for e in eps); P=len(eps); ml=max(e[2] for e in eps)
    l2=math.log2(m0); minRa=min(e[4] for e in eps)
    rows.append((m0,l2,O,P,ml,minRa,-Rmin))
    print(f"{m0:>9} {l2:>7.2f} {O:>6} {P:>4} {ml:>5} {O/l2:>9.3f} {P/l2:>9.3f} {minRa:>8.3f} {-Rmin:>7.2f}")

print()
print("Scan: how does P grow with log2 m0?")
import statistics
buckets={}
for m0 in range(3, 300001, 2):
    r = episodes(m0, c=1.0)
    if r is None: continue
    eps,E,Rmin,tot = r
    O=sum(e[2] for e in eps); P=len(eps)
    b=int(math.log2(m0))
    buckets.setdefault(b,[]).append((O,P))
print(f"{'log2 m0':>8} {'seeds':>7} {'mean O':>8} {'max O':>6} {'mean P':>7} {'max P':>6} {'max O/log2m0':>13}")
for b in sorted(buckets):
    v=buckets[b]
    if len(v)<5: continue
    Os=[x[0] for x in v]; Ps=[x[1] for x in v]
    print(f"{b:>8} {len(v):>7} {statistics.mean(Os):>8.2f} {max(Os):>6} {statistics.mean(Ps):>7.2f} {max(Ps):>6} {max(Os)/max(b,1):>13.3f}")
