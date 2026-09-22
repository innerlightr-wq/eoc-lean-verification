from fractions import Fraction
from decimal import Decimal, getcontext
getcontext().prec=60
A=Fraction(Decimal(3).ln()/Decimal(2).ln()).limit_denominator(10**30)
def floor_k_alpha(k): return (k*A).numerator//(k*A).denominator
# enumerate zero-confined words: digits>=1, S_k <= floor(k*alpha) for 1<=k<=N
def words(N):
    out=[]
    def rec(k,S,w):
        if k==N: out.append((tuple(w),S)); return
        lim=floor_k_alpha(k+1)
        for d in range(1,lim-S+1):
            rec(k+1,S+d,w+[d])
    rec(0,0,[])
    return out
def leastRealizer(w):
    N=len(w); S=sum(w); q=0; s=0
    for i in range(N): q=3*q+2**s; s+=w[i]
    M=2**(S+1); return ((2**S-q)%M)*pow(pow(3,-1,M),N,M)%M, S
print("Decisive test for candidate C1 (deficit as added datum):")
print("among ZERO-CONFINED words, does a LARGER deficit force a LARGER least realizer?")
print(" %3s %7s %10s %12s %12s %12s"%("N","#words","corr(sign)","minLR@maxDef","minLR@minDef","global minLR"))
import statistics
for N in range(6,17):
    W=words(N)
    rows=[]
    for w,S in W:
        lr,SS=leastRealizer(w)
        defic=floor_k_alpha(N)-SS
        rows.append((defic,lr))
    defs=sorted(set(r[0] for r in rows))
    dmax,dmin=max(defs),min(defs)
    lr_at_max=min(r[1] for r in rows if r[0]==dmax)
    lr_at_min=min(r[1] for r in rows if r[0]==dmin)
    gmin=min(r[1] for r in rows)
    # rank correlation sign between deficit and log2 leastRealizer
    xs=[r[0] for r in rows]; ys=[r[1].bit_length() for r in rows]
    mx,my=statistics.mean(xs),statistics.mean(ys)
    cov=sum((a-mx)*(b-my) for a,b in zip(xs,ys))
    print(" %3d %7d %10s %12d %12d %12d"%(N,len(W),"+" if cov>0 else "-",lr_at_max,lr_at_min,gmin))
print()
print("interpretation: leastRealizer(d,N) < 2^{S_N+1}, and deficit REDUCES S_N.")
print("So a larger deficit tightens the UPPER bound on the least realizer -- the wrong direction")
print("for proving least realizers unbounded. The sign column confirms it empirically.")
