from decimal import Decimal, getcontext
from math import comb, log, log2
getcontext().prec=50
def D(x): return Decimal(str(x))
L2=Decimal(2).ln()
lam=Decimal(3).ln()/L2
def H(p):
    p=Decimal(p); return (-p*p.ln()-(1-p)*(1-p).ln())/L2
def f(x): return H(x)-Decimal(x)*lam
lo,hi=Decimal('0.5000001'),Decimal('0.6299')
for _ in range(200):
    mid=(lo+hi)/2
    if f(mid)>0: lo=mid
    else: hi=mid
g=(lo+hi)/2
print("=== Theorem 2.3 optimization ===")
print("  lambda = log2 3 = %s"%str(lam)[:14])
print("  1/lambda        = %s"%str(1/lam)[:14])
print("  gamma* (root of H(g)=g*lambda) = %s    paper: 0.6090897..."%str(g)[:14])
print("  H(gamma*)       = %s"%str(H(g))[:14])
print("  gamma*.lambda   = %s"%str(g*lam)[:14])
print("  beta*           = %s    paper: 0.9653844..."%str(g*lam)[:14])
print("  1/beta*         = %s    paper: 1.0358567..."%str(1/(g*lam))[:14])
print("  beta* < 1 ?  %s   <-- ESSENTIAL for the Prop 3.1 dyadic sum"%(g*lam<1))
print("  gamma* in (1/2, 1/lambda)?  %s"%(Decimal('0.5')<g<1/lam))
print("\n  max(H(gamma), gamma*lambda) near the crossing:")
for x in ['0.52','0.58','0.6090897','0.62','0.6309']:
    xx=D(x); print("    gamma=%-10s H=%-12s g.lam=%-12s max=%s"%(x,str(H(xx))[:10],str(xx*lam)[:10],str(max(H(xx),xx*lam))[:10]))
print("\n=== entropy bound  sum_{i >= gamma N} C(N,i) <= 2^{N H(gamma)}   (gamma >= 1/2) ===")
bad=[]
for N in range(1,300):
    for gg in ['0.5','0.55','0.6090897','0.65','0.7','0.9']:
        thr=D(gg)*N
        start=int(thr) if thr==int(thr) else int(thr)+1
        lhs=sum(comb(N,i) for i in range(start,N+1))
        rhs=float(2)**float(N*H(D(gg)))
        if lhs>rhs*(1+1e-9): bad.append((N,gg,lhs,rhs))
print("  violations over N<=299 x 6 values of gamma: %d  %s"%(len(bad),bad[:3]))
print("\n=== Rozier identification: H(g)=g*lambda  <=>  H(g)/g = lambda ===")
print("  H(gamma*)/gamma* = %s ;  lambda = %s"%(str(H(g)/g)[:14],str(lam)[:14]))
print("\n=== Prop 3.1 dyadic sum converges iff beta < 1 ===")
for b in ['0.9653844','0.99','1.0','1.01']:
    bb=float(b); s=sum((i+2)*2**(i*bb)*2**(-i) for i in range(0,400))
    print("   beta=%-10s partial sum_{i<400} (i+2)2^{i(beta-1)} = %s"%(b, ("%.4g"%s) if s<1e30 else "DIVERGES"))
