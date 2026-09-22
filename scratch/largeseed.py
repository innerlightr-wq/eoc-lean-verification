from functools import lru_cache
from math import log2
@lru_cache(maxsize=None)
def oscS(c,n):
    if n==0: return 0
    p=oscS(c,n-1); return p+(2 if 2**p<=(2**c)*3**(n-1) else 1)
def oscD(c,n):
    p=oscS(c,n); return 2 if 2**p<=(2**c)*3**n else 1
def InC(c,n): return 2**oscS(c,n)<=(2**c)*3**n
def exits(c,N): return [n for n in range(N) if not InC(c,n)]
def leastRealizer(c,N):
    S=oscS(c,N); q=0
    for i in range(N): q=3*q+2**oscS(c,i)
    M=2**(S+1); return ((2**S-q)%M)*pow(pow(3,-1,M),N,M)%M
def check(c,N,m0):
    m=m0
    for i in range(N):
        y=3*m+1;d=0
        while y%2==0: y//=2;d+=1
        if d!=oscD(c,i): return False
        m=y
    return True

c=1; e=exits(c,20000); e0=e[0]
print("exists_large_realizer: r + 2^(S_N+1)*(M+1) realizes the same prefix (c=1)")
print(" %4s %4s %6s %10s %12s %10s %10s"%("B","N","t","log2 m0","realizes?","odd?","ratio bd"))
for B in (5,10):
    N=e[B]+1; r=leastRealizer(c,N); S=oscS(c,N); mod=2**(S+1)
    occ=sum(1 for n in range(N) if InC(c,n))
    for t in (0,1,10**6,10**30):
        m0=r+mod*t
        L=log2(m0)
        # surrogate charge Q >= (B+1)(L-c); actual prefix occupation = occ <= e0+2B
        ratio_lb=(L-c)/(2+e0)
        print(" %4d %4d %6s %10.1f %12s %10s %10.1f"%(B,N,("%.0e"%t if t else "0"),L,
              check(c,N,m0),m0%2==1,ratio_lb))
    print("     occ(prefix)=%d, e0+2B=%d, (B+1)(L-c)/occ for t=1e30 : %.1f"%(
        occ,e0+2*B,(B+1)*(log2(r+mod*10**30)-c)/occ))
print("\n=> seeds unbounded BY CONSTRUCTION; prefix episode data unchanged; ratio grows without bound")
