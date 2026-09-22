from math import log2
from functools import lru_cache
@lru_cache(maxsize=None)
def oscS(c,n):
    if n==0: return 0
    p=oscS(c,n-1); return p+(2 if 2**p<=(2**c)*3**(n-1) else 1)
def oscD(c,n):
    p=oscS(c,n); return 2 if 2**p<=(2**c)*3**n else 1
def leastRealizer(c,N):
    d=[oscD(c,i) for i in range(N)]; S=oscS(c,N)
    q=0
    for i in range(N): q=3*q+2**oscS(c,i)
    M=2**(S+1); return ((2**S-q)%M)*pow(pow(3,-1,M),N,M)%M, S
def full_stats(m,c=1):
    """true occupation and episode count of the GENUINE orbit of m, to arrival at 1"""
    S=0;n=0;x=m;prev=True;re=0;Oc=1
    while x!=1:
        y=3*x+1;d=0
        while y%2==0: y//=2;d+=1
        S+=d;n+=1;x=y
        inC=2**S<=(2**c)*3**n
        if inC and not prev: re+=1
        if inC: Oc+=1
        prev=inC
        if n>2000000: return None
    return re+1,Oc,n
c=1
print(" %4s %10s %10s %12s %10s %10s %12s"%("N","log2 m0","episodes","occupation O1","n*(stop)","O1/log2m0","P/log2m0"))
for N in (10,20,30,40,50,60,70,80):
    m0,S=leastRealizer(c,N)
    st=full_stats(m0,c)
    if st is None: print(" %4d  did not terminate within cap"%N); continue
    P,Oc,nstar=st
    L=log2(m0)
    print(" %4d %10.2f %10d %12d %10d %10.3f %12.3f"%(N,L,P,Oc,nstar,Oc/L,P/L))
