from functools import lru_cache
from math import log2
@lru_cache(maxsize=None)
def oscS(c,n):
    if n==0: return 0
    p=oscS(c,n-1); return p+(2 if 2**p<=(2**c)*3**(n-1) else 1)
def InC(c,n): return 2**oscS(c,n) <= (2**c)*3**n
def exits(c,N): return [n for n in range(N) if not InC(c,n)]

print("=== exit gaps: claim  exitTime(i+1) <= exitTime(i) + 3 ===")
for c in (0,1,2,5):
    e=exits(c,4000)
    gaps=[e[i+1]-e[i] for i in range(len(e)-1)]
    print("  c=%d  first exit e0=%3d  #exits<4000=%4d  gap set=%s  max gap=%d"%(
        c,e[0],len(e),sorted(set(gaps)),max(gaps)))

print("\n=== prefix occupation vs exits, N = exitTime(B)+1 ===")
c=1; e=exits(c,20000)
print("  %4s %6s %7s %9s %11s %14s"%("B","N","#exits","occ(prefix)","e0+2B bound","2N+1 (log2 m0 cap)"))
for B in (5,10,20,40,80):
    N=e[B]+1
    occ=sum(1 for n in range(N) if InC(c,n))
    print("  %4d %6d %7d %9d %11d %14d"%(B,N,len([x for x in e if x<N]),occ,e[0]+2*B,2*N+1))
    assert occ <= e[0]+2*B, "prefix occupation bound fails"
    assert N <= e[0]+3*B+1, "linear exit-time bound fails"
print("  all asserted bounds hold")

print("\n=== post-arrival tail: corridor times after the orbit reaches 1 ===")
print("  claim: m_n=1 for n>=n* forces 4^k <= 2^c 3^k, so k <= 3*2^c - 3 (Bernoulli)")
for c in (0,1,2,5,8):
    k=0
    while 4**k <= (2**c)*3**k: k+=1
    print("   c=%2d : true max tail index k = %3d ; Bernoulli bound 3*2^c-3 = %5d"%(c,k-1,3*2**c-3))

print("\n=== the packaged bounds of many_reentries_with_small_seed, checked numerically ===")
def leastRealizer(c,N):
    S=oscS(c,N); q=0
    for i in range(N): q=3*q+2**oscS(c,i)
    M=2**(S+1); return ((2**S-q)%M)*pow(pow(3,-1,M),N,M)%M
for c in (0,1,2):
    e=exits(c,20000); e0=e[0]
    print("  c=%d (e0=%d)"%(c,e0))
    print("    %4s %6s %14s %16s %12s %12s"%("B","N","log2 m0","6B+2e0+3","occ(prefix)","e0+2B"))
    for B in (5,10,20,40):
        N=e[B]+1; m0=leastRealizer(c,N)
        occ=sum(1 for n in range(N) if InC(c,n))
        lg=log2(m0) if m0>0 else 0
        ok1 = m0 < 2**(6*B+2*e0+3); ok2 = occ <= e0+2*B
        print("    %4d %6d %14.2f %16d %12d %12d  %s"%(B,N,lg,6*B+2*e0+3,occ,e0+2*B,
              "OK" if (ok1 and ok2) else "FAIL"))
        assert ok1 and ok2
    print("    B >= (log2 m0 - 2e0 - 3)/6 holds for all rows above")
