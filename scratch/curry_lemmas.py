def T(n): return n//2 if n%2==0 else (3*n+1)//2
def Tk(n,k):
    for _ in range(k): n=T(n)
    return n
def mN(n,N):
    c=0
    for _ in range(N):
        if n%2: c+=1
        n=T(n)
    return c
print("=== Lemma 2.1: prefix depends only on n mod 2^N, and is a BIJECTION Z/2^N -> {0,1}^N ===")
bad=0
for N in range(0,13):
    seen={}
    for r in range(2**N):
        pref=tuple((Tk(r,j))%2 for j in range(N))
        seen.setdefault(pref,[]).append(r)
    if len(seen)!=2**N: bad+=1
    # residue-dependence check on representatives beyond the first period
    for r in range(2**N):
        p1=tuple((Tk(r,j))%2 for j in range(N))
        p2=tuple((Tk(r+3*2**N,j))%2 for j in range(N))
        if p1!=p2: bad+=1
print("  bijection + residue-dependence, N<=12 : %d failures"%bad)

print("\n=== Lemma 2.1 formula:  T^N(n + r 2^N) = T^N(n) + r 3^{m_N(n)} ===")
bad=0; cnt=0
for N in range(0,11):
    for n in range(1,400):
        m=mN(n,N)
        for r in range(0,6):
            cnt+=1
            if Tk(n+r*2**N,N)!=Tk(n,N)+r*3**m: bad+=1
print("  %d identities checked, %d failures"%(cnt,bad))

print("\n=== Lemma 2.2:  T^N(n) < 3^{m_N(n)} (2^{-N} n + 1)   (N>=1) ===")
bad=0; cnt=0; tight=0
for N in range(1,13):
    for n in range(1,3000):
        m=mN(n,N); cnt+=1
        if not (Tk(n,N) < 3**m*(n/2**N + 1)): bad+=1
print("  %d cases, %d failures"%(cnt,bad))

print("\n=== Thm 2.3 covering step: every y in [a,a+X) has y-z2^N or y-(z+1)2^N in [1,X] ===")
import math
bad=0; cnt=0
for X in range(2,400):
    N=X.bit_length()-1          # floor(log2 X)
    assert 2**N<=X<2**(N+1)
    for a in range(1,200):
        z=(a-1)//2**N           # z2^N < a <= (z+1)2^N
        assert z*2**N < a <= (z+1)*2**N
        for y in range(a,a+X):
            cnt+=1
            ok = (1<=y-z*2**N<=X) or (1<=y-(z+1)*2**N<=X)
            if not ok: bad+=1
print("  %d points checked over X<400, a<200 : %d failures"%(cnt,bad))

print("\n=== residue class mod 2^N meets [1,X] in <= X/2^N + 1 <= 3 points (since X < 2^{N+1}) ===")
bad=0
for X in range(2,600):
    N=X.bit_length()-1
    for c in range(2**N):
        k=len([s for s in range(1,X+1) if s%2**N==c])
        if k>3 or k>X/2**N+1: bad+=1
print("  failures: %d"%bad)
