from math import log2
A=log2(3)
def realizes(m,d):
    for x in d:
        y=3*m+1;v=0
        while y%2==0: y//=2;v+=1
        if v!=x: return False
        m=y
    return True
def Lc(m,c):
    """largest N with R_j <= c for all 0<=j<=N (single-window lifetime from the seed)"""
    S=0;n=0
    while True:
        if S-n*A>c: return n-1
        y=3*m+1;d=0
        while y%2==0: y//=2;d+=1
        S+=d;n+=1;m=y
        if n>4000: return n
def rmin_direct(N,c):
    """min odd m with L_c(m) >= N"""
    m=1
    while True:
        if Lc(m,c)>=N: return m
        m+=2
        if m>4*10**6: return None
def words(N,c):
    out=[]
    def rec(k,S,w):
        if k==N: out.append(tuple(w)); return
        # need R_j <= c for j<=N, i.e. 2^{S_j} <= 2^c 3^j
        for d in range(1,6):
            S2=S+d
            if 2**S2 <= (2**c)*3**(k+1): rec(k+1,S2,w+[d])
    rec(0,0,[])
    return out
def leastRealizer(d):
    N=len(d);S=sum(d);q=0;s=0
    for i in range(N): q=3*q+2**s; s+=d[i]
    M=2**(S+1); r=((pow(2,S,M)-q)*pow(pow(3,N,M),-1,M))%M
    return r if r else M
print("prop:inversion:  r_min(N,c) = min{ m odd : L_c(m) >= N }")
print(" %3s %3s %14s %14s %s"%("N","c","min over words","direct search","agree?"))
ok=True
for c in (0,1):
    for N in range(1,13):
        W=words(N,c)
        a=min(leastRealizer(list(d)) for d in W) if W else None
        b=rmin_direct(N,c)
        agree = (a==b)
        ok &= agree
        print(" %3d %3d %14s %14s %s"%(N,c,a,b,"YES" if agree else "*** NO ***"))
print("all agree:",ok)
