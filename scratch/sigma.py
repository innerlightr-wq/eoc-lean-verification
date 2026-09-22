from math import log2
A=log2(3)
def stats(m,c):
    """returns (#re-entries, occupation O_c, episode lengths) over the orbit until it reaches 1"""
    S=0;n=0;x=m;inC_prev=True;re=0;Oc=1;runs=[];k=1
    while x!=1:
        y=3*x+1;d=0
        while y%2==0: y//=2;d+=1
        S+=d;n+=1;x=y
        inC = 2**S <= (2**c)*3**n
        if inC and not inC_prev: re+=1
        if inC: Oc+=1;k+=1
        else:
            if k: runs.append(k)
            k=0
        inC_prev=inC
        if n>100000: break
    if k: runs.append(k)
    return re,Oc,runs

print("=== sigma_c(p): least odd seed whose orbit has at least p corridor re-entries ===")
for c in (0,1):
    best={}
    for m in range(1,4000001,2):
        re,_,_=stats(m,c)
        for p in range(1,re+1):
            if p not in best: best[p]=m
    print(" c=%d"%c)
    print("   %3s %14s %10s %12s"%("p","sigma_c(p)","log2","log2/p"))
    for p in sorted(best):
        if p<=14: print("   %3d %14d %10.3f %12.3f"%(p,best[p],log2(best[p]),log2(best[p])/p))
