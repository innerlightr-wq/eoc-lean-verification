import random
from math import log2
def stats(m,c=1):
    S=0;n=0;x=m;prev=True;re=0;Oc=1;runs=[];k=1
    while x!=1:
        y=3*x+1;d=0
        while y%2==0: y//=2;d+=1
        S+=d;n+=1;x=y
        inC = 2**S <= (2**c)*3**n
        if inC and not prev: re+=1
        if inC: Oc+=1;k+=1
        else:
            if k: runs.append(k)
            k=0
        prev=inC
    if k: runs.append(k)
    return re,Oc,runs
random.seed(20260922)
print("controlled: 2000 random odd seeds per bucket, c=1")
print(" %6s %8s %8s %9s %9s %9s"%("log2m0","meanP","maxP","meanLen","maxLen","meanO1"))
for b in range(13,25):
    lo,hi=2**b,2**(b+1)
    Ps=[];Ls=[];Os=[]
    for _ in range(2000):
        m=random.randrange(lo,hi)|1
        re,Oc,runs=stats(m)
        Ps.append(re+1); Os.append(Oc); Ls+= runs
    print(" %6d %8.3f %8d %9.3f %9d %9.3f"%(b,sum(Ps)/len(Ps),max(Ps),sum(Ls)/len(Ls),max(Ls),sum(Os)/len(Os)))
