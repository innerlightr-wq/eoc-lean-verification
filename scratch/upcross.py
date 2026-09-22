"""Each episode after the first is an UP-CROSSING of the fixed level Lam = m_0 2^{E-c}.
Since m_{n+1} = (3m_n+1)/2^{d} <= (3m_n+1)/2, an up-crossing from below Lam must land in
[Lam, 1.5*Lam + 1).  The landing points are DISTINCT orbit values (injectivity).

So P <= #{distinct odd integers in [Lam, 1.5 Lam)} ~ Lam/4 -- a resource that is not
double counted, but is EXPONENTIALLY larger than the O(1) needed.
"""
import math
alpha=math.log2(3)
def v2(x):
    r=0
    while x&1==0: x>>=1; r+=1
    return r

bad=0; tot=0; land={}
maxP=0
for m0 in range(3, 120001, 2):
    mi=m0; S=0; n=0; E=0.0; inC=None; P=0; prev=None; lands=[]
    while n<5000:
        R=S-alpha*n
        cur=(R<=1.0)
        if cur and not inC and n>0:
            # an up-crossing: previous value was below the level, this one at/above
            lam = m0*2**(E-1.0)
            tot+=1
            if not (lam <= mi < 1.5*lam + 1.0000001): bad+=1
            lands.append(mi)
        if cur and not inC: P+=1
        inC=cur
        if mi==1 and n>0: break
        t=3*mi+1; d=v2(t); E+=math.log2(1+1/(3*mi)); S+=d; mi=t>>d; n+=1
    maxP=max(maxP,P)
    if len(lands)!=len(set(lands)): print("REPEAT LANDING at", m0)

print(f"up-crossings examined: {tot}")
print(f"  landing outside [Lam, 1.5 Lam + 1): {bad}")
print(f"  landing points distinct within each orbit: yes (no repeats found)")
print(f"  max P over odd m0 < 120001: {maxP}")
print()
print("So each return consumes a distinct orbit value in a band of multiplicative width 1.5")
print("just above the starting scale.  That band holds ~ m_0 2^{-c}/4 odd integers --")
print("exponentially many in log2 m_0, so the resource cannot yield P = O(1).")
