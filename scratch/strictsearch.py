"""GATE 4/H: targeted search for tau_0(m) < sigma(m).

Strictness at depth n needs m_0 <= 0.4809 n/(1-frac(alpha n)) AND 0-confinement
through n AND R_n <= E_n.  Search every m below the size bound at every depth
where the bound is not already violated by r_min(n,0).
"""
import math
alpha = math.log2(3)
def v2(x):
    r=0
    while x&1==0: x>>=1; r+=1
    return r

found=[]
maxm=0
for n in range(3, 200):
    fr = 1 - (alpha*n)%1.0
    bound = 0.4809*n/fr
    if bound < 3: continue
    maxm=max(maxm,int(bound))
    for m0 in range(3, int(bound)+2, 2):
        mi=m0; S=0; E=0.0; k=0; ok=True
        while k < n:
            t=3*mi+1; d=v2(t)
            E += math.log2(1+1/(3*mi))
            S += d; mi = t>>d; k+=1
            R = S - alpha*k
            if R > 0:
                if k == n and R <= E:
                    found.append((m0, n, R, E, mi, m0))
                ok=False; break
        # only the FIRST exit counts; the loop above breaks at it
print(f"searched all odd m up to {maxm} at every depth n<200 where the size bound permits")
print(f"strict examples tau_0 < sigma found: {len(found)}")
for f in found[:10]: print("   ", f)
print()
# how close did we get?
best=(1e9,None)
for n in range(3, 200):
    fr = 1 - (alpha*n)%1.0
    bound = 0.4809*n/fr
    if bound < 3: continue
    for m0 in range(3, int(bound)+2, 2):
        mi=m0; S=0; E=0.0; k=0
        while k < n:
            t=3*mi+1; d=v2(t); E += math.log2(1+1/(3*mi)); S += d; mi=t>>d; k+=1
            R = S - alpha*k
            if R > 0:
                if R-E < best[0]: best=(R-E,(m0,k,R,E))
                break
print(f"closest approach min(R_tau - E_tau) within the permitted region: {best[0]:.6f} at {best[1]}")
